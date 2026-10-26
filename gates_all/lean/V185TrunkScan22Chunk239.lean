import V185TrunkScan22Chunk238

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2130942 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_2130942 : Nat := 118140960795 + 2130942 * 2 ^ 59
def prefixEnd_2130942 : Nat := 4983230072969 + 3 ^ 40 * 2130942 * 2
def baseEnd_2130942 : Nat := 243154998411845980738885

theorem tailTrace_2130942 : CollatzResearch.WordTrace tailWord_2130942 prefixEnd_2130942 243154998411845980738885 := by
  unfold tailWord_2130942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715229980746068095536385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51814559897312363176194053 9715229980746068095536385)
  ·
    refine ⟨7286422485559551071652289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9715229980746068095536385 7286422485559551071652289)
    ·
      refine ⟨5464816864169663303739217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7286422485559551071652289 5464816864169663303739217)
      ·
        refine ⟨4098612648127247477804413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5464816864169663303739217 4098612648127247477804413)
        ·
          refine ⟨1536979743047717804176655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4098612648127247477804413 1536979743047717804176655)
          ·
            refine ⟨2305469614571576706264983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536979743047717804176655 2305469614571576706264983)
            ·
              refine ⟨3458204421857365059397475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305469614571576706264983 3458204421857365059397475)
              ·
                refine ⟨5187306632786047589096213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458204421857365059397475 5187306632786047589096213)
                ·
                  refine ⟨243154998411845980738885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5187306632786047589096213 243154998411845980738885)
                  ·
                    rfl

theorem cell22_2130942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_2130942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2130942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2130942 prefixEnd_2130942 := by exact prefixLift 2130942
  have htrace : WordTrace (prefixWord ++ tailWord_2130942) baseStart_2130942 baseEnd_2130942 := by
    simpa [prefixWord, tailWord_2130942, baseEnd_2130942] using wordTrace_append hprefix tailTrace_2130942
  have hstable : (prefixWord ++ tailWord_2130942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2130942).length < 2 ^ (prefixWord ++ tailWord_2130942).sum := by decide
  have hdescent : baseEnd_2130942 < baseStart_2130942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2130942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131002 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_2131002 : Nat := 118140960795 + 2131002 * 2 ^ 59
def prefixEnd_2131002 : Nat := 4983230072969 + 3 ^ 40 * 2131002 * 2
def baseEnd_2131002 : Nat := 729485534461717785716471

theorem tailTrace_2131002 : CollatzResearch.WordTrace tailWord_2131002 prefixEnd_2131002 729485534461717785716471 := by
  unfold tailWord_2131002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19431007056437793752868815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51816018817167450007650173 19431007056437793752868815)
  ·
    refine ⟨29146510584656690629303223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19431007056437793752868815 29146510584656690629303223)
    ·
      refine ⟨43719765876985035943954835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29146510584656690629303223 43719765876985035943954835)
      ·
        refine ⟨65579648815477553915932253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43719765876985035943954835 65579648815477553915932253)
        ·
          refine ⟨24592368305804082718474595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65579648815477553915932253 24592368305804082718474595)
          ·
            refine ⟨36888552458706124077711893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24592368305804082718474595 36888552458706124077711893)
            ·
              refine ⟨1729150896501849566142745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36888552458706124077711893 1729150896501849566142745)
              ·
                refine ⟨1296863172376387174607059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729150896501849566142745 1296863172376387174607059)
                ·
                  refine ⟨1945294758564580761910589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296863172376387174607059 1945294758564580761910589)
                  ·
                    refine ⟨729485534461717785716471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945294758564580761910589 729485534461717785716471)
                    ·
                      rfl

theorem cell22_2131002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_2131002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131002 prefixEnd_2131002 := by exact prefixLift 2131002
  have htrace : WordTrace (prefixWord ++ tailWord_2131002) baseStart_2131002 baseEnd_2131002 := by
    simpa [prefixWord, tailWord_2131002, baseEnd_2131002] using wordTrace_append hprefix tailTrace_2131002
  have hstable : (prefixWord ++ tailWord_2131002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131002).length < 2 ^ (prefixWord ++ tailWord_2131002).sum := by decide
  have hdescent : baseEnd_2131002 < baseStart_2131002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131011 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_2131011 : Nat := 118140960795 + 2131011 * 2 ^ 59
def prefixEnd_2131011 : Nat := 4983230072969 + 3 ^ 40 * 2131011 * 2
def baseEnd_2131011 : Nat := 729488615345644762241443

theorem tailTrace_2131011 : CollatzResearch.WordTrace tailWord_2131011 prefixEnd_2131011 729488615345644762241443 := by
  unfold tailWord_2131011
  simp only [CollatzResearch.WordTrace]
  refine ⟨77724356482718569548552887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51816237655145713032368591 77724356482718569548552887)
  ·
    refine ⟨116586534724077854322829331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77724356482718569548552887 116586534724077854322829331)
    ·
      refine ⟨174879802086116781484243997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116586534724077854322829331 174879802086116781484243997)
      ·
        refine ⟨65579925782293793056591499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174879802086116781484243997 65579925782293793056591499)
        ·
          refine ⟨98369888673440689584887249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65579925782293793056591499 98369888673440689584887249)
          ·
            refine ⟨73777416505080517188665437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98369888673440689584887249 73777416505080517188665437)
            ·
              refine ⟨27666531189405193945749539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73777416505080517188665437 27666531189405193945749539)
              ·
                refine ⟨41499796784107790918624309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27666531189405193945749539 41499796784107790918624309)
                ·
                  refine ⟨3890605948510105398621029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41499796784107790918624309 3890605948510105398621029)
                  ·
                    refine ⟨729488615345644762241443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890605948510105398621029 729488615345644762241443)
                    ·
                      rfl

theorem cell22_2131011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_2131011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131011 prefixEnd_2131011 := by exact prefixLift 2131011
  have htrace : WordTrace (prefixWord ++ tailWord_2131011) baseStart_2131011 baseEnd_2131011 := by
    simpa [prefixWord, tailWord_2131011, baseEnd_2131011] using wordTrace_append hprefix tailTrace_2131011
  have hstable : (prefixWord ++ tailWord_2131011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131011).length < 2 ^ (prefixWord ++ tailWord_2131011).sum := by decide
  have hdescent : baseEnd_2131011 < baseStart_2131011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131028 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2131028 : Nat := 118140960795 + 2131028 * 2 ^ 59
def prefixEnd_2131028 : Nat := 4983230072969 + 3 ^ 40 * 2131028 * 2
def baseEnd_2131028 : Nat := 729494434793062384566391

theorem tailTrace_2131028 : CollatzResearch.WordTrace tailWord_2131028 prefixEnd_2131028 729494434793062384566391 := by
  unfold tailWord_2131028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38862488261828490725960869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51816651015771320967947825 38862488261828490725960869)
  ·
    refine ⟨7286716549092842011117663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38862488261828490725960869 7286716549092842011117663)
    ·
      refine ⟨10930074823639263016676495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7286716549092842011117663 10930074823639263016676495)
      ·
        refine ⟨16395112235458894525014743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930074823639263016676495 16395112235458894525014743)
        ·
          refine ⟨24592668353188341787522115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16395112235458894525014743 24592668353188341787522115)
          ·
            refine ⟨36889002529782512681283173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24592668353188341787522115 36889002529782512681283173)
            ·
              refine ⟨6916687974334221127740595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36889002529782512681283173 6916687974334221127740595)
              ·
                refine ⟨10375031961501331691610893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6916687974334221127740595 10375031961501331691610893)
                ·
                  refine ⟨3890636985562999384354085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10375031961501331691610893 3890636985562999384354085)
                  ·
                    refine ⟨729494434793062384566391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890636985562999384354085 729494434793062384566391)
                    ·
                      rfl

theorem cell22_2131028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2131028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131028 prefixEnd_2131028 := by exact prefixLift 2131028
  have htrace : WordTrace (prefixWord ++ tailWord_2131028) baseStart_2131028 baseEnd_2131028 := by
    simpa [prefixWord, tailWord_2131028, baseEnd_2131028] using wordTrace_append hprefix tailTrace_2131028
  have hstable : (prefixWord ++ tailWord_2131028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131028).length < 2 ^ (prefixWord ++ tailWord_2131028).sum := by decide
  have hdescent : baseEnd_2131028 < baseStart_2131028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131073 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2131073 : Nat := 118140960795 + 2131073 * 2 ^ 59
def prefixEnd_2131073 : Nat := 4983230072969 + 3 ^ 40 * 2131073 * 2
def baseEnd_2131073 : Nat := 729509839212697267191253

theorem tailTrace_2131073 : CollatzResearch.WordTrace tailWord_2131073 prefixEnd_2131073 729509839212697267191253 := by
  unfold tailWord_2131073
  simp only [CollatzResearch.WordTrace]
  refine ⟨77726617808493954137309873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51817745205662636091539915 77726617808493954137309873)
  ·
    refine ⟨58294963356370465602982405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77726617808493954137309873 58294963356370465602982405)
    ·
      refine ⟨10930305629319462300559201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58294963356370465602982405 10930305629319462300559201)
      ·
        refine ⟨8197729221989596725419401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10930305629319462300559201 8197729221989596725419401)
        ·
          refine ⟨6148296916492197544064551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8197729221989596725419401 6148296916492197544064551)
          ·
            refine ⟨9222445374738296316096827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148296916492197544064551 9222445374738296316096827)
            ·
              refine ⟨13833668062107444474145241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222445374738296316096827 13833668062107444474145241)
              ·
                refine ⟨10375251046580583355608931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13833668062107444474145241 10375251046580583355608931)
                ·
                  refine ⟨15562876569870875033413397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10375251046580583355608931 15562876569870875033413397)
                  ·
                    refine ⟨729509839212697267191253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15562876569870875033413397 729509839212697267191253)
                    ·
                      rfl

theorem cell22_2131073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2131073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131073 prefixEnd_2131073 := by exact prefixLift 2131073
  have htrace : WordTrace (prefixWord ++ tailWord_2131073) baseStart_2131073 baseEnd_2131073 := by
    simpa [prefixWord, tailWord_2131073, baseEnd_2131073] using wordTrace_append hprefix tailTrace_2131073
  have hstable : (prefixWord ++ tailWord_2131073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131073).length < 2 ^ (prefixWord ++ tailWord_2131073).sum := by decide
  have hdescent : baseEnd_2131073 < baseStart_2131073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131126 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2131126 : Nat := 118140960795 + 2131126 * 2 ^ 59
def prefixEnd_2131126 : Nat := 4983230072969 + 3 ^ 40 * 2131126 * 2
def baseEnd_2131126 : Nat := 729527982195822795616091

theorem tailTrace_2131126 : CollatzResearch.WordTrace tailWord_2131126 prefixEnd_2131126 729527982195822795616091 := by
  unfold tailWord_2131126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858034429831371511811827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51819033918201296125992821 4858034429831371511811827)
  ·
    refine ⟨7287051644747057267717741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4858034429831371511811827 7287051644747057267717741)
    ·
      refine ⟨2732644366780146475394153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7287051644747057267717741 2732644366780146475394153)
      ·
        refine ⟨2049483275085109856545615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2732644366780146475394153 2049483275085109856545615)
        ·
          refine ⟨3074224912627664784818423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049483275085109856545615 3074224912627664784818423)
          ·
            refine ⟨4611337368941497177227635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074224912627664784818423 4611337368941497177227635)
            ·
              refine ⟨6917006053412245765841453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4611337368941497177227635 6917006053412245765841453)
              ·
                refine ⟨2593877270029592162190545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6917006053412245765841453 2593877270029592162190545)
                ·
                  refine ⟨1945407952522194121642909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593877270029592162190545 1945407952522194121642909)
                  ·
                    refine ⟨729527982195822795616091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945407952522194121642909 729527982195822795616091)
                    ·
                      rfl

theorem cell22_2131126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2131126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131126 prefixEnd_2131126 := by exact prefixLift 2131126
  have htrace : WordTrace (prefixWord ++ tailWord_2131126) baseStart_2131126 baseEnd_2131126 := by
    simpa [prefixWord, tailWord_2131126, baseEnd_2131126] using wordTrace_append hprefix tailTrace_2131126
  have hstable : (prefixWord ++ tailWord_2131126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131126).length < 2 ^ (prefixWord ++ tailWord_2131126).sum := by decide
  have hdescent : baseEnd_2131126 < baseStart_2131126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131210 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_2131210 : Nat := 118140960795 + 2131210 * 2 ^ 59
def prefixEnd_2131210 : Nat := 4983230072969 + 3 ^ 40 * 2131210 * 2
def baseEnd_2131210 : Nat := 729556737112474576515833

theorem tailTrace_2131210 : CollatzResearch.WordTrace tailWord_2131210 prefixEnd_2131210 729556737112474576515833 := by
  unfold tailWord_2131210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19432903652249406633761771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51821076405998417690031389 19432903652249406633761771)
  ·
    refine ⟨29149355478374109950642657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19432903652249406633761771 29149355478374109950642657)
    ·
      refine ⟨21862016608780582462981993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29149355478374109950642657 21862016608780582462981993)
      ·
        refine ⟨16396512456585436847236495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21862016608780582462981993 16396512456585436847236495)
        ·
          refine ⟨24594768684878155270854743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16396512456585436847236495 24594768684878155270854743)
          ·
            refine ⟨36892153027317232906282115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24594768684878155270854743 36892153027317232906282115)
            ·
              refine ⟨55338229540975849359423173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36892153027317232906282115 55338229540975849359423173)
              ·
                refine ⟨10375918038932971754891845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55338229540975849359423173 10375918038932971754891845)
                ·
                  refine ⟨1945484632299932204042221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10375918038932971754891845 1945484632299932204042221)
                  ·
                    refine ⟨729556737112474576515833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945484632299932204042221 729556737112474576515833)
                    ·
                      rfl

theorem cell22_2131210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2131210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131210 prefixEnd_2131210 := by exact prefixLift 2131210
  have htrace : WordTrace (prefixWord ++ tailWord_2131210) baseStart_2131210 baseEnd_2131210 := by
    simpa [prefixWord, tailWord_2131210, baseEnd_2131210] using wordTrace_append hprefix tailTrace_2131210
  have hstable : (prefixWord ++ tailWord_2131210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131210).length < 2 ^ (prefixWord ++ tailWord_2131210).sum := by decide
  have hdescent : baseEnd_2131210 < baseStart_2131210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131212 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_2131212 : Nat := 118140960795 + 2131212 * 2 ^ 59
def prefixEnd_2131212 : Nat := 4983230072969 + 3 ^ 40 * 2131212 * 2
def baseEnd_2131212 : Nat := 243185807251115745988609

theorem tailTrace_2131212 : CollatzResearch.WordTrace tailWord_2131212 prefixEnd_2131212 243185807251115745988609 := by
  unfold tailWord_2131212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38865843777495190438309945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51821125036660253917746593 38865843777495190438309945)
  ·
    refine ⟨29149382833121392828732459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38865843777495190438309945 29149382833121392828732459)
    ·
      refine ⟨43724074249682089243098689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29149382833121392828732459 43724074249682089243098689)
      ·
        refine ⟨32793055687261566932324017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43724074249682089243098689 32793055687261566932324017)
        ·
          refine ⟨24594791765446175199243013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32793055687261566932324017 24594791765446175199243013)
          ·
            refine ⟨4611523456021157849858065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24594791765446175199243013 4611523456021157849858065)
            ·
              refine ⟨3458642592015868387393549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4611523456021157849858065 3458642592015868387393549)
              ·
                refine ⟨1296990972005950645272581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3458642592015868387393549 1296990972005950645272581)
                ·
                  refine ⟨243185807251115745988609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1296990972005950645272581 243185807251115745988609)
                  ·
                    rfl

theorem cell22_2131212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_2131212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131212 prefixEnd_2131212 := by exact prefixLift 2131212
  have htrace : WordTrace (prefixWord ++ tailWord_2131212) baseStart_2131212 baseEnd_2131212 := by
    simpa [prefixWord, tailWord_2131212, baseEnd_2131212] using wordTrace_append hprefix tailTrace_2131212
  have hstable : (prefixWord ++ tailWord_2131212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131212).length < 2 ^ (prefixWord ++ tailWord_2131212).sum := by decide
  have hdescent : baseEnd_2131212 < baseStart_2131212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131214 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2131214 : Nat := 118140960795 + 2131214 * 2 ^ 59
def prefixEnd_2131214 : Nat := 4983230072969 + 3 ^ 40 * 2131214 * 2
def baseEnd_2131214 : Nat := 729558106394219899415821

theorem tailTrace_2131214 : CollatzResearch.WordTrace tailWord_2131214 prefixEnd_2131214 729558106394219899415821 := by
  unfold tailWord_2131214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9716470062622891902274087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51821173667322090145461797 9716470062622891902274087)
  ·
    refine ⟨14574705093934337853411131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9716470062622891902274087 14574705093934337853411131)
    ·
      refine ⟨21862057640901506780116697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14574705093934337853411131 21862057640901506780116697)
      ·
        refine ⟨16396543230676130085087523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21862057640901506780116697 16396543230676130085087523)
        ·
          refine ⟨24594814846014195127631285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16396543230676130085087523 24594814846014195127631285)
          ·
            refine ⟨2305763891813830793215433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24594814846014195127631285 2305763891813830793215433)
            ·
              refine ⟨1729322918860373094911575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2305763891813830793215433 1729322918860373094911575)
              ·
                refine ⟨2593984378290559642367363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729322918860373094911575 2593984378290559642367363)
                ·
                  refine ⟨3890976567435839463551045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593984378290559642367363 3890976567435839463551045)
                  ·
                    refine ⟨729558106394219899415821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890976567435839463551045 729558106394219899415821)
                    ·
                      rfl

theorem cell22_2131214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2131214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131214 prefixEnd_2131214 := by exact prefixLift 2131214
  have htrace : WordTrace (prefixWord ++ tailWord_2131214) baseStart_2131214 baseEnd_2131214 := by
    simpa [prefixWord, tailWord_2131214, baseEnd_2131214] using wordTrace_append hprefix tailTrace_2131214
  have hstable : (prefixWord ++ tailWord_2131214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131214).length < 2 ^ (prefixWord ++ tailWord_2131214).sum := by decide
  have hdescent : baseEnd_2131214 < baseStart_2131214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131223 : List Nat := [1, 1, 3, 4, 1, 1, 11]
def baseStart_2131223 : Nat := 118140960795 + 2131223 * 2 ^ 59
def prefixEnd_2131223 : Nat := 4983230072969 + 3 ^ 40 * 2131223 * 2
def baseEnd_2131223 : Nat := 27020784714005439849659

theorem tailTrace_2131223 : CollatzResearch.WordTrace tailWord_2131223 prefixEnd_2131223 27020784714005439849659 := by
  unfold tailWord_2131223
  simp only [CollatzResearch.WordTrace]
  refine ⟨77732088757950529755270323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51821392505300353170180215 77732088757950529755270323)
  ·
    refine ⟨116598133136925794632905485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77732088757950529755270323 116598133136925794632905485)
    ·
      refine ⟨43724299926347172987339557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116598133136925794632905485 43724299926347172987339557)
      ·
        refine ⟨8198306236190094935126167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43724299926347172987339557 8198306236190094935126167)
        ·
          refine ⟨12297459354285142402689251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8198306236190094935126167 12297459354285142402689251)
          ·
            refine ⟨18446189031427713604033877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12297459354285142402689251 18446189031427713604033877)
            ·
              refine ⟨27020784714005439849659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18446189031427713604033877 27020784714005439849659)
              ·
                rfl

theorem cell22_2131223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 11].length) (baseStart_2131223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131223 prefixEnd_2131223 := by exact prefixLift 2131223
  have htrace : WordTrace (prefixWord ++ tailWord_2131223) baseStart_2131223 baseEnd_2131223 := by
    simpa [prefixWord, tailWord_2131223, baseEnd_2131223] using wordTrace_append hprefix tailTrace_2131223
  have hstable : (prefixWord ++ tailWord_2131223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131223).length < 2 ^ (prefixWord ++ tailWord_2131223).sum := by decide
  have hdescent : baseEnd_2131223 < baseStart_2131223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131285 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 7]
def baseStart_2131285 : Nat := 118140960795 + 2131285 * 2 ^ 59
def prefixEnd_2131285 : Nat := 4983230072969 + 3 ^ 40 * 2131285 * 2
def baseEnd_2131285 : Nat := 243194137048399793630201

theorem tailTrace_2131285 : CollatzResearch.WordTrace tailWord_2131285 prefixEnd_2131285 243194137048399793630201 := by
  unfold tailWord_2131285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77734350083725914344027309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51822900055817276229351539 77734350083725914344027309)
  ·
    refine ⟨29150381281397217879010241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77734350083725914344027309 29150381281397217879010241)
    ·
      refine ⟨21862785961047913409257681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29150381281397217879010241 21862785961047913409257681)
      ·
        refine ⟨16397089470785935056943261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21862785961047913409257681 16397089470785935056943261)
        ·
          refine ⟨6148908551544725646353723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16397089470785935056943261 6148908551544725646353723)
          ·
            refine ⟨9223362827317088469530585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148908551544725646353723 9223362827317088469530585)
            ·
              refine ⟨6917522120487816352147939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9223362827317088469530585 6917522120487816352147939)
              ·
                refine ⟨10376283180731724528221909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6917522120487816352147939 10376283180731724528221909)
                ·
                  refine ⟨243194137048399793630201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10376283180731724528221909 243194137048399793630201)
                  ·
                    rfl

theorem cell22_2131285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_2131285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131285 prefixEnd_2131285 := by exact prefixLift 2131285
  have htrace : WordTrace (prefixWord ++ tailWord_2131285) baseStart_2131285 baseEnd_2131285 := by
    simpa [prefixWord, tailWord_2131285, baseEnd_2131285] using wordTrace_append hprefix tailTrace_2131285
  have hstable : (prefixWord ++ tailWord_2131285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131285).length < 2 ^ (prefixWord ++ tailWord_2131285).sum := by decide
  have hdescent : baseEnd_2131285 < baseStart_2131285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131360 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_2131360 : Nat := 118140960795 + 2131360 * 2 ^ 59
def prefixEnd_2131360 : Nat := 4983230072969 + 3 ^ 40 * 2131360 * 2
def baseEnd_2131360 : Nat := 729608085177924185265373

theorem tailTrace_2131360 : CollatzResearch.WordTrace tailWord_2131360 prefixEnd_2131360 729608085177924185265373 := by
  unfold tailWord_2131360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38868542779227101076503767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51824723705636134768671689 38868542779227101076503767)
  ·
    refine ⟨58302814168840651614755651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38868542779227101076503767 58302814168840651614755651)
    ·
      refine ⟨87454221253260977422133477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58302814168840651614755651 87454221253260977422133477)
      ·
        refine ⟨16397666484986433266650027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87454221253260977422133477 16397666484986433266650027)
        ·
          refine ⟨24596499727479649899975041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16397666484986433266650027 24596499727479649899975041)
          ·
            refine ⟨18447374795609737424981281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24596499727479649899975041 18447374795609737424981281)
            ·
              refine ⟨13835531096707303068735961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18447374795609737424981281 13835531096707303068735961)
              ·
                refine ⟨10376648322530477301551971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13835531096707303068735961 10376648322530477301551971)
                ·
                  refine ⟨15564972483795715952327957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10376648322530477301551971 15564972483795715952327957)
                  ·
                    refine ⟨729608085177924185265373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15564972483795715952327957 729608085177924185265373)
                    ·
                      rfl

theorem cell22_2131360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_2131360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131360 prefixEnd_2131360 := by exact prefixLift 2131360
  have htrace : WordTrace (prefixWord ++ tailWord_2131360) baseStart_2131360 baseEnd_2131360 := by
    simpa [prefixWord, tailWord_2131360, baseEnd_2131360] using wordTrace_append hprefix tailTrace_2131360
  have hstable : (prefixWord ++ tailWord_2131360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131360).length < 2 ^ (prefixWord ++ tailWord_2131360).sum := by decide
  have hdescent : baseEnd_2131360 < baseStart_2131360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131362 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2131362 : Nat := 118140960795 + 2131362 * 2 ^ 59
def prefixEnd_2131362 : Nat := 4983230072969 + 3 ^ 40 * 2131362 * 2
def baseEnd_2131362 : Nat := 729608769818796846715367

theorem tailTrace_2131362 : CollatzResearch.WordTrace tailWord_2131362 prefixEnd_2131362 729608769818796846715367 := by
  unfold tailWord_2131362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19434289626111739123645085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51824772336297970996386893 19434289626111739123645085)
  ·
    refine ⟨7287858609791902171366907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19434289626111739123645085 7287858609791902171366907)
    ·
      refine ⟨10931787914687853257050361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7287858609791902171366907 10931787914687853257050361)
      ·
        refine ⟨8198840936015889942787771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10931787914687853257050361 8198840936015889942787771)
        ·
          refine ⟨12298261404023834914181657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8198840936015889942787771 12298261404023834914181657)
          ·
            refine ⟨9223696053017876185636243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12298261404023834914181657 9223696053017876185636243)
            ·
              refine ⟨13835544079526814278454365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9223696053017876185636243 13835544079526814278454365)
              ·
                refine ⟨5188329029822555354420387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13835544079526814278454365 5188329029822555354420387)
                ·
                  refine ⟨7782493544733833031630581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188329029822555354420387 7782493544733833031630581)
                  ·
                    refine ⟨729608769818796846715367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7782493544733833031630581 729608769818796846715367)
                    ·
                      rfl

theorem cell22_2131362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2131362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131362 prefixEnd_2131362 := by exact prefixLift 2131362
  have htrace : WordTrace (prefixWord ++ tailWord_2131362) baseStart_2131362 baseEnd_2131362 := by
    simpa [prefixWord, tailWord_2131362, baseEnd_2131362] using wordTrace_append hprefix tailTrace_2131362
  have hstable : (prefixWord ++ tailWord_2131362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131362).length < 2 ^ (prefixWord ++ tailWord_2131362).sum := by decide
  have hdescent : baseEnd_2131362 < baseStart_2131362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131396 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2131396 : Nat := 118140960795 + 2131396 * 2 ^ 59
def prefixEnd_2131396 : Nat := 4983230072969 + 3 ^ 40 * 2131396 * 2
def baseEnd_2131396 : Nat := 729620408713632091365263

theorem tailTrace_2131396 : CollatzResearch.WordTrace tailWord_2131396 prefixEnd_2131396 729620408713632091365263 := by
  unfold tailWord_2131396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38869199293161890150659021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51825599057549186867545361 38869199293161890150659021)
  ·
    refine ⟨14575949734935708806497133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38869199293161890150659021 14575949734935708806497133)
    ·
      refine ⟨5465981150600890802436425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14575949734935708806497133 5465981150600890802436425)
      ·
        refine ⟨4099485862950668101827319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465981150600890802436425 4099485862950668101827319)
        ·
          refine ⟨6149228794426002152740979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099485862950668101827319 6149228794426002152740979)
          ·
            refine ⟨9223843191639003229111469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6149228794426002152740979 9223843191639003229111469)
            ·
              refine ⟨3458941196864626210916801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9223843191639003229111469 3458941196864626210916801)
              ·
                refine ⟨2594205897648469658187601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3458941196864626210916801 2594205897648469658187601)
                ·
                  refine ⟨1945654423236352243640701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2594205897648469658187601 1945654423236352243640701)
                  ·
                    refine ⟨729620408713632091365263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945654423236352243640701 729620408713632091365263)
                    ·
                      rfl

theorem cell22_2131396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2131396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131396 prefixEnd_2131396 := by exact prefixLift 2131396
  have htrace : WordTrace (prefixWord ++ tailWord_2131396) baseStart_2131396 baseEnd_2131396 := by
    simpa [prefixWord, tailWord_2131396, baseEnd_2131396] using wordTrace_append hprefix tailTrace_2131396
  have hstable : (prefixWord ++ tailWord_2131396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131396).length < 2 ^ (prefixWord ++ tailWord_2131396).sum := by decide
  have hdescent : baseEnd_2131396 < baseStart_2131396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131407 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 3, 3]
def baseStart_2131407 : Nat := 118140960795 + 2131407 * 2 ^ 59
def prefixEnd_2131407 : Nat := 4983230072969 + 3 ^ 40 * 2131407 * 2
def baseEnd_2131407 : Nat := 729624174238431729340229

theorem tailTrace_2131407 : CollatzResearch.WordTrace tailWord_2131407 prefixEnd_2131407 729624174238431729340229 := by
  unfold tailWord_2131407
  simp only [CollatzResearch.WordTrace]
  refine ⟨77738799789283929179968475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51825866526189286119978983 77738799789283929179968475)
  ·
    refine ⟨116608199683925893769952713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77738799789283929179968475 116608199683925893769952713)
    ·
      refine ⟨87456149762944420327464535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116608199683925893769952713 87456149762944420327464535)
      ·
        refine ⟨131184224644416630491196803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87456149762944420327464535 131184224644416630491196803)
        ·
          refine ⟨196776336966624945736795205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131184224644416630491196803 196776336966624945736795205)
          ·
            refine ⟨36895563181242177325649101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196776336966624945736795205 36895563181242177325649101)
            ·
              refine ⟨13835836192965816497118413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36895563181242177325649101 13835836192965816497118413)
              ·
                refine ⟨5188438572362181186419405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13835836192965816497118413 5188438572362181186419405)
                ·
                  refine ⟨1945664464635817944907277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5188438572362181186419405 1945664464635817944907277)
                  ·
                    refine ⟨729624174238431729340229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945664464635817944907277 729624174238431729340229)
                    ·
                      rfl

theorem cell22_2131407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_2131407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131407 prefixEnd_2131407 := by exact prefixLift 2131407
  have htrace : WordTrace (prefixWord ++ tailWord_2131407) baseStart_2131407 baseEnd_2131407 := by
    simpa [prefixWord, tailWord_2131407, baseEnd_2131407] using wordTrace_append hprefix tailTrace_2131407
  have hstable : (prefixWord ++ tailWord_2131407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131407).length < 2 ^ (prefixWord ++ tailWord_2131407).sum := by decide
  have hdescent : baseEnd_2131407 < baseStart_2131407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131435 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_2131435 : Nat := 118140960795 + 2131435 * 2 ^ 59
def prefixEnd_2131435 : Nat := 4983230072969 + 3 ^ 40 * 2131435 * 2
def baseEnd_2131435 : Nat := 729633759210648989640143

theorem tailTrace_2131435 : CollatzResearch.WordTrace tailWord_2131435 prefixEnd_2131435 729633759210648989640143 := by
  unfold tailWord_2131435
  simp only [CollatzResearch.WordTrace]
  refine ⟨77739821033182489961987759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51826547355454993307991839 77739821033182489961987759)
  ·
    refine ⟨116609731549773734942981639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77739821033182489961987759 116609731549773734942981639)
    ·
      refine ⟨174914597324660602414472459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116609731549773734942981639 174914597324660602414472459)
      ·
        refine ⟨262371895986990903621708689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174914597324660602414472459 262371895986990903621708689)
        ·
          refine ⟨196778921990243177716281517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262371895986990903621708689 196778921990243177716281517)
          ·
            refine ⟨73792095746341191643605569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196778921990243177716281517 73792095746341191643605569)
            ·
              refine ⟨55344071809755893732704177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73792095746341191643605569 55344071809755893732704177)
              ·
                refine ⟨41508053857316920299528133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55344071809755893732704177 41508053857316920299528133)
                ·
                  refine ⟨7782760098246922556161525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41508053857316920299528133 7782760098246922556161525)
                  ·
                    refine ⟨729633759210648989640143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7782760098246922556161525 729633759210648989640143)
                    ·
                      rfl

theorem cell22_2131435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_2131435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131435 prefixEnd_2131435 := by exact prefixLift 2131435
  have htrace : WordTrace (prefixWord ++ tailWord_2131435) baseStart_2131435 baseEnd_2131435 := by
    simpa [prefixWord, tailWord_2131435, baseEnd_2131435] using wordTrace_append hprefix tailTrace_2131435
  have hstable : (prefixWord ++ tailWord_2131435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131435).length < 2 ^ (prefixWord ++ tailWord_2131435).sum := by decide
  have hdescent : baseEnd_2131435 < baseStart_2131435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131441 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 1, 3]
def baseStart_2131441 : Nat := 118140960795 + 2131441 * 2 ^ 59
def prefixEnd_2131441 : Nat := 4983230072969 + 3 ^ 40 * 2131441 * 2
def baseEnd_2131441 : Nat := 729635813133266973990125

theorem tailTrace_2131441 : CollatzResearch.WordTrace tailWord_2131441 prefixEnd_2131441 729635813133266973990125 := by
  unfold tailWord_2131441
  simp only [CollatzResearch.WordTrace]
  refine ⟨77740039871160752986706177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51826693247440501991137451 77740039871160752986706177)
  ·
    refine ⟨58305029903370564740029633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77740039871160752986706177 58305029903370564740029633)
    ·
      refine ⟨43728772427527923555022225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58305029903370564740029633 43728772427527923555022225)
      ·
        refine ⟨32796579320645942666266669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43728772427527923555022225 32796579320645942666266669)
        ·
          refine ⟨12298717245242228499850001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32796579320645942666266669 12298717245242228499850001)
          ·
            refine ⟨9224037933931671374887501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12298717245242228499850001 9224037933931671374887501)
            ·
              refine ⟨3459014225224376765582813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9224037933931671374887501 3459014225224376765582813)
              ·
                refine ⟨1297130334459141287093555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3459014225224376765582813 1297130334459141287093555)
                ·
                  refine ⟨1945695501688711930640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297130334459141287093555 1945695501688711930640333)
                  ·
                    refine ⟨729635813133266973990125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945695501688711930640333 729635813133266973990125)
                    ·
                      rfl

theorem cell22_2131441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_2131441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131441 prefixEnd_2131441 := by exact prefixLift 2131441
  have htrace : WordTrace (prefixWord ++ tailWord_2131441) baseStart_2131441 baseEnd_2131441 := by
    simpa [prefixWord, tailWord_2131441, baseEnd_2131441] using wordTrace_append hprefix tailTrace_2131441
  have hstable : (prefixWord ++ tailWord_2131441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131441).length < 2 ^ (prefixWord ++ tailWord_2131441).sum := by decide
  have hdescent : baseEnd_2131441 < baseStart_2131441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131458 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2131458 : Nat := 118140960795 + 2131458 * 2 ^ 59
def prefixEnd_2131458 : Nat := 4983230072969 + 3 ^ 40 * 2131458 * 2
def baseEnd_2131458 : Nat := 729641632580684596315073

theorem tailTrace_2131458 : CollatzResearch.WordTrace tailWord_2131458 prefixEnd_2131458 729641632580684596315073 := by
  unfold tailWord_2131458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19435164978024791222518757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51827106608066109926716685 19435164978024791222518757)
  ·
    refine ⟨3644093433379648354222267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19435164978024791222518757 3644093433379648354222267)
    ·
      refine ⟨5466140150069472531333401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3644093433379648354222267 5466140150069472531333401)
      ·
        refine ⟨4099605112552104398500051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5466140150069472531333401 4099605112552104398500051)
        ·
          refine ⟨6149407668828156597750077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099605112552104398500051 6149407668828156597750077)
          ·
            refine ⟨2306027875810558724156279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6149407668828156597750077 2306027875810558724156279)
            ·
              refine ⟨3459041813715838086234419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306027875810558724156279 3459041813715838086234419)
              ·
                refine ⟨5188562720573757129351629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459041813715838086234419 5188562720573757129351629)
                ·
                  refine ⟨1945711020215158923506861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5188562720573757129351629 1945711020215158923506861)
                  ·
                    refine ⟨729641632580684596315073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945711020215158923506861 729641632580684596315073)
                    ·
                      rfl

theorem cell22_2131458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2131458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131458 prefixEnd_2131458 := by exact prefixLift 2131458
  have htrace : WordTrace (prefixWord ++ tailWord_2131458) baseStart_2131458 baseEnd_2131458 := by
    simpa [prefixWord, tailWord_2131458, baseEnd_2131458] using wordTrace_append hprefix tailTrace_2131458
  have hstable : (prefixWord ++ tailWord_2131458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131458).length < 2 ^ (prefixWord ++ tailWord_2131458).sum := by decide
  have hdescent : baseEnd_2131458 < baseStart_2131458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131516 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_2131516 : Nat := 118140960795 + 2131516 * 2 ^ 59
def prefixEnd_2131516 : Nat := 4983230072969 + 3 ^ 40 * 2131516 * 2
def baseEnd_2131516 : Nat := 243220495721997259454965

theorem tailTrace_2131516 : CollatzResearch.WordTrace tailWord_2131516 prefixEnd_2131516 243220495721997259454965 := by
  unfold tailWord_2131516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38871387672944520397843201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51828516897259360530457601 38871387672944520397843201)
  ·
    refine ⟨29153540754708390298382401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38871387672944520397843201 29153540754708390298382401)
    ·
      refine ⟨21865155566031292723786801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29153540754708390298382401 21865155566031292723786801)
      ·
        refine ⟨16398866674523469542840101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21865155566031292723786801 16398866674523469542840101)
        ·
          refine ⟨3074787501473150539282519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16398866674523469542840101 3074787501473150539282519)
          ·
            refine ⟨4612181252209725808923779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074787501473150539282519 4612181252209725808923779)
            ·
              refine ⟨6918271878314588713385669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612181252209725808923779 6918271878314588713385669)
              ·
                refine ⟨1297175977183985383759813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6918271878314588713385669 1297175977183985383759813)
                ·
                  refine ⟨243220495721997259454965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297175977183985383759813 243220495721997259454965)
                  ·
                    rfl

theorem cell22_2131516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_2131516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131516 prefixEnd_2131516 := by exact prefixLift 2131516
  have htrace : WordTrace (prefixWord ++ tailWord_2131516) baseStart_2131516 baseEnd_2131516 := by
    simpa [prefixWord, tailWord_2131516, baseEnd_2131516] using wordTrace_append hprefix tailTrace_2131516
  have hstable : (prefixWord ++ tailWord_2131516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131516).length < 2 ^ (prefixWord ++ tailWord_2131516).sum := by decide
  have hdescent : baseEnd_2131516 < baseStart_2131516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131565 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_2131565 : Nat := 118140960795 + 2131565 * 2 ^ 59
def prefixEnd_2131565 : Nat := 4983230072969 + 3 ^ 40 * 2131565 * 2
def baseEnd_2131565 : Nat := 729678260867371983889745

theorem tailTrace_2131565 : CollatzResearch.WordTrace tailWord_2131565 prefixEnd_2131565 729678260867371983889745 := by
  unfold tailWord_2131565
  simp only [CollatzResearch.WordTrace]
  refine ⟨77744562522711522164220149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51829708348474348109480099 77744562522711522164220149)
  ·
    refine ⟨7288552736504205202895639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77744562522711522164220149 7288552736504205202895639)
    ·
      refine ⟨10932829104756307804343459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7288552736504205202895639 10932829104756307804343459)
      ·
        refine ⟨16399243657134461706515189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10932829104756307804343459 16399243657134461706515189)
        ·
          refine ⟨1537429092856355784985799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16399243657134461706515189 1537429092856355784985799)
          ·
            refine ⟨2306143639284533677478699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537429092856355784985799 2306143639284533677478699)
            ·
              refine ⟨3459215458926800516218049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306143639284533677478699 3459215458926800516218049)
              ·
                refine ⟨2594411594195100387163537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3459215458926800516218049 2594411594195100387163537)
                ·
                  refine ⟨1945808695646325290372653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2594411594195100387163537 1945808695646325290372653)
                  ·
                    refine ⟨729678260867371983889745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1945808695646325290372653 729678260867371983889745)
                    ·
                      rfl

theorem cell22_2131565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_2131565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131565 prefixEnd_2131565 := by exact prefixLift 2131565
  have htrace : WordTrace (prefixWord ++ tailWord_2131565) baseStart_2131565 baseEnd_2131565 := by
    simpa [prefixWord, tailWord_2131565, baseEnd_2131565] using wordTrace_append hprefix tailTrace_2131565
  have hstable : (prefixWord ++ tailWord_2131565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131565).length < 2 ^ (prefixWord ++ tailWord_2131565).sum := by decide
  have hdescent : baseEnd_2131565 < baseStart_2131565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131619 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 1, 4]
def baseStart_2131619 : Nat := 118140960795 + 2131619 * 2 ^ 59
def prefixEnd_2131619 : Nat := 4983230072969 + 3 ^ 40 * 2131619 * 2
def baseEnd_2131619 : Nat := 729696746170933843039579

theorem tailTrace_2131619 : CollatzResearch.WordTrace tailWord_2131619 prefixEnd_2131619 729696746170933843039579 := by
  unfold tailWord_2131619
  simp only [CollatzResearch.WordTrace]
  refine ⟨77746532064515889386685911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51831021376343926257790607 77746532064515889386685911)
  ·
    refine ⟨116619798096773834080028867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77746532064515889386685911 116619798096773834080028867)
    ·
      refine ⟨174929697145160751120043301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116619798096773834080028867 174929697145160751120043301)
      ·
        refine ⟨32799318214717640835008119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174929697145160751120043301 32799318214717640835008119)
        ·
          refine ⟨49198977322076461252512179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32799318214717640835008119 49198977322076461252512179)
          ·
            refine ⟨73798465983114691878768269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49198977322076461252512179 73798465983114691878768269)
            ·
              refine ⟨27674424743668009454538101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73798465983114691878768269 27674424743668009454538101)
              ·
                refine ⟨2594477319718875886362947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27674424743668009454538101 2594477319718875886362947)
                ·
                  refine ⟨3891715979578313829544421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594477319718875886362947 3891715979578313829544421)
                  ·
                    refine ⟨729696746170933843039579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3891715979578313829544421 729696746170933843039579)
                    ·
                      rfl

theorem cell22_2131619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4].length) (baseStart_2131619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131619 prefixEnd_2131619 := by exact prefixLift 2131619
  have htrace : WordTrace (prefixWord ++ tailWord_2131619) baseStart_2131619 baseEnd_2131619 := by
    simpa [prefixWord, tailWord_2131619, baseEnd_2131619] using wordTrace_append hprefix tailTrace_2131619
  have hstable : (prefixWord ++ tailWord_2131619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131619).length < 2 ^ (prefixWord ++ tailWord_2131619).sum := by decide
  have hdescent : baseEnd_2131619 < baseStart_2131619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131634 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_2131634 : Nat := 118140960795 + 2131634 * 2 ^ 59
def prefixEnd_2131634 : Nat := 4983230072969 + 3 ^ 40 * 2131634 * 2
def baseEnd_2131634 : Nat := 243233960325826267971511

theorem tailTrace_2131634 : CollatzResearch.WordTrace tailWord_2131634 prefixEnd_2131634 243233960325826267971511 := by
  unfold tailWord_2131634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436769789865386737120489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51831386106307697965654637 19436769789865386737120489)
  ·
    refine ⟨14577577342399040052840367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19436769789865386737120489 14577577342399040052840367)
    ·
      refine ⟨21866366013598560079260551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14577577342399040052840367 21866366013598560079260551)
      ·
        refine ⟨32799549020397840118890827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21866366013598560079260551 32799549020397840118890827)
        ·
          refine ⟨49199323530596760178336241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32799549020397840118890827 49199323530596760178336241)
          ·
            refine ⟨36899492647947570133752181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49199323530596760178336241 36899492647947570133752181)
            ·
              refine ⟨3459327435745084700039267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36899492647947570133752181 3459327435745084700039267)
              ·
                refine ⟨5188991153617627050058901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459327435745084700039267 5188991153617627050058901)
                ·
                  refine ⟨243233960325826267971511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5188991153617627050058901 243233960325826267971511)
                  ·
                    rfl

theorem cell22_2131634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_2131634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131634 prefixEnd_2131634 := by exact prefixLift 2131634
  have htrace : WordTrace (prefixWord ++ tailWord_2131634) baseStart_2131634 baseEnd_2131634 := by
    simpa [prefixWord, tailWord_2131634, baseEnd_2131634] using wordTrace_append hprefix tailTrace_2131634
  have hstable : (prefixWord ++ tailWord_2131634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131634).length < 2 ^ (prefixWord ++ tailWord_2131634).sum := by decide
  have hdescent : baseEnd_2131634 < baseStart_2131634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131666 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2131666 : Nat := 118140960795 + 2131666 * 2 ^ 59
def prefixEnd_2131666 : Nat := 4983230072969 + 3 ^ 40 * 2131666 * 2
def baseEnd_2131666 : Nat := 729712835231441387114435

theorem tailTrace_2131666 : CollatzResearch.WordTrace tailWord_2131666 prefixEnd_2131666 729712835231441387114435 := by
  unfold tailWord_2131666
  simp only [CollatzResearch.WordTrace]
  refine ⟨19437061573836404103411713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51832164196897077609097901 19437061573836404103411713)
  ·
    refine ⟨14577796180377303077558785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19437061573836404103411713 14577796180377303077558785)
    ·
      refine ⟨10933347135282977308169089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14577796180377303077558785 10933347135282977308169089)
      ·
        refine ⟨8200010351462232981126817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10933347135282977308169089 8200010351462232981126817)
        ·
          refine ⟨6150007763596674735845113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8200010351462232981126817 6150007763596674735845113)
          ·
            refine ⟨4612505822697506051883835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6150007763596674735845113 4612505822697506051883835)
            ·
              refine ⟨6918758734046259077825753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612505822697506051883835 6918758734046259077825753)
              ·
                refine ⟨5189069050534694308369315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6918758734046259077825753 5189069050534694308369315)
                ·
                  refine ⟨7783603575802041462553973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189069050534694308369315 7783603575802041462553973)
                  ·
                    refine ⟨729712835231441387114435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7783603575802041462553973 729712835231441387114435)
                    ·
                      rfl

theorem cell22_2131666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2131666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131666 prefixEnd_2131666 := by exact prefixLift 2131666
  have htrace : WordTrace (prefixWord ++ tailWord_2131666) baseStart_2131666 baseEnd_2131666 := by
    simpa [prefixWord, tailWord_2131666, baseEnd_2131666] using wordTrace_append hprefix tailTrace_2131666
  have hstable : (prefixWord ++ tailWord_2131666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131666).length < 2 ^ (prefixWord ++ tailWord_2131666).sum := by decide
  have hdescent : baseEnd_2131666 < baseStart_2131666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131700 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2131700 : Nat := 118140960795 + 2131700 * 2 ^ 59
def prefixEnd_2131700 : Nat := 4983230072969 + 3 ^ 40 * 2131700 * 2
def baseEnd_2131700 : Nat := 729724474126276631764331

theorem tailTrace_2131700 : CollatzResearch.WordTrace tailWord_2131700 prefixEnd_2131700 729724474126276631764331 := by
  unfold tailWord_2131700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38874743188611220110192277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51832990918148293480256369 38874743188611220110192277)
  ·
    refine ⟨1822253586966150942665263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38874743188611220110192277 1822253586966150942665263)
    ·
      refine ⟨2733380380449226413997895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1822253586966150942665263 2733380380449226413997895)
      ·
        refine ⟨4100070570673839620996843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2733380380449226413997895 4100070570673839620996843)
        ·
          refine ⟨6150105856010759431495265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100070570673839620996843 6150105856010759431495265)
          ·
            refine ⟨4612579392008069573621449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6150105856010759431495265 4612579392008069573621449)
            ·
              refine ⟨3459434544006052180216087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612579392008069573621449 3459434544006052180216087)
              ·
                refine ⟨5189151816009078270324131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459434544006052180216087 5189151816009078270324131)
                ·
                  refine ⟨7783727724013617405486197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5189151816009078270324131 7783727724013617405486197)
                  ·
                    refine ⟨729724474126276631764331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7783727724013617405486197 729724474126276631764331)
                    ·
                      rfl

theorem cell22_2131700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2131700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131700 prefixEnd_2131700 := by exact prefixLift 2131700
  have htrace : WordTrace (prefixWord ++ tailWord_2131700) baseStart_2131700 baseEnd_2131700 := by
    simpa [prefixWord, tailWord_2131700, baseEnd_2131700] using wordTrace_append hprefix tailTrace_2131700
  have hstable : (prefixWord ++ tailWord_2131700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131700).length < 2 ^ (prefixWord ++ tailWord_2131700).sum := by decide
  have hdescent : baseEnd_2131700 < baseStart_2131700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131801 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_2131801 : Nat := 118140960795 + 2131801 * 2 ^ 59
def prefixEnd_2131801 : Nat := 4983230072969 + 3 ^ 40 * 2131801 * 2
def baseEnd_2131801 : Nat := 729759048490346034989021

theorem tailTrace_2131801 : CollatzResearch.WordTrace tailWord_2131801 prefixEnd_2131801 729759048490346034989021 := by
  unfold tailWord_2131801
  simp only [CollatzResearch.WordTrace]
  refine ⟨77753170149856534469811257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51835446766571022979874171 77753170149856534469811257)
  ·
    refine ⟨58314877612392400852358443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77753170149856534469811257 58314877612392400852358443)
    ·
      refine ⟨87472316418588601278537665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58314877612392400852358443 87472316418588601278537665)
      ·
        refine ⟨65604237313941450958903249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87472316418588601278537665 65604237313941450958903249)
        ·
          refine ⟨49203177985456088219177437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65604237313941450958903249 49203177985456088219177437)
          ·
            refine ⟨18451191744546033082191539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49203177985456088219177437 18451191744546033082191539)
            ·
              refine ⟨27676787616819049623287309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18451191744546033082191539 27676787616819049623287309)
              ·
                refine ⟨10378795356307143608732741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27676787616819049623287309 10378795356307143608732741)
                ·
                  refine ⟨1946024129307589426637389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10378795356307143608732741 1946024129307589426637389)
                  ·
                    refine ⟨729759048490346034989021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946024129307589426637389 729759048490346034989021)
                    ·
                      rfl

theorem cell22_2131801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_2131801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131801 prefixEnd_2131801 := by exact prefixLift 2131801
  have htrace : WordTrace (prefixWord ++ tailWord_2131801) baseStart_2131801 baseEnd_2131801 := by
    simpa [prefixWord, tailWord_2131801, baseEnd_2131801] using wordTrace_append hprefix tailTrace_2131801
  have hstable : (prefixWord ++ tailWord_2131801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131801).length < 2 ^ (prefixWord ++ tailWord_2131801).sum := by decide
  have hdescent : baseEnd_2131801 < baseStart_2131801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131816 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2131816 : Nat := 118140960795 + 2131816 * 2 ^ 59
def prefixEnd_2131816 : Nat := 4983230072969 + 3 ^ 40 * 2131816 * 2
def baseEnd_2131816 : Nat := 729764183296890995863975

theorem tailTrace_2131816 : CollatzResearch.WordTrace tailWord_2131816 prefixEnd_2131816 729764183296890995863975 := by
  unfold tailWord_2131816
  simp only [CollatzResearch.WordTrace]
  refine ⟨38876858622401096015803651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51835811496534794687738201 38876858622401096015803651)
  ·
    refine ⟨58315287933601644023705477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38876858622401096015803651 58315287933601644023705477)
    ·
      refine ⟨10934116487550308254444777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58315287933601644023705477 10934116487550308254444777)
      ·
        refine ⟨8200587365662731190833583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10934116487550308254444777 8200587365662731190833583)
        ·
          refine ⟨12300881048494096786250375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200587365662731190833583 12300881048494096786250375)
          ·
            refine ⟨18451321572741145179375563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300881048494096786250375 18451321572741145179375563)
            ·
              refine ⟨27676982359111717769063345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18451321572741145179375563 27676982359111717769063345)
              ·
                refine ⟨20757736769333788326797509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27676982359111717769063345 20757736769333788326797509)
                ·
                  refine ⟨3892075644250085311274533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20757736769333788326797509 3892075644250085311274533)
                  ·
                    refine ⟨729764183296890995863975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892075644250085311274533 729764183296890995863975)
                    ·
                      rfl

theorem cell22_2131816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2131816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131816 prefixEnd_2131816 := by exact prefixLift 2131816
  have htrace : WordTrace (prefixWord ++ tailWord_2131816) baseStart_2131816 baseEnd_2131816 := by
    simpa [prefixWord, tailWord_2131816, baseEnd_2131816] using wordTrace_append hprefix tailTrace_2131816
  have hstable : (prefixWord ++ tailWord_2131816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131816).length < 2 ^ (prefixWord ++ tailWord_2131816).sum := by decide
  have hdescent : baseEnd_2131816 < baseStart_2131816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131854 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_2131854 : Nat := 118140960795 + 2131854 * 2 ^ 59
def prefixEnd_2131854 : Nat := 4983230072969 + 3 ^ 40 * 2131854 * 2
def baseEnd_2131854 : Nat := 243259063824490521137953

theorem tailTrace_2131854 : CollatzResearch.WordTrace tailWord_2131854 prefixEnd_2131854 243259063824490521137953 := by
  unfold tailWord_2131854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719387902333065565186327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51836735479109683014327077 9719387902333065565186327)
  ·
    refine ⟨14579081853499598347779491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9719387902333065565186327 14579081853499598347779491)
    ·
      refine ⟨21868622780249397521669237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14579081853499598347779491 21868622780249397521669237)
      ·
        refine ⟨2050183385648381017656491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21868622780249397521669237 2050183385648381017656491)
        ·
          refine ⟨3075275078472571526484737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050183385648381017656491 3075275078472571526484737)
          ·
            refine ⟨2306456308854428644863553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075275078472571526484737 2306456308854428644863553)
            ·
              refine ⟨1729842231640821483647665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306456308854428644863553 1729842231640821483647665)
              ·
                refine ⟨1297381673730616112735749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729842231640821483647665 1297381673730616112735749)
                ·
                  refine ⟨243259063824490521137953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1297381673730616112735749 243259063824490521137953)
                  ·
                    rfl

theorem cell22_2131854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_2131854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131854 prefixEnd_2131854 := by exact prefixLift 2131854
  have htrace : WordTrace (prefixWord ++ tailWord_2131854) baseStart_2131854 baseEnd_2131854 := by
    simpa [prefixWord, tailWord_2131854, baseEnd_2131854] using wordTrace_append hprefix tailTrace_2131854
  have hstable : (prefixWord ++ tailWord_2131854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131854).length < 2 ^ (prefixWord ++ tailWord_2131854).sum := by decide
  have hdescent : baseEnd_2131854 < baseStart_2131854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131859 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 11]
def baseStart_2131859 : Nat := 118140960795 + 2131859 * 2 ^ 59
def prefixEnd_2131859 : Nat := 4983230072969 + 3 ^ 40 * 2131859 * 2
def baseEnd_2131859 : Nat := 243259634358551072346281

theorem tailTrace_2131859 : CollatzResearch.WordTrace tailWord_2131859 prefixEnd_2131859 243259634358551072346281 := by
  unfold tailWord_2131859
  simp only [CollatzResearch.WordTrace]
  refine ⟨77755285583646410375422631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51836857055764273583615087 77755285583646410375422631)
  ·
    refine ⟨116632928375469615563133947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77755285583646410375422631 116632928375469615563133947)
    ·
      refine ⟨174949392563204423344700921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116632928375469615563133947 174949392563204423344700921)
      ·
        refine ⟨131212044422403317508525691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174949392563204423344700921 131212044422403317508525691)
        ·
          refine ⟨196818066633604976262788537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131212044422403317508525691 196818066633604976262788537)
          ·
            refine ⟨147613549975203732197091403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196818066633604976262788537 147613549975203732197091403)
            ·
              refine ⟨221420324962805598295637105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147613549975203732197091403 221420324962805598295637105)
              ·
                refine ⟨166065243722104198721727829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221420324962805598295637105 166065243722104198721727829)
                ·
                  refine ⟨243259634358551072346281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 166065243722104198721727829 243259634358551072346281)
                  ·
                    rfl

theorem cell22_2131859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_2131859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131859 prefixEnd_2131859 := by exact prefixLift 2131859
  have htrace : WordTrace (prefixWord ++ tailWord_2131859) baseStart_2131859 baseEnd_2131859 := by
    simpa [prefixWord, tailWord_2131859, baseEnd_2131859] using wordTrace_append hprefix tailTrace_2131859
  have hstable : (prefixWord ++ tailWord_2131859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131859).length < 2 ^ (prefixWord ++ tailWord_2131859).sum := by decide
  have hdescent : baseEnd_2131859 < baseStart_2131859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131951 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_2131951 : Nat := 118140960795 + 2131951 * 2 ^ 59
def prefixEnd_2131951 : Nat := 4983230072969 + 3 ^ 40 * 2131951 * 2
def baseEnd_2131951 : Nat := 729810396555795643738561

theorem tailTrace_2131951 : CollatzResearch.WordTrace tailWord_2131951 prefixEnd_2131951 729810396555795643738561 := by
  unfold tailWord_2131951
  simp only [CollatzResearch.WordTrace]
  refine ⟨77758641099313110087771707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51839094066208740058514471 77758641099313110087771707)
  ·
    refine ⟨116637961648969665131657561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77758641099313110087771707 116637961648969665131657561)
    ·
      refine ⟨87478471236727248848743171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116637961648969665131657561 87478471236727248848743171)
      ·
        refine ⟨131217706855090873273114757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87478471236727248848743171 131217706855090873273114757)
        ·
          refine ⟨24603320035329538738709017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131217706855090873273114757 24603320035329538738709017)
          ·
            refine ⟨18452490026497154054031763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24603320035329538738709017 18452490026497154054031763)
            ·
              refine ⟨27678735039745731081047645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18452490026497154054031763 27678735039745731081047645)
              ·
                refine ⟨10379525639904649155392867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27678735039745731081047645 10379525639904649155392867)
                ·
                  refine ⟨15569288459856973733089301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10379525639904649155392867 15569288459856973733089301)
                  ·
                    refine ⟨729810396555795643738561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15569288459856973733089301 729810396555795643738561)
                    ·
                      rfl

theorem cell22_2131951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_2131951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131951 prefixEnd_2131951 := by exact prefixLift 2131951
  have htrace : WordTrace (prefixWord ++ tailWord_2131951) baseStart_2131951 baseEnd_2131951 := by
    simpa [prefixWord, tailWord_2131951, baseEnd_2131951] using wordTrace_append hprefix tailTrace_2131951
  have hstable : (prefixWord ++ tailWord_2131951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131951).length < 2 ^ (prefixWord ++ tailWord_2131951).sum := by decide
  have hdescent : baseEnd_2131951 < baseStart_2131951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2131972 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_2131972 : Nat := 118140960795 + 2131972 * 2 ^ 59
def prefixEnd_2131972 : Nat := 4983230072969 + 3 ^ 40 * 2131972 * 2
def baseEnd_2131972 : Nat := 243272528428319529654499

theorem tailTrace_2131972 : CollatzResearch.WordTrace tailWord_2131972 prefixEnd_2131972 243272528428319529654499 := by
  unfold tailWord_2131972
  simp only [CollatzResearch.WordTrace]
  refine ⟨38879703516118515337143085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51839604688158020449524113 38879703516118515337143085)
  ·
    refine ⟨14579888818544443251428657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38879703516118515337143085 14579888818544443251428657)
    ·
      refine ⟨10934916613908332438571493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14579888818544443251428657 10934916613908332438571493)
      ·
        refine ⟨2050296865107812332232155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10934916613908332438571493 2050296865107812332232155)
        ·
          refine ⟨3075445297661718498348233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050296865107812332232155 3075445297661718498348233)
          ·
            refine ⟨2306583973246288873761175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075445297661718498348233 2306583973246288873761175)
            ·
              refine ⟨3459875959869433310641763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306583973246288873761175 3459875959869433310641763)
              ·
                refine ⟨5189813939804149965962645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459875959869433310641763 5189813939804149965962645)
                ·
                  refine ⟨243272528428319529654499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5189813939804149965962645 243272528428319529654499)
                  ·
                    rfl

theorem cell22_2131972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_2131972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2131972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2131972 prefixEnd_2131972 := by exact prefixLift 2131972
  have htrace : WordTrace (prefixWord ++ tailWord_2131972) baseStart_2131972 baseEnd_2131972 := by
    simpa [prefixWord, tailWord_2131972, baseEnd_2131972] using wordTrace_append hprefix tailTrace_2131972
  have hstable : (prefixWord ++ tailWord_2131972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2131972).length < 2 ^ (prefixWord ++ tailWord_2131972).sum := by decide
  have hdescent : baseEnd_2131972 < baseStart_2131972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2131972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132011 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 7]
def baseStart_2132011 : Nat := 118140960795 + 2132011 * 2 ^ 59
def prefixEnd_2132011 : Nat := 4983230072969 + 3 ^ 40 * 2132011 * 2
def baseEnd_2132011 : Nat := 243276978593991829079459

theorem tailTrace_2132011 : CollatzResearch.WordTrace tailWord_2132011 prefixEnd_2132011 243276978593991829079459 := by
  unfold tailWord_2132011
  simp only [CollatzResearch.WordTrace]
  refine ⟨77760829479095740334955887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51840552986063826889970591 77760829479095740334955887)
  ·
    refine ⟨116641244218643610502433831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77760829479095740334955887 116641244218643610502433831)
    ·
      refine ⟨174961866327965415753650747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116641244218643610502433831 174961866327965415753650747)
      ·
        refine ⟨262442799491948123630476121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174961866327965415753650747 262442799491948123630476121)
        ·
          refine ⟨196832099618961092722857091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262442799491948123630476121 196832099618961092722857091)
          ·
            refine ⟨295248149428441639084285637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196832099618961092722857091 295248149428441639084285637)
            ·
              refine ⟨55359028017832807328303557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 295248149428441639084285637 55359028017832807328303557)
              ·
                refine ⟨10379817753343651374056917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55359028017832807328303557 10379817753343651374056917)
                ·
                  refine ⟨243276978593991829079459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10379817753343651374056917 243276978593991829079459)
                  ·
                    rfl

theorem cell22_2132011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_2132011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132011 prefixEnd_2132011 := by exact prefixLift 2132011
  have htrace : WordTrace (prefixWord ++ tailWord_2132011) baseStart_2132011 baseEnd_2132011 := by
    simpa [prefixWord, tailWord_2132011, baseEnd_2132011] using wordTrace_append hprefix tailTrace_2132011
  have hstable : (prefixWord ++ tailWord_2132011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132011).length < 2 ^ (prefixWord ++ tailWord_2132011).sum := by decide
  have hdescent : baseEnd_2132011 < baseStart_2132011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132032 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 1, 3]
def baseStart_2132032 : Nat := 118140960795 + 2132032 * 2 ^ 59
def prefixEnd_2132032 : Nat := 4983230072969 + 3 ^ 40 * 2132032 * 2
def baseEnd_2132032 : Nat := 729838124511138432463313

theorem tailTrace_2132032 : CollatzResearch.WordTrace tailWord_2132032 prefixEnd_2132032 729838124511138432463313 := by
  unfold tailWord_2132032
  simp only [CollatzResearch.WordTrace]
  refine ⟨38880797706009830460735175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51841063608013107280980233 38880797706009830460735175)
  ·
    refine ⟨58321196559014745691102763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38880797706009830460735175 58321196559014745691102763)
    ·
      refine ⟨87481794838522118536654145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58321196559014745691102763 87481794838522118536654145)
      ·
        refine ⟨65611346128891588902490609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87481794838522118536654145 65611346128891588902490609)
        ·
          refine ⟨49208509596668691676867957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65611346128891588902490609 49208509596668691676867957)
          ·
            refine ⟨4613297774687689844706371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49208509596668691676867957 4613297774687689844706371)
            ·
              refine ⟨6919946662031534767059557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613297774687689844706371 6919946662031534767059557)
              ·
                refine ⟨1297489999130912768823667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6919946662031534767059557 1297489999130912768823667)
                ·
                  refine ⟨1946234998696369153235501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297489999130912768823667 1946234998696369153235501)
                  ·
                    refine ⟨729838124511138432463313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946234998696369153235501 729838124511138432463313)
                    ·
                      rfl

theorem cell22_2132032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_2132032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132032 prefixEnd_2132032 := by exact prefixLift 2132032
  have htrace : WordTrace (prefixWord ++ tailWord_2132032) baseStart_2132032 baseEnd_2132032 := by
    simpa [prefixWord, tailWord_2132032, baseEnd_2132032] using wordTrace_append hprefix tailTrace_2132032
  have hstable : (prefixWord ++ tailWord_2132032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132032).length < 2 ^ (prefixWord ++ tailWord_2132032).sum := by decide
  have hdescent : baseEnd_2132032 < baseStart_2132032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132045 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2132045 : Nat := 118140960795 + 2132045 * 2 ^ 59
def prefixEnd_2132045 : Nat := 4983230072969 + 3 ^ 40 * 2132045 * 2
def baseEnd_2132045 : Nat := 243280858225603577296091

theorem tailTrace_2132045 : CollatzResearch.WordTrace tailWord_2132045 prefixEnd_2132045 243280858225603577296091 := by
  unfold tailWord_2132045
  simp only [CollatzResearch.WordTrace]
  refine ⟨77762069560972564141693589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51841379707315042761129059 77762069560972564141693589)
  ·
    refine ⟨3645097010670588944141887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77762069560972564141693589 3645097010670588944141887)
    ·
      refine ⟨5467645516005883416212831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645097010670588944141887 5467645516005883416212831)
      ·
        refine ⟨8201468274008825124319247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467645516005883416212831 8201468274008825124319247)
        ·
          refine ⟨12302202411013237686478871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8201468274008825124319247 12302202411013237686478871)
          ·
            refine ⟨18453303616519856529718307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12302202411013237686478871 18453303616519856529718307)
            ·
              refine ⟨27679955424779784794577461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18453303616519856529718307 27679955424779784794577461)
              ·
                refine ⟨2594995821073104824491637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27679955424779784794577461 2594995821073104824491637)
                ·
                  refine ⟨243280858225603577296091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2594995821073104824491637 243280858225603577296091)
                  ·
                    rfl

theorem cell22_2132045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2132045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132045 prefixEnd_2132045 := by exact prefixLift 2132045
  have htrace : WordTrace (prefixWord ++ tailWord_2132045) baseStart_2132045 baseEnd_2132045 := by
    simpa [prefixWord, tailWord_2132045, baseEnd_2132045] using wordTrace_append hprefix tailTrace_2132045
  have hstable : (prefixWord ++ tailWord_2132045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132045).length < 2 ^ (prefixWord ++ tailWord_2132045).sum := by decide
  have hdescent : baseEnd_2132045 < baseStart_2132045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132058 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_2132058 : Nat := 118140960795 + 2132058 * 2 ^ 59
def prefixEnd_2132058 : Nat := 4983230072969 + 3 ^ 40 * 2132058 * 2
def baseEnd_2132058 : Nat := 729847024842483031313233

theorem tailTrace_2132058 : CollatzResearch.WordTrace tailWord_2132058 prefixEnd_2132058 729847024842483031313233 := by
  unfold tailWord_2132058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440635927481366840479207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51841695806616978241277885 19440635927481366840479207)
  ·
    refine ⟨29160953891222050260718811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19440635927481366840479207 29160953891222050260718811)
    ·
      refine ⟨43741430836833075391078217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29160953891222050260718811 43741430836833075391078217)
      ·
        refine ⟨32806073127624806543308663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43741430836833075391078217 32806073127624806543308663)
        ·
          refine ⟨49209109691437209814962995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32806073127624806543308663 49209109691437209814962995)
          ·
            refine ⟨73813664537155814722444493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49209109691437209814962995 73813664537155814722444493)
            ·
              refine ⟨27680124201433430520916685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73813664537155814722444493 27680124201433430520916685)
              ·
                refine ⟨10380046575537536445343757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27680124201433430520916685 10380046575537536445343757)
                ·
                  refine ⟨3892517465826576167003909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10380046575537536445343757 3892517465826576167003909)
                  ·
                    refine ⟨729847024842483031313233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3892517465826576167003909 729847024842483031313233)
                    ·
                      rfl

theorem cell22_2132058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_2132058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132058 prefixEnd_2132058 := by exact prefixLift 2132058
  have htrace : WordTrace (prefixWord ++ tailWord_2132058) baseStart_2132058 baseEnd_2132058 := by
    simpa [prefixWord, tailWord_2132058, baseEnd_2132058] using wordTrace_append hprefix tailTrace_2132058
  have hstable : (prefixWord ++ tailWord_2132058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132058).length < 2 ^ (prefixWord ++ tailWord_2132058).sum := by decide
  have hdescent : baseEnd_2132058 < baseStart_2132058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132066 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2132066 : Nat := 118140960795 + 2132066 * 2 ^ 59
def prefixEnd_2132066 : Nat := 4983230072969 + 3 ^ 40 * 2132066 * 2
def baseEnd_2132066 : Nat := 729849763405973677113209

theorem tailTrace_2132066 : CollatzResearch.WordTrace tailWord_2132066 prefixEnd_2132066 729849763405973677113209 := by
  unfold tailWord_2132066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440708873474121182052013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51841890329264323152138701 19440708873474121182052013)
  ·
    refine ⟨7290265827552795443269505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19440708873474121182052013 7290265827552795443269505)
    ·
      refine ⟨5467699370664596582452129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7290265827552795443269505 5467699370664596582452129)
      ·
        refine ⟨4100774527998447436839097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5467699370664596582452129 4100774527998447436839097)
        ·
          refine ⟨3075580895998835577629323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100774527998447436839097 3075580895998835577629323)
          ·
            refine ⟨4613371343998253366443985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075580895998835577629323 4613371343998253366443985)
            ·
              refine ⟨3460028507998690024832989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613371343998253366443985 3460028507998690024832989)
              ·
                refine ⟨1297510690499508759312371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3460028507998690024832989 1297510690499508759312371)
                ·
                  refine ⟨1946266035749263138968557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297510690499508759312371 1946266035749263138968557)
                  ·
                    refine ⟨729849763405973677113209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946266035749263138968557 729849763405973677113209)
                    ·
                      rfl

theorem cell22_2132066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2132066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132066 prefixEnd_2132066 := by exact prefixLift 2132066
  have htrace : WordTrace (prefixWord ++ tailWord_2132066) baseStart_2132066 baseEnd_2132066 := by
    simpa [prefixWord, tailWord_2132066, baseEnd_2132066] using wordTrace_append hprefix tailTrace_2132066
  have hstable : (prefixWord ++ tailWord_2132066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132066).length < 2 ^ (prefixWord ++ tailWord_2132066).sum := by decide
  have hdescent : baseEnd_2132066 < baseStart_2132066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132103 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2132103 : Nat := 118140960795 + 2132103 * 2 ^ 59
def prefixEnd_2132103 : Nat := 4983230072969 + 3 ^ 40 * 2132103 * 2
def baseEnd_2132103 : Nat := 729862429262117913938095

theorem tailTrace_2132103 : CollatzResearch.WordTrace tailWord_2132103 prefixEnd_2132103 729862429262117913938095 := by
  unfold tailWord_2132103
  simp only [CollatzResearch.WordTrace]
  refine ⟨77764184994762440047304963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51842789996508293364869975 77764184994762440047304963)
  ·
    refine ⟨116646277492143660070957445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77764184994762440047304963 116646277492143660070957445)
    ·
      refine ⟨21871177029776936263304521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116646277492143660070957445 21871177029776936263304521)
      ·
        refine ⟨16403382772332702197478391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21871177029776936263304521 16403382772332702197478391)
        ·
          refine ⟨24605074158499053296217587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16403382772332702197478391 24605074158499053296217587)
          ·
            refine ⟨36907611237748579944326381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24605074158499053296217587 36907611237748579944326381)
            ·
              refine ⟨13840354214155717479122393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36907611237748579944326381 13840354214155717479122393)
              ·
                refine ⟨10380265660616788109341795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13840354214155717479122393 10380265660616788109341795)
                ·
                  refine ⟨15570398490925182164012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10380265660616788109341795 15570398490925182164012693)
                  ·
                    refine ⟨729862429262117913938095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15570398490925182164012693 729862429262117913938095)
                    ·
                      rfl

theorem cell22_2132103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2132103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132103 prefixEnd_2132103 := by exact prefixLift 2132103
  have htrace : WordTrace (prefixWord ++ tailWord_2132103) baseStart_2132103 baseEnd_2132103 := by
    simpa [prefixWord, tailWord_2132103, baseEnd_2132103] using wordTrace_append hprefix tailTrace_2132103
  have hstable : (prefixWord ++ tailWord_2132103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132103).length < 2 ^ (prefixWord ++ tailWord_2132103).sum := by decide
  have hdescent : baseEnd_2132103 < baseStart_2132103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132156 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_2132156 : Nat := 118140960795 + 2132156 * 2 ^ 59
def prefixEnd_2132156 : Nat := 4983230072969 + 3 ^ 40 * 2132156 * 2
def baseEnd_2132156 : Nat := 729880572245243442362933

theorem tailTrace_2132156 : CollatzResearch.WordTrace tailWord_2132156 prefixEnd_2132156 729880572245243442362933 := by
  unfold tailWord_2132156
  simp only [CollatzResearch.WordTrace]
  refine ⟨38883059031785215049492161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51844078709046953399322881 38883059031785215049492161)
  ·
    refine ⟨29162294273838911287119121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38883059031785215049492161 29162294273838911287119121)
    ·
      refine ⟨21871720705379183465339341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29162294273838911287119121 21871720705379183465339341)
      ·
        refine ⟨8201895264517193799502253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21871720705379183465339341 8201895264517193799502253)
        ·
          refine ⟨3075710724193947674813345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8201895264517193799502253 3075710724193947674813345)
          ·
            refine ⟨2306783043145460756110009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075710724193947674813345 2306783043145460756110009)
            ·
              refine ⟨1730087282359095567082507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306783043145460756110009 1730087282359095567082507)
              ·
                refine ⟨2595130923538643350623761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730087282359095567082507 2595130923538643350623761)
                ·
                  refine ⟨1946348192653982512967821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595130923538643350623761 1946348192653982512967821)
                  ·
                    refine ⟨729880572245243442362933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946348192653982512967821 729880572245243442362933)
                    ·
                      rfl

theorem cell22_2132156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_2132156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132156 prefixEnd_2132156 := by exact prefixLift 2132156
  have htrace : WordTrace (prefixWord ++ tailWord_2132156) baseStart_2132156 baseEnd_2132156 := by
    simpa [prefixWord, tailWord_2132156, baseEnd_2132156] using wordTrace_append hprefix tailTrace_2132156
  have hstable : (prefixWord ++ tailWord_2132156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132156).length < 2 ^ (prefixWord ++ tailWord_2132156).sum := by decide
  have hdescent : baseEnd_2132156 < baseStart_2132156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132197 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 5]
def baseStart_2132197 : Nat := 118140960795 + 2132197 * 2 ^ 59
def prefixEnd_2132197 : Nat := 4983230072969 + 3 ^ 40 * 2132197 * 2
def baseEnd_2132197 : Nat := 243298202461044334029269

theorem tailTrace_2132197 : CollatzResearch.WordTrace tailWord_2132197 prefixEnd_2132197 243298202461044334029269 := by
  unfold tailWord_2132197
  simp only [CollatzResearch.WordTrace]
  refine ⟨77767613456421894101226845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51845075637614596067484563 77767613456421894101226845)
  ·
    refine ⟨29162855046158210287960067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77767613456421894101226845 29162855046158210287960067)
    ·
      refine ⟨43744282569237315431940101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29162855046158210287960067 43744282569237315431940101)
      ·
        refine ⟨8202052981731996643488769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43744282569237315431940101 8202052981731996643488769)
        ·
          refine ⟨6151539736298997482616577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8202052981731996643488769 6151539736298997482616577)
          ·
            refine ⟨4613654802224248111962433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6151539736298997482616577 4613654802224248111962433)
            ·
              refine ⟨3460241101668186083971825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613654802224248111962433 3460241101668186083971825)
              ·
                refine ⟨2595180826251139562978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460241101668186083971825 2595180826251139562978869)
                ·
                  refine ⟨243298202461044334029269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2595180826251139562978869 243298202461044334029269)
                  ·
                    rfl

theorem cell22_2132197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_2132197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132197 prefixEnd_2132197 := by exact prefixLift 2132197
  have htrace : WordTrace (prefixWord ++ tailWord_2132197) baseStart_2132197 baseEnd_2132197 := by
    simpa [prefixWord, tailWord_2132197, baseEnd_2132197] using wordTrace_append hprefix tailTrace_2132197
  have hstable : (prefixWord ++ tailWord_2132197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132197).length < 2 ^ (prefixWord ++ tailWord_2132197).sum := by decide
  have hdescent : baseEnd_2132197 < baseStart_2132197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132208 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_2132208 : Nat := 118140960795 + 2132208 * 2 ^ 59
def prefixEnd_2132208 : Nat := 4983230072969 + 3 ^ 40 * 2132208 * 2
def baseEnd_2132208 : Nat := 243299457635977546687591

theorem tailTrace_2132208 : CollatzResearch.WordTrace tailWord_2132208 prefixEnd_2132208 243299457635977546687591 := by
  unfold tailWord_2132208
  simp only [CollatzResearch.WordTrace]
  refine ⟨38884007329691021489938639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51845343106254695319918185 38884007329691021489938639)
  ·
    refine ⟨58326010994536532234907959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38884007329691021489938639 58326010994536532234907959)
    ·
      refine ⟨87489016491804798352361939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58326010994536532234907959 87489016491804798352361939)
      ·
        refine ⟨131233524737707197528542909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87489016491804798352361939 131233524737707197528542909)
        ·
          refine ⟨49212571776640199073203591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131233524737707197528542909 49212571776640199073203591)
          ·
            refine ⟨73818857664960298609805387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49212571776640199073203591 73818857664960298609805387)
            ·
              refine ⟨110728286497440447914708081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73818857664960298609805387 110728286497440447914708081)
              ·
                refine ⟨83046214873080335936031061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110728286497440447914708081 83046214873080335936031061)
                ·
                  refine ⟨243299457635977546687591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83046214873080335936031061 243299457635977546687591)
                  ·
                    rfl

theorem cell22_2132208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_2132208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132208 prefixEnd_2132208 := by exact prefixLift 2132208
  have htrace : WordTrace (prefixWord ++ tailWord_2132208) baseStart_2132208 baseEnd_2132208 := by
    simpa [prefixWord, tailWord_2132208, baseEnd_2132208] using wordTrace_append hprefix tailTrace_2132208
  have hstable : (prefixWord ++ tailWord_2132208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132208).length < 2 ^ (prefixWord ++ tailWord_2132208).sum := by decide
  have hdescent : baseEnd_2132208 < baseStart_2132208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132225 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 6]
def baseStart_2132225 : Nat := 118140960795 + 2132225 * 2 ^ 59
def prefixEnd_2132225 : Nat := 4983230072969 + 3 ^ 40 * 2132225 * 2
def baseEnd_2132225 : Nat := 243301397451783420795907

theorem tailTrace_2132225 : CollatzResearch.WordTrace tailWord_2132225 prefixEnd_2132225 243301397451783420795907 := by
  unfold tailWord_2132225
  simp only [CollatzResearch.WordTrace]
  refine ⟨77768634700320454883246129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51845756466880303255497419 77768634700320454883246129)
  ·
    refine ⟨58326476025240341162434597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77768634700320454883246129 58326476025240341162434597)
    ·
      refine ⟨10936214254732563967956487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58326476025240341162434597 10936214254732563967956487)
      ·
        refine ⟨16404321382098845951934731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10936214254732563967956487 16404321382098845951934731)
        ·
          refine ⟨24606482073148268927902097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16404321382098845951934731 24606482073148268927902097)
          ·
            refine ⟨18454861554861201695926573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24606482073148268927902097 18454861554861201695926573)
            ·
              refine ⟨6920573083072950635972465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18454861554861201695926573 6920573083072950635972465)
              ·
                refine ⟨5190429812304712976979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6920573083072950635972465 5190429812304712976979349)
                ·
                  refine ⟨243301397451783420795907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5190429812304712976979349 243301397451783420795907)
                  ·
                    rfl

theorem cell22_2132225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_2132225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132225 prefixEnd_2132225 := by exact prefixLift 2132225
  have htrace : WordTrace (prefixWord ++ tailWord_2132225) baseStart_2132225 baseEnd_2132225 := by
    simpa [prefixWord, tailWord_2132225, baseEnd_2132225] using wordTrace_append hprefix tailTrace_2132225
  have hstable : (prefixWord ++ tailWord_2132225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132225).length < 2 ^ (prefixWord ++ tailWord_2132225).sum := by decide
  have hdescent : baseEnd_2132225 < baseStart_2132225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132274 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_2132274 : Nat := 118140960795 + 2132274 * 2 ^ 59
def prefixEnd_2132274 : Nat := 4983230072969 + 3 ^ 40 * 2132274 * 2
def baseEnd_2132274 : Nat := 729920966056730467912571

theorem tailTrace_2132274 : CollatzResearch.WordTrace tailWord_2132274 prefixEnd_2132274 729920966056730467912571 := by
  unfold tailWord_2132274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19442605469285734062944969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51846947918095290834519917 19442605469285734062944969)
  ·
    refine ⟨14581954101964300547208727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19442605469285734062944969 14581954101964300547208727)
    ·
      refine ⟨21872931152946450820813091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14581954101964300547208727 21872931152946450820813091)
      ·
        refine ⟨32809396729419676231219637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21872931152946450820813091 32809396729419676231219637)
        ·
          refine ⟨3075880943383094646676841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32809396729419676231219637 3075880943383094646676841)
          ·
            refine ⟨2306910707537320985007631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075880943383094646676841 2306910707537320985007631)
            ·
              refine ⟨3460366061305981477511447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306910707537320985007631 3460366061305981477511447)
              ·
                refine ⟨5190549091958972216267171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460366061305981477511447 5190549091958972216267171)
                ·
                  refine ⟨7785823637938458324400757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5190549091958972216267171 7785823637938458324400757)
                  ·
                    refine ⟨729920966056730467912571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7785823637938458324400757 729920966056730467912571)
                    ·
                      rfl

theorem cell22_2132274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_2132274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132274 prefixEnd_2132274 := by exact prefixLift 2132274
  have htrace : WordTrace (prefixWord ++ tailWord_2132274) baseStart_2132274 baseEnd_2132274 := by
    simpa [prefixWord, tailWord_2132274, baseEnd_2132274] using wordTrace_append hprefix tailTrace_2132274
  have hstable : (prefixWord ++ tailWord_2132274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132274).length < 2 ^ (prefixWord ++ tailWord_2132274).sum := by decide
  have hdescent : baseEnd_2132274 < baseStart_2132274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132319 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 1, 3]
def baseStart_2132319 : Nat := 118140960795 + 2132319 * 2 ^ 59
def prefixEnd_2132319 : Nat := 4983230072969 + 3 ^ 40 * 2132319 * 2
def baseEnd_2132319 : Nat := 729936370476365350537433

theorem tailTrace_2132319 : CollatzResearch.WordTrace tailWord_2132319 prefixEnd_2132319 729936370476365350537433 := by
  unfold tailWord_2132319
  simp only [CollatzResearch.WordTrace]
  refine ⟨77772063161979908937168011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51848042107986605958112007 77772063161979908937168011)
  ·
    refine ⟨116658094742969863405752017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77772063161979908937168011 116658094742969863405752017)
    ·
      refine ⟨87493571057227397554314013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116658094742969863405752017 87493571057227397554314013)
      ·
        refine ⟨32810089146460274082867755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87493571057227397554314013 32810089146460274082867755)
        ·
          refine ⟨49215133719690411124301633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32810089146460274082867755 49215133719690411124301633)
          ·
            refine ⟨36911350289767808343226225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49215133719690411124301633 36911350289767808343226225)
            ·
              refine ⟨27683512717325856257419669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36911350289767808343226225 27683512717325856257419669)
              ·
                refine ⟨1297664658624649512066547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27683512717325856257419669 1297664658624649512066547)
                ·
                  refine ⟨1946496987936974268099821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297664658624649512066547 1946496987936974268099821)
                  ·
                    refine ⟨729936370476365350537433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946496987936974268099821 729936370476365350537433)
                    ·
                      rfl

theorem cell22_2132319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_2132319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132319 prefixEnd_2132319 := by exact prefixLift 2132319
  have htrace : WordTrace (prefixWord ++ tailWord_2132319) baseStart_2132319 baseEnd_2132319 := by
    simpa [prefixWord, tailWord_2132319, baseEnd_2132319] using wordTrace_append hprefix tailTrace_2132319
  have hstable : (prefixWord ++ tailWord_2132319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132319).length < 2 ^ (prefixWord ++ tailWord_2132319).sum := by decide
  have hdescent : baseEnd_2132319 < baseStart_2132319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132407 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2132407 : Nat := 118140960795 + 2132407 * 2 ^ 59
def prefixEnd_2132407 : Nat := 4983230072969 + 3 ^ 40 * 2132407 * 2
def baseEnd_2132407 : Nat := 729966494674762454337163

theorem tailTrace_2132407 : CollatzResearch.WordTrace tailWord_2132407 prefixEnd_2132407 729966494674762454337163 := by
  unfold tailWord_2132407
  simp only [CollatzResearch.WordTrace]
  refine ⟨77775272785661099966371475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51850181857107399977580983 77775272785661099966371475)
  ·
    refine ⟨116662909178491649949557213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77775272785661099966371475 116662909178491649949557213)
    ·
      refine ⟨43748590941934368731083955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116662909178491649949557213 43748590941934368731083955)
      ·
        refine ⟨65622886412901553096625933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43748590941934368731083955 65622886412901553096625933)
        ·
          refine ⟨24608582404838082411234725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65622886412901553096625933 24608582404838082411234725)
          ·
            refine ⟨4614109200907140452106511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24608582404838082411234725 4614109200907140452106511)
            ·
              refine ⟨6921163801360710678159767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614109200907140452106511 6921163801360710678159767)
              ·
                refine ⟨10381745702041066017239651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6921163801360710678159767 10381745702041066017239651)
                ·
                  refine ⟨15572618553061599025859477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10381745702041066017239651 15572618553061599025859477)
                  ·
                    refine ⟨729966494674762454337163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15572618553061599025859477 729966494674762454337163)
                    ·
                      rfl

theorem cell22_2132407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2132407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132407 prefixEnd_2132407 := by exact prefixLift 2132407
  have htrace : WordTrace (prefixWord ++ tailWord_2132407) baseStart_2132407 baseEnd_2132407 := by
    simpa [prefixWord, tailWord_2132407, baseEnd_2132407] using wordTrace_append hprefix tailTrace_2132407
  have hstable : (prefixWord ++ tailWord_2132407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132407).length < 2 ^ (prefixWord ++ tailWord_2132407).sum := by decide
  have hdescent : baseEnd_2132407 < baseStart_2132407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132484 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_2132484 : Nat := 118140960795 + 2132484 * 2 ^ 59
def prefixEnd_2132484 : Nat := 4983230072969 + 3 ^ 40 * 2132484 * 2
def baseEnd_2132484 : Nat := 243330951116119973387309

theorem tailTrace_2132484 : CollatzResearch.WordTrace tailWord_2132484 prefixEnd_2132484 243330951116119973387309 := by
  unfold tailWord_2132484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38889040603191071058462253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51852054137588094744616337 38889040603191071058462253)
  ·
    refine ⟨14583390226196651646923345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38889040603191071058462253 14583390226196651646923345)
    ·
      refine ⟨10937542669647488735192509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14583390226196651646923345 10937542669647488735192509)
      ·
        refine ⟨4101578501117808275697191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10937542669647488735192509 4101578501117808275697191)
        ·
          refine ⟨6152367751676712413545787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101578501117808275697191 6152367751676712413545787)
          ·
            refine ⟨9228551627515068620318681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152367751676712413545787 9228551627515068620318681)
            ·
              refine ⟨6921413720636301465239011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9228551627515068620318681 6921413720636301465239011)
              ·
                refine ⟨10382120580954452197858517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6921413720636301465239011 10382120580954452197858517)
                ·
                  refine ⟨243330951116119973387309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10382120580954452197858517 243330951116119973387309)
                  ·
                    rfl

theorem cell22_2132484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_2132484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132484 prefixEnd_2132484 := by exact prefixLift 2132484
  have htrace : WordTrace (prefixWord ++ tailWord_2132484) baseStart_2132484 baseEnd_2132484 := by
    simpa [prefixWord, tailWord_2132484, baseEnd_2132484] using wordTrace_append hprefix tailTrace_2132484
  have hstable : (prefixWord ++ tailWord_2132484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132484).length < 2 ^ (prefixWord ++ tailWord_2132484).sum := by decide
  have hdescent : baseEnd_2132484 < baseStart_2132484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132531 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 1, 4]
def baseStart_2132531 : Nat := 118140960795 + 2132531 * 2 ^ 59
def prefixEnd_2132531 : Nat := 4983230072969 + 3 ^ 40 * 2132531 * 2
def baseEnd_2132531 : Nat := 730008942408867464236783

theorem tailTrace_2132531 : CollatzResearch.WordTrace tailWord_2132531 prefixEnd_2132531 730008942408867464236783 := by
  unfold tailWord_2132531
  simp only [CollatzResearch.WordTrace]
  refine ⟨77779795437211869143885447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51853196958141246095923631 77779795437211869143885447)
  ·
    refine ⟨116669693155817803715828171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77779795437211869143885447 116669693155817803715828171)
    ·
      refine ⟨175004539733726705573742257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116669693155817803715828171 175004539733726705573742257)
      ·
        refine ⟨131253404800295029180306693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175004539733726705573742257 131253404800295029180306693)
        ·
          refine ⟨24610013400055317971307505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131253404800295029180306693 24610013400055317971307505)
          ·
            refine ⟨18457510050041488478480629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24610013400055317971307505 18457510050041488478480629)
            ·
              refine ⟨1730391567191389544857559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18457510050041488478480629 1730391567191389544857559)
              ·
                refine ⟨2595587350787084317286339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730391567191389544857559 2595587350787084317286339)
                ·
                  refine ⟨3893381026180626475929509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595587350787084317286339 3893381026180626475929509)
                  ·
                    refine ⟨730008942408867464236783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893381026180626475929509 730008942408867464236783)
                    ·
                      rfl

theorem cell22_2132531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 4].length) (baseStart_2132531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132531 prefixEnd_2132531 := by exact prefixLift 2132531
  have htrace : WordTrace (prefixWord ++ tailWord_2132531) baseStart_2132531 baseEnd_2132531 := by
    simpa [prefixWord, tailWord_2132531, baseEnd_2132531] using wordTrace_append hprefix tailTrace_2132531
  have hstable : (prefixWord ++ tailWord_2132531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132531).length < 2 ^ (prefixWord ++ tailWord_2132531).sum := by decide
  have hdescent : baseEnd_2132531 < baseStart_2132531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132544 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_2132544 : Nat := 118140960795 + 2132544 * 2 ^ 59
def prefixEnd_2132544 : Nat := 4983230072969 + 3 ^ 40 * 2132544 * 2
def baseEnd_2132544 : Nat := 730013392574539763661743

theorem tailTrace_2132544 : CollatzResearch.WordTrace tailWord_2132544 prefixEnd_2132544 730013392574539763661743 := by
  unfold tailWord_2132544
  simp only [CollatzResearch.WordTrace]
  refine ⟨38890134793082386182054343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51853513057443181576072457 38890134793082386182054343)
  ·
    refine ⟨58335202189623579273081515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38890134793082386182054343 58335202189623579273081515)
    ·
      refine ⟨87502803284435368909622273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58335202189623579273081515 87502803284435368909622273)
      ·
        refine ⟨65627102463326526682216705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87502803284435368909622273 65627102463326526682216705)
        ·
          refine ⟨49220326847494895011662529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65627102463326526682216705 49220326847494895011662529)
          ·
            refine ⟨36915245135621171258746897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49220326847494895011662529 36915245135621171258746897)
            ·
              refine ⟨27686433851715878444060173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36915245135621171258746897 27686433851715878444060173)
              ·
                refine ⟨10382412694393454416522565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27686433851715878444060173 10382412694393454416522565)
                ·
                  refine ⟨1946702380198772703097981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10382412694393454416522565 1946702380198772703097981)
                  ·
                    refine ⟨730013392574539763661743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946702380198772703097981 730013392574539763661743)
                    ·
                      rfl

theorem cell22_2132544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_2132544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132544 prefixEnd_2132544 := by exact prefixLift 2132544
  have htrace : WordTrace (prefixWord ++ tailWord_2132544) baseStart_2132544 baseEnd_2132544 := by
    simpa [prefixWord, tailWord_2132544, baseEnd_2132544] using wordTrace_append hprefix tailTrace_2132544
  have hstable : (prefixWord ++ tailWord_2132544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132544).length < 2 ^ (prefixWord ++ tailWord_2132544).sum := by decide
  have hdescent : baseEnd_2132544 < baseStart_2132544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132561 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_2132561 : Nat := 118140960795 + 2132561 * 2 ^ 59
def prefixEnd_2132561 : Nat := 4983230072969 + 3 ^ 40 * 2132561 * 2
def baseEnd_2132561 : Nat := 730019212021957385986691

theorem tailTrace_2132561 : CollatzResearch.WordTrace tailWord_2132561 prefixEnd_2132561 730019212021957385986691 := by
  unfold tailWord_2132561
  simp only [CollatzResearch.WordTrace]
  refine ⟨77780889627103184267477537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51853926418068789511651691 77780889627103184267477537)
  ·
    refine ⟨58335667220327388200608153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77780889627103184267477537 58335667220327388200608153)
    ·
      refine ⟨43751750415245541150456115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58335667220327388200608153 43751750415245541150456115)
      ·
        refine ⟨65627625622868311725684173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43751750415245541150456115 65627625622868311725684173)
        ·
          refine ⟨24610359608575616897131565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65627625622868311725684173 24610359608575616897131565)
          ·
            refine ⟨9228884853215856336424337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24610359608575616897131565 9228884853215856336424337)
            ·
              refine ⟨6921663639911892252318253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9228884853215856336424337 6921663639911892252318253)
              ·
                refine ⟨2595623864966959594619345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6921663639911892252318253 2595623864966959594619345)
                ·
                  refine ⟨1946717898725219695964509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595623864966959594619345 1946717898725219695964509)
                  ·
                    refine ⟨730019212021957385986691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946717898725219695964509 730019212021957385986691)
                    ·
                      rfl

theorem cell22_2132561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_2132561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132561 prefixEnd_2132561 := by exact prefixLift 2132561
  have htrace : WordTrace (prefixWord ++ tailWord_2132561) baseStart_2132561 baseEnd_2132561 := by
    simpa [prefixWord, tailWord_2132561, baseEnd_2132561] using wordTrace_append hprefix tailTrace_2132561
  have hstable : (prefixWord ++ tailWord_2132561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132561).length < 2 ^ (prefixWord ++ tailWord_2132561).sum := by decide
  have hdescent : baseEnd_2132561 < baseStart_2132561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132587 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_2132587 : Nat := 118140960795 + 2132587 * 2 ^ 59
def prefixEnd_2132587 : Nat := 4983230072969 + 3 ^ 40 * 2132587 * 2
def baseEnd_2132587 : Nat := 730028112353301984836611

theorem tailTrace_2132587 : CollatzResearch.WordTrace tailWord_2132587 prefixEnd_2132587 730028112353301984836611 := by
  unfold tailWord_2132587
  simp only [CollatzResearch.WordTrace]
  refine ⟨77781837925008990707924015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51854558616672660471949343 77781837925008990707924015)
  ·
    refine ⟨116672756887513486061886023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77781837925008990707924015 116672756887513486061886023)
    ·
      refine ⟨175009135331270229092829035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116672756887513486061886023 175009135331270229092829035)
      ·
        refine ⟨262513702996905343639243553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175009135331270229092829035 262513702996905343639243553)
        ·
          refine ⟨196885277247679007729432665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262513702996905343639243553 196885277247679007729432665)
          ·
            refine ⟨147663957935759255797074499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196885277247679007729432665 147663957935759255797074499)
            ·
              refine ⟨221495936903638883695611749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147663957935759255797074499 221495936903638883695611749)
              ·
                refine ⟨41530488169432290692927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221495936903638883695611749 41530488169432290692927203)
                ·
                  refine ⟨62295732254148436039390805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41530488169432290692927203 62295732254148436039390805)
                  ·
                    refine ⟨730028112353301984836611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62295732254148436039390805 730028112353301984836611)
                    ·
                      rfl

theorem cell22_2132587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_2132587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132587 prefixEnd_2132587 := by exact prefixLift 2132587
  have htrace : WordTrace (prefixWord ++ tailWord_2132587) baseStart_2132587 baseEnd_2132587 := by
    simpa [prefixWord, tailWord_2132587, baseEnd_2132587] using wordTrace_append hprefix tailTrace_2132587
  have hstable : (prefixWord ++ tailWord_2132587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132587).length < 2 ^ (prefixWord ++ tailWord_2132587).sum := by decide
  have hdescent : baseEnd_2132587 < baseStart_2132587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132657 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_2132657 : Nat := 118140960795 + 2132657 * 2 ^ 59
def prefixEnd_2132657 : Nat := 4983230072969 + 3 ^ 40 * 2132657 * 2
def baseEnd_2132657 : Nat := 730052074783845135586397

theorem tailTrace_2132657 : CollatzResearch.WordTrace tailWord_2132657 prefixEnd_2132657 730052074783845135586397 := by
  unfold tailWord_2132657
  simp only [CollatzResearch.WordTrace]
  refine ⟨77784391034755392662972225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51856260689836928441981483 77784391034755392662972225)
  ·
    refine ⟨58338293276066544497229169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77784391034755392662972225 58338293276066544497229169)
    ·
      refine ⟨43753719957049908372921877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58338293276066544497229169 43753719957049908372921877)
      ·
        refine ⟨2050955622986714454980713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43753719957049908372921877 2050955622986714454980713)
        ·
          refine ⟨1538216717240035841235535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050955622986714454980713 1538216717240035841235535)
          ·
            refine ⟨2307325075860053761853303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538216717240035841235535 2307325075860053761853303)
            ·
              refine ⟨3460987613790080642779955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307325075860053761853303 3460987613790080642779955)
              ·
                refine ⟨5191481420685120964169933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460987613790080642779955 5191481420685120964169933)
                ·
                  refine ⟨1946805532756920361563725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5191481420685120964169933 1946805532756920361563725)
                  ·
                    refine ⟨730052074783845135586397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1946805532756920361563725 730052074783845135586397)
                    ·
                      rfl

theorem cell22_2132657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_2132657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132657 prefixEnd_2132657 := by exact prefixLift 2132657
  have htrace : WordTrace (prefixWord ++ tailWord_2132657) baseStart_2132657 baseEnd_2132657 := by
    simpa [prefixWord, tailWord_2132657, baseEnd_2132657] using wordTrace_append hprefix tailTrace_2132657
  have hstable : (prefixWord ++ tailWord_2132657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132657).length < 2 ^ (prefixWord ++ tailWord_2132657).sum := by decide
  have hdescent : baseEnd_2132657 < baseStart_2132657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132696 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_2132696 : Nat := 118140960795 + 2132696 * 2 ^ 59
def prefixEnd_2132696 : Nat := 4983230072969 + 3 ^ 40 * 2132696 * 2
def baseEnd_2132696 : Nat := 730065425280862033861277

theorem tailTrace_2132696 : CollatzResearch.WordTrace tailWord_2132696 prefixEnd_2132696 730065425280862033861277 := by
  unfold tailWord_2132696
  simp only [CollatzResearch.WordTrace]
  refine ⟨38892906740807051161820971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51857208987742734882427961 38892906740807051161820971)
  ·
    refine ⟨58339360111210576742731457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38892906740807051161820971 58339360111210576742731457)
    ·
      refine ⟨43754520083407932557048593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58339360111210576742731457 43754520083407932557048593)
      ·
        refine ⟨32815890062555949417786445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43754520083407932557048593 32815890062555949417786445)
        ·
          refine ⟨12305958773458481031669917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32815890062555949417786445 12305958773458481031669917)
          ·
            refine ⟨4614734540046930386876219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12305958773458481031669917 4614734540046930386876219)
            ·
              refine ⟨6922101810070395580314329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4614734540046930386876219 6922101810070395580314329)
              ·
                refine ⟨5191576357552796685235747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6922101810070395580314329 5191576357552796685235747)
                ·
                  refine ⟨7787364536329195027853621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5191576357552796685235747 7787364536329195027853621)
                  ·
                    refine ⟨730065425280862033861277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7787364536329195027853621 730065425280862033861277)
                    ·
                      rfl

theorem cell22_2132696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_2132696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132696 prefixEnd_2132696 := by exact prefixLift 2132696
  have htrace : WordTrace (prefixWord ++ tailWord_2132696) baseStart_2132696 baseEnd_2132696 := by
    simpa [prefixWord, tailWord_2132696, baseEnd_2132696] using wordTrace_append hprefix tailTrace_2132696
  have hstable : (prefixWord ++ tailWord_2132696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132696).length < 2 ^ (prefixWord ++ tailWord_2132696).sum := by decide
  have hdescent : baseEnd_2132696 < baseStart_2132696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132709 : List Nat := [1, 3, 1, 4, 1, 12]
def baseStart_2132709 : Nat := 118140960795 + 2132709 * 2 ^ 59
def prefixEnd_2132709 : Nat := 4983230072969 + 3 ^ 40 * 2132709 * 2
def baseEnd_2132709 : Nat := 9013208338846102880077

theorem tailTrace_2132709 : CollatzResearch.WordTrace tailWord_2132709 prefixEnd_2132709 9013208338846102880077 := by
  unfold tailWord_2132709
  simp only [CollatzResearch.WordTrace]
  refine ⟨77786287630567005543865181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51857525087044670362576787 77786287630567005543865181)
  ·
    refine ⟨29169857861462627078949443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77786287630567005543865181 29169857861462627078949443)
    ·
      refine ⟨43754786792193940618424165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29169857861462627078949443 43754786792193940618424165)
      ·
        refine ⟨8204022523536363865954531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43754786792193940618424165 8204022523536363865954531)
        ·
          refine ⟨12306033785304545798931797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8204022523536363865954531 12306033785304545798931797)
          ·
            refine ⟨9013208338846102880077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12306033785304545798931797 9013208338846102880077)
            ·
              rfl

theorem cell22_2132709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 12].length) (baseStart_2132709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132709 prefixEnd_2132709 := by exact prefixLift 2132709
  have htrace : WordTrace (prefixWord ++ tailWord_2132709) baseStart_2132709 baseEnd_2132709 := by
    simpa [prefixWord, tailWord_2132709, baseEnd_2132709] using wordTrace_append hprefix tailTrace_2132709
  have hstable : (prefixWord ++ tailWord_2132709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132709).length < 2 ^ (prefixWord ++ tailWord_2132709).sum := by decide
  have hdescent : baseEnd_2132709 < baseStart_2132709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132739 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_2132739 : Nat := 118140960795 + 2132739 * 2 ^ 59
def prefixEnd_2132739 : Nat := 4983230072969 + 3 ^ 40 * 2132739 * 2
def baseEnd_2132739 : Nat := 730080145059624255036145

theorem tailTrace_2132739 : CollatzResearch.WordTrace tailWord_2132739 prefixEnd_2132739 730080145059624255036145 := by
  unfold tailWord_2132739
  simp only [CollatzResearch.WordTrace]
  refine ⟨77787381820458320667457271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51858254546972213778304847 77787381820458320667457271)
  ·
    refine ⟨116681072730687481001185907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77787381820458320667457271 116681072730687481001185907)
    ·
      refine ⟨175021609096031221501778861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116681072730687481001185907 175021609096031221501778861)
      ·
        refine ⟨65633103411011708063167073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175021609096031221501778861 65633103411011708063167073)
        ·
          refine ⟨49224827558258781047375305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65633103411011708063167073 49224827558258781047375305)
          ·
            refine ⟨36918620668694085785531479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49224827558258781047375305 36918620668694085785531479)
            ·
              refine ⟨55377931003041128678297219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36918620668694085785531479 55377931003041128678297219)
              ·
                refine ⟨83066896504561693017445829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55377931003041128678297219 83066896504561693017445829)
                ·
                  refine ⟨15575043094605317440771093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83066896504561693017445829 15575043094605317440771093)
                  ·
                    refine ⟨730080145059624255036145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15575043094605317440771093 730080145059624255036145)
                    ·
                      rfl

theorem cell22_2132739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_2132739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132739 prefixEnd_2132739 := by exact prefixLift 2132739
  have htrace : WordTrace (prefixWord ++ tailWord_2132739) baseStart_2132739 baseEnd_2132739 := by
    simpa [prefixWord, tailWord_2132739, baseEnd_2132739] using wordTrace_append hprefix tailTrace_2132739
  have hstable : (prefixWord ++ tailWord_2132739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132739).length < 2 ^ (prefixWord ++ tailWord_2132739).sum := by decide
  have hdescent : baseEnd_2132739 < baseStart_2132739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132743 : List Nat := [1, 1, 4, 4, 1, 2, 3, 6]
def baseStart_2132743 : Nat := 118140960795 + 2132743 * 2 ^ 59
def prefixEnd_2132743 : Nat := 4983230072969 + 3 ^ 40 * 2132743 * 2
def baseEnd_2132743 : Nat := 81120168260152175326237

theorem tailTrace_2132743 : CollatzResearch.WordTrace tailWord_2132743 prefixEnd_2132743 81120168260152175326237 := by
  unfold tailWord_2132743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77787527712443829350602883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51858351808295886233735255 77787527712443829350602883)
  ·
    refine ⟨116681291568665744025904325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77787527712443829350602883 116681291568665744025904325)
    ·
      refine ⟨21877742169124827004857061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116681291568665744025904325 21877742169124827004857061)
      ·
        refine ⟨4102076656710905063410699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21877742169124827004857061 4102076656710905063410699)
        ·
          refine ⟨6153114985066357595116049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102076656710905063410699 6153114985066357595116049)
          ·
            refine ⟨4614836238799768196337037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153114985066357595116049 4614836238799768196337037)
            ·
              refine ⟨1730563589549913073626389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4614836238799768196337037 1730563589549913073626389)
              ·
                refine ⟨81120168260152175326237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1730563589549913073626389 81120168260152175326237)
                ·
                  rfl

theorem cell22_2132743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 6].length) (baseStart_2132743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132743 prefixEnd_2132743 := by exact prefixLift 2132743
  have htrace : WordTrace (prefixWord ++ tailWord_2132743) baseStart_2132743 baseEnd_2132743 := by
    simpa [prefixWord, tailWord_2132743, baseEnd_2132743] using wordTrace_append hprefix tailTrace_2132743
  have hstable : (prefixWord ++ tailWord_2132743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132743).length < 2 ^ (prefixWord ++ tailWord_2132743).sum := by decide
  have hdescent : baseEnd_2132743 < baseStart_2132743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132786 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2132786 : Nat := 118140960795 + 2132786 * 2 ^ 59
def prefixEnd_2132786 : Nat := 4983230072969 + 3 ^ 40 * 2132786 * 2
def baseEnd_2132786 : Nat := 730096234120131799111001

theorem tailTrace_2132786 : CollatzResearch.WordTrace tailWord_2132786 prefixEnd_2132786 730096234120131799111001 := by
  unfold tailWord_2132786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19447274012822011923604553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51859397367525365129612141 19447274012822011923604553)
  ·
    refine ⟨14585455509616508942703415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19447274012822011923604553 14585455509616508942703415)
    ·
      refine ⟨21878183264424763414055123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14585455509616508942703415 21878183264424763414055123)
      ·
        refine ⟨32817274896637145121082685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21878183264424763414055123 32817274896637145121082685)
        ·
          refine ⟨12306478086238929420406007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32817274896637145121082685 12306478086238929420406007)
          ·
            refine ⟨18459717129358394130609011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12306478086238929420406007 18459717129358394130609011)
            ·
              refine ⟨27689575694037591195913517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18459717129358394130609011 27689575694037591195913517)
              ·
                refine ⟨10383590885264096698467569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27689575694037591195913517 10383590885264096698467569)
                ·
                  refine ⟨7787693163948072523850677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10383590885264096698467569 7787693163948072523850677)
                  ·
                    refine ⟨730096234120131799111001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7787693163948072523850677 730096234120131799111001)
                    ·
                      rfl

theorem cell22_2132786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2132786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132786 prefixEnd_2132786 := by exact prefixLift 2132786
  have htrace : WordTrace (prefixWord ++ tailWord_2132786) baseStart_2132786 baseEnd_2132786 := by
    simpa [prefixWord, tailWord_2132786, baseEnd_2132786] using wordTrace_append hprefix tailTrace_2132786
  have hstable : (prefixWord ++ tailWord_2132786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132786).length < 2 ^ (prefixWord ++ tailWord_2132786).sum := by decide
  have hdescent : baseEnd_2132786 < baseStart_2132786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132818 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2132818 : Nat := 118140960795 + 2132818 * 2 ^ 59
def prefixEnd_2132818 : Nat := 4983230072969 + 3 ^ 40 * 2132818 * 2
def baseEnd_2132818 : Nat := 730107188374094382310903

theorem tailTrace_2132818 : CollatzResearch.WordTrace tailWord_2132818 prefixEnd_2132818 730107188374094382310903 := by
  unfold tailWord_2132818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19447565796793029289895777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51860175458114744773055405 19447565796793029289895777)
  ·
    refine ⟨14585674347594771967421833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19447565796793029289895777 14585674347594771967421833)
    ·
      refine ⟨10939255760696078975566375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14585674347594771967421833 10939255760696078975566375)
      ·
        refine ⟨16408883641044118463349563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10939255760696078975566375 16408883641044118463349563)
        ·
          refine ⟨24613325461566177695024345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16408883641044118463349563 24613325461566177695024345)
          ·
            refine ⟨18459994096174633271268259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24613325461566177695024345 18459994096174633271268259)
            ·
              refine ⟨27689991144261949906902389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18459994096174633271268259 27689991144261949906902389)
              ·
                refine ⟨2595936669774557803772099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27689991144261949906902389 2595936669774557803772099)
                ·
                  refine ⟨3893905004661836705658149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595936669774557803772099 3893905004661836705658149)
                  ·
                    refine ⟨730107188374094382310903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3893905004661836705658149 730107188374094382310903)
                    ·
                      rfl

theorem cell22_2132818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2132818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132818 prefixEnd_2132818 := by exact prefixLift 2132818
  have htrace : WordTrace (prefixWord ++ tailWord_2132818) baseStart_2132818 baseEnd_2132818 := by
    simpa [prefixWord, tailWord_2132818, baseEnd_2132818] using wordTrace_append hprefix tailTrace_2132818
  have hstable : (prefixWord ++ tailWord_2132818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132818).length < 2 ^ (prefixWord ++ tailWord_2132818).sum := by decide
  have hdescent : baseEnd_2132818 < baseStart_2132818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132861 : List Nat := [1, 4, 1, 1, 2, 1, 4, 8]
def baseStart_2132861 : Nat := 118140960795 + 2132861 * 2 ^ 59
def prefixEnd_2132861 : Nat := 4983230072969 + 3 ^ 40 * 2132861 * 2
def baseEnd_2132861 : Nat := 81124656461428511498419

theorem tailTrace_2132861 : CollatzResearch.WordTrace tailWord_2132861 prefixEnd_2132861 81124656461428511498419 := by
  unfold tailWord_2132861
  simp only [CollatzResearch.WordTrace]
  refine ⟨77791831526016335503398437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51861221017344223668932291 77791831526016335503398437)
  ·
    refine ⟨14585968411128062906887207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77791831526016335503398437 14585968411128062906887207)
    ·
      refine ⟨21878952616692094360330811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14585968411128062906887207 21878952616692094360330811)
      ·
        refine ⟨32818428925038141540496217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21878952616692094360330811 32818428925038141540496217)
        ·
          refine ⟨24613821693778606155372163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32818428925038141540496217 24613821693778606155372163)
          ·
            refine ⟨36920732540667909233058245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24613821693778606155372163 36920732540667909233058245)
            ·
              refine ⟨6922637351375232981198421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36920732540667909233058245 6922637351375232981198421)
              ·
                refine ⟨81124656461428511498419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6922637351375232981198421 81124656461428511498419)
                ·
                  rfl

theorem cell22_2132861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 8].length) (baseStart_2132861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132861 prefixEnd_2132861 := by exact prefixLift 2132861
  have htrace : WordTrace (prefixWord ++ tailWord_2132861) baseStart_2132861 baseEnd_2132861 := by
    simpa [prefixWord, tailWord_2132861, baseEnd_2132861] using wordTrace_append hprefix tailTrace_2132861
  have hstable : (prefixWord ++ tailWord_2132861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132861).length < 2 ^ (prefixWord ++ tailWord_2132861).sum := by decide
  have hdescent : baseEnd_2132861 < baseStart_2132861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132957 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 5]
def baseStart_2132957 : Nat := 118140960795 + 2132957 * 2 ^ 59
def prefixEnd_2132957 : Nat := 4983230072969 + 3 ^ 40 * 2132957 * 2
def baseEnd_2132957 : Nat := 243384923638248117695159

theorem tailTrace_2132957 : CollatzResearch.WordTrace tailWord_2132957 prefixEnd_2132957 243384923638248117695159 := by
  unfold tailWord_2132957
  simp only [CollatzResearch.WordTrace]
  refine ⟨77795332933668543898893125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51863555289112362599262083 77795332933668543898893125)
  ·
    refine ⟨14586624925062851981042461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77795332933668543898893125 14586624925062851981042461)
    ·
      refine ⟨5469984346898569492890923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14586624925062851981042461 5469984346898569492890923)
      ·
        refine ⟨8204976520347854239336385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469984346898569492890923 8204976520347854239336385)
        ·
          refine ⟨6153732390260890679502289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8204976520347854239336385 6153732390260890679502289)
          ·
            refine ⟨4615299292695668009626717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153732390260890679502289 4615299292695668009626717)
            ·
              refine ⟨1730737234760875503610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4615299292695668009626717 1730737234760875503610019)
              ·
                refine ⟨2596105852141313255415029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730737234760875503610019 2596105852141313255415029)
                ·
                  refine ⟨243384923638248117695159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2596105852141313255415029 243384923638248117695159)
                  ·
                    rfl

theorem cell22_2132957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_2132957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132957 prefixEnd_2132957 := by exact prefixLift 2132957
  have htrace : WordTrace (prefixWord ++ tailWord_2132957) baseStart_2132957 baseEnd_2132957 := by
    simpa [prefixWord, tailWord_2132957, baseEnd_2132957] using wordTrace_append hprefix tailTrace_2132957
  have hstable : (prefixWord ++ tailWord_2132957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132957).length < 2 ^ (prefixWord ++ tailWord_2132957).sum := by decide
  have hdescent : baseEnd_2132957 < baseStart_2132957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132968 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_2132968 : Nat := 118140960795 + 2132968 * 2 ^ 59
def prefixEnd_2132968 : Nat := 4983230072969 + 3 ^ 40 * 2132968 * 2
def baseEnd_2132968 : Nat := 243386178813181330353481

theorem tailTrace_2132968 : CollatzResearch.WordTrace tailWord_2132968 prefixEnd_2132968 243386178813181330353481 := by
  unfold tailWord_2132968
  simp only [CollatzResearch.WordTrace]
  refine ⟨38897867068314346388771779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51863822757752461851695705 38897867068314346388771779)
  ·
    refine ⟨58346800602471519583157669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38897867068314346388771779 58346800602471519583157669)
    ·
      refine ⟨10940025112963409921842063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58346800602471519583157669 10940025112963409921842063)
      ·
        refine ⟨16410037669445114882763095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10940025112963409921842063 16410037669445114882763095)
        ·
          refine ⟨24615056504167672324144643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16410037669445114882763095 24615056504167672324144643)
          ·
            refine ⟨36922584756251508486216965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24615056504167672324144643 36922584756251508486216965)
            ·
              refine ⟨6922984641797157841165681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36922584756251508486216965 6922984641797157841165681)
              ·
                refine ⟨5192238481347868380874261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6922984641797157841165681 5192238481347868380874261)
                ·
                  refine ⟨243386178813181330353481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5192238481347868380874261 243386178813181330353481)
                  ·
                    rfl

theorem cell22_2132968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_2132968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132968 prefixEnd_2132968 := by exact prefixLift 2132968
  have htrace : WordTrace (prefixWord ++ tailWord_2132968) baseStart_2132968 baseEnd_2132968 := by
    simpa [prefixWord, tailWord_2132968, baseEnd_2132968] using wordTrace_append hprefix tailTrace_2132968
  have hstable : (prefixWord ++ tailWord_2132968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132968).length < 2 ^ (prefixWord ++ tailWord_2132968).sum := by decide
  have hdescent : baseEnd_2132968 < baseStart_2132968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132970 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2132970 : Nat := 118140960795 + 2132970 * 2 ^ 59
def prefixEnd_2132970 : Nat := 4983230072969 + 3 ^ 40 * 2132970 * 2
def baseEnd_2132970 : Nat := 730159221080416652510437

theorem tailTrace_2132970 : CollatzResearch.WordTrace tailWord_2132970 prefixEnd_2132970 730159221080416652510437 := by
  unfold tailWord_2132970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448951770655361779779091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51863871388414298079410909 19448951770655361779779091)
  ·
    refine ⟨29173427655983042669668637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19448951770655361779779091 29173427655983042669668637)
    ·
      refine ⟨10940035370993641001125739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29173427655983042669668637 10940035370993641001125739)
      ·
        refine ⟨16410053056490461501688609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10940035370993641001125739 16410053056490461501688609)
        ·
          refine ⟨12307539792367846126266457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16410053056490461501688609 12307539792367846126266457)
          ·
            refine ⟨9230654844275884594699843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12307539792367846126266457 9230654844275884594699843)
            ·
              refine ⟨13845982266413826892049765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9230654844275884594699843 13845982266413826892049765)
              ·
                refine ⟨2596121674952592542259331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13845982266413826892049765 2596121674952592542259331)
                ·
                  refine ⟨3894182512428888813388997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596121674952592542259331 3894182512428888813388997)
                  ·
                    refine ⟨730159221080416652510437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894182512428888813388997 730159221080416652510437)
                    ·
                      rfl

theorem cell22_2132970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2132970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132970 prefixEnd_2132970 := by exact prefixLift 2132970
  have htrace : WordTrace (prefixWord ++ tailWord_2132970) baseStart_2132970 baseEnd_2132970 := by
    simpa [prefixWord, tailWord_2132970, baseEnd_2132970] using wordTrace_append hprefix tailTrace_2132970
  have hstable : (prefixWord ++ tailWord_2132970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132970).length < 2 ^ (prefixWord ++ tailWord_2132970).sum := by decide
  have hdescent : baseEnd_2132970 < baseStart_2132970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2132978 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_2132978 : Nat := 118140960795 + 2132978 * 2 ^ 59
def prefixEnd_2132978 : Nat := 4983230072969 + 3 ^ 40 * 2132978 * 2
def baseEnd_2132978 : Nat := 730161959643907298310413

theorem tailTrace_2132978 : CollatzResearch.WordTrace tailWord_2132978 prefixEnd_2132978 730161959643907298310413 := by
  unfold tailWord_2132978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19449024716648116121351897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51864065911061642990271725 19449024716648116121351897)
  ·
    refine ⟨14586768537486087091013923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19449024716648116121351897 14586768537486087091013923)
    ·
      refine ⟨21880152806229130636520885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586768537486087091013923 21880152806229130636520885)
      ·
        refine ⟨2051264325583980997173833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21880152806229130636520885 2051264325583980997173833)
        ·
          refine ⟨1538448244187985747880375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2051264325583980997173833 1538448244187985747880375)
          ·
            refine ⟨2307672366281978621820563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538448244187985747880375 2307672366281978621820563)
            ·
              refine ⟨3461508549422967932730845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307672366281978621820563 3461508549422967932730845)
              ·
                refine ⟨1298065706033612974774067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3461508549422967932730845 1298065706033612974774067)
                ·
                  refine ⟨1947098559050419462161101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298065706033612974774067 1947098559050419462161101)
                  ·
                    refine ⟨730161959643907298310413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947098559050419462161101 730161959643907298310413)
                    ·
                      rfl

theorem cell22_2132978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_2132978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2132978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2132978 prefixEnd_2132978 := by exact prefixLift 2132978
  have htrace : WordTrace (prefixWord ++ tailWord_2132978) baseStart_2132978 baseEnd_2132978 := by
    simpa [prefixWord, tailWord_2132978, baseEnd_2132978] using wordTrace_append hprefix tailTrace_2132978
  have hstable : (prefixWord ++ tailWord_2132978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2132978).length < 2 ^ (prefixWord ++ tailWord_2132978).sum := by decide
  have hdescent : baseEnd_2132978 < baseStart_2132978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2132978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133000 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2133000 : Nat := 118140960795 + 2133000 * 2 ^ 59
def prefixEnd_2133000 : Nat := 4983230072969 + 3 ^ 40 * 2133000 * 2
def baseEnd_2133000 : Nat := 730169490693506574260345

theorem tailTrace_2133000 : CollatzResearch.WordTrace tailWord_2133000 prefixEnd_2133000 730169490693506574260345 := by
  unfold tailWord_2133000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38898450636256381121354227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51864600848341841495138969 38898450636256381121354227)
  ·
    refine ⟨58347675954384571682031341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38898450636256381121354227 58347675954384571682031341)
    ·
      refine ⟨21880378482894214380761753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58347675954384571682031341 21880378482894214380761753)
      ·
        refine ⟨16410283862170660785571315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21880378482894214380761753 16410283862170660785571315)
        ·
          refine ⟨24615425793255991178356973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16410283862170660785571315 24615425793255991178356973)
          ·
            refine ⟨9230784672470996691883865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24615425793255991178356973 9230784672470996691883865)
            ·
              refine ⟨6923088504353247518912899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9230784672470996691883865 6923088504353247518912899)
              ·
                refine ⟨10384632756529871278369349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6923088504353247518912899 10384632756529871278369349)
                ·
                  refine ⟨1947118641849350864694253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10384632756529871278369349 1947118641849350864694253)
                  ·
                    refine ⟨730169490693506574260345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947118641849350864694253 730169490693506574260345)
                    ·
                      rfl

theorem cell22_2133000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2133000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133000 prefixEnd_2133000 := by exact prefixLift 2133000
  have htrace : WordTrace (prefixWord ++ tailWord_2133000) baseStart_2133000 baseEnd_2133000 := by
    simpa [prefixWord, tailWord_2133000, baseEnd_2133000] using wordTrace_append hprefix tailTrace_2133000
  have hstable : (prefixWord ++ tailWord_2133000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133000).length < 2 ^ (prefixWord ++ tailWord_2133000).sum := by decide
  have hdescent : baseEnd_2133000 < baseStart_2133000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133013 : List Nat := [1, 3, 2, 1, 4, 1, 1, 9]
def baseStart_2133013 : Nat := 118140960795 + 2133013 * 2 ^ 59
def prefixEnd_2133013 : Nat := 4983230072969 + 3 ^ 40 * 2133013 * 2
def baseEnd_2133013 : Nat := 81130437873242097076145

theorem tailTrace_2133013 : CollatzResearch.WordTrace tailWord_2133013 prefixEnd_2133013 81130437873242097076145 := by
  unfold tailWord_2133013
  simp only [CollatzResearch.WordTrace]
  refine ⟨77797375421465665462931693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51864916947643776975287795 77797375421465665462931693)
  ·
    refine ⟨29174015783049624548599385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77797375421465665462931693 29174015783049624548599385)
    ·
      refine ⟨21880511837287218411449539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29174015783049624548599385 21880511837287218411449539)
      ·
        refine ⟨32820767755930827617174309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21880511837287218411449539 32820767755930827617174309)
        ·
          refine ⟨6153893954237030178220183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32820767755930827617174309 6153893954237030178220183)
          ·
            refine ⟨9230840931355545267330275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6153893954237030178220183 9230840931355545267330275)
            ·
              refine ⟨13846261397033317900995413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9230840931355545267330275 13846261397033317900995413)
              ·
                refine ⟨81130437873242097076145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13846261397033317900995413 81130437873242097076145)
                ·
                  rfl

theorem cell22_2133013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 9].length) (baseStart_2133013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133013 prefixEnd_2133013 := by exact prefixLift 2133013
  have htrace : WordTrace (prefixWord ++ tailWord_2133013) baseStart_2133013 baseEnd_2133013 := by
    simpa [prefixWord, tailWord_2133013, baseEnd_2133013] using wordTrace_append hprefix tailTrace_2133013
  have hstable : (prefixWord ++ tailWord_2133013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133013).length < 2 ^ (prefixWord ++ tailWord_2133013).sum := by decide
  have hdescent : baseEnd_2133013 < baseStart_2133013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133017 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_2133017 : Nat := 118140960795 + 2133017 * 2 ^ 59
def prefixEnd_2133017 : Nat := 4983230072969 + 3 ^ 40 * 2133017 * 2
def baseEnd_2133017 : Nat := 730175310140924196585293

theorem tailTrace_2133017 : CollatzResearch.WordTrace tailWord_2133017 prefixEnd_2133017 730175310140924196585293 := by
  unfold tailWord_2133017
  simp only [CollatzResearch.WordTrace]
  refine ⟨77797521313451174146077305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51865014208967449430718203 77797521313451174146077305)
  ·
    refine ⟨58348140985088380609557979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77797521313451174146077305 58348140985088380609557979)
    ·
      refine ⟨87522211477632570914336969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58348140985088380609557979 87522211477632570914336969)
      ·
        refine ⟨65641658608224428185752727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87522211477632570914336969 65641658608224428185752727)
        ·
          refine ⟨98462487912336642278629091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65641658608224428185752727 98462487912336642278629091)
          ·
            refine ⟨147693731868504963417943637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98462487912336642278629091 147693731868504963417943637)
            ·
              refine ⟨1730785920334042540054027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 147693731868504963417943637 1730785920334042540054027)
              ·
                refine ⟨2596178880501063810081041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730785920334042540054027 2596178880501063810081041)
                ·
                  refine ⟨1947134160375797857560781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596178880501063810081041 1947134160375797857560781)
                  ·
                    refine ⟨730175310140924196585293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947134160375797857560781 730175310140924196585293)
                    ·
                      rfl

theorem cell22_2133017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_2133017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133017 prefixEnd_2133017 := by exact prefixLift 2133017
  have htrace : WordTrace (prefixWord ++ tailWord_2133017) baseStart_2133017 baseEnd_2133017 := by
    simpa [prefixWord, tailWord_2133017, baseEnd_2133017] using wordTrace_append hprefix tailTrace_2133017
  have hstable : (prefixWord ++ tailWord_2133017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133017).length < 2 ^ (prefixWord ++ tailWord_2133017).sum := by decide
  have hdescent : baseEnd_2133017 < baseStart_2133017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133073 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2133073 : Nat := 118140960795 + 2133073 * 2 ^ 59
def prefixEnd_2133073 : Nat := 4983230072969 + 3 ^ 40 * 2133073 * 2
def baseEnd_2133073 : Nat := 730194480085358717185121

theorem tailTrace_2133073 : CollatzResearch.WordTrace tailWord_2133073 prefixEnd_2133073 730194480085358717185121 := by
  unfold tailWord_2133073
  simp only [CollatzResearch.WordTrace]
  refine ⟨77799563801248295710115873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51866375867498863806743915 77799563801248295710115873)
  ·
    refine ⟨58349672850936221782586905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77799563801248295710115873 58349672850936221782586905)
    ·
      refine ⟨43762254638202166336940179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58349672850936221782586905 43762254638202166336940179)
      ·
        refine ⟨65643381957303249505410269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43762254638202166336940179 65643381957303249505410269)
        ·
          refine ⟨24616268233988718564528851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65643381957303249505410269 24616268233988718564528851)
          ·
            refine ⟨36924402350983077846793277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24616268233988718564528851 36924402350983077846793277)
            ·
              refine ⟨13846650881618654192547479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36924402350983077846793277 13846650881618654192547479)
              ·
                refine ⟨20769976322427981288821219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13846650881618654192547479 20769976322427981288821219)
                ·
                  refine ⟨31154964483641971933231829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20769976322427981288821219 31154964483641971933231829)
                  ·
                    refine ⟨730194480085358717185121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31154964483641971933231829 730194480085358717185121)
                    ·
                      rfl

theorem cell22_2133073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2133073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133073 prefixEnd_2133073 := by exact prefixLift 2133073
  have htrace : WordTrace (prefixWord ++ tailWord_2133073) baseStart_2133073 baseEnd_2133073 := by
    simpa [prefixWord, tailWord_2133073, baseEnd_2133073] using wordTrace_append hprefix tailTrace_2133073
  have hstable : (prefixWord ++ tailWord_2133073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133073).length < 2 ^ (prefixWord ++ tailWord_2133073).sum := by decide
  have hdescent : baseEnd_2133073 < baseStart_2133073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133103 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 8]
def baseStart_2133103 : Nat := 118140960795 + 2133103 * 2 ^ 59
def prefixEnd_2133103 : Nat := 4983230072969 + 3 ^ 40 * 2133103 * 2
def baseEnd_2133103 : Nat := 243401583232816212978343

theorem tailTrace_2133103 : CollatzResearch.WordTrace tailWord_2133103 prefixEnd_2133103 243401583232816212978343 := by
  unfold tailWord_2133103
  simp only [CollatzResearch.WordTrace]
  refine ⟨77800657991139610833707963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51867105327426407222471975 77800657991139610833707963)
  ·
    refine ⟨116700986986709416250561945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77800657991139610833707963 116700986986709416250561945)
    ·
      refine ⟨87525740240032062187921459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116700986986709416250561945 87525740240032062187921459)
      ·
        refine ⟨131288610360048093281882189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87525740240032062187921459 131288610360048093281882189)
        ·
          refine ⟨49233228885018034980705821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131288610360048093281882189 49233228885018034980705821)
          ·
            refine ⟨18462460831881763117764683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49233228885018034980705821 18462460831881763117764683)
            ·
              refine ⟨27693691247822644676647025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18462460831881763117764683 27693691247822644676647025)
              ·
                refine ⟨20770268435866983507485269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27693691247822644676647025 20770268435866983507485269)
                ·
                  refine ⟨243401583232816212978343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20770268435866983507485269 243401583232816212978343)
                  ·
                    rfl

theorem cell22_2133103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_2133103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133103 prefixEnd_2133103 := by exact prefixLift 2133103
  have htrace : WordTrace (prefixWord ++ tailWord_2133103) baseStart_2133103 baseEnd_2133103 := by
    simpa [prefixWord, tailWord_2133103, baseEnd_2133103] using wordTrace_append hprefix tailTrace_2133103
  have hstable : (prefixWord ++ tailWord_2133103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133103).length < 2 ^ (prefixWord ++ tailWord_2133103).sum := by decide
  have hdescent : baseEnd_2133103 < baseStart_2133103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133182 : List Nat := [4, 2, 1, 1, 3, 2, 2, 7]
def baseStart_2133182 : Nat := 118140960795 + 2133182 * 2 ^ 59
def prefixEnd_2133182 : Nat := 4983230072969 + 3 ^ 40 * 2133182 * 2
def baseEnd_2133182 : Nat := 81136865890324307356643

theorem tailTrace_2133182 : CollatzResearch.WordTrace tailWord_2133182 prefixEnd_2133182 81136865890324307356643 := by
  unfold tailWord_2133182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9725442419731675915729225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51869026238568938217222533 9725442419731675915729225)
  ·
    refine ⟨7294081814798756936796919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9725442419731675915729225 7294081814798756936796919)
    ·
      refine ⟨10941122722198135405195379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7294081814798756936796919 10941122722198135405195379)
      ·
        refine ⟨16411684083297203107793069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10941122722198135405195379 16411684083297203107793069)
        ·
          refine ⟨6154381531236451165422401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16411684083297203107793069 6154381531236451165422401)
          ·
            refine ⟨4615786148427338374066801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154381531236451165422401 4615786148427338374066801)
            ·
              refine ⟨3461839611320503780550101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615786148427338374066801 3461839611320503780550101)
              ·
                refine ⟨81136865890324307356643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3461839611320503780550101 81136865890324307356643)
                ·
                  rfl

theorem cell22_2133182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_2133182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133182 prefixEnd_2133182 := by exact prefixLift 2133182
  have htrace : WordTrace (prefixWord ++ tailWord_2133182) baseStart_2133182 baseEnd_2133182 := by
    simpa [prefixWord, tailWord_2133182, baseEnd_2133182] using wordTrace_append hprefix tailTrace_2133182
  have hstable : (prefixWord ++ tailWord_2133182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133182).length < 2 ^ (prefixWord ++ tailWord_2133182).sum := by decide
  have hdescent : baseEnd_2133182 < baseStart_2133182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133190 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2133190 : Nat := 118140960795 + 2133190 * 2 ^ 59
def prefixEnd_2133190 : Nat := 4983230072969 + 3 ^ 40 * 2133190 * 2
def baseEnd_2133190 : Nat := 730234531576409412009763

theorem tailTrace_2133190 : CollatzResearch.WordTrace tailWord_2133190 prefixEnd_2133190 730234531576409412009763 := by
  unfold tailWord_2133190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431369723182013271628907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51869220761216283128083349 2431369723182013271628907)
  ·
    refine ⟨3647054584773019907443361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431369723182013271628907 3647054584773019907443361)
    ·
      refine ⟨2735290938579764930582521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647054584773019907443361 2735290938579764930582521)
      ·
        refine ⟨2051468203934823697936891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2735290938579764930582521 2051468203934823697936891)
        ·
          refine ⟨3077202305902235546905337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051468203934823697936891 3077202305902235546905337)
          ·
            refine ⟨2307901729426676660179003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077202305902235546905337 2307901729426676660179003)
            ·
              refine ⟨3461852594140014990268505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307901729426676660179003 3461852594140014990268505)
              ·
                refine ⟨2596389445605011242701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461852594140014990268505 2596389445605011242701379)
                ·
                  refine ⟨3894584168407516864052069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596389445605011242701379 3894584168407516864052069)
                  ·
                    refine ⟨730234531576409412009763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894584168407516864052069 730234531576409412009763)
                    ·
                      rfl

theorem cell22_2133190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2133190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133190 prefixEnd_2133190 := by exact prefixLift 2133190
  have htrace : WordTrace (prefixWord ++ tailWord_2133190) baseStart_2133190 baseEnd_2133190 := by
    simpa [prefixWord, tailWord_2133190, baseEnd_2133190] using wordTrace_append hprefix tailTrace_2133190
  have hstable : (prefixWord ++ tailWord_2133190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133190).length < 2 ^ (prefixWord ++ tailWord_2133190).sum := by decide
  have hdescent : baseEnd_2133190 < baseStart_2133190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133227 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 5]
def baseStart_2133227 : Nat := 118140960795 + 2133227 * 2 ^ 59
def prefixEnd_2133227 : Nat := 4983230072969 + 3 ^ 40 * 2133227 * 2
def baseEnd_2133227 : Nat := 243415732477517882944883

theorem tailTrace_2133227 : CollatzResearch.WordTrace tailWord_2133227 prefixEnd_2133227 243415732477517882944883 := by
  unfold tailWord_2133227
  simp only [CollatzResearch.WordTrace]
  refine ⟨77805180642690380011221935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51870120428460253340814623 77805180642690380011221935)
  ·
    refine ⟨116707770964035570016832903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77805180642690380011221935 116707770964035570016832903)
    ·
      refine ⟨175061656446053355025249355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116707770964035570016832903 175061656446053355025249355)
      ·
        refine ⟨262592484669080032537874033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175061656446053355025249355 262592484669080032537874033)
        ·
          refine ⟨196944363501810024403405525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262592484669080032537874033 196944363501810024403405525)
          ·
            refine ⟨4615883519573672446954817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 196944363501810024403405525 4615883519573672446954817)
            ·
              refine ⟨3461912639680254335216113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615883519573672446954817 3461912639680254335216113)
              ·
                refine ⟨2596434479760190751412085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461912639680254335216113 2596434479760190751412085)
                ·
                  refine ⟨243415732477517882944883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2596434479760190751412085 243415732477517882944883)
                  ·
                    rfl

theorem cell22_2133227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 5].length) (baseStart_2133227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133227 prefixEnd_2133227 := by exact prefixLift 2133227
  have htrace : WordTrace (prefixWord ++ tailWord_2133227) baseStart_2133227 baseEnd_2133227 := by
    simpa [prefixWord, tailWord_2133227, baseEnd_2133227] using wordTrace_append hprefix tailTrace_2133227
  have hstable : (prefixWord ++ tailWord_2133227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133227).length < 2 ^ (prefixWord ++ tailWord_2133227).sum := by decide
  have hdescent : baseEnd_2133227 < baseStart_2133227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133231 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 1, 3]
def baseStart_2133231 : Nat := 118140960795 + 2133231 * 2 ^ 59
def prefixEnd_2133231 : Nat := 4983230072969 + 3 ^ 40 * 2133231 * 2
def baseEnd_2133231 : Nat := 730248566714298971734637

theorem tailTrace_2133231 : CollatzResearch.WordTrace tailWord_2133231 prefixEnd_2133231 730248566714298971734637 := by
  unfold tailWord_2133231
  simp only [CollatzResearch.WordTrace]
  refine ⟨77805326534675888694367547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51870217689783925796245031 77805326534675888694367547)
  ·
    refine ⟨116707989802013833041551321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77805326534675888694367547 116707989802013833041551321)
    ·
      refine ⟨87530992351510374781163491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116707989802013833041551321 87530992351510374781163491)
      ·
        refine ⟨131296488527265562171745237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87530992351510374781163491 131296488527265562171745237)
        ·
          refine ⟨3077261449857786613400279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 131296488527265562171745237 3077261449857786613400279)
          ·
            refine ⟨4615892174786679920100419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077261449857786613400279 4615892174786679920100419)
            ·
              refine ⟨6923838262180019880150629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615892174786679920100419 6923838262180019880150629)
              ·
                refine ⟨1298219674158753727528243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6923838262180019880150629 1298219674158753727528243)
                ·
                  refine ⟨1947329511238130591292365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298219674158753727528243 1947329511238130591292365)
                  ·
                    refine ⟨730248566714298971734637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947329511238130591292365 730248566714298971734637)
                    ·
                      rfl

theorem cell22_2133231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_2133231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133231 prefixEnd_2133231 := by exact prefixLift 2133231
  have htrace : WordTrace (prefixWord ++ tailWord_2133231) baseStart_2133231 baseEnd_2133231 := by
    simpa [prefixWord, tailWord_2133231, baseEnd_2133231] using wordTrace_append hprefix tailTrace_2133231
  have hstable : (prefixWord ++ tailWord_2133231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133231).length < 2 ^ (prefixWord ++ tailWord_2133231).sum := by decide
  have hdescent : baseEnd_2133231 < baseStart_2133231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133257 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_2133257 : Nat := 118140960795 + 2133257 * 2 ^ 59
def prefixEnd_2133257 : Nat := 4983230072969 + 3 ^ 40 * 2133257 * 2
def baseEnd_2133257 : Nat := 730257467045643570584557

theorem tailTrace_2133257 : CollatzResearch.WordTrace tailWord_2133257 prefixEnd_2133257 730257467045643570584557 := by
  unfold tailWord_2133257
  simp only [CollatzResearch.WordTrace]
  refine ⟨77806274832581695134814025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51870849888387796756542683 77806274832581695134814025)
  ·
    refine ⟨58354706124436271351110519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77806274832581695134814025 58354706124436271351110519)
    ·
      refine ⟨87532059186654407026665779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58354706124436271351110519 87532059186654407026665779)
      ·
        refine ⟨131298088779981610539998669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87532059186654407026665779 131298088779981610539998669)
        ·
          refine ⟨49236783292493103952499501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131298088779981610539998669 49236783292493103952499501)
          ·
            refine ⟨18463793734684913982187313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49236783292493103952499501 18463793734684913982187313)
            ·
              refine ⟨13847845301013685486640485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18463793734684913982187313 13847845301013685486640485)
              ·
                refine ⟨2596470993940066028745091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13847845301013685486640485 2596470993940066028745091)
                ·
                  refine ⟨3894706490910099043117637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596470993940066028745091 3894706490910099043117637)
                  ·
                    refine ⟨730257467045643570584557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894706490910099043117637 730257467045643570584557)
                    ·
                      rfl

theorem cell22_2133257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_2133257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133257 prefixEnd_2133257 := by exact prefixLift 2133257
  have htrace : WordTrace (prefixWord ++ tailWord_2133257) baseStart_2133257 baseEnd_2133257 := by
    simpa [prefixWord, tailWord_2133257, baseEnd_2133257] using wordTrace_append hprefix tailTrace_2133257
  have hstable : (prefixWord ++ tailWord_2133257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133257).length < 2 ^ (prefixWord ++ tailWord_2133257).sum := by decide
  have hdescent : baseEnd_2133257 < baseStart_2133257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133274 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_2133274 : Nat := 118140960795 + 2133274 * 2 ^ 59
def prefixEnd_2133274 : Nat := 4983230072969 + 3 ^ 40 * 2133274 * 2
def baseEnd_2133274 : Nat := 730263286493061192909505

theorem tailTrace_2133274 : CollatzResearch.WordTrace tailWord_2133274 prefixEnd_2133274 730263286493061192909505 := by
  unfold tailWord_2133274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19451723718380026759545719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51871263249013404692121917 19451723718380026759545719)
  ·
    refine ⟨29177585577570040139318579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19451723718380026759545719 29177585577570040139318579)
    ·
      refine ⟨43766378366355060208977869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29177585577570040139318579 43766378366355060208977869)
      ·
        refine ⟨16412391887383147578366701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43766378366355060208977869 16412391887383147578366701)
        ·
          refine ⟨6154646957768680341887513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16412391887383147578366701 6154646957768680341887513)
          ·
            refine ⟨4615985218326510256415635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154646957768680341887513 4615985218326510256415635)
            ·
              refine ⟨6923977827489765384623453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4615985218326510256415635 6923977827489765384623453)
              ·
                refine ⟨2596491685308662019233795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6923977827489765384623453 2596491685308662019233795)
                ·
                  refine ⟨3894737527962993028850693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2596491685308662019233795 3894737527962993028850693)
                  ·
                    refine ⟨730263286493061192909505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3894737527962993028850693 730263286493061192909505)
                    ·
                      rfl

theorem cell22_2133274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_2133274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133274 prefixEnd_2133274 := by exact prefixLift 2133274
  have htrace : WordTrace (prefixWord ++ tailWord_2133274) baseStart_2133274 baseEnd_2133274 := by
    simpa [prefixWord, tailWord_2133274, baseEnd_2133274] using wordTrace_append hprefix tailTrace_2133274
  have hstable : (prefixWord ++ tailWord_2133274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133274).length < 2 ^ (prefixWord ++ tailWord_2133274).sum := by decide
  have hdescent : baseEnd_2133274 < baseStart_2133274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133278 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2133278 : Nat := 118140960795 + 2133278 * 2 ^ 59
def prefixEnd_2133278 : Nat := 4983230072969 + 3 ^ 40 * 2133278 * 2
def baseEnd_2133278 : Nat := 243421551924935505269831

theorem tailTrace_2133278 : CollatzResearch.WordTrace tailWord_2133278 prefixEnd_2133278 243421551924935505269831 := by
  unfold tailWord_2133278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9725880095688201965166061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51871360510337077147552325 9725880095688201965166061)
  ·
    refine ⟨3647205035883075736937273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9725880095688201965166061 3647205035883075736937273)
    ·
      refine ⟨2735403776912306802702955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647205035883075736937273 2735403776912306802702955)
      ·
        refine ⟨4103105665368460204054433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735403776912306802702955 4103105665368460204054433)
        ·
          refine ⟨3077329249026345153040825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4103105665368460204054433 3077329249026345153040825)
          ·
            refine ⟨2307996936769758864780619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3077329249026345153040825 2307996936769758864780619)
            ·
              refine ⟨3461995405154638297170929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307996936769758864780619 3461995405154638297170929)
              ·
                refine ⟨2596496553865978722878197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3461995405154638297170929 2596496553865978722878197)
                ·
                  refine ⟨243421551924935505269831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2596496553865978722878197 243421551924935505269831)
                  ·
                    rfl

theorem cell22_2133278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2133278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133278 prefixEnd_2133278 := by exact prefixLift 2133278
  have htrace : WordTrace (prefixWord ++ tailWord_2133278) baseStart_2133278 baseEnd_2133278 := by
    simpa [prefixWord, tailWord_2133278, baseEnd_2133278] using wordTrace_append hprefix tailTrace_2133278
  have hstable : (prefixWord ++ tailWord_2133278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133278).length < 2 ^ (prefixWord ++ tailWord_2133278).sum := by decide
  have hdescent : baseEnd_2133278 < baseStart_2133278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133315 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_2133315 : Nat := 118140960795 + 2133315 * 2 ^ 59
def prefixEnd_2133315 : Nat := 4983230072969 + 3 ^ 40 * 2133315 * 2
def baseEnd_2133315 : Nat := 730277321630950752634379

theorem tailTrace_2133315 : CollatzResearch.WordTrace tailWord_2133315 prefixEnd_2133315 730277321630950752634379 := by
  unfold tailWord_2133315
  simp only [CollatzResearch.WordTrace]
  refine ⟨77808390266371571040425399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51872260177581047360283599 77808390266371571040425399)
  ·
    refine ⟨116712585399557356560638099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77808390266371571040425399 116712585399557356560638099)
    ·
      refine ⟨175068878099336034840957149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116712585399557356560638099 175068878099336034840957149)
      ·
        refine ⟨65650829287251013065358931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175068878099336034840957149 65650829287251013065358931)
        ·
          refine ⟨98476243930876519598038397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65650829287251013065358931 98476243930876519598038397)
          ·
            refine ⟨36928591474078694849264399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98476243930876519598038397 36928591474078694849264399)
            ·
              refine ⟨55392887211118042273896599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36928591474078694849264399 55392887211118042273896599)
              ·
                refine ⟨83089330816677063410844899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55392887211118042273896599 83089330816677063410844899)
                ·
                  refine ⟨124633996225015595116267349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83089330816677063410844899 124633996225015595116267349)
                  ·
                    refine ⟨730277321630950752634379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124633996225015595116267349 730277321630950752634379)
                    ·
                      rfl

theorem cell22_2133315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_2133315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133315 prefixEnd_2133315 := by exact prefixLift 2133315
  have htrace : WordTrace (prefixWord ++ tailWord_2133315) baseStart_2133315 baseEnd_2133315 := by
    simpa [prefixWord, tailWord_2133315, baseEnd_2133315] using wordTrace_append hprefix tailTrace_2133315
  have hstable : (prefixWord ++ tailWord_2133315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133315).length < 2 ^ (prefixWord ++ tailWord_2133315).sum := by decide
  have hdescent : baseEnd_2133315 < baseStart_2133315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133396 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2133396 : Nat := 118140960795 + 2133396 * 2 ^ 59
def prefixEnd_2133396 : Nat := 4983230072969 + 3 ^ 40 * 2133396 * 2
def baseEnd_2133396 : Nat := 243435016528764513786377

theorem tailTrace_2133396 : CollatzResearch.WordTrace tailWord_2133396 prefixEnd_2133396 243435016528764513786377 := by
  unfold tailWord_2133396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38905672289539060937062021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51874229719385414582749361 38905672289539060937062021)
  ·
    refine ⟨7294813554288573925699129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38905672289539060937062021 7294813554288573925699129)
    ·
      refine ⟨5471110165716430444274347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7294813554288573925699129 5471110165716430444274347)
      ·
        refine ⟨8206665248574645666411521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5471110165716430444274347 8206665248574645666411521)
        ·
          refine ⟨6154998936430984249808641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8206665248574645666411521 6154998936430984249808641)
          ·
            refine ⟨4616249202323238187356481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6154998936430984249808641 4616249202323238187356481)
            ·
              refine ⟨3462186901742428640517361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4616249202323238187356481 3462186901742428640517361)
              ·
                refine ⟨2596640176306821480388021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462186901742428640517361 2596640176306821480388021)
                ·
                  refine ⟨243435016528764513786377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2596640176306821480388021 243435016528764513786377)
                  ·
                    rfl

theorem cell22_2133396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2133396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133396 prefixEnd_2133396 := by exact prefixLift 2133396
  have htrace : WordTrace (prefixWord ++ tailWord_2133396) baseStart_2133396 baseEnd_2133396 := by
    simpa [prefixWord, tailWord_2133396, baseEnd_2133396] using wordTrace_append hprefix tailTrace_2133396
  have hstable : (prefixWord ++ tailWord_2133396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133396).length < 2 ^ (prefixWord ++ tailWord_2133396).sum := by decide
  have hdescent : baseEnd_2133396 < baseStart_2133396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133454 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2133454 : Nat := 118140960795 + 2133454 * 2 ^ 59
def prefixEnd_2133454 : Nat := 4983230072969 + 3 ^ 40 * 2133454 * 2
def baseEnd_2133454 : Nat := 730324904171600723408953

theorem tailTrace_2133454 : CollatzResearch.WordTrace tailWord_2133454 prefixEnd_2133454 730324904171600723408953 := by
  unfold tailWord_2133454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726682501608499722466927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51875640008578665186490277 9726682501608499722466927)
  ·
    refine ⟨14590023752412749583700391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9726682501608499722466927 14590023752412749583700391)
    ·
      refine ⟨21885035628619124375550587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14590023752412749583700391 21885035628619124375550587)
      ·
        refine ⟨32827553442928686563325881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21885035628619124375550587 32827553442928686563325881)
        ·
          refine ⟨24620665082196514922494411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32827553442928686563325881 24620665082196514922494411)
          ·
            refine ⟨36930997623294772383741617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24620665082196514922494411 36930997623294772383741617)
            ·
              refine ⟨27698248217471079287806213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36930997623294772383741617 27698248217471079287806213)
              ·
                refine ⟨5193421540775827366463665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27698248217471079287806213 5193421540775827366463665)
                ·
                  refine ⟨3895066155581870524847749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5193421540775827366463665 3895066155581870524847749)
                  ·
                    refine ⟨730324904171600723408953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895066155581870524847749 730324904171600723408953)
                    ·
                      rfl

theorem cell22_2133454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2133454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133454 prefixEnd_2133454 := by exact prefixLift 2133454
  have htrace : WordTrace (prefixWord ++ tailWord_2133454) baseStart_2133454 baseEnd_2133454 := by
    simpa [prefixWord, tailWord_2133454, baseEnd_2133454] using wordTrace_append hprefix tailTrace_2133454
  have hstable : (prefixWord ++ tailWord_2133454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133454).length < 2 ^ (prefixWord ++ tailWord_2133454).sum := by decide
  have hdescent : baseEnd_2133454 < baseStart_2133454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133473 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_2133473 : Nat := 118140960795 + 2133473 * 2 ^ 59
def prefixEnd_2133473 : Nat := 4983230072969 + 3 ^ 40 * 2133473 * 2
def baseEnd_2133473 : Nat := 730331408259891007183895

theorem tailTrace_2133473 : CollatzResearch.WordTrace tailWord_2133473 prefixEnd_2133473 730331408259891007183895 := by
  unfold tailWord_2133473
  simp only [CollatzResearch.WordTrace]
  refine ⟨77814152999799164024677073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51876101999866109349784715 77814152999799164024677073)
  ·
    refine ⟨58360614749849373018507805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77814152999799164024677073 58360614749849373018507805)
    ·
      refine ⟨21885230531193514881940427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58360614749849373018507805 21885230531193514881940427)
      ·
        refine ⟨32827845796790272322910641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21885230531193514881940427 32827845796790272322910641)
        ·
          refine ⟨24620884347592704242182981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32827845796790272322910641 24620884347592704242182981)
          ·
            refine ⟨4616415815173632045409309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24620884347592704242182981 4616415815173632045409309)
            ·
              refine ⟨1731155930690112017028491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4616415815173632045409309 1731155930690112017028491)
              ·
                refine ⟨2596733896035168025542737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731155930690112017028491 2596733896035168025542737)
                ·
                  refine ⟨1947550422026376019157053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596733896035168025542737 1947550422026376019157053)
                  ·
                    refine ⟨730331408259891007183895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947550422026376019157053 730331408259891007183895)
                    ·
                      rfl

theorem cell22_2133473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_2133473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133473 prefixEnd_2133473 := by exact prefixLift 2133473
  have htrace : WordTrace (prefixWord ++ tailWord_2133473) baseStart_2133473 baseEnd_2133473 := by
    simpa [prefixWord, tailWord_2133473, baseEnd_2133473] using wordTrace_append hprefix tailTrace_2133473
  have hstable : (prefixWord ++ tailWord_2133473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133473).length < 2 ^ (prefixWord ++ tailWord_2133473).sum := by decide
  have hdescent : baseEnd_2133473 < baseStart_2133473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133484 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_2133484 : Nat := 118140960795 + 2133484 * 2 ^ 59
def prefixEnd_2133484 : Nat := 4983230072969 + 3 ^ 40 * 2133484 * 2
def baseEnd_2133484 : Nat := 730335173784690645158861

theorem tailTrace_2133484 : CollatzResearch.WordTrace tailWord_2133484 prefixEnd_2133484 730335173784690645158861 := by
  unfold tailWord_2133484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38907277101379656451663753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51876369468506208602218337 38907277101379656451663753)
  ·
    refine ⟨29180457826034742338747815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38907277101379656451663753 29180457826034742338747815)
    ·
      refine ⟨43770686739052113508121723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29180457826034742338747815 43770686739052113508121723)
      ·
        refine ⟨65656030108578170262182585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43770686739052113508121723 65656030108578170262182585)
        ·
          refine ⟨49242022581433627696636939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65656030108578170262182585 49242022581433627696636939)
          ·
            refine ⟨73863033872150441544955409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49242022581433627696636939 73863033872150441544955409)
            ·
              refine ⟨55397275404112831158716557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73863033872150441544955409 55397275404112831158716557)
              ·
                refine ⟨20773978276542311684518709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55397275404112831158716557 20773978276542311684518709)
                ·
                  refine ⟨1947560463425841720423629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20773978276542311684518709 1947560463425841720423629)
                  ·
                    refine ⟨730335173784690645158861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947560463425841720423629 730335173784690645158861)
                    ·
                      rfl

theorem cell22_2133484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_2133484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133484 prefixEnd_2133484 := by exact prefixLift 2133484
  have htrace : WordTrace (prefixWord ++ tailWord_2133484) baseStart_2133484 baseEnd_2133484 := by
    simpa [prefixWord, tailWord_2133484, baseEnd_2133484] using wordTrace_append hprefix tailTrace_2133484
  have hstable : (prefixWord ++ tailWord_2133484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133484).length < 2 ^ (prefixWord ++ tailWord_2133484).sum := by decide
  have hdescent : baseEnd_2133484 < baseStart_2133484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133514 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_2133514 : Nat := 118140960795 + 2133514 * 2 ^ 59
def prefixEnd_2133514 : Nat := 4983230072969 + 3 ^ 40 * 2133514 * 2
def baseEnd_2133514 : Nat := 243448481132593522302923

theorem tailTrace_2133514 : CollatzResearch.WordTrace tailWord_2133514 prefixEnd_2133514 243448481132593522302923 := by
  unfold tailWord_2133514
  simp only [CollatzResearch.WordTrace]
  refine ⟨19453912098162657006729899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51877098928433752017946397 19453912098162657006729899)
  ·
    refine ⟨29180868147243985510094849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19453912098162657006729899 29180868147243985510094849)
    ·
      refine ⟨21885651110432989132571137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29180868147243985510094849 21885651110432989132571137)
      ·
        refine ⟨16414238332824741849428353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21885651110432989132571137 16414238332824741849428353)
        ·
          refine ⟨12310678749618556387071265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16414238332824741849428353 12310678749618556387071265)
          ·
            refine ⟨9233009062213917290303449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12310678749618556387071265 9233009062213917290303449)
            ·
              refine ⟨6924756796660437967727587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9233009062213917290303449 6924756796660437967727587)
              ·
                refine ⟨10387135194990656951591381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6924756796660437967727587 10387135194990656951591381)
                ·
                  refine ⟨243448481132593522302923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10387135194990656951591381 243448481132593522302923)
                  ·
                    rfl

theorem cell22_2133514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_2133514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133514 prefixEnd_2133514 := by exact prefixLift 2133514
  have htrace : WordTrace (prefixWord ++ tailWord_2133514) baseStart_2133514 baseEnd_2133514 := by
    simpa [prefixWord, tailWord_2133514, baseEnd_2133514] using wordTrace_append hprefix tailTrace_2133514
  have hstable : (prefixWord ++ tailWord_2133514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133514).length < 2 ^ (prefixWord ++ tailWord_2133514).sum := by decide
  have hdescent : baseEnd_2133514 < baseStart_2133514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133524 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2133524 : Nat := 118140960795 + 2133524 * 2 ^ 59
def prefixEnd_2133524 : Nat := 4983230072969 + 3 ^ 40 * 2133524 * 2
def baseEnd_2133524 : Nat := 730348866602143874158739

theorem tailTrace_2133524 : CollatzResearch.WordTrace tailWord_2133524 prefixEnd_2133524 730348866602143874158739 := by
  unfold tailWord_2133524
  simp only [CollatzResearch.WordTrace]
  refine ⟨38908006561307199867391813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51877342081742933156522417 38908006561307199867391813)
  ·
    refine ⟨7295251230245099975135965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38908006561307199867391813 7295251230245099975135965)
    ·
      refine ⟨2735719211341912490675987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7295251230245099975135965 2735719211341912490675987)
      ·
        refine ⟨4103578817012868736013981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2735719211341912490675987 4103578817012868736013981)
        ·
          refine ⟨1538842056379825776005243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4103578817012868736013981 1538842056379825776005243)
          ·
            refine ⟨2308263084569738664007865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538842056379825776005243 2308263084569738664007865)
            ·
              refine ⟨1731197313427303998005899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308263084569738664007865 1731197313427303998005899)
              ·
                refine ⟨2596795970140955997008849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731197313427303998005899 2596795970140955997008849)
                ·
                  refine ⟨1947596977605716997756637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2596795970140955997008849 1947596977605716997756637)
                  ·
                    refine ⟨730348866602143874158739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947596977605716997756637 730348866602143874158739)
                    ·
                      rfl

theorem cell22_2133524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2133524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133524 prefixEnd_2133524 := by exact prefixLift 2133524
  have htrace : WordTrace (prefixWord ++ tailWord_2133524) baseStart_2133524 baseEnd_2133524 := by
    simpa [prefixWord, tailWord_2133524, baseEnd_2133524] using wordTrace_append hprefix tailTrace_2133524
  have hstable : (prefixWord ++ tailWord_2133524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133524).length < 2 ^ (prefixWord ++ tailWord_2133524).sum := by decide
  have hdescent : baseEnd_2133524 < baseStart_2133524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133589 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2133589 : Nat := 118140960795 + 2133589 * 2 ^ 59
def prefixEnd_2133589 : Nat := 4983230072969 + 3 ^ 40 * 2133589 * 2
def baseEnd_2133589 : Nat := 730371117430505371283539

theorem tailTrace_2133589 : CollatzResearch.WordTrace tailWord_2133589 prefixEnd_2133589 730371117430505371283539 := by
  unfold tailWord_2133589
  simp only [CollatzResearch.WordTrace]
  refine ⟨77818383867378915835899821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51878922578252610557266547 77818383867378915835899821)
  ·
    refine ⟨29181893950267093438462433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77818383867378915835899821 29181893950267093438462433)
    ·
      refine ⟨21886420462700320078846825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29181893950267093438462433 21886420462700320078846825)
      ·
        refine ⟨16414815347025240059135119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21886420462700320078846825 16414815347025240059135119)
        ·
          refine ⟨24622223020537860088702679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16414815347025240059135119 24622223020537860088702679)
          ·
            refine ⟨36933334530806790133054019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24622223020537860088702679 36933334530806790133054019)
            ·
              refine ⟨55400001796210185199581029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36933334530806790133054019 55400001796210185199581029)
              ·
                refine ⟨10387500336789409724921443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55400001796210185199581029 10387500336789409724921443)
                ·
                  refine ⟨15581250505184114587382165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10387500336789409724921443 15581250505184114587382165)
                  ·
                    refine ⟨730371117430505371283539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15581250505184114587382165 730371117430505371283539)
                    ·
                      rfl

theorem cell22_2133589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2133589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133589 prefixEnd_2133589 := by exact prefixLift 2133589
  have htrace : WordTrace (prefixWord ++ tailWord_2133589) baseStart_2133589 baseEnd_2133589 := by
    simpa [prefixWord, tailWord_2133589, baseEnd_2133589] using wordTrace_append hprefix tailTrace_2133589
  have hstable : (prefixWord ++ tailWord_2133589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133589).length < 2 ^ (prefixWord ++ tailWord_2133589).sum := by decide
  have hdescent : baseEnd_2133589 < baseStart_2133589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133591 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 1, 5]
def baseStart_2133591 : Nat := 118140960795 + 2133591 * 2 ^ 59
def prefixEnd_2133591 : Nat := 4983230072969 + 3 ^ 40 * 2133591 * 2
def baseEnd_2133591 : Nat := 730371802071378032733533

theorem tailTrace_2133591 : CollatzResearch.WordTrace tailWord_2133591 prefixEnd_2133591 730371802071378032733533 := by
  unfold tailWord_2133591
  simp only [CollatzResearch.WordTrace]
  refine ⟨77818456813371670177472627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51878971208914446784981751 77818456813371670177472627)
  ·
    refine ⟨116727685220057505266208941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77818456813371670177472627 116727685220057505266208941)
    ·
      refine ⟨43772881957521564474828353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116727685220057505266208941 43772881957521564474828353)
      ·
        refine ⟨32829661468141173356121265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43772881957521564474828353 32829661468141173356121265)
        ·
          refine ⟨24622246101105880017090949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32829661468141173356121265 24622246101105880017090949)
          ·
            refine ⟨4616671143957352503204553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24622246101105880017090949 4616671143957352503204553)
            ·
              refine ⟨3462503357968014377403415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4616671143957352503204553 3462503357968014377403415)
              ·
                refine ⟨5193755036952021566105123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462503357968014377403415 5193755036952021566105123)
                ·
                  refine ⟨7790632555428032349157685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5193755036952021566105123 7790632555428032349157685)
                  ·
                    refine ⟨730371802071378032733533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7790632555428032349157685 730371802071378032733533)
                    ·
                      rfl

theorem cell22_2133591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_2133591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133591 prefixEnd_2133591 := by exact prefixLift 2133591
  have htrace : WordTrace (prefixWord ++ tailWord_2133591) baseStart_2133591 baseEnd_2133591 := by
    simpa [prefixWord, tailWord_2133591, baseEnd_2133591] using wordTrace_append hprefix tailTrace_2133591
  have hstable : (prefixWord ++ tailWord_2133591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133591).length < 2 ^ (prefixWord ++ tailWord_2133591).sum := by decide
  have hdescent : baseEnd_2133591 < baseStart_2133591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133621 : List Nat := [1, 3, 4, 2, 1, 2, 9]
def baseStart_2133621 : Nat := 118140960795 + 2133621 * 2 ^ 59
def prefixEnd_2133621 : Nat := 4983230072969 + 3 ^ 40 * 2133621 * 2
def baseEnd_2133621 : Nat := 27051187840165479795683

theorem tailTrace_2133621 : CollatzResearch.WordTrace tailWord_2133621 prefixEnd_2133621 27051187840165479795683 := by
  unfold tailWord_2133621
  simp only [CollatzResearch.WordTrace]
  refine ⟨77819551003262985301064717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51879700668841990200709811 77819551003262985301064717)
  ·
    refine ⟨29182331626223619487899269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77819551003262985301064717 29182331626223619487899269)
    ·
      refine ⟨5471687179916928653981113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29182331626223619487899269 5471687179916928653981113)
      ·
        refine ⟨4103765384937696490485835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5471687179916928653981113 4103765384937696490485835)
        ·
          refine ⟨6155648077406544735728753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4103765384937696490485835 6155648077406544735728753)
          ·
            refine ⟨4616736058054908551796565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6155648077406544735728753 4616736058054908551796565)
            ·
              refine ⟨27051187840165479795683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4616736058054908551796565 27051187840165479795683)
              ·
                rfl

theorem cell22_2133621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 9].length) (baseStart_2133621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133621 prefixEnd_2133621 := by exact prefixLift 2133621
  have htrace : WordTrace (prefixWord ++ tailWord_2133621) baseStart_2133621 baseEnd_2133621 := by
    simpa [prefixWord, tailWord_2133621, baseEnd_2133621] using wordTrace_append hprefix tailTrace_2133621
  have hstable : (prefixWord ++ tailWord_2133621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133621).length < 2 ^ (prefixWord ++ tailWord_2133621).sum := by decide
  have hdescent : baseEnd_2133621 < baseStart_2133621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133672 : List Nat := [2, 1, 7, 1, 2, 1, 8]
def baseStart_2133672 : Nat := 118140960795 + 2133672 * 2 ^ 59
def prefixEnd_2133672 : Nat := 4983230072969 + 3 ^ 40 * 2133672 * 2
def baseEnd_2133672 : Nat := 27051834445434104498455

theorem tailTrace_2133672 : CollatzResearch.WordTrace tailWord_2133672 prefixEnd_2133672 27051834445434104498455 := by
  unfold tailWord_2133672
  simp only [CollatzResearch.WordTrace]
  refine ⟨38910705563039110505585635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51880940750718814007447513 38910705563039110505585635)
  ·
    refine ⟨58366058344558665758378453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38910705563039110505585635 58366058344558665758378453)
    ·
      refine ⟨1367954492450593728711995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 58366058344558665758378453 1367954492450593728711995)
      ·
        refine ⟨2051931738675890593067993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367954492450593728711995 2051931738675890593067993)
        ·
          refine ⟨1538948804006917944800995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2051931738675890593067993 1538948804006917944800995)
          ·
            refine ⟨2308423206010376917201493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538948804006917944800995 2308423206010376917201493)
            ·
              refine ⟨27051834445434104498455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2308423206010376917201493 27051834445434104498455)
              ·
                rfl

theorem cell22_2133672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 8].length) (baseStart_2133672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133672 prefixEnd_2133672 := by exact prefixLift 2133672
  have htrace : WordTrace (prefixWord ++ tailWord_2133672) baseStart_2133672 baseEnd_2133672 := by
    simpa [prefixWord, tailWord_2133672, baseEnd_2133672] using wordTrace_append hprefix tailTrace_2133672
  have hstable : (prefixWord ++ tailWord_2133672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133672).length < 2 ^ (prefixWord ++ tailWord_2133672).sum := by decide
  have hdescent : baseEnd_2133672 < baseStart_2133672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133687 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 1, 3]
def baseStart_2133687 : Nat := 118140960795 + 2133687 * 2 ^ 59
def prefixEnd_2133687 : Nat := 4983230072969 + 3 ^ 40 * 2133687 * 2
def baseEnd_2133687 : Nat := 730404664833265782333239

theorem tailTrace_2133687 : CollatzResearch.WordTrace tailWord_2133687 prefixEnd_2133687 730404664833265782333239 := by
  unfold tailWord_2133687
  simp only [CollatzResearch.WordTrace]
  refine ⟨77821958221023878572967315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51881305480682585715311543 77821958221023878572967315)
  ·
    refine ⟨116732937331535817859450973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77821958221023878572967315 116732937331535817859450973)
    ·
      refine ⟨43774851499325931697294115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116732937331535817859450973 43774851499325931697294115)
      ·
        refine ⟨65662277248988897545941173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43774851499325931697294115 65662277248988897545941173)
        ·
          refine ⟨6155838492092709144931985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65662277248988897545941173 6155838492092709144931985)
          ·
            refine ⟨4616878869069531858698989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6155838492092709144931985 4616878869069531858698989)
            ·
              refine ⟨1731329575901074447012121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4616878869069531858698989 1731329575901074447012121)
              ·
                refine ⟨1298497181925805835259091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731329575901074447012121 1298497181925805835259091)
                ·
                  refine ⟨1947745772888708752888637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298497181925805835259091 1947745772888708752888637)
                  ·
                    refine ⟨730404664833265782333239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947745772888708752888637 730404664833265782333239)
                    ·
                      rfl

theorem cell22_2133687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_2133687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133687 prefixEnd_2133687 := by exact prefixLift 2133687
  have htrace : WordTrace (prefixWord ++ tailWord_2133687) baseStart_2133687 baseEnd_2133687 := by
    simpa [prefixWord, tailWord_2133687, baseEnd_2133687] using wordTrace_append hprefix tailTrace_2133687
  have hstable : (prefixWord ++ tailWord_2133687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133687).length < 2 ^ (prefixWord ++ tailWord_2133687).sum := by decide
  have hdescent : baseEnd_2133687 < baseStart_2133687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133696 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_2133696 : Nat := 118140960795 + 2133696 * 2 ^ 59
def prefixEnd_2133696 : Nat := 4983230072969 + 3 ^ 40 * 2133696 * 2
def baseEnd_2133696 : Nat := 730407745717192758858211

theorem tailTrace_2133696 : CollatzResearch.WordTrace tailWord_2133696 prefixEnd_2133696 730407745717192758858211 := by
  unfold tailWord_2133696
  simp only [CollatzResearch.WordTrace]
  refine ⟨38911143238995636555022471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51881524318660848740029961 38911143238995636555022471)
  ·
    refine ⟨58366714858493454832533707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38911143238995636555022471 58366714858493454832533707)
    ·
      refine ⟨87550072287740182248800561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58366714858493454832533707 87550072287740182248800561)
      ·
        refine ⟨65662554215805136686600421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87550072287740182248800561 65662554215805136686600421)
        ·
          refine ⟨12311728915463463128737579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65662554215805136686600421 12311728915463463128737579)
          ·
            refine ⟨18467593373195194693106369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12311728915463463128737579 18467593373195194693106369)
            ·
              refine ⟨13850695029896396019829777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18467593373195194693106369 13850695029896396019829777)
              ·
                refine ⟨10388021272422297014872333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13850695029896396019829777 10388021272422297014872333)
                ·
                  refine ⟨3895507977158361380577125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10388021272422297014872333 3895507977158361380577125)
                  ·
                    refine ⟨730407745717192758858211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895507977158361380577125 730407745717192758858211)
                    ·
                      rfl

theorem cell22_2133696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_2133696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133696 prefixEnd_2133696 := by exact prefixLift 2133696
  have htrace : WordTrace (prefixWord ++ tailWord_2133696) baseStart_2133696 baseEnd_2133696 := by
    simpa [prefixWord, tailWord_2133696, baseEnd_2133696] using wordTrace_append hprefix tailTrace_2133696
  have hstable : (prefixWord ++ tailWord_2133696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133696).length < 2 ^ (prefixWord ++ tailWord_2133696).sum := by decide
  have hdescent : baseEnd_2133696 < baseStart_2133696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133713 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2133713 : Nat := 118140960795 + 2133713 * 2 ^ 59
def prefixEnd_2133713 : Nat := 4983230072969 + 3 ^ 40 * 2133713 * 2
def baseEnd_2133713 : Nat := 730413565164610381183159

theorem tailTrace_2133713 : CollatzResearch.WordTrace tailWord_2133713 prefixEnd_2133713 730413565164610381183159 := by
  unfold tailWord_2133713
  simp only [CollatzResearch.WordTrace]
  refine ⟨77822906518929685013413793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51881937679286456675609195 77822906518929685013413793)
  ·
    refine ⟨58367179889197263760060345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77822906518929685013413793 58367179889197263760060345)
    ·
      refine ⟨43775384916897947820045259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58367179889197263760060345 43775384916897947820045259)
      ·
        refine ⟨65663077375346921730067889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43775384916897947820045259 65663077375346921730067889)
        ·
          refine ⟨49247308031510191297550917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65663077375346921730067889 49247308031510191297550917)
          ·
            refine ⟨9233870255908160868290797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49247308031510191297550917 9233870255908160868290797)
            ·
              refine ⟨3462701345965560325609049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9233870255908160868290797 3462701345965560325609049)
              ·
                refine ⟨2597026009474170244206787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462701345965560325609049 2597026009474170244206787)
                ·
                  refine ⟨3895539014211255366310181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597026009474170244206787 3895539014211255366310181)
                  ·
                    refine ⟨730413565164610381183159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3895539014211255366310181 730413565164610381183159)
                    ·
                      rfl

theorem cell22_2133713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2133713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133713 prefixEnd_2133713 := by exact prefixLift 2133713
  have htrace : WordTrace (prefixWord ++ tailWord_2133713) baseStart_2133713 baseEnd_2133713 := by
    simpa [prefixWord, tailWord_2133713, baseEnd_2133713] using wordTrace_append hprefix tailTrace_2133713
  have hstable : (prefixWord ++ tailWord_2133713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133713).length < 2 ^ (prefixWord ++ tailWord_2133713).sum := by decide
  have hdescent : baseEnd_2133713 < baseStart_2133713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133745 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 4]
def baseStart_2133745 : Nat := 118140960795 + 2133745 * 2 ^ 59
def prefixEnd_2133745 : Nat := 4983230072969 + 3 ^ 40 * 2133745 * 2
def baseEnd_2133745 : Nat := 243474839806190988127687

theorem tailTrace_2133745 : CollatzResearch.WordTrace tailWord_2133745 prefixEnd_2133745 243474839806190988127687 := by
  unfold tailWord_2133745
  simp only [CollatzResearch.WordTrace]
  refine ⟨77824073654813754478578689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51882715769875836319052459 77824073654813754478578689)
  ·
    refine ⟨58368055241110315858934017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77824073654813754478578689 58368055241110315858934017)
    ·
      refine ⟨43776041430832736894200513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58368055241110315858934017 43776041430832736894200513)
      ·
        refine ⟨32832031073124552670650385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43776041430832736894200513 32832031073124552670650385)
        ·
          refine ⟨24624023304843414502987789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32832031073124552670650385 24624023304843414502987789)
          ·
            refine ⟨9234008739316280438620421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24624023304843414502987789 9234008739316280438620421)
            ·
              refine ⟨1731376638621802582241329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9234008739316280438620421 1731376638621802582241329)
              ·
                refine ⟨1298532478966351936680997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731376638621802582241329 1298532478966351936680997)
                ·
                  refine ⟨243474839806190988127687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298532478966351936680997 243474839806190988127687)
                  ·
                    rfl

theorem cell22_2133745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_2133745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133745 prefixEnd_2133745 := by exact prefixLift 2133745
  have htrace : WordTrace (prefixWord ++ tailWord_2133745) baseStart_2133745 baseEnd_2133745 := by
    simpa [prefixWord, tailWord_2133745, baseEnd_2133745] using wordTrace_append hprefix tailTrace_2133745
  have hstable : (prefixWord ++ tailWord_2133745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133745).length < 2 ^ (prefixWord ++ tailWord_2133745).sum := by decide
  have hdescent : baseEnd_2133745 < baseStart_2133745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133788 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2133788 : Nat := 118140960795 + 2133788 * 2 ^ 59
def prefixEnd_2133788 : Nat := 4983230072969 + 3 ^ 40 * 2133788 * 2
def baseEnd_2133788 : Nat := 730439239197335185557929

theorem tailTrace_2133788 : CollatzResearch.WordTrace tailWord_2133788 prefixEnd_2133788 730439239197335185557929 := by
  unfold tailWord_2133788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38912820996828986411197009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51883761329105315214929345 38912820996828986411197009)
  ·
    refine ⟨29184615747621739808397757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38912820996828986411197009 29184615747621739808397757)
    ·
      refine ⟨10944230905358152428149159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29184615747621739808397757 10944230905358152428149159)
      ·
        refine ⟨16416346358037228642223739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10944230905358152428149159 16416346358037228642223739)
        ·
          refine ⟨24624519537055842963335609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16416346358037228642223739 24624519537055842963335609)
          ·
            refine ⟨18468389652791882222501707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24624519537055842963335609 18468389652791882222501707)
            ·
              refine ⟨27702584479187823333752561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18468389652791882222501707 27702584479187823333752561)
              ·
                refine ⟨20776938359390867500314421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27702584479187823333752561 20776938359390867500314421)
                ·
                  refine ⟨1947837971192893828154477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20776938359390867500314421 1947837971192893828154477)
                  ·
                    refine ⟨730439239197335185557929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1947837971192893828154477 730439239197335185557929)
                    ·
                      rfl

theorem cell22_2133788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2133788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133788 prefixEnd_2133788 := by exact prefixLift 2133788
  have htrace : WordTrace (prefixWord ++ tailWord_2133788) baseStart_2133788 baseEnd_2133788 := by
    simpa [prefixWord, tailWord_2133788, baseEnd_2133788] using wordTrace_append hprefix tailTrace_2133788
  have hstable : (prefixWord ++ tailWord_2133788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133788).length < 2 ^ (prefixWord ++ tailWord_2133788).sum := by decide
  have hdescent : baseEnd_2133788 < baseStart_2133788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133895 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2133895 : Nat := 118140960795 + 2133895 * 2 ^ 59
def prefixEnd_2133895 : Nat := 4983230072969 + 3 ^ 40 * 2133895 * 2
def baseEnd_2133895 : Nat := 730475867484022573132601

theorem tailTrace_2133895 : CollatzResearch.WordTrace tailWord_2133895 prefixEnd_2133895 730475867484022573132601 := by
  unfold tailWord_2133895
  simp only [CollatzResearch.WordTrace]
  refine ⟨77829544604270330096539139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51886363069513553397692759 77829544604270330096539139)
  ·
    refine ⟨116744316906405495144808709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77829544604270330096539139 116744316906405495144808709)
    ·
      refine ⟨21889559419951030339651633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116744316906405495144808709 21889559419951030339651633)
      ·
        refine ⟨16417169564963272754738725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21889559419951030339651633 16417169564963272754738725)
        ·
          refine ⟨3078219293430613641513511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16417169564963272754738725 3078219293430613641513511)
          ·
            refine ⟨4617328940145920462270267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078219293430613641513511 4617328940145920462270267)
            ·
              refine ⟨6925993410218880693405401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617328940145920462270267 6925993410218880693405401)
              ·
                refine ⟨5194495057664160520054051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6925993410218880693405401 5194495057664160520054051)
                ·
                  refine ⟨7791742586496240780081077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5194495057664160520054051 7791742586496240780081077)
                  ·
                    refine ⟨730475867484022573132601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7791742586496240780081077 730475867484022573132601)
                    ·
                      rfl

theorem cell22_2133895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2133895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133895 prefixEnd_2133895 := by exact prefixLift 2133895
  have htrace : WordTrace (prefixWord ++ tailWord_2133895) baseStart_2133895 baseEnd_2133895 := by
    simpa [prefixWord, tailWord_2133895, baseEnd_2133895] using wordTrace_append hprefix tailTrace_2133895
  have hstable : (prefixWord ++ tailWord_2133895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133895).length < 2 ^ (prefixWord ++ tailWord_2133895).sum := by decide
  have hdescent : baseEnd_2133895 < baseStart_2133895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133908 : List Nat := [2, 4, 2, 1, 1, 12]
def baseStart_2133908 : Nat := 118140960795 + 2133908 * 2 ^ 59
def prefixEnd_2133908 : Nat := 4983230072969 + 3 ^ 40 * 2133908 * 2
def baseEnd_2133908 : Nat := 9018275526539442871081

theorem tailTrace_2133908 : CollatzResearch.WordTrace tailWord_2133908 prefixEnd_2133908 9018275526539442871081 := by
  unfold tailWord_2133908
  simp only [CollatzResearch.WordTrace]
  refine ⟨38915009376611616658381189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51886679168815488877841585 38915009376611616658381189)
  ·
    refine ⟨7296564258114678123446473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38915009376611616658381189 7296564258114678123446473)
    ·
      refine ⟨5472423193586008592584855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7296564258114678123446473 5472423193586008592584855)
      ·
        refine ⟨8208634790379012888877283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472423193586008592584855 8208634790379012888877283)
        ·
          refine ⟨12312952185568519333315925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208634790379012888877283 12312952185568519333315925)
          ·
            refine ⟨9018275526539442871081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12312952185568519333315925 9018275526539442871081)
            ·
              rfl

theorem cell22_2133908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 12].length) (baseStart_2133908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133908 prefixEnd_2133908 := by exact prefixLift 2133908
  have htrace : WordTrace (prefixWord ++ tailWord_2133908) baseStart_2133908 baseEnd_2133908 := by
    simpa [prefixWord, tailWord_2133908, baseEnd_2133908] using wordTrace_append hprefix tailTrace_2133908
  have hstable : (prefixWord ++ tailWord_2133908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133908).length < 2 ^ (prefixWord ++ tailWord_2133908).sum := by decide
  have hdescent : baseEnd_2133908 < baseStart_2133908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133914 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_2133914 : Nat := 118140960795 + 2133914 * 2 ^ 59
def prefixEnd_2133914 : Nat := 4983230072969 + 3 ^ 40 * 2133914 * 2
def baseEnd_2133914 : Nat := 243494123857437618969181

theorem tailTrace_2133914 : CollatzResearch.WordTrace tailWord_2133914 prefixEnd_2133914 243494123857437618969181 := by
  unfold tailWord_2133914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19457559397800374085370199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51886825060800997560987197 19457559397800374085370199)
  ·
    refine ⟨29186339096700561128055299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19457559397800374085370199 29186339096700561128055299)
    ·
      refine ⟨43779508645050841692082949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29186339096700561128055299 43779508645050841692082949)
      ·
        refine ⟨8208657870947032817265553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43779508645050841692082949 8208657870947032817265553)
        ·
          refine ⟨6156493403210274612949165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8208657870947032817265553 6156493403210274612949165)
          ·
            refine ⟨2308685026203852979855937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6156493403210274612949165 2308685026203852979855937)
            ·
              refine ⟨1731513769652889734891953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308685026203852979855937 1731513769652889734891953)
              ·
                refine ⟨1298635327239667301168965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731513769652889734891953 1298635327239667301168965)
                ·
                  refine ⟨243494123857437618969181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298635327239667301168965 243494123857437618969181)
                  ·
                    rfl

theorem cell22_2133914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_2133914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133914 prefixEnd_2133914 := by exact prefixLift 2133914
  have htrace : WordTrace (prefixWord ++ tailWord_2133914) baseStart_2133914 baseEnd_2133914 := by
    simpa [prefixWord, tailWord_2133914, baseEnd_2133914] using wordTrace_append hprefix tailTrace_2133914
  have hstable : (prefixWord ++ tailWord_2133914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133914).length < 2 ^ (prefixWord ++ tailWord_2133914).sum := by decide
  have hdescent : baseEnd_2133914 < baseStart_2133914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133968 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_2133968 : Nat := 118140960795 + 2133968 * 2 ^ 59
def prefixEnd_2133968 : Nat := 4983230072969 + 3 ^ 40 * 2133968 * 2
def baseEnd_2133968 : Nat := 730500856875874716057377

theorem tailTrace_2133968 : CollatzResearch.WordTrace tailWord_2133968 prefixEnd_2133968 730500856875874716057377 := by
  unfold tailWord_2133968
  simp only [CollatzResearch.WordTrace]
  refine ⟨38916103566502931781973279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51888138088670575709297705 38916103566502931781973279)
  ·
    refine ⟨58374155349754397672959919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38916103566502931781973279 58374155349754397672959919)
    ·
      refine ⟨87561233024631596509439879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58374155349754397672959919 87561233024631596509439879)
      ·
        refine ⟨131341849536947394764159819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87561233024631596509439879 131341849536947394764159819)
        ·
          refine ⟨197012774305421092146239729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131341849536947394764159819 197012774305421092146239729)
          ·
            refine ⟨147759580729065819109679797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197012774305421092146239729 147759580729065819109679797)
            ·
              refine ⟨13852460693349920541532481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147759580729065819109679797 13852460693349920541532481)
              ·
                refine ⟨10389345520012440406149361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13852460693349920541532481 10389345520012440406149361)
                ·
                  refine ⟨7792009140009330304612021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10389345520012440406149361 7792009140009330304612021)
                  ·
                    refine ⟨730500856875874716057377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7792009140009330304612021 730500856875874716057377)
                    ·
                      rfl

theorem cell22_2133968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_2133968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133968 prefixEnd_2133968 := by exact prefixLift 2133968
  have htrace : WordTrace (prefixWord ++ tailWord_2133968) baseStart_2133968 baseEnd_2133968 := by
    simpa [prefixWord, tailWord_2133968, baseEnd_2133968] using wordTrace_append hprefix tailTrace_2133968
  have hstable : (prefixWord ++ tailWord_2133968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133968).length < 2 ^ (prefixWord ++ tailWord_2133968).sum := by decide
  have hdescent : baseEnd_2133968 < baseStart_2133968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2133987 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 5]
def baseStart_2133987 : Nat := 118140960795 + 2133987 * 2 ^ 59
def prefixEnd_2133987 : Nat := 4983230072969 + 3 ^ 40 * 2133987 * 2
def baseEnd_2133987 : Nat := 243502453654721666610773

theorem tailTrace_2133987 : CollatzResearch.WordTrace tailWord_2133987 prefixEnd_2133987 243502453654721666610773 := by
  unfold tailWord_2133987
  simp only [CollatzResearch.WordTrace]
  refine ⟨77832900119937029808888215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51888600079958019872592143 77832900119937029808888215)
  ·
    refine ⟨116749350179905544713332323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77832900119937029808888215 116749350179905544713332323)
    ·
      refine ⟨175124025269858317069998485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116749350179905544713332323 175124025269858317069998485)
      ·
        refine ⟨8208938684524608612656179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175124025269858317069998485 8208938684524608612656179)
        ·
          refine ⟨12313408026786912918984269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8208938684524608612656179 12313408026786912918984269)
          ·
            refine ⟨4617528010045092344619101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12313408026786912918984269 4617528010045092344619101)
            ·
              refine ⟨1731573003766909629232163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4617528010045092344619101 1731573003766909629232163)
              ·
                refine ⟨2597359505650364443848245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1731573003766909629232163 2597359505650364443848245)
                ·
                  refine ⟨243502453654721666610773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597359505650364443848245 243502453654721666610773)
                  ·
                    rfl

theorem cell22_2133987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 5].length) (baseStart_2133987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2133987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2133987 prefixEnd_2133987 := by exact prefixLift 2133987
  have htrace : WordTrace (prefixWord ++ tailWord_2133987) baseStart_2133987 baseEnd_2133987 := by
    simpa [prefixWord, tailWord_2133987, baseEnd_2133987] using wordTrace_append hprefix tailTrace_2133987
  have hstable : (prefixWord ++ tailWord_2133987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2133987).length < 2 ^ (prefixWord ++ tailWord_2133987).sum := by decide
  have hdescent : baseEnd_2133987 < baseStart_2133987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2133987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134000 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_2134000 : Nat := 118140960795 + 2134000 * 2 ^ 59
def prefixEnd_2134000 : Nat := 4983230072969 + 3 ^ 40 * 2134000 * 2
def baseEnd_2134000 : Nat := 730511811129837299257279

theorem tailTrace_2134000 : CollatzResearch.WordTrace tailWord_2134000 prefixEnd_2134000 730511811129837299257279 := by
  unfold tailWord_2134000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38916687134444966514555727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51888916179259955352740969 38916687134444966514555727)
  ·
    refine ⟨58375030701667449771833591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38916687134444966514555727 58375030701667449771833591)
    ·
      refine ⟨87562546052501174657750387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58375030701667449771833591 87562546052501174657750387)
      ·
        refine ⟨131343819078751761986625581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87562546052501174657750387 131343819078751761986625581)
        ·
          refine ⟨49253932154531910744984593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131343819078751761986625581 49253932154531910744984593)
          ·
            refine ⟨36940449115898933058738445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49253932154531910744984593 36940449115898933058738445)
            ·
              refine ⟨13852668418462099897026917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36940449115898933058738445 13852668418462099897026917)
              ·
                refine ⟨2597375328461643730692547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13852668418462099897026917 2597375328461643730692547)
                ·
                  refine ⟨3896062992692465596038821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2597375328461643730692547 3896062992692465596038821)
                  ·
                    refine ⟨730511811129837299257279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3896062992692465596038821 730511811129837299257279)
                    ·
                      rfl

theorem cell22_2134000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_2134000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134000 prefixEnd_2134000 := by exact prefixLift 2134000
  have htrace : WordTrace (prefixWord ++ tailWord_2134000) baseStart_2134000 baseEnd_2134000 := by
    simpa [prefixWord, tailWord_2134000, baseEnd_2134000] using wordTrace_append hprefix tailTrace_2134000
  have hstable : (prefixWord ++ tailWord_2134000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134000).length < 2 ^ (prefixWord ++ tailWord_2134000).sum := by decide
  have hdescent : baseEnd_2134000 < baseStart_2134000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134047 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 2, 3]
def baseStart_2134047 : Nat := 118140960795 + 2134047 * 2 ^ 59
def prefixEnd_2134047 : Nat := 4983230072969 + 3 ^ 40 * 2134047 * 2
def baseEnd_2134047 : Nat := 730527900190344843332135

theorem tailTrace_2134047 : CollatzResearch.WordTrace tailWord_2134047 prefixEnd_2134047 730527900190344843332135 := by
  unfold tailWord_2134047
  simp only [CollatzResearch.WordTrace]
  refine ⟨77835088499719660056072395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51890058999813106704048263 77835088499719660056072395)
  ·
    refine ⟨116752632749579490084108593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77835088499719660056072395 116752632749579490084108593)
    ·
      refine ⟨87564474562184617563081445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116752632749579490084108593 87564474562184617563081445)
      ·
        refine ⟨16418338980409615793077771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87564474562184617563081445 16418338980409615793077771)
        ·
          refine ⟨24627508470614423689616657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16418338980409615793077771 24627508470614423689616657)
          ·
            refine ⟨18470631352960817767212493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24627508470614423689616657 18470631352960817767212493)
            ·
              refine ⟨6926486757360306662704685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18470631352960817767212493 6926486757360306662704685)
              ·
                refine ⟨2597432534010114998514257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6926486757360306662704685 2597432534010114998514257)
                ·
                  refine ⟨1948074400507586248885693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2597432534010114998514257 1948074400507586248885693)
                  ·
                    refine ⟨730527900190344843332135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948074400507586248885693 730527900190344843332135)
                    ·
                      rfl

theorem cell22_2134047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_2134047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134047 prefixEnd_2134047 := by exact prefixLift 2134047
  have htrace : WordTrace (prefixWord ++ tailWord_2134047) baseStart_2134047 baseEnd_2134047 := by
    simpa [prefixWord, tailWord_2134047, baseEnd_2134047] using wordTrace_append hprefix tailTrace_2134047
  have hstable : (prefixWord ++ tailWord_2134047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134047).length < 2 ^ (prefixWord ++ tailWord_2134047).sum := by decide
  have hdescent : baseEnd_2134047 < baseStart_2134047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134062 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2134062 : Nat := 118140960795 + 2134062 * 2 ^ 59
def prefixEnd_2134062 : Nat := 4983230072969 + 3 ^ 40 * 2134062 * 2
def baseEnd_2134062 : Nat := 730533034996889804207089

theorem tailTrace_2134062 : CollatzResearch.WordTrace tailWord_2134062 prefixEnd_2134062 730533034996889804207089 := by
  unfold tailWord_2134062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729454449333164702233555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51890423729776878411912293 9729454449333164702233555)
  ·
    refine ⟨14594181673999747053350333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9729454449333164702233555 14594181673999747053350333)
    ·
      refine ⟨5472818127749905145006375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14594181673999747053350333 5472818127749905145006375)
      ·
        refine ⟨8209227191624857717509563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472818127749905145006375 8209227191624857717509563)
        ·
          refine ⟨12313840787437286576264345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8209227191624857717509563 12313840787437286576264345)
          ·
            refine ⟨9235380590577964932198259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12313840787437286576264345 9235380590577964932198259)
            ·
              refine ⟨13853070885866947398297389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9235380590577964932198259 13853070885866947398297389)
              ·
                refine ⟨5194901582200105274361521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13853070885866947398297389 5194901582200105274361521)
                ·
                  refine ⟨3896176186650078955771141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5194901582200105274361521 3896176186650078955771141)
                  ·
                    refine ⟨730533034996889804207089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3896176186650078955771141 730533034996889804207089)
                    ·
                      rfl

theorem cell22_2134062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2134062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134062 prefixEnd_2134062 := by exact prefixLift 2134062
  have htrace : WordTrace (prefixWord ++ tailWord_2134062) baseStart_2134062 baseEnd_2134062 := by
    simpa [prefixWord, tailWord_2134062, baseEnd_2134062] using wordTrace_append hprefix tailTrace_2134062
  have hstable : (prefixWord ++ tailWord_2134062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134062).length < 2 ^ (prefixWord ++ tailWord_2134062).sum := by decide
  have hdescent : baseEnd_2134062 < baseStart_2134062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134075 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 5, 3]
def baseStart_2134075 : Nat := 118140960795 + 2134075 * 2 ^ 59
def prefixEnd_2134075 : Nat := 4983230072969 + 3 ^ 40 * 2134075 * 2
def baseEnd_2134075 : Nat := 730537485162562103632049

theorem tailTrace_2134075 : CollatzResearch.WordTrace tailWord_2134075 prefixEnd_2134075 730537485162562103632049 := by
  unfold tailWord_2134075
  simp only [CollatzResearch.WordTrace]
  refine ⟨77836109743618220838091679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51890739829078813892061119 77836109743618220838091679)
  ·
    refine ⟨116754164615427331257137519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77836109743618220838091679 116754164615427331257137519)
    ·
      refine ⟨175131246923140996885706279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116754164615427331257137519 175131246923140996885706279)
      ·
        refine ⟨262696870384711495328559419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175131246923140996885706279 262696870384711495328559419)
        ·
          refine ⟨394045305577067242992839129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262696870384711495328559419 394045305577067242992839129)
          ·
            refine ⟨295533979182800432244629347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394045305577067242992839129 295533979182800432244629347)
            ·
              refine ⟨443300968774200648366944021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295533979182800432244629347 443300968774200648366944021)
              ·
                refine ⟨20779732911290655392200501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 443300968774200648366944021 20779732911290655392200501)
                ·
                  refine ⟨1948099960433498943018797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20779732911290655392200501 1948099960433498943018797)
                  ·
                    refine ⟨730537485162562103632049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948099960433498943018797 730537485162562103632049)
                    ·
                      rfl

theorem cell22_2134075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3].length) (baseStart_2134075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134075 prefixEnd_2134075 := by exact prefixLift 2134075
  have htrace : WordTrace (prefixWord ++ tailWord_2134075) baseStart_2134075 baseEnd_2134075 := by
    simpa [prefixWord, tailWord_2134075, baseEnd_2134075] using wordTrace_append hprefix tailTrace_2134075
  have hstable : (prefixWord ++ tailWord_2134075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134075).length < 2 ^ (prefixWord ++ tailWord_2134075).sum := by decide
  have hdescent : baseEnd_2134075 < baseStart_2134075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134105 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 5]
def baseStart_2134105 : Nat := 118140960795 + 2134105 * 2 ^ 59
def prefixEnd_2134105 : Nat := 4983230072969 + 3 ^ 40 * 2134105 * 2
def baseEnd_2134105 : Nat := 243515918258550675127319

theorem tailTrace_2134105 : CollatzResearch.WordTrace tailWord_2134105 prefixEnd_2134105 243515918258550675127319 := by
  unfold tailWord_2134105
  simp only [CollatzResearch.WordTrace]
  refine ⟨77837203933509535961683769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51891469289006357307789179 77837203933509535961683769)
  ·
    refine ⟨58377902950132151971262827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77837203933509535961683769 58377902950132151971262827)
    ·
      refine ⟨87566854425198227956894241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58377902950132151971262827 87566854425198227956894241)
      ·
        refine ⟨65675140818898670967670681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87566854425198227956894241 65675140818898670967670681)
        ·
          refine ⟨49256355614174003225753011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65675140818898670967670681 49256355614174003225753011)
          ·
            refine ⟨73884533421261004838629517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49256355614174003225753011 73884533421261004838629517)
            ·
              refine ⟨27706700032972876814486069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73884533421261004838629517 27706700032972876814486069)
              ·
                refine ⟨2597503128091207201358069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27706700032972876814486069 2597503128091207201358069)
                ·
                  refine ⟨243515918258550675127319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597503128091207201358069 243515918258550675127319)
                  ·
                    rfl

theorem cell22_2134105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_2134105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134105 prefixEnd_2134105 := by exact prefixLift 2134105
  have htrace : WordTrace (prefixWord ++ tailWord_2134105) baseStart_2134105 baseEnd_2134105 := by
    simpa [prefixWord, tailWord_2134105, baseEnd_2134105] using wordTrace_append hprefix tailTrace_2134105
  have hstable : (prefixWord ++ tailWord_2134105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134105).length < 2 ^ (prefixWord ++ tailWord_2134105).sum := by decide
  have hdescent : baseEnd_2134105 < baseStart_2134105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134109 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2134109 : Nat := 118140960795 + 2134109 * 2 ^ 59
def prefixEnd_2134109 : Nat := 4983230072969 + 3 ^ 40 * 2134109 * 2
def baseEnd_2134109 : Nat := 730549124057397348281945

theorem tailTrace_2134109 : CollatzResearch.WordTrace tailWord_2134109 prefixEnd_2134109 730549124057397348281945 := by
  unfold tailWord_2134109
  simp only [CollatzResearch.WordTrace]
  refine ⟨77837349825495044644829381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51891566550330029763219587 77837349825495044644829381)
  ·
    refine ⟨14594503092280320870905509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77837349825495044644829381 14594503092280320870905509)
    ·
      refine ⟨2736469329802560163294783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14594503092280320870905509 2736469329802560163294783)
      ·
        refine ⟨4104703994703840244942175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736469329802560163294783 4104703994703840244942175)
        ·
          refine ⟨6157055992055760367413263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104703994703840244942175 6157055992055760367413263)
          ·
            refine ⟨9235583988083640551119895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157055992055760367413263 9235583988083640551119895)
            ·
              refine ⟨13853375982125460826679843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9235583988083640551119895 13853375982125460826679843)
              ·
                refine ⟨20780063973188191240019765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13853375982125460826679843 20780063973188191240019765)
                ·
                  refine ⟨1948130997486392928751853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20780063973188191240019765 1948130997486392928751853)
                  ·
                    refine ⟨730549124057397348281945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948130997486392928751853 730549124057397348281945)
                    ·
                      rfl

theorem cell22_2134109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2134109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134109 prefixEnd_2134109 := by exact prefixLift 2134109
  have htrace : WordTrace (prefixWord ++ tailWord_2134109) baseStart_2134109 baseEnd_2134109 := by
    simpa [prefixWord, tailWord_2134109, baseEnd_2134109] using wordTrace_append hprefix tailTrace_2134109
  have hstable : (prefixWord ++ tailWord_2134109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134109).length < 2 ^ (prefixWord ++ tailWord_2134109).sum := by decide
  have hdescent : baseEnd_2134109 < baseStart_2134109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134126 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2134126 : Nat := 118140960795 + 2134126 * 2 ^ 59
def prefixEnd_2134126 : Nat := 4983230072969 + 3 ^ 40 * 2134126 * 2
def baseEnd_2134126 : Nat := 730554943504814970606893

theorem tailTrace_2134126 : CollatzResearch.WordTrace tailWord_2134126 prefixEnd_2134126 730554943504814970606893 := by
  unfold tailWord_2134126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729746233304182068524779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51891979910955637698798821 9729746233304182068524779)
  ·
    refine ⟨14594619349956273102787169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9729746233304182068524779 14594619349956273102787169)
    ·
      refine ⟨10945964512467204827090377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14594619349956273102787169 10945964512467204827090377)
      ·
        refine ⟨8209473384350403620317783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10945964512467204827090377 8209473384350403620317783)
        ·
          refine ⟨12314210076525605430476675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8209473384350403620317783 12314210076525605430476675)
          ·
            refine ⟨18471315114788408145715013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12314210076525605430476675 18471315114788408145715013)
            ·
              refine ⟨3463371584022826527321565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18471315114788408145715013 3463371584022826527321565)
              ·
                refine ⟨1298764344008559947745587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3463371584022826527321565 1298764344008559947745587)
                ·
                  refine ⟨1948146516012839921618381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298764344008559947745587 1948146516012839921618381)
                  ·
                    refine ⟨730554943504814970606893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948146516012839921618381 730554943504814970606893)
                    ·
                      rfl

theorem cell22_2134126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2134126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134126 prefixEnd_2134126 := by exact prefixLift 2134126
  have htrace : WordTrace (prefixWord ++ tailWord_2134126) baseStart_2134126 baseEnd_2134126 := by
    simpa [prefixWord, tailWord_2134126, baseEnd_2134126] using wordTrace_append hprefix tailTrace_2134126
  have hstable : (prefixWord ++ tailWord_2134126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134126).length < 2 ^ (prefixWord ++ tailWord_2134126).sum := by decide
  have hdescent : baseEnd_2134126 < baseStart_2134126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134212 : List Nat := [2, 3, 3, 1, 2, 1, 1, 9]
def baseStart_2134212 : Nat := 118140960795 + 2134212 * 2 ^ 59
def prefixEnd_2134212 : Nat := 4983230072969 + 3 ^ 40 * 2134212 * 2
def baseEnd_2134212 : Nat := 81176042562482156995181

theorem tailTrace_2134212 : CollatzResearch.WordTrace tailWord_2134212 prefixEnd_2134212 81176042562482156995181 := by
  unfold tailWord_2134212
  simp only [CollatzResearch.WordTrace]
  refine ⟨38920553272060946617914445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51894071029414595490552593 38920553272060946617914445)
  ·
    refine ⟨14595207477022854981717917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38920553272060946617914445 14595207477022854981717917)
    ·
      refine ⟨5473202803883570618144219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14595207477022854981717917 5473202803883570618144219)
      ·
        refine ⟨8209804205825355927216329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5473202803883570618144219 8209804205825355927216329)
        ·
          refine ⟨6157353154369016945412247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8209804205825355927216329 6157353154369016945412247)
          ·
            refine ⟨9236029731553525418118371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157353154369016945412247 9236029731553525418118371)
            ·
              refine ⟨13854044597330288127177557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9236029731553525418118371 13854044597330288127177557)
              ·
                refine ⟨81176042562482156995181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13854044597330288127177557 81176042562482156995181)
                ·
                  rfl

theorem cell22_2134212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_2134212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134212 prefixEnd_2134212 := by exact prefixLift 2134212
  have htrace : WordTrace (prefixWord ++ tailWord_2134212) baseStart_2134212 baseEnd_2134212 := by
    simpa [prefixWord, tailWord_2134212, baseEnd_2134212] using wordTrace_append hprefix tailTrace_2134212
  have hstable : (prefixWord ++ tailWord_2134212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134212).length < 2 ^ (prefixWord ++ tailWord_2134212).sum := by decide
  have hdescent : baseEnd_2134212 < baseStart_2134212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134257 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 5]
def baseStart_2134257 : Nat := 118140960795 + 2134257 * 2 ^ 59
def prefixEnd_2134257 : Nat := 4983230072969 + 3 ^ 40 * 2134257 * 2
def baseEnd_2134257 : Nat := 243533262493991431860497

theorem tailTrace_2134257 : CollatzResearch.WordTrace tailWord_2134257 prefixEnd_2134257 243533262493991431860497 := by
  unfold tailWord_2134257
  simp only [CollatzResearch.WordTrace]
  refine ⟨77842747828958865921217025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51895165219305910614144683 77842747828958865921217025)
  ·
    refine ⟨58382060871719149440912769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77842747828958865921217025 58382060871719149440912769)
    ·
      refine ⟨43786545653789362080684577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58382060871719149440912769 43786545653789362080684577)
      ·
        refine ⟨32839909240342021560513433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43786545653789362080684577 32839909240342021560513433)
        ·
          refine ⟨24629931930256516170385075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32839909240342021560513433 24629931930256516170385075)
          ·
            refine ⟨36944897895384774255577613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24629931930256516170385075 36944897895384774255577613)
            ·
              refine ⟨13854336710769290345841605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36944897895384774255577613 13854336710769290345841605)
              ·
                refine ⟨2597688133269241939845301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13854336710769290345841605 2597688133269241939845301)
                ·
                  refine ⟨243533262493991431860497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597688133269241939845301 243533262493991431860497)
                  ·
                    rfl

theorem cell22_2134257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_2134257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134257 prefixEnd_2134257 := by exact prefixLift 2134257
  have htrace : WordTrace (prefixWord ++ tailWord_2134257) baseStart_2134257 baseEnd_2134257 := by
    simpa [prefixWord, tailWord_2134257, baseEnd_2134257] using wordTrace_append hprefix tailTrace_2134257
  have hstable : (prefixWord ++ tailWord_2134257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134257).length < 2 ^ (prefixWord ++ tailWord_2134257).sum := by decide
  have hdescent : baseEnd_2134257 < baseStart_2134257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134319 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 4]
def baseStart_2134319 : Nat := 118140960795 + 2134319 * 2 ^ 59
def prefixEnd_2134319 : Nat := 4983230072969 + 3 ^ 40 * 2134319 * 2
def baseEnd_2134319 : Nat := 243540337116342266843767

theorem tailTrace_2134319 : CollatzResearch.WordTrace tailWord_2134319 prefixEnd_2134319 243540337116342266843767 := by
  unfold tailWord_2134319
  simp only [CollatzResearch.WordTrace]
  refine ⟨77845009154734250509974011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51896672769822833673316007 77845009154734250509974011)
  ·
    refine ⟨116767513732101375764961017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77845009154734250509974011 116767513732101375764961017)
    ·
      refine ⟨87575635299076031823720763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116767513732101375764961017 87575635299076031823720763)
      ·
        refine ⟨131363452948614047735581145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87575635299076031823720763 131363452948614047735581145)
        ·
          refine ⟨98522589711460535801685859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131363452948614047735581145 98522589711460535801685859)
          ·
            refine ⟨147783884567190803702528789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98522589711460535801685859 147783884567190803702528789)
            ·
              refine ⟨6927369589087068923556037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147783884567190803702528789 6927369589087068923556037)
              ·
                refine ⟨1298881797953825423166757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6927369589087068923556037 1298881797953825423166757)
                ·
                  refine ⟨243540337116342266843767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298881797953825423166757 243540337116342266843767)
                  ·
                    rfl

theorem cell22_2134319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 4].length) (baseStart_2134319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134319 prefixEnd_2134319 := by exact prefixLift 2134319
  have htrace : WordTrace (prefixWord ++ tailWord_2134319) baseStart_2134319 baseEnd_2134319 := by
    simpa [prefixWord, tailWord_2134319, baseEnd_2134319] using wordTrace_append hprefix tailTrace_2134319
  have hstable : (prefixWord ++ tailWord_2134319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134319).length < 2 ^ (prefixWord ++ tailWord_2134319).sum := by decide
  have hdescent : baseEnd_2134319 < baseStart_2134319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134332 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2134332 : Nat := 118140960795 + 2134332 * 2 ^ 59
def prefixEnd_2134332 : Nat := 4983230072969 + 3 ^ 40 * 2134332 * 2
def baseEnd_2134332 : Nat := 730625461514699099956261

theorem tailTrace_2134332 : CollatzResearch.WordTrace tailWord_2134332 prefixEnd_2134332 730625461514699099956261 := by
  unfold tailWord_2134332
  simp only [CollatzResearch.WordTrace]
  refine ⟨38922741651843576865098625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51896988869124769153464833 38922741651843576865098625)
  ·
    refine ⟨29192056238882682648823969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38922741651843576865098625 29192056238882682648823969)
    ·
      refine ⟨21894042179162011986617977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29192056238882682648823969 21894042179162011986617977)
      ·
        refine ⟨16420531634371508989963483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21894042179162011986617977 16420531634371508989963483)
        ·
          refine ⟨24630797451557263484945225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16420531634371508989963483 24630797451557263484945225)
          ·
            refine ⟨18473098088667947613708919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24630797451557263484945225 18473098088667947613708919)
            ·
              refine ⟨27709647133001921420563379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18473098088667947613708919 27709647133001921420563379)
              ·
                refine ⟨41564470699502882130845069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27709647133001921420563379 41564470699502882130845069)
                ·
                  refine ⟨15586676512313580799066901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41564470699502882130845069 15586676512313580799066901)
                  ·
                    refine ⟨730625461514699099956261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15586676512313580799066901 730625461514699099956261)
                    ·
                      rfl

theorem cell22_2134332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2134332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134332 prefixEnd_2134332 := by exact prefixLift 2134332
  have htrace : WordTrace (prefixWord ++ tailWord_2134332) baseStart_2134332 baseEnd_2134332 := by
    simpa [prefixWord, tailWord_2134332, baseEnd_2134332] using wordTrace_append hprefix tailTrace_2134332
  have hstable : (prefixWord ++ tailWord_2134332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134332).length < 2 ^ (prefixWord ++ tailWord_2134332).sum := by decide
  have hdescent : baseEnd_2134332 < baseStart_2134332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134377 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_2134377 : Nat := 118140960795 + 2134377 * 2 ^ 59
def prefixEnd_2134377 : Nat := 4983230072969 + 3 ^ 40 * 2134377 * 2
def baseEnd_2134377 : Nat := 730640865934333982581123

theorem tailTrace_2134377 : CollatzResearch.WordTrace tailWord_2134377 prefixEnd_2134377 730640865934333982581123 := by
  unfold tailWord_2134377
  simp only [CollatzResearch.WordTrace]
  refine ⟨77847124588524126415585385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51898083059016084277056923 77847124588524126415585385)
  ·
    refine ⟨58385343441393094811689039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77847124588524126415585385 58385343441393094811689039)
    ·
      refine ⟨87578015162089642217533559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58385343441393094811689039 87578015162089642217533559)
      ·
        refine ⟨131367022743134463326300339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87578015162089642217533559 131367022743134463326300339)
        ·
          refine ⟨197050534114701694989450509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131367022743134463326300339 197050534114701694989450509)
          ·
            refine ⟨73893950293013135621043941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197050534114701694989450509 73893950293013135621043941)
            ·
              refine ⟨13855115679939962928945739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73893950293013135621043941 13855115679939962928945739)
              ·
                refine ⟨20782673519909944393418609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13855115679939962928945739 20782673519909944393418609)
                ·
                  refine ⟨15587005139932458295063957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20782673519909944393418609 15587005139932458295063957)
                  ·
                    refine ⟨730640865934333982581123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15587005139932458295063957 730640865934333982581123)
                    ·
                      rfl

theorem cell22_2134377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_2134377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134377 prefixEnd_2134377 := by exact prefixLift 2134377
  have htrace : WordTrace (prefixWord ++ tailWord_2134377) baseStart_2134377 baseEnd_2134377 := by
    simpa [prefixWord, tailWord_2134377, baseEnd_2134377] using wordTrace_append hprefix tailTrace_2134377
  have hstable : (prefixWord ++ tailWord_2134377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134377).length < 2 ^ (prefixWord ++ tailWord_2134377).sum := by decide
  have hdescent : baseEnd_2134377 < baseStart_2134377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134426 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_2134426 : Nat := 118140960795 + 2134426 * 2 ^ 59
def prefixEnd_2134426 : Nat := 4983230072969 + 3 ^ 40 * 2134426 * 2
def baseEnd_2134426 : Nat := 243552546545238062701991

theorem tailTrace_2134426 : CollatzResearch.WordTrace tailWord_2134426 prefixEnd_2134426 243552546545238062701991 := by
  unfold tailWord_2134426
  simp only [CollatzResearch.WordTrace]
  refine ⟨19462227941336651946029783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51899274510231071856079421 19462227941336651946029783)
  ·
    refine ⟨29193341912004977919044675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19462227941336651946029783 29193341912004977919044675)
    ·
      refine ⟨43790012868007466878567013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29193341912004977919044675 43790012868007466878567013)
      ·
        refine ⟨8210627412751400039731315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43790012868007466878567013 8210627412751400039731315)
        ·
          refine ⟨12315941119127100059596973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210627412751400039731315 12315941119127100059596973)
          ·
            refine ⟨4618477919672662522348865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12315941119127100059596973 4618477919672662522348865)
            ·
              refine ⟨3463858439754496891761649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4618477919672662522348865 3463858439754496891761649)
              ·
                refine ⟨2597893829815872668821237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3463858439754496891761649 2597893829815872668821237)
                ·
                  refine ⟨243552546545238062701991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597893829815872668821237 243552546545238062701991)
                  ·
                    rfl

theorem cell22_2134426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_2134426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134426 prefixEnd_2134426 := by exact prefixLift 2134426
  have htrace : WordTrace (prefixWord ++ tailWord_2134426) baseStart_2134426 baseEnd_2134426 := by
    simpa [prefixWord, tailWord_2134426, baseEnd_2134426] using wordTrace_append hprefix tailTrace_2134426
  have hstable : (prefixWord ++ tailWord_2134426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134426).length < 2 ^ (prefixWord ++ tailWord_2134426).sum := by decide
  have hdescent : baseEnd_2134426 < baseStart_2134426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134471 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 4]
def baseStart_2134471 : Nat := 118140960795 + 2134471 * 2 ^ 59
def prefixEnd_2134471 : Nat := 4983230072969 + 3 ^ 40 * 2134471 * 2
def baseEnd_2134471 : Nat := 243557681351783023576945

theorem tailTrace_2134471 : CollatzResearch.WordTrace tailWord_2134471 prefixEnd_2134471 243557681351783023576945 := by
  unfold tailWord_2134471
  simp only [CollatzResearch.WordTrace]
  refine ⟨77850553050183580469507267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51900368700122386979671511 77850553050183580469507267)
  ·
    refine ⟨116775829575275370704260901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77850553050183580469507267 116775829575275370704260901)
    ·
      refine ⟨21895468045364132007048919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116775829575275370704260901 21895468045364132007048919)
      ·
        refine ⟨32843202068046198010573379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21895468045364132007048919 32843202068046198010573379)
        ·
          refine ⟨49264803102069297015860069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32843202068046198010573379 49264803102069297015860069)
          ·
            refine ⟨9237150581637993190473763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49264803102069297015860069 9237150581637993190473763)
            ·
              refine ⟨13855725872456989785710645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9237150581637993190473763 13855725872456989785710645)
              ·
                refine ⟨1298974300542842792410373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13855725872456989785710645 1298974300542842792410373)
                ·
                  refine ⟨243557681351783023576945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298974300542842792410373 243557681351783023576945)
                  ·
                    rfl

theorem cell22_2134471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 4].length) (baseStart_2134471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134471 prefixEnd_2134471 := by exact prefixLift 2134471
  have htrace : WordTrace (prefixWord ++ tailWord_2134471) baseStart_2134471 baseEnd_2134471 := by
    simpa [prefixWord, tailWord_2134471, baseEnd_2134471] using wordTrace_append hprefix tailTrace_2134471
  have hstable : (prefixWord ++ tailWord_2134471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134471).length < 2 ^ (prefixWord ++ tailWord_2134471).sum := by decide
  have hdescent : baseEnd_2134471 < baseStart_2134471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134559 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_2134559 : Nat := 118140960795 + 2134559 * 2 ^ 59
def prefixEnd_2134559 : Nat := 4983230072969 + 3 ^ 40 * 2134559 * 2
def baseEnd_2134559 : Nat := 730703168253746174530565

theorem tailTrace_2134559 : CollatzResearch.WordTrace tailWord_2134559 prefixEnd_2134559 730703168253746174530565 := by
  unfold tailWord_2134559
  simp only [CollatzResearch.WordTrace]
  refine ⟨77853762673864771498710731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51902508449243180999140487 77853762673864771498710731)
  ·
    refine ⟨116780644010797157248066097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77853762673864771498710731 116780644010797157248066097)
    ·
      refine ⟨87585483008097867936049573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116780644010797157248066097 87585483008097867936049573)
      ·
        refine ⟨16422278064018350238009295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87585483008097867936049573 16422278064018350238009295)
        ·
          refine ⟨24633417096027525357013943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16422278064018350238009295 24633417096027525357013943)
          ·
            refine ⟨36950125644041288035520915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24633417096027525357013943 36950125644041288035520915)
            ·
              refine ⟨55425188466061932053281373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36950125644041288035520915 55425188466061932053281373)
              ·
                refine ⟨20784445674773224519980515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55425188466061932053281373 20784445674773224519980515)
                ·
                  refine ⟨31176668512159836779970773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20784445674773224519980515 31176668512159836779970773)
                  ·
                    refine ⟨730703168253746174530565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31176668512159836779970773 730703168253746174530565)
                    ·
                      rfl

theorem cell22_2134559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_2134559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134559 prefixEnd_2134559 := by exact prefixLift 2134559
  have htrace : WordTrace (prefixWord ++ tailWord_2134559) baseStart_2134559 baseEnd_2134559 := by
    simpa [prefixWord, tailWord_2134559, baseEnd_2134559] using wordTrace_append hprefix tailTrace_2134559
  have hstable : (prefixWord ++ tailWord_2134559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134559).length < 2 ^ (prefixWord ++ tailWord_2134559).sum := by decide
  have hdescent : baseEnd_2134559 < baseStart_2134559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134561 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 5]
def baseStart_2134561 : Nat := 118140960795 + 2134561 * 2 ^ 59
def prefixEnd_2134561 : Nat := 4983230072969 + 3 ^ 40 * 2134561 * 2
def baseEnd_2134561 : Nat := 243567950964872945326853

theorem tailTrace_2134561 : CollatzResearch.WordTrace tailWord_2134561 prefixEnd_2134561 243567950964872945326853 := by
  unfold tailWord_2134561
  simp only [CollatzResearch.WordTrace]
  refine ⟨77853835619857525840283537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51902557079905017226855691 77853835619857525840283537)
  ·
    refine ⟨58390376714893144380212653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77853835619857525840283537 58390376714893144380212653)
    ·
      refine ⟨21896391268084929142579745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58390376714893144380212653 21896391268084929142579745)
      ·
        refine ⟨16422293451063696856934809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21896391268084929142579745 16422293451063696856934809)
        ·
          refine ⟨12316720088297772642701107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16422293451063696856934809 12316720088297772642701107)
          ·
            refine ⟨18475080132446658964051661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12316720088297772642701107 18475080132446658964051661)
            ·
              refine ⟨6928155049667497111519373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18475080132446658964051661 6928155049667497111519373)
              ·
                refine ⟨2598058143625311416819765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6928155049667497111519373 2598058143625311416819765)
                ·
                  refine ⟨243567950964872945326853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598058143625311416819765 243567950964872945326853)
                  ·
                    rfl

theorem cell22_2134561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_2134561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134561 prefixEnd_2134561 := by exact prefixLift 2134561
  have htrace : WordTrace (prefixWord ++ tailWord_2134561) baseStart_2134561 baseEnd_2134561 := by
    simpa [prefixWord, tailWord_2134561, baseEnd_2134561] using wordTrace_append hprefix tailTrace_2134561
  have hstable : (prefixWord ++ tailWord_2134561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134561).length < 2 ^ (prefixWord ++ tailWord_2134561).sum := by decide
  have hdescent : baseEnd_2134561 < baseStart_2134561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134638 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2134638 : Nat := 118140960795 + 2134638 * 2 ^ 59
def prefixEnd_2134638 : Nat := 4983230072969 + 3 ^ 40 * 2134638 * 2
def baseEnd_2134638 : Nat := 730730211568216301805323

theorem tailTrace_2134638 : CollatzResearch.WordTrace tailWord_2134638 prefixEnd_2134638 730730211568216301805323 := by
  unfold tailWord_2134638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732080505072320998854571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51904429360385711993891045 9732080505072320998854571)
  ·
    refine ⟨14598120757608481498281857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9732080505072320998854571 14598120757608481498281857)
    ·
      refine ⟨10948590568206361123711393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14598120757608481498281857 10948590568206361123711393)
      ·
        refine ⟨8211442926154770842783545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10948590568206361123711393 8211442926154770842783545)
        ·
          refine ⟨6158582194616078132087659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8211442926154770842783545 6158582194616078132087659)
          ·
            refine ⟨9237873291924117198131489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158582194616078132087659 9237873291924117198131489)
            ·
              refine ⟨6928404968943087898598617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9237873291924117198131489 6928404968943087898598617)
              ·
                refine ⟨5196303726707315923948963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6928404968943087898598617 5196303726707315923948963)
                ·
                  refine ⟨7794455590060973885923445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5196303726707315923948963 7794455590060973885923445)
                  ·
                    refine ⟨730730211568216301805323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7794455590060973885923445 730730211568216301805323)
                    ·
                      rfl

theorem cell22_2134638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2134638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134638 prefixEnd_2134638 := by exact prefixLift 2134638
  have htrace : WordTrace (prefixWord ++ tailWord_2134638) baseStart_2134638 baseEnd_2134638 := by
    simpa [prefixWord, tailWord_2134638, baseEnd_2134638] using wordTrace_append hprefix tailTrace_2134638
  have hstable : (prefixWord ++ tailWord_2134638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134638).length < 2 ^ (prefixWord ++ tailWord_2134638).sum := by decide
  have hdescent : baseEnd_2134638 < baseStart_2134638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134640 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_2134640 : Nat := 118140960795 + 2134640 * 2 ^ 59
def prefixEnd_2134640 : Nat := 4983230072969 + 3 ^ 40 * 2134640 * 2
def baseEnd_2134640 : Nat := 243576965403029654418439

theorem tailTrace_2134640 : CollatzResearch.WordTrace tailWord_2134640 prefixEnd_2134640 243576965403029654418439 := by
  unfold tailWord_2134640
  simp only [CollatzResearch.WordTrace]
  refine ⟨38928358493285661166204687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51904477991047548221606249 38928358493285661166204687)
  ·
    refine ⟨58392537739928491749307031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38928358493285661166204687 58392537739928491749307031)
    ·
      refine ⟨87588806609892737623960547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58392537739928491749307031 87588806609892737623960547)
      ·
        refine ⟨131383209914839106435940821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87588806609892737623960547 131383209914839106435940821)
        ·
          refine ⟨3079293982379041557092363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 131383209914839106435940821 3079293982379041557092363)
          ·
            refine ⟨4618940973568562335638545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079293982379041557092363 4618940973568562335638545)
            ·
              refine ⟨3464205730176421751728909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4618940973568562335638545 3464205730176421751728909)
              ·
                refine ⟨1299077148816158156898341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3464205730176421751728909 1299077148816158156898341)
                ·
                  refine ⟨243576965403029654418439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299077148816158156898341 243576965403029654418439)
                  ·
                    rfl

theorem cell22_2134640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_2134640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134640 prefixEnd_2134640 := by exact prefixLift 2134640
  have htrace : WordTrace (prefixWord ++ tailWord_2134640) baseStart_2134640 baseEnd_2134640 := by
    simpa [prefixWord, tailWord_2134640, baseEnd_2134640] using wordTrace_append hprefix tailTrace_2134640
  have hstable : (prefixWord ++ tailWord_2134640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134640).length < 2 ^ (prefixWord ++ tailWord_2134640).sum := by decide
  have hdescent : baseEnd_2134640 < baseStart_2134640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134642 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2134642 : Nat := 118140960795 + 2134642 * 2 ^ 59
def prefixEnd_2134642 : Nat := 4983230072969 + 3 ^ 40 * 2134642 * 2
def baseEnd_2134642 : Nat := 730731580849961624705311

theorem tailTrace_2134642 : CollatzResearch.WordTrace tailWord_2134642 prefixEnd_2134642 730731580849961624705311 := by
  unfold tailWord_2134642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464197483141019168495545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51904526621709384449321453 19464197483141019168495545)
  ·
    refine ⟨14598148112355764376371659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19464197483141019168495545 14598148112355764376371659)
    ·
      refine ⟨21897222168533646564557489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14598148112355764376371659 21897222168533646564557489)
      ·
        refine ⟨16422916626400234923418117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21897222168533646564557489 16422916626400234923418117)
        ·
          refine ⟨3079296867450044048140897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16422916626400234923418117 3079296867450044048140897)
          ·
            refine ⟨2309472650587533036105673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079296867450044048140897 2309472650587533036105673)
            ·
              refine ⟨1732104487940649777079255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309472650587533036105673 1732104487940649777079255)
              ·
                refine ⟨2598156731910974665618883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732104487940649777079255 2598156731910974665618883)
                ·
                  refine ⟨3897235097866461998428325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598156731910974665618883 3897235097866461998428325)
                  ·
                    refine ⟨730731580849961624705311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897235097866461998428325 730731580849961624705311)
                    ·
                      rfl

theorem cell22_2134642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2134642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134642 prefixEnd_2134642 := by exact prefixLift 2134642
  have htrace : WordTrace (prefixWord ++ tailWord_2134642) baseStart_2134642 baseEnd_2134642 := by
    simpa [prefixWord, tailWord_2134642, baseEnd_2134642] using wordTrace_append hprefix tailTrace_2134642
  have hstable : (prefixWord ++ tailWord_2134642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134642).length < 2 ^ (prefixWord ++ tailWord_2134642).sum := by decide
  have hdescent : baseEnd_2134642 < baseStart_2134642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134730 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_2134730 : Nat := 118140960795 + 2134730 * 2 ^ 59
def prefixEnd_2134730 : Nat := 4983230072969 + 3 ^ 40 * 2134730 * 2
def baseEnd_2134730 : Nat := 243587235016119576168347

theorem tailTrace_2134730 : CollatzResearch.WordTrace tailWord_2134730 prefixEnd_2134730 243587235016119576168347 := by
  unfold tailWord_2134730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19464999889061316925796411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51906666370830178468790429 19464999889061316925796411)
  ·
    refine ⟨29197499833591975388694617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19464999889061316925796411 29197499833591975388694617)
    ·
      refine ⟨21898124875193981541520963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29197499833591975388694617 21898124875193981541520963)
      ·
        refine ⟨32847187312790972312281445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21898124875193981541520963 32847187312790972312281445)
        ·
          refine ⟨6158847621148307308552771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32847187312790972312281445 6158847621148307308552771)
          ·
            refine ⟨9238271431722460962829157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158847621148307308552771 9238271431722460962829157)
            ·
              refine ⟨1732175893447961430530467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9238271431722460962829157 1732175893447961430530467)
              ·
                refine ⟨2598263840171942145795701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732175893447961430530467 2598263840171942145795701)
                ·
                  refine ⟨243587235016119576168347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598263840171942145795701 243587235016119576168347)
                  ·
                    rfl

theorem cell22_2134730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_2134730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134730 prefixEnd_2134730 := by exact prefixLift 2134730
  have htrace : WordTrace (prefixWord ++ tailWord_2134730) baseStart_2134730 baseEnd_2134730 := by
    simpa [prefixWord, tailWord_2134730, baseEnd_2134730] using wordTrace_append hprefix tailTrace_2134730
  have hstable : (prefixWord ++ tailWord_2134730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134730).length < 2 ^ (prefixWord ++ tailWord_2134730).sum := by decide
  have hdescent : baseEnd_2134730 < baseStart_2134730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134743 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_2134743 : Nat := 118140960795 + 2134743 * 2 ^ 59
def prefixEnd_2134743 : Nat := 4983230072969 + 3 ^ 40 * 2134743 * 2
def baseEnd_2134743 : Nat := 730766155214031027930001

theorem tailTrace_2134743 : CollatzResearch.WordTrace tailWord_2134743 prefixEnd_2134743 730766155214031027930001 := by
  unfold tailWord_2134743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77860473705198170923408883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51906982470132113948939255 77860473705198170923408883)
  ·
    refine ⟨116790710557797256385113325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77860473705198170923408883 116790710557797256385113325)
    ·
      refine ⟨43796516459173971144417497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116790710557797256385113325 43796516459173971144417497)
      ·
        refine ⟨32847387344380478358313123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43796516459173971144417497 32847387344380478358313123)
        ·
          refine ⟨49271081016570717537469685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32847387344380478358313123 49271081016570717537469685)
          ·
            refine ⟨4619163845303504769137783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49271081016570717537469685 4619163845303504769137783)
            ·
              refine ⟨6928745767955257153706675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619163845303504769137783 6928745767955257153706675)
              ·
                refine ⟨10393118651932885730560013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6928745767955257153706675 10393118651932885730560013)
                ·
                  refine ⟨3897419494474832148960005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10393118651932885730560013 3897419494474832148960005)
                  ·
                    refine ⟨730766155214031027930001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897419494474832148960005 730766155214031027930001)
                    ·
                      rfl

theorem cell22_2134743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_2134743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134743 prefixEnd_2134743 := by exact prefixLift 2134743
  have htrace : WordTrace (prefixWord ++ tailWord_2134743) baseStart_2134743 baseEnd_2134743 := by
    simpa [prefixWord, tailWord_2134743, baseEnd_2134743] using wordTrace_append hprefix tailTrace_2134743
  have hstable : (prefixWord ++ tailWord_2134743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134743).length < 2 ^ (prefixWord ++ tailWord_2134743).sum := by decide
  have hdescent : baseEnd_2134743 < baseStart_2134743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134771 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_2134771 : Nat := 118140960795 + 2134771 * 2 ^ 59
def prefixEnd_2134771 : Nat := 4983230072969 + 3 ^ 40 * 2134771 * 2
def baseEnd_2134771 : Nat := 730775740186248288229915

theorem tailTrace_2134771 : CollatzResearch.WordTrace tailWord_2134771 prefixEnd_2134771 730775740186248288229915 := by
  unfold tailWord_2134771
  simp only [CollatzResearch.WordTrace]
  refine ⟨77861494949096731705428167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51907663299397821136952111 77861494949096731705428167)
  ·
    refine ⟨116792242423645097558142251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77861494949096731705428167 116792242423645097558142251)
    ·
      refine ⟨175188363635467646337213377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116792242423645097558142251 175188363635467646337213377)
      ·
        refine ⟨131391272726600734752910033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175188363635467646337213377 131391272726600734752910033)
        ·
          refine ⟨98543454544950551064682525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131391272726600734752910033 98543454544950551064682525)
          ·
            refine ⟨36953795454356456649255947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98543454544950551064682525 36953795454356456649255947)
            ·
              refine ⟨55430693181534684973883921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36953795454356456649255947 55430693181534684973883921)
              ·
                refine ⟨41573019886151013730412941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55430693181534684973883921 41573019886151013730412941)
                ·
                  refine ⟨15589882457306630148904853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41573019886151013730412941 15589882457306630148904853)
                  ·
                    refine ⟨730775740186248288229915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15589882457306630148904853 730775740186248288229915)
                    ·
                      rfl

theorem cell22_2134771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_2134771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134771 prefixEnd_2134771 := by exact prefixLift 2134771
  have htrace : WordTrace (prefixWord ++ tailWord_2134771) baseStart_2134771 baseEnd_2134771 := by
    simpa [prefixWord, tailWord_2134771, baseEnd_2134771] using wordTrace_append hprefix tailTrace_2134771
  have hstable : (prefixWord ++ tailWord_2134771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134771).length < 2 ^ (prefixWord ++ tailWord_2134771).sum := by decide
  have hdescent : baseEnd_2134771 < baseStart_2134771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134788 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2134788 : Nat := 118140960795 + 2134788 * 2 ^ 59
def prefixEnd_2134788 : Nat := 4983230072969 + 3 ^ 40 * 2134788 * 2
def baseEnd_2134788 : Nat := 730781559633665910554863

theorem tailTrace_2134788 : CollatzResearch.WordTrace tailWord_2134788 prefixEnd_2134788 730781559633665910554863 := by
  unfold tailWord_2134788
  simp only [CollatzResearch.WordTrace]
  refine ⟨38931057495017571804398509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51908076660023429072531345 38931057495017571804398509)
  ·
    refine ⟨14599146560631589426649441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38931057495017571804398509 14599146560631589426649441)
    ·
      refine ⟨10949359920473692069987081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14599146560631589426649441 10949359920473692069987081)
      ·
        refine ⟨8212019940355269052490311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10949359920473692069987081 8212019940355269052490311)
        ·
          refine ⟨12318029910532903578735467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8212019940355269052490311 12318029910532903578735467)
          ·
            refine ⟨18477044865799355368103201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12318029910532903578735467 18477044865799355368103201)
            ·
              refine ⟨13857783649349516526077401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18477044865799355368103201 13857783649349516526077401)
              ·
                refine ⟨10393337737012137394558051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13857783649349516526077401 10393337737012137394558051)
                ·
                  refine ⟨15590006605518206091837077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10393337737012137394558051 15590006605518206091837077)
                  ·
                    refine ⟨730781559633665910554863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15590006605518206091837077 730781559633665910554863)
                    ·
                      rfl

theorem cell22_2134788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2134788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134788 prefixEnd_2134788 := by exact prefixLift 2134788
  have htrace : WordTrace (prefixWord ++ tailWord_2134788) baseStart_2134788 baseEnd_2134788 := by
    simpa [prefixWord, tailWord_2134788, baseEnd_2134788] using wordTrace_append hprefix tailTrace_2134788
  have hstable : (prefixWord ++ tailWord_2134788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134788).length < 2 ^ (prefixWord ++ tailWord_2134788).sum := by decide
  have hdescent : baseEnd_2134788 < baseStart_2134788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134803 : List Nat := [1, 1, 1, 2, 1, 3, 7, 6]
def baseStart_2134803 : Nat := 118140960795 + 2134803 * 2 ^ 59
def prefixEnd_2134803 : Nat := 4983230072969 + 3 ^ 40 * 2134803 * 2
def baseEnd_2134803 : Nat := 81198521604467874603313

theorem tailTrace_2134803 : CollatzResearch.WordTrace tailWord_2134803 prefixEnd_2134803 81198521604467874603313 := by
  unfold tailWord_2134803
  simp only [CollatzResearch.WordTrace]
  refine ⟨77862662084980801170593063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51908441389987200780395375 77862662084980801170593063)
  ·
    refine ⟨116793993127471201755889595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77862662084980801170593063 116793993127471201755889595)
    ·
      refine ⟨175190989691206802633834393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116793993127471201755889595 175190989691206802633834393)
      ·
        refine ⟨131393242268405101975375795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175190989691206802633834393 131393242268405101975375795)
        ·
          refine ⟨197089863402607652963063693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131393242268405101975375795 197089863402607652963063693)
          ·
            refine ⟨73908698775977869861148885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197089863402607652963063693 73908698775977869861148885)
            ·
              refine ⟨1732235127561981324870677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73908698775977869861148885 1732235127561981324870677)
              ·
                refine ⟨81198521604467874603313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1732235127561981324870677 81198521604467874603313)
                ·
                  rfl

theorem cell22_2134803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 6].length) (baseStart_2134803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134803 prefixEnd_2134803 := by exact prefixLift 2134803
  have htrace : WordTrace (prefixWord ++ tailWord_2134803) baseStart_2134803 baseEnd_2134803 := by
    simpa [prefixWord, tailWord_2134803, baseEnd_2134803] using wordTrace_append hprefix tailTrace_2134803
  have hstable : (prefixWord ++ tailWord_2134803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134803).length < 2 ^ (prefixWord ++ tailWord_2134803).sum := by decide
  have hdescent : baseEnd_2134803 < baseStart_2134803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134835 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 3, 3]
def baseStart_2134835 : Nat := 118140960795 + 2134835 * 2 ^ 59
def prefixEnd_2134835 : Nat := 4983230072969 + 3 ^ 40 * 2134835 * 2
def baseEnd_2134835 : Nat := 730797648694173454629719

theorem tailTrace_2134835 : CollatzResearch.WordTrace tailWord_2134835 prefixEnd_2134835 730797648694173454629719 := by
  unfold tailWord_2134835
  simp only [CollatzResearch.WordTrace]
  refine ⟨77863829220864870635757959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51909219480576580423838639 77863829220864870635757959)
  ·
    refine ⟨116795743831297305953636939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77863829220864870635757959 116795743831297305953636939)
    ·
      refine ⟨175193615746945958930455409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116795743831297305953636939 175193615746945958930455409)
      ·
        refine ⟨131395211810209469197841557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175193615746945958930455409 131395211810209469197841557)
        ·
          refine ⟨6159150553603568868648823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131395211810209469197841557 6159150553603568868648823)
          ·
            refine ⟨9238725830405353302973235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6159150553603568868648823 9238725830405353302973235)
            ·
              refine ⟨13858088745608029954459853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238725830405353302973235 13858088745608029954459853)
              ·
                refine ⟨5196783279603011232922445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13858088745608029954459853 5196783279603011232922445)
                ·
                  refine ⟨1948793729851129212345917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5196783279603011232922445 1948793729851129212345917)
                  ·
                    refine ⟨730797648694173454629719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1948793729851129212345917 730797648694173454629719)
                    ·
                      rfl

theorem cell22_2134835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 3].length) (baseStart_2134835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134835 prefixEnd_2134835 := by exact prefixLift 2134835
  have htrace : WordTrace (prefixWord ++ tailWord_2134835) baseStart_2134835 baseEnd_2134835 := by
    simpa [prefixWord, tailWord_2134835, baseEnd_2134835] using wordTrace_append hprefix tailTrace_2134835
  have hstable : (prefixWord ++ tailWord_2134835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134835).length < 2 ^ (prefixWord ++ tailWord_2134835).sum := by decide
  have hdescent : baseEnd_2134835 < baseStart_2134835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134848 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_2134848 : Nat := 118140960795 + 2134848 * 2 ^ 59
def prefixEnd_2134848 : Nat := 4983230072969 + 3 ^ 40 * 2134848 * 2
def baseEnd_2134848 : Nat := 243600699619948584684893

theorem tailTrace_2134848 : CollatzResearch.WordTrace tailWord_2134848 prefixEnd_2134848 243600699619948584684893 := by
  unfold tailWord_2134848
  simp only [CollatzResearch.WordTrace]
  refine ⟨38932151684908886927990599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51909535579878515903987465 38932151684908886927990599)
  ·
    refine ⟨58398227527363330391985899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38932151684908886927990599 58398227527363330391985899)
    ·
      refine ⟨87597341291044995587978849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58398227527363330391985899 87597341291044995587978849)
      ·
        refine ⟨65698005968283746690984137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87597341291044995587978849 65698005968283746690984137)
        ·
          refine ⟨49273504476212810018238103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65698005968283746690984137 49273504476212810018238103)
          ·
            refine ⟨73910256714319215027357155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49273504476212810018238103 73910256714319215027357155)
            ·
              refine ⟨110865385071478822541035733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73910256714319215027357155 110865385071478822541035733)
              ·
                refine ⟨2598407462612784903305525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110865385071478822541035733 2598407462612784903305525)
                ·
                  refine ⟨243600699619948584684893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598407462612784903305525 243600699619948584684893)
                  ·
                    rfl

theorem cell22_2134848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_2134848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134848 prefixEnd_2134848 := by exact prefixLift 2134848
  have htrace : WordTrace (prefixWord ++ tailWord_2134848) baseStart_2134848 baseEnd_2134848 := by
    simpa [prefixWord, tailWord_2134848, baseEnd_2134848] using wordTrace_append hprefix tailTrace_2134848
  have hstable : (prefixWord ++ tailWord_2134848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134848).length < 2 ^ (prefixWord ++ tailWord_2134848).sum := by decide
  have hdescent : baseEnd_2134848 < baseStart_2134848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134908 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2134908 : Nat := 118140960795 + 2134908 * 2 ^ 59
def prefixEnd_2134908 : Nat := 4983230072969 + 3 ^ 40 * 2134908 * 2
def baseEnd_2134908 : Nat := 730822638086025597554495

theorem tailTrace_2134908 : CollatzResearch.WordTrace tailWord_2134908 prefixEnd_2134908 730822638086025597554495 := by
  unfold tailWord_2134908
  simp only [CollatzResearch.WordTrace]
  refine ⟨38933245874800202051582689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51910994499733602735443585 38933245874800202051582689)
  ·
    refine ⟨29199934406100151538687017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38933245874800202051582689 29199934406100151538687017)
    ·
      refine ⟨21899950804575113654015263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29199934406100151538687017 21899950804575113654015263)
      ·
        refine ⟨32849926206862670481022895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21899950804575113654015263 32849926206862670481022895)
        ·
          refine ⟨49274889310294005721534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32849926206862670481022895 49274889310294005721534343)
          ·
            refine ⟨73912333965441008582301515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49274889310294005721534343 73912333965441008582301515)
            ·
              refine ⟨110868500948161512873452273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73912333965441008582301515 110868500948161512873452273)
              ·
                refine ⟨83151375711121134655089205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110868500948161512873452273 83151375711121134655089205)
                ·
                  refine ⟨7795441472917606373914613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83151375711121134655089205 7795441472917606373914613)
                  ·
                    refine ⟨730822638086025597554495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7795441472917606373914613 730822638086025597554495)
                    ·
                      rfl

theorem cell22_2134908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2134908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134908 prefixEnd_2134908 := by exact prefixLift 2134908
  have htrace : WordTrace (prefixWord ++ tailWord_2134908) baseStart_2134908 baseEnd_2134908 := by
    simpa [prefixWord, tailWord_2134908, baseEnd_2134908] using wordTrace_append hprefix tailTrace_2134908
  have hstable : (prefixWord ++ tailWord_2134908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134908).length < 2 ^ (prefixWord ++ tailWord_2134908).sum := by decide
  have hdescent : baseEnd_2134908 < baseStart_2134908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134923 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_2134923 : Nat := 118140960795 + 2134923 * 2 ^ 59
def prefixEnd_2134923 : Nat := 4983230072969 + 3 ^ 40 * 2134923 * 2
def baseEnd_2134923 : Nat := 730827772892570558429449

theorem tailTrace_2134923 : CollatzResearch.WordTrace tailWord_2134923 prefixEnd_2134923 730827772892570558429449 := by
  unfold tailWord_2134923
  simp only [CollatzResearch.WordTrace]
  refine ⟨77867038844546061664961423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51911359229697374443307615 77867038844546061664961423)
  ·
    refine ⟨116800558266819092497442135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77867038844546061664961423 116800558266819092497442135)
    ·
      refine ⟨175200837400228638746163203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116800558266819092497442135 175200837400228638746163203)
      ·
        refine ⟨262801256100342958119244805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175200837400228638746163203 262801256100342958119244805)
        ·
          refine ⟨49275235518814304647358401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262801256100342958119244805 49275235518814304647358401)
          ·
            refine ⟨36956426639110728485518801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49275235518814304647358401 36956426639110728485518801)
            ·
              refine ⟨27717319979333046364139101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36956426639110728485518801 27717319979333046364139101)
              ·
                refine ⟨10393994992249892386552163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27717319979333046364139101 10393994992249892386552163)
                ·
                  refine ⟨15590992488374838579828245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10393994992249892386552163 15590992488374838579828245)
                  ·
                    refine ⟨730827772892570558429449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15590992488374838579828245 730827772892570558429449)
                    ·
                      rfl

theorem cell22_2134923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_2134923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134923 prefixEnd_2134923 := by exact prefixLift 2134923
  have htrace : WordTrace (prefixWord ++ tailWord_2134923) baseStart_2134923 baseEnd_2134923 := by
    simpa [prefixWord, tailWord_2134923, baseEnd_2134923] using wordTrace_append hprefix tailTrace_2134923
  have hstable : (prefixWord ++ tailWord_2134923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134923).length < 2 ^ (prefixWord ++ tailWord_2134923).sum := by decide
  have hdescent : baseEnd_2134923 < baseStart_2134923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2134938 : List Nat := [3, 1, 1, 4, 13]
def baseStart_2134938 : Nat := 118140960795 + 2134938 * 2 ^ 59
def prefixEnd_2134938 : Nat := 4983230072969 + 3 ^ 40 * 2134938 * 2
def baseEnd_2134938 : Nat := 3007542830037512425121

theorem tailTrace_2134938 : CollatzResearch.WordTrace tailWord_2134938 prefixEnd_2134938 3007542830037512425121 := by
  unfold tailWord_2134938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19466896484872929806689367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51911723959661146151171645 19466896484872929806689367)
  ·
    refine ⟨29200344727309394710034051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19466896484872929806689367 29200344727309394710034051)
    ·
      refine ⟨43800517090964092065051077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29200344727309394710034051 43800517090964092065051077)
      ·
        refine ⟨8212596954555767262197077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43800517090964092065051077 8212596954555767262197077)
        ·
          refine ⟨3007542830037512425121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8212596954555767262197077 3007542830037512425121)
          ·
            rfl

theorem cell22_2134938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 13].length) (baseStart_2134938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2134938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2134938 prefixEnd_2134938 := by exact prefixLift 2134938
  have htrace : WordTrace (prefixWord ++ tailWord_2134938) baseStart_2134938 baseEnd_2134938 := by
    simpa [prefixWord, tailWord_2134938, baseEnd_2134938] using wordTrace_append hprefix tailTrace_2134938
  have hstable : (prefixWord ++ tailWord_2134938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2134938).length < 2 ^ (prefixWord ++ tailWord_2134938).sum := by decide
  have hdescent : baseEnd_2134938 < baseStart_2134938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2134938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135000 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_2135000 : Nat := 118140960795 + 2135000 * 2 ^ 59
def prefixEnd_2135000 : Nat := 4983230072969 + 3 ^ 40 * 2135000 * 2
def baseEnd_2135000 : Nat := 243618043855389341418071

theorem tailTrace_2135000 : CollatzResearch.WordTrace tailWord_2135000 prefixEnd_2135000 243618043855389341418071 := by
  unfold tailWord_2135000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38934923632633551907757227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51913231510178069210342969 38934923632633551907757227)
  ·
    refine ⟨58402385448950327861635841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38934923632633551907757227 58402385448950327861635841)
    ·
      refine ⟨43801789086712745896226881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58402385448950327861635841 43801789086712745896226881)
      ·
        refine ⟨32851341815034559422170161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43801789086712745896226881 32851341815034559422170161)
        ·
          refine ⟨24638506361275919566627621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32851341815034559422170161 24638506361275919566627621)
          ·
            refine ⟨4619719942739234918742679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24638506361275919566627621 4619719942739234918742679)
            ·
              refine ⟨6929579914108852378114019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619719942739234918742679 6929579914108852378114019)
              ·
                refine ⟨10394369871163278567171029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6929579914108852378114019 10394369871163278567171029)
                ·
                  refine ⟨243618043855389341418071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10394369871163278567171029 243618043855389341418071)
                  ·
                    rfl

theorem cell22_2135000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_2135000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135000 prefixEnd_2135000 := by exact prefixLift 2135000
  have htrace : WordTrace (prefixWord ++ tailWord_2135000) baseStart_2135000 baseEnd_2135000 := by
    simpa [prefixWord, tailWord_2135000, baseEnd_2135000] using wordTrace_append hprefix tailTrace_2135000
  have hstable : (prefixWord ++ tailWord_2135000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135000).length < 2 ^ (prefixWord ++ tailWord_2135000).sum := by decide
  have hdescent : baseEnd_2135000 < baseStart_2135000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135047 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2135047 : Nat := 118140960795 + 2135047 * 2 ^ 59
def prefixEnd_2135047 : Nat := 4983230072969 + 3 ^ 40 * 2135047 * 2
def baseEnd_2135047 : Nat := 730870220626675568329069

theorem tailTrace_2135047 : CollatzResearch.WordTrace tailWord_2135047 prefixEnd_2135047 730870220626675568329069 := by
  unfold tailWord_2135047
  simp only [CollatzResearch.WordTrace]
  refine ⟨77871561496096830842475395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51914374330731220561650263 77871561496096830842475395)
  ·
    refine ⟨116807342244145246263713093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77871561496096830842475395 116807342244145246263713093)
    ·
      refine ⟨21901376670777233674446205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116807342244145246263713093 21901376670777233674446205)
      ·
        refine ⟨8213016251541462627917327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21901376670777233674446205 8213016251541462627917327)
        ·
          refine ⟨12319524377312193941875991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213016251541462627917327 12319524377312193941875991)
          ·
            refine ⟨18479286565968290912813987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12319524377312193941875991 18479286565968290912813987)
            ·
              refine ⟨27718929848952436369220981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18479286565968290912813987 27718929848952436369220981)
              ·
                refine ⟨2598649673339290909614467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27718929848952436369220981 2598649673339290909614467)
                ·
                  refine ⟨3897974510008936364421701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2598649673339290909614467 3897974510008936364421701)
                  ·
                    refine ⟨730870220626675568329069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3897974510008936364421701 730870220626675568329069)
                    ·
                      rfl

theorem cell22_2135047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2135047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135047 prefixEnd_2135047 := by exact prefixLift 2135047
  have htrace : WordTrace (prefixWord ++ tailWord_2135047) baseStart_2135047 baseEnd_2135047 := by
    simpa [prefixWord, tailWord_2135047, baseEnd_2135047] using wordTrace_append hprefix tailTrace_2135047
  have hstable : (prefixWord ++ tailWord_2135047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135047).length < 2 ^ (prefixWord ++ tailWord_2135047).sum := by decide
  have hdescent : baseEnd_2135047 < baseStart_2135047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135090 : List Nat := [3, 2, 1, 1, 2, 2, 1, 10]
def baseStart_2135090 : Nat := 118140960795 + 2135090 * 2 ^ 59
def prefixEnd_2135090 : Nat := 4983230072969 + 3 ^ 40 * 2135090 * 2
def baseEnd_2135090 : Nat := 81209437822826421055993

theorem tailTrace_2135090 : CollatzResearch.WordTrace tailWord_2135090 prefixEnd_2135090 81209437822826421055993 := by
  unfold tailWord_2135090
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468282458735262296572681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51915419889960699457527149 19468282458735262296572681)
  ·
    refine ⟨14601211844051446722429511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19468282458735262296572681 14601211844051446722429511)
    ·
      refine ⟨21901817766077170083644267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14601211844051446722429511 21901817766077170083644267)
      ·
        refine ⟨32852726649115755125466401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21901817766077170083644267 32852726649115755125466401)
        ·
          refine ⟨24639544986836816344099801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32852726649115755125466401 24639544986836816344099801)
          ·
            refine ⟨18479658740127612258074851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24639544986836816344099801 18479658740127612258074851)
            ·
              refine ⟨27719488110191418387112277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18479658740127612258074851 27719488110191418387112277)
              ·
                refine ⟨81209437822826421055993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27719488110191418387112277 81209437822826421055993)
                ·
                  rfl

theorem cell22_2135090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_2135090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135090 prefixEnd_2135090 := by exact prefixLift 2135090
  have htrace : WordTrace (prefixWord ++ tailWord_2135090) baseStart_2135090 baseEnd_2135090 := by
    simpa [prefixWord, tailWord_2135090, baseEnd_2135090] using wordTrace_append hprefix tailTrace_2135090
  have hstable : (prefixWord ++ tailWord_2135090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135090).length < 2 ^ (prefixWord ++ tailWord_2135090).sum := by decide
  have hdescent : baseEnd_2135090 < baseStart_2135090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135094 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2135094 : Nat := 118140960795 + 2135094 * 2 ^ 59
def prefixEnd_2135094 : Nat := 4983230072969 + 3 ^ 40 * 2135094 * 2
def baseEnd_2135094 : Nat := 730886309687183112403925

theorem tailTrace_2135094 : CollatzResearch.WordTrace tailWord_2135094 prefixEnd_2135094 730886309687183112403925 := by
  unfold tailWord_2135094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867079732932909866839771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51915517151284371912957557 4867079732932909866839771)
  ·
    refine ⟨7300619599399364800259657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4867079732932909866839771 7300619599399364800259657)
    ·
      refine ⟨5475464699549523600194743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7300619599399364800259657 5475464699549523600194743)
      ·
        refine ⟨8213197049324285400292115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475464699549523600194743 8213197049324285400292115)
        ·
          refine ⟨12319795573986428100438173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213197049324285400292115 12319795573986428100438173)
          ·
            refine ⟨4619923340244910537664315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12319795573986428100438173 4619923340244910537664315)
            ·
              refine ⟨6929885010367365806496473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4619923340244910537664315 6929885010367365806496473)
              ·
                refine ⟨5197413757775524354872355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6929885010367365806496473 5197413757775524354872355)
                ·
                  refine ⟨7796120636663286532308533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5197413757775524354872355 7796120636663286532308533)
                  ·
                    refine ⟨730886309687183112403925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7796120636663286532308533 730886309687183112403925)
                    ·
                      rfl

theorem cell22_2135094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2135094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135094 prefixEnd_2135094 := by exact prefixLift 2135094
  have htrace : WordTrace (prefixWord ++ tailWord_2135094) baseStart_2135094 baseEnd_2135094 := by
    simpa [prefixWord, tailWord_2135094, baseEnd_2135094] using wordTrace_append hprefix tailTrace_2135094
  have hstable : (prefixWord ++ tailWord_2135094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135094).length < 2 ^ (prefixWord ++ tailWord_2135094).sum := by decide
  have hdescent : baseEnd_2135094 < baseStart_2135094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135169 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 5]
def baseStart_2135169 : Nat := 118140960795 + 2135169 * 2 ^ 59
def prefixEnd_2135169 : Nat := 4983230072969 + 3 ^ 40 * 2135169 * 2
def baseEnd_2135169 : Nat := 243637327906635972259565

theorem tailTrace_2135169 : CollatzResearch.WordTrace tailWord_2135169 prefixEnd_2135169 243637327906635972259565 := by
  unfold tailWord_2135169
  simp only [CollatzResearch.WordTrace]
  refine ⟨77876011201654845678416561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51917340801103230452277707 77876011201654845678416561)
  ·
    refine ⟨58407008401241134258812421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77876011201654845678416561 58407008401241134258812421)
    ·
      refine ⟨10951314075232712673527329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58407008401241134258812421 10951314075232712673527329)
      ·
        refine ⟨8213485556424534505145497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10951314075232712673527329 8213485556424534505145497)
        ·
          refine ⟨6160114167318400878859123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8213485556424534505145497 6160114167318400878859123)
          ·
            refine ⟨9240171250977601318288685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160114167318400878859123 9240171250977601318288685)
            ·
              refine ⟨3465064219116600494358257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9240171250977601318288685 3465064219116600494358257)
              ·
                refine ⟨2598798164337450370768693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3465064219116600494358257 2598798164337450370768693)
                ·
                  refine ⟨243637327906635972259565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598798164337450370768693 243637327906635972259565)
                  ·
                    rfl

theorem cell22_2135169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_2135169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135169 prefixEnd_2135169 := by exact prefixLift 2135169
  have htrace : WordTrace (prefixWord ++ tailWord_2135169) baseStart_2135169 baseEnd_2135169 := by
    simpa [prefixWord, tailWord_2135169, baseEnd_2135169] using wordTrace_append hprefix tailTrace_2135169
  have hstable : (prefixWord ++ tailWord_2135169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135169).length < 2 ^ (prefixWord ++ tailWord_2135169).sum := by decide
  have hdescent : baseEnd_2135169 < baseStart_2135169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135186 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_2135186 : Nat := 118140960795 + 2135186 * 2 ^ 59
def prefixEnd_2135186 : Nat := 4983230072969 + 3 ^ 40 * 2135186 * 2
def baseEnd_2135186 : Nat := 243639267722441846367881

theorem tailTrace_2135186 : CollatzResearch.WordTrace tailWord_2135186 prefixEnd_2135186 243639267722441846367881 := by
  unfold tailWord_2135186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469157810648314395446353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51917754161728838387856941 19469157810648314395446353)
  ·
    refine ⟨14601868357986235796584765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19469157810648314395446353 14601868357986235796584765)
    ·
      refine ⟨5475700634244838423719287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14601868357986235796584765 5475700634244838423719287)
      ·
        refine ⟨8213550951367257635578931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5475700634244838423719287 8213550951367257635578931)
        ·
          refine ⟨12320326427050886453368397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8213550951367257635578931 12320326427050886453368397)
          ·
            refine ⟨4620122410144082420013149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12320326427050886453368397 4620122410144082420013149)
            ·
              refine ⟨1732545903804030907504931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4620122410144082420013149 1732545903804030907504931)
              ·
                refine ⟨2598818855706046361257397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732545903804030907504931 2598818855706046361257397)
                ·
                  refine ⟨243639267722441846367881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2598818855706046361257397 243639267722441846367881)
                  ·
                    rfl

theorem cell22_2135186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_2135186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135186 prefixEnd_2135186 := by exact prefixLift 2135186
  have htrace : WordTrace (prefixWord ++ tailWord_2135186) baseStart_2135186 baseEnd_2135186 := by
    simpa [prefixWord, tailWord_2135186, baseEnd_2135186] using wordTrace_append hprefix tailTrace_2135186
  have hstable : (prefixWord ++ tailWord_2135186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135186).length < 2 ^ (prefixWord ++ tailWord_2135186).sum := by decide
  have hdescent : baseEnd_2135186 < baseStart_2135186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135197 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 6]
def baseStart_2135197 : Nat := 118140960795 + 2135197 * 2 ^ 59
def prefixEnd_2135197 : Nat := 4983230072969 + 3 ^ 40 * 2135197 * 2
def baseEnd_2135197 : Nat := 243640522897375059026203

theorem tailTrace_2135197 : CollatzResearch.WordTrace tailWord_2135197 prefixEnd_2135197 243640522897375059026203 := by
  unfold tailWord_2135197
  simp only [CollatzResearch.WordTrace]
  refine ⟨77877032445553406460435845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51918021630368937640290563 77877032445553406460435845)
  ·
    refine ⟨14601943583541263711331721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77877032445553406460435845 14601943583541263711331721)
    ·
      refine ⟨10951457687655947783498791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14601943583541263711331721 10951457687655947783498791)
      ·
        refine ⟨16427186531483921675248187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10951457687655947783498791 16427186531483921675248187)
        ·
          refine ⟨24640779797225882512872281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16427186531483921675248187 24640779797225882512872281)
          ·
            refine ⟨18480584847919411884654211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24640779797225882512872281 18480584847919411884654211)
            ·
              refine ⟨27720877271879117826981317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18480584847919411884654211 27720877271879117826981317)
              ·
                refine ⟨5197664488477334592558997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27720877271879117826981317 5197664488477334592558997)
                ·
                  refine ⟨243640522897375059026203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5197664488477334592558997 243640522897375059026203)
                  ·
                    rfl

theorem cell22_2135197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_2135197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135197 prefixEnd_2135197 := by exact prefixLift 2135197
  have htrace : WordTrace (prefixWord ++ tailWord_2135197) baseStart_2135197 baseEnd_2135197 := by
    simpa [prefixWord, tailWord_2135197, baseEnd_2135197] using wordTrace_append hprefix tailTrace_2135197
  have hstable : (prefixWord ++ tailWord_2135197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135197).length < 2 ^ (prefixWord ++ tailWord_2135197).sum := by decide
  have hdescent : baseEnd_2135197 < baseStart_2135197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135229 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_2135229 : Nat := 118140960795 + 2135229 * 2 ^ 59
def prefixEnd_2135229 : Nat := 4983230072969 + 3 ^ 40 * 2135229 * 2
def baseEnd_2135229 : Nat := 730932522946087760278511

theorem tailTrace_2135229 : CollatzResearch.WordTrace tailWord_2135229 prefixEnd_2135229 730932522946087760278511 := by
  unfold tailWord_2135229
  simp only [CollatzResearch.WordTrace]
  refine ⟨77878199581437475925600741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51918799720958317283733827 77878199581437475925600741)
  ·
    refine ⟨14602162421519526736050139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77878199581437475925600741 14602162421519526736050139)
    ·
      refine ⟨21903243632279290104075209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14602162421519526736050139 21903243632279290104075209)
      ·
        refine ⟨16427432724209467578056407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21903243632279290104075209 16427432724209467578056407)
        ·
          refine ⟨24641149086314201367084611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16427432724209467578056407 24641149086314201367084611)
          ·
            refine ⟨36961723629471302050626917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24641149086314201367084611 36961723629471302050626917)
            ·
              refine ⟨6930323180525869134492547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36961723629471302050626917 6930323180525869134492547)
              ·
                refine ⟨10395484770788803701738821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6930323180525869134492547 10395484770788803701738821)
                ·
                  refine ⟨1949153394522900694076029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10395484770788803701738821 1949153394522900694076029)
                  ·
                    refine ⟨730932522946087760278511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949153394522900694076029 730932522946087760278511)
                    ·
                      rfl

theorem cell22_2135229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_2135229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135229 prefixEnd_2135229 := by exact prefixLift 2135229
  have htrace : WordTrace (prefixWord ++ tailWord_2135229) baseStart_2135229 baseEnd_2135229 := by
    simpa [prefixWord, tailWord_2135229, baseEnd_2135229] using wordTrace_append hprefix tailTrace_2135229
  have hstable : (prefixWord ++ tailWord_2135229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135229).length < 2 ^ (prefixWord ++ tailWord_2135229).sum := by decide
  have hdescent : baseEnd_2135229 < baseStart_2135229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135242 : List Nat := [3, 1, 2, 1, 3, 2, 1, 9]
def baseStart_2135242 : Nat := 118140960795 + 2135242 * 2 ^ 59
def prefixEnd_2135242 : Nat := 4983230072969 + 3 ^ 40 * 2135242 * 2
def baseEnd_2135242 : Nat := 81215219234640006633719

theorem tailTrace_2135242 : CollatzResearch.WordTrace tailWord_2135242 prefixEnd_2135242 81215219234640006633719 := by
  unfold tailWord_2135242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19469668432597594786455995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51919115820260252763882653 19469668432597594786455995)
  ·
    refine ⟨29204502648896392179683993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19469668432597594786455995 29204502648896392179683993)
    ·
      refine ⟨21903376986672294134762995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29204502648896392179683993 21903376986672294134762995)
      ·
        refine ⟨32855065480008441202144493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21903376986672294134762995 32855065480008441202144493)
        ·
          refine ⟨12320649555003165450804185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32855065480008441202144493 12320649555003165450804185)
          ·
            refine ⟨9240487166252374088103139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12320649555003165450804185 9240487166252374088103139)
            ·
              refine ⟨13860730749378561132154709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240487166252374088103139 13860730749378561132154709)
              ·
                refine ⟨81215219234640006633719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13860730749378561132154709 81215219234640006633719)
                ·
                  rfl

theorem cell22_2135242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_2135242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135242 prefixEnd_2135242 := by exact prefixLift 2135242
  have htrace : WordTrace (prefixWord ++ tailWord_2135242) baseStart_2135242 baseEnd_2135242 := by
    simpa [prefixWord, tailWord_2135242, baseEnd_2135242] using wordTrace_append hprefix tailTrace_2135242
  have hstable : (prefixWord ++ tailWord_2135242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135242).length < 2 ^ (prefixWord ++ tailWord_2135242).sum := by decide
  have hdescent : baseEnd_2135242 < baseStart_2135242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135325 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2135325 : Nat := 118140960795 + 2135325 * 2 ^ 59
def prefixEnd_2135325 : Nat := 4983230072969 + 3 ^ 40 * 2135325 * 2
def baseEnd_2135325 : Nat := 730965385707975509878217

theorem tailTrace_2135325 : CollatzResearch.WordTrace tailWord_2135325 prefixEnd_2135325 730965385707975509878217 := by
  unfold tailWord_2135325
  simp only [CollatzResearch.WordTrace]
  refine ⟨77881700989089684321095429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51921133992726456214063619 77881700989089684321095429)
  ·
    refine ⟨14602818935454315810205393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77881700989089684321095429 14602818935454315810205393)
    ·
      refine ⟨10952114201590736857654045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14602818935454315810205393 10952114201590736857654045)
      ·
        refine ⟨4107042825596526321620267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10952114201590736857654045 4107042825596526321620267)
        ·
          refine ⟨6160564238394789482430401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107042825596526321620267 6160564238394789482430401)
          ·
            refine ⟨4620423178796092111822801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6160564238394789482430401 4620423178796092111822801)
            ·
              refine ⟨3465317384097069083867101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4620423178796092111822801 3465317384097069083867101)
              ·
                refine ⟨1299494019036400906450163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3465317384097069083867101 1299494019036400906450163)
                ·
                  refine ⟨1949241028554601359675245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299494019036400906450163 1949241028554601359675245)
                  ·
                    refine ⟨730965385707975509878217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949241028554601359675245 730965385707975509878217)
                    ·
                      rfl

theorem cell22_2135325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2135325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135325 prefixEnd_2135325 := by exact prefixLift 2135325
  have htrace : WordTrace (prefixWord ++ tailWord_2135325) baseStart_2135325 baseEnd_2135325 := by
    simpa [prefixWord, tailWord_2135325, baseEnd_2135325] using wordTrace_append hprefix tailTrace_2135325
  have hstable : (prefixWord ++ tailWord_2135325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135325).length < 2 ^ (prefixWord ++ tailWord_2135325).sum := by decide
  have hdescent : baseEnd_2135325 < baseStart_2135325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135338 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_2135338 : Nat := 118140960795 + 2135338 * 2 ^ 59
def prefixEnd_2135338 : Nat := 4983230072969 + 3 ^ 40 * 2135338 * 2
def baseEnd_2135338 : Nat := 243656611957882603101059

theorem tailTrace_2135338 : CollatzResearch.WordTrace tailWord_2135338 prefixEnd_2135338 243656611957882603101059 := by
  unfold tailWord_2135338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470543784510646885329667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51921450092028391694212445 19470543784510646885329667)
  ·
    refine ⟨29205815676765970327994501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19470543784510646885329667 29205815676765970327994501)
    ·
      refine ⟨5476090439393619436498969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29205815676765970327994501 5476090439393619436498969)
      ·
        refine ⟨4107067829545214577374227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5476090439393619436498969 4107067829545214577374227)
        ·
          refine ⟨6160601744317821866061341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107067829545214577374227 6160601744317821866061341)
          ·
            refine ⟨2310225654119183199773003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6160601744317821866061341 2310225654119183199773003)
            ·
              refine ⟨3465338481178774799659505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310225654119183199773003 3465338481178774799659505)
              ·
                refine ⟨2599003860884081099744629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3465338481178774799659505 2599003860884081099744629)
                ·
                  refine ⟨243656611957882603101059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599003860884081099744629 243656611957882603101059)
                  ·
                    rfl

theorem cell22_2135338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_2135338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135338 prefixEnd_2135338 := by exact prefixLift 2135338
  have htrace : WordTrace (prefixWord ++ tailWord_2135338) baseStart_2135338 baseEnd_2135338 := by
    simpa [prefixWord, tailWord_2135338, baseEnd_2135338] using wordTrace_append hprefix tailTrace_2135338
  have hstable : (prefixWord ++ tailWord_2135338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135338).length < 2 ^ (prefixWord ++ tailWord_2135338).sum := by decide
  have hdescent : baseEnd_2135338 < baseStart_2135338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135349 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 6]
def baseStart_2135349 : Nat := 118140960795 + 2135349 * 2 ^ 59
def prefixEnd_2135349 : Nat := 4983230072969 + 3 ^ 40 * 2135349 * 2
def baseEnd_2135349 : Nat := 243657867132815815759381

theorem tailTrace_2135349 : CollatzResearch.WordTrace tailWord_2135349 prefixEnd_2135349 243657867132815815759381 := by
  unfold tailWord_2135349
  simp only [CollatzResearch.WordTrace]
  refine ⟨77882576341002736419969101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51921717560668490946646067 77882576341002736419969101)
  ·
    refine ⟨29205966127876026157488413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77882576341002736419969101 29205966127876026157488413)
    ·
      refine ⟨10952237297953509809058155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29205966127876026157488413 10952237297953509809058155)
      ·
        refine ⟨16428355946930264713587233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10952237297953509809058155 16428355946930264713587233)
        ·
          refine ⟨12321266960197698535190425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16428355946930264713587233 12321266960197698535190425)
          ·
            refine ⟨9240950220148273901392819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12321266960197698535190425 9240950220148273901392819)
            ·
              refine ⟨13861425330222410852089229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9240950220148273901392819 13861425330222410852089229)
              ·
                refine ⟨5198034498833404069533461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13861425330222410852089229 5198034498833404069533461)
                ·
                  refine ⟨243657867132815815759381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5198034498833404069533461 243657867132815815759381)
                  ·
                    rfl

theorem cell22_2135349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_2135349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135349 prefixEnd_2135349 := by exact prefixLift 2135349
  have htrace : WordTrace (prefixWord ++ tailWord_2135349) baseStart_2135349 baseEnd_2135349 := by
    simpa [prefixWord, tailWord_2135349, baseEnd_2135349] using wordTrace_append hprefix tailTrace_2135349
  have hstable : (prefixWord ++ tailWord_2135349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135349).length < 2 ^ (prefixWord ++ tailWord_2135349).sum := by decide
  have hdescent : baseEnd_2135349 < baseStart_2135349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135379 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_2135379 : Nat := 118140960795 + 2135379 * 2 ^ 59
def prefixEnd_2135379 : Nat := 4983230072969 + 3 ^ 40 * 2135379 * 2
def baseEnd_2135379 : Nat := 730983871011537369028051

theorem tailTrace_2135379 : CollatzResearch.WordTrace tailWord_2135379 prefixEnd_2135379 730983871011537369028051 := by
  unfold tailWord_2135379
  simp only [CollatzResearch.WordTrace]
  refine ⟨77883670530894051543561191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51922447020596034362374127 77883670530894051543561191)
  ·
    refine ⟨116825505796341077315341787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77883670530894051543561191 116825505796341077315341787)
    ·
      refine ⟨175238258694511615973012681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116825505796341077315341787 175238258694511615973012681)
      ·
        refine ⟨131428694020883711979759511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175238258694511615973012681 131428694020883711979759511)
        ·
          refine ⟨197143041031325567969639267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131428694020883711979759511 197143041031325567969639267)
          ·
            refine ⟨295714561546988351954458901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197143041031325567969639267 295714561546988351954458901)
            ·
              refine ⟨13861620072515078997865261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 295714561546988351954458901 13861620072515078997865261)
              ·
                refine ⟨5198107527193154624199473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13861620072515078997865261 5198107527193154624199473)
                ·
                  refine ⟨3898580645394865968149605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198107527193154624199473 3898580645394865968149605)
                  ·
                    refine ⟨730983871011537369028051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3898580645394865968149605 730983871011537369028051)
                    ·
                      rfl

theorem cell22_2135379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_2135379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135379 prefixEnd_2135379 := by exact prefixLift 2135379
  have htrace : WordTrace (prefixWord ++ tailWord_2135379) baseStart_2135379 baseEnd_2135379 := by
    simpa [prefixWord, tailWord_2135379, baseEnd_2135379] using wordTrace_append hprefix tailTrace_2135379
  have hstable : (prefixWord ++ tailWord_2135379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135379).length < 2 ^ (prefixWord ++ tailWord_2135379).sum := by decide
  have hdescent : baseEnd_2135379 < baseStart_2135379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135381 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_2135381 : Nat := 118140960795 + 2135381 * 2 ^ 59
def prefixEnd_2135381 : Nat := 4983230072969 + 3 ^ 40 * 2135381 * 2
def baseEnd_2135381 : Nat := 730984555652410030478045

theorem tailTrace_2135381 : CollatzResearch.WordTrace tailWord_2135381 prefixEnd_2135381 730984555652410030478045 := by
  unfold tailWord_2135381
  simp only [CollatzResearch.WordTrace]
  refine ⟨77883743476886805885133997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51922495651257870590089331 77883743476886805885133997)
  ·
    refine ⟨29206403803832552206925249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77883743476886805885133997 29206403803832552206925249)
    ·
      refine ⟨21904802852874414155193937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29206403803832552206925249 21904802852874414155193937)
      ·
        refine ⟨16428602139655810616395453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21904802852874414155193937 16428602139655810616395453)
        ·
          refine ⟨6160725802370928981148295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16428602139655810616395453 6160725802370928981148295)
          ·
            refine ⟨9241088703556393471722443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6160725802370928981148295 9241088703556393471722443)
            ·
              refine ⟨13861633055334590207583665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9241088703556393471722443 13861633055334590207583665)
              ·
                refine ⟨10396224791500942655687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13861633055334590207583665 10396224791500942655687749)
                ·
                  refine ⟨1949292148406426747941453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10396224791500942655687749 1949292148406426747941453)
                  ·
                    refine ⟨730984555652410030478045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949292148406426747941453 730984555652410030478045)
                    ·
                      rfl

theorem cell22_2135381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_2135381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135381 prefixEnd_2135381 := by exact prefixLift 2135381
  have htrace : WordTrace (prefixWord ++ tailWord_2135381) baseStart_2135381 baseEnd_2135381 := by
    simpa [prefixWord, tailWord_2135381, baseEnd_2135381] using wordTrace_append hprefix tailTrace_2135381
  have hstable : (prefixWord ++ tailWord_2135381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135381).length < 2 ^ (prefixWord ++ tailWord_2135381).sum := by decide
  have hdescent : baseEnd_2135381 < baseStart_2135381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135383 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 4]
def baseStart_2135383 : Nat := 118140960795 + 2135383 * 2 ^ 59
def prefixEnd_2135383 : Nat := 4983230072969 + 3 ^ 40 * 2135383 * 2
def baseEnd_2135383 : Nat := 243661746764427563976013

theorem tailTrace_2135383 : CollatzResearch.WordTrace tailWord_2135383 prefixEnd_2135383 243661746764427563976013 := by
  unfold tailWord_2135383
  simp only [CollatzResearch.WordTrace]
  refine ⟨77883816422879560226706803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51922544281919706817804535 77883816422879560226706803)
  ·
    refine ⟨116825724634319340340060205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77883816422879560226706803 116825724634319340340060205)
    ·
      refine ⟨43809646737869752627522577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116825724634319340340060205 43809646737869752627522577)
      ·
        refine ⟨32857235053402314470641933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43809646737869752627522577 32857235053402314470641933)
        ·
          refine ⟨12321463145025867926490725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32857235053402314470641933 12321463145025867926490725)
          ·
            refine ⟨2310274339692350236217011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12321463145025867926490725 2310274339692350236217011)
            ·
              refine ⟨3465411509538525354325517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310274339692350236217011 3465411509538525354325517)
              ·
                refine ⟨1299529316076947007872069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3465411509538525354325517 1299529316076947007872069)
                ·
                  refine ⟨243661746764427563976013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299529316076947007872069 243661746764427563976013)
                  ·
                    rfl

theorem cell22_2135383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 4].length) (baseStart_2135383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135383 prefixEnd_2135383 := by exact prefixLift 2135383
  have htrace : WordTrace (prefixWord ++ tailWord_2135383) baseStart_2135383 baseEnd_2135383 := by
    simpa [prefixWord, tailWord_2135383, baseEnd_2135383] using wordTrace_append hprefix tailTrace_2135383
  have hstable : (prefixWord ++ tailWord_2135383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135383).length < 2 ^ (prefixWord ++ tailWord_2135383).sum := by decide
  have hdescent : baseEnd_2135383 < baseStart_2135383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135396 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2135396 : Nat := 118140960795 + 2135396 * 2 ^ 59
def prefixEnd_2135396 : Nat := 4983230072969 + 3 ^ 40 * 2135396 * 2
def baseEnd_2135396 : Nat := 730989690458954991352999

theorem tailTrace_2135396 : CollatzResearch.WordTrace tailWord_2135396 prefixEnd_2135396 730989690458954991352999 := by
  unfold tailWord_2135396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38942145285916231723465021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51922860381221642297953361 38942145285916231723465021)
  ·
    refine ⟨14603304482218586896299383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38942145285916231723465021 14603304482218586896299383)
    ·
      refine ⟨21904956723327880344449075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14603304482218586896299383 21904956723327880344449075)
      ·
        refine ⟨32857435084991820516673613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21904956723327880344449075 32857435084991820516673613)
        ·
          refine ⟨12321538156871932693752605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32857435084991820516673613 12321538156871932693752605)
          ·
            refine ⟨4620576808826974760157227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12321538156871932693752605 4620576808826974760157227)
            ·
              refine ⟨6930865213240462140235841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4620576808826974760157227 6930865213240462140235841)
              ·
                refine ⟨5198148909930346605176881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6930865213240462140235841 5198148909930346605176881)
                ·
                  refine ⟨3898611682447759953882661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5198148909930346605176881 3898611682447759953882661)
                  ·
                    refine ⟨730989690458954991352999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3898611682447759953882661 730989690458954991352999)
                    ·
                      rfl

theorem cell22_2135396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2135396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135396 prefixEnd_2135396 := by exact prefixLift 2135396
  have htrace : WordTrace (prefixWord ++ tailWord_2135396) baseStart_2135396 baseEnd_2135396 := by
    simpa [prefixWord, tailWord_2135396, baseEnd_2135396] using wordTrace_append hprefix tailTrace_2135396
  have hstable : (prefixWord ++ tailWord_2135396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135396).length < 2 ^ (prefixWord ++ tailWord_2135396).sum := by decide
  have hdescent : baseEnd_2135396 < baseStart_2135396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135400 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_2135400 : Nat := 118140960795 + 2135400 * 2 ^ 59
def prefixEnd_2135400 : Nat := 4983230072969 + 3 ^ 40 * 2135400 * 2
def baseEnd_2135400 : Nat := 243663686580233438084329

theorem tailTrace_2135400 : CollatzResearch.WordTrace tailWord_2135400 prefixEnd_2135400 243663686580233438084329 := by
  unfold tailWord_2135400
  simp only [CollatzResearch.WordTrace]
  refine ⟨38942218231908986065037827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51922957642545314753383769 38942218231908986065037827)
  ·
    refine ⟨58413327347863479097556741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38942218231908986065037827 58413327347863479097556741)
    ·
      refine ⟨10952498877724402330791889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58413327347863479097556741 10952498877724402330791889)
      ·
        refine ⟨8214374158293301748093917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10952498877724402330791889 8214374158293301748093917)
        ·
          refine ⟨3080390309359988155535219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8214374158293301748093917 3080390309359988155535219)
          ·
            refine ⟨4620585464039982233302829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080390309359988155535219 4620585464039982233302829)
            ·
              refine ⟨1732719549014993337488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4620585464039982233302829 1732719549014993337488561)
              ·
                refine ⟨1299539661761245003116421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732719549014993337488561 1299539661761245003116421)
                ·
                  refine ⟨243663686580233438084329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299539661761245003116421 243663686580233438084329)
                  ·
                    rfl

theorem cell22_2135400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_2135400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135400 prefixEnd_2135400 := by exact prefixLift 2135400
  have htrace : WordTrace (prefixWord ++ tailWord_2135400) baseStart_2135400 baseEnd_2135400 := by
    simpa [prefixWord, tailWord_2135400, baseEnd_2135400] using wordTrace_append hprefix tailTrace_2135400
  have hstable : (prefixWord ++ tailWord_2135400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135400).length < 2 ^ (prefixWord ++ tailWord_2135400).sum := by decide
  have hdescent : baseEnd_2135400 < baseStart_2135400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135456 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_2135456 : Nat := 118140960795 + 2135456 * 2 ^ 59
def prefixEnd_2135456 : Nat := 4983230072969 + 3 ^ 40 * 2135456 * 2
def baseEnd_2135456 : Nat := 243670076561711611617605

theorem tailTrace_2135456 : CollatzResearch.WordTrace tailWord_2135456 prefixEnd_2135456 243670076561711611617605 := by
  unfold tailWord_2135456
  simp only [CollatzResearch.WordTrace]
  refine ⟨38943239475807546847057111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51924319301076729129409481 38943239475807546847057111)
  ·
    refine ⟨58414859213711320270585667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38943239475807546847057111 58414859213711320270585667)
    ·
      refine ⟨87622288820566980405878501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58414859213711320270585667 87622288820566980405878501)
      ·
        refine ⟨16429179153856308826102219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87622288820566980405878501 16429179153856308826102219)
        ·
          refine ⟨24643768730784463239153329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16429179153856308826102219 24643768730784463239153329)
          ·
            refine ⟨18482826548088347429364997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24643768730784463239153329 18482826548088347429364997)
            ·
              refine ⟨3465529977766565143005937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18482826548088347429364997 3465529977766565143005937)
              ·
                refine ⟨2599147483324923857254453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3465529977766565143005937 2599147483324923857254453)
                ·
                  refine ⟨243670076561711611617605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599147483324923857254453 243670076561711611617605)
                  ·
                    rfl

theorem cell22_2135456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_2135456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135456 prefixEnd_2135456 := by exact prefixLift 2135456
  have htrace : WordTrace (prefixWord ++ tailWord_2135456) baseStart_2135456 baseEnd_2135456 := by
    simpa [prefixWord, tailWord_2135456, baseEnd_2135456] using wordTrace_append hprefix tailTrace_2135456
  have hstable : (prefixWord ++ tailWord_2135456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135456).length < 2 ^ (prefixWord ++ tailWord_2135456).sum := by decide
  have hdescent : baseEnd_2135456 < baseStart_2135456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135503 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 1, 4]
def baseStart_2135503 : Nat := 118140960795 + 2135503 * 2 ^ 59
def prefixEnd_2135503 : Nat := 4983230072969 + 3 ^ 40 * 2135503 * 2
def baseEnd_2135503 : Nat := 731026318745642378927671

theorem tailTrace_2135503 : CollatzResearch.WordTrace tailWord_2135503 prefixEnd_2135503 731026318745642378927671 := by
  unfold tailWord_2135503
  simp only [CollatzResearch.WordTrace]
  refine ⟨77888193182444820721075163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51925462121629880480716775 77888193182444820721075163)
  ·
    refine ⟨116832289773667231081612745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77888193182444820721075163 116832289773667231081612745)
    ·
      refine ⟨87624217330250423311209559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116832289773667231081612745 87624217330250423311209559)
      ·
        refine ⟨131436325995375634966814339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87624217330250423311209559 131436325995375634966814339)
        ·
          refine ⟨197154488993063452450221509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131436325995375634966814339 197154488993063452450221509)
          ·
            refine ⟨36966466686199397334416533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197154488993063452450221509 36966466686199397334416533)
            ·
              refine ⟨1732803125915596750050775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36966466686199397334416533 1732803125915596750050775)
              ·
                refine ⟨2599204688873395125076163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1732803125915596750050775 2599204688873395125076163)
                ·
                  refine ⟨3898807033310092687614245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599204688873395125076163 3898807033310092687614245)
                  ·
                    refine ⟨731026318745642378927671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3898807033310092687614245 731026318745642378927671)
                    ·
                      rfl

theorem cell22_2135503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_2135503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135503 prefixEnd_2135503 := by exact prefixLift 2135503
  have htrace : WordTrace (prefixWord ++ tailWord_2135503) baseStart_2135503 baseEnd_2135503 := by
    simpa [prefixWord, tailWord_2135503, baseEnd_2135503] using wordTrace_append hprefix tailTrace_2135503
  have hstable : (prefixWord ++ tailWord_2135503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135503).length < 2 ^ (prefixWord ++ tailWord_2135503).sum := by decide
  have hdescent : baseEnd_2135503 < baseStart_2135503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135563 : List Nat := [1, 1, 1, 1, 9, 1, 8]
def baseStart_2135563 : Nat := 118140960795 + 2135563 * 2 ^ 59
def prefixEnd_2135563 : Nat := 4983230072969 + 3 ^ 40 * 2135563 * 2
def baseEnd_2135563 : Nat := 27075809554511934163981

theorem tailTrace_2135563 : CollatzResearch.WordTrace tailWord_2135563 prefixEnd_2135563 27075809554511934163981 := by
  unfold tailWord_2135563
  simp only [CollatzResearch.WordTrace]
  refine ⟨77890381562227450968259343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51926921041484967312172895 77890381562227450968259343)
  ·
    refine ⟨116835572343341176452389015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77890381562227450968259343 116835572343341176452389015)
    ·
      refine ⟨175253358515011764678583523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116835572343341176452389015 175253358515011764678583523)
      ·
        refine ⟨262880037772517647017875285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175253358515011764678583523 262880037772517647017875285)
        ·
          refine ⟨1540312721323345587995363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 262880037772517647017875285 1540312721323345587995363)
          ·
            refine ⟨2310469081985018381993045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540312721323345587995363 2310469081985018381993045)
            ·
              refine ⟨27075809554511934163981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2310469081985018381993045 27075809554511934163981)
              ·
                rfl

theorem cell22_2135563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 8].length) (baseStart_2135563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135563 prefixEnd_2135563 := by exact prefixLift 2135563
  have htrace : WordTrace (prefixWord ++ tailWord_2135563) baseStart_2135563 baseEnd_2135563 := by
    simpa [prefixWord, tailWord_2135563, baseEnd_2135563] using wordTrace_append hprefix tailTrace_2135563
  have hstable : (prefixWord ++ tailWord_2135563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135563).length < 2 ^ (prefixWord ++ tailWord_2135563).sum := by decide
  have hdescent : baseEnd_2135563 < baseStart_2135563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135629 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2135629 : Nat := 118140960795 + 2135629 * 2 ^ 59
def prefixEnd_2135629 : Nat := 4983230072969 + 3 ^ 40 * 2135629 * 2
def baseEnd_2135629 : Nat := 731069451120620050277285

theorem tailTrace_2135629 : CollatzResearch.WordTrace tailWord_2135629 prefixEnd_2135629 731069451120620050277285 := by
  unfold tailWord_2135629
  simp only [CollatzResearch.WordTrace]
  refine ⟨77892788779988344240161941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51928525853325562826774627 77892788779988344240161941)
  ·
    refine ⟨3651224474061953636257591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77892788779988344240161941 3651224474061953636257591)
    ·
      refine ⟨5476836711092930454386387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3651224474061953636257591 5476836711092930454386387)
      ·
        refine ⟨8215255066639395681579581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476836711092930454386387 8215255066639395681579581)
        ·
          refine ⟨3080720649989773380592343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8215255066639395681579581 3080720649989773380592343)
          ·
            refine ⟨4621080974984660070888515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080720649989773380592343 4621080974984660070888515)
            ·
              refine ⟨6931621462476990106332773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621080974984660070888515 6931621462476990106332773)
              ·
                refine ⟨1299679024214435644937395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6931621462476990106332773 1299679024214435644937395)
                ·
                  refine ⟨1949518536321653467406093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299679024214435644937395 1949518536321653467406093)
                  ·
                    refine ⟨731069451120620050277285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949518536321653467406093 731069451120620050277285)
                    ·
                      rfl

theorem cell22_2135629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2135629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135629 prefixEnd_2135629 := by exact prefixLift 2135629
  have htrace : WordTrace (prefixWord ++ tailWord_2135629) baseStart_2135629 baseEnd_2135629 := by
    simpa [prefixWord, tailWord_2135629, baseEnd_2135629] using wordTrace_append hprefix tailTrace_2135629
  have hstable : (prefixWord ++ tailWord_2135629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135629).length < 2 ^ (prefixWord ++ tailWord_2135629).sum := by decide
  have hdescent : baseEnd_2135629 < baseStart_2135629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135653 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 6]
def baseStart_2135653 : Nat := 118140960795 + 2135653 * 2 ^ 59
def prefixEnd_2135653 : Nat := 4983230072969 + 3 ^ 40 * 2135653 * 2
def baseEnd_2135653 : Nat := 243692555603697329225737

theorem tailTrace_2135653 : CollatzResearch.WordTrace tailWord_2135653 prefixEnd_2135653 243692555603697329225737 := by
  unfold tailWord_2135653
  simp only [CollatzResearch.WordTrace]
  refine ⟨77893664131901396339035613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51929109421267597559357075 77893664131901396339035613)
  ·
    refine ⟨29210124049463023627138355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77893664131901396339035613 29210124049463023627138355)
    ·
      refine ⟨43815186074194535440707533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29210124049463023627138355 43815186074194535440707533)
      ·
        refine ⟨16430694777822950790265325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43815186074194535440707533 16430694777822950790265325)
        ·
          refine ⟨6161510541683606546349497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16430694777822950790265325 6161510541683606546349497)
          ·
            refine ⟨4621132906262704909762123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6161510541683606546349497 4621132906262704909762123)
            ·
              refine ⟨6931699359394057364643185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621132906262704909762123 6931699359394057364643185)
              ·
                refine ⟨5198774519545543023482389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6931699359394057364643185 5198774519545543023482389)
                ·
                  refine ⟨243692555603697329225737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5198774519545543023482389 243692555603697329225737)
                  ·
                    rfl

theorem cell22_2135653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_2135653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135653 prefixEnd_2135653 := by exact prefixLift 2135653
  have htrace : WordTrace (prefixWord ++ tailWord_2135653) baseStart_2135653 baseEnd_2135653 := by
    simpa [prefixWord, tailWord_2135653, baseEnd_2135653] using wordTrace_append hprefix tailTrace_2135653
  have hstable : (prefixWord ++ tailWord_2135653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135653).length < 2 ^ (prefixWord ++ tailWord_2135653).sum := by decide
  have hdescent : baseEnd_2135653 < baseStart_2135653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135743 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 5]
def baseStart_2135743 : Nat := 118140960795 + 2135743 * 2 ^ 59
def prefixEnd_2135743 : Nat := 4983230072969 + 3 ^ 40 * 2135743 * 2
def baseEnd_2135743 : Nat := 243702825216787250975645

theorem tailTrace_2135743 : CollatzResearch.WordTrace tailWord_2135743 prefixEnd_2135743 243702825216787250975645 := by
  unfold tailWord_2135743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77896946701575341709811883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51931297801050227806541255 77896946701575341709811883)
  ·
    refine ⟨116845420052363012564717825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77896946701575341709811883 116845420052363012564717825)
    ·
      refine ⟨87634065039272259423538369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116845420052363012564717825 87634065039272259423538369)
      ·
        refine ⟨65725548779454194567653777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87634065039272259423538369 65725548779454194567653777)
        ·
          refine ⟨49294161584590645925740333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65725548779454194567653777 49294161584590645925740333)
          ·
            refine ⟨18485310594221492222152625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49294161584590645925740333 18485310594221492222152625)
            ·
              refine ⟨13863982945666119166614469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18485310594221492222152625 13863982945666119166614469)
              ·
                refine ⟨2599496802312397343740213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13863982945666119166614469 2599496802312397343740213)
                ·
                  refine ⟨243702825216787250975645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2599496802312397343740213 243702825216787250975645)
                  ·
                    rfl

theorem cell22_2135743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 5].length) (baseStart_2135743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135743 prefixEnd_2135743 := by exact prefixLift 2135743
  have htrace : WordTrace (prefixWord ++ tailWord_2135743) baseStart_2135743 baseEnd_2135743 := by
    simpa [prefixWord, tailWord_2135743, baseEnd_2135743] using wordTrace_append hprefix tailTrace_2135743
  have hstable : (prefixWord ++ tailWord_2135743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135743).length < 2 ^ (prefixWord ++ tailWord_2135743).sum := by decide
  have hdescent : baseEnd_2135743 < baseStart_2135743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135758 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2135758 : Nat := 118140960795 + 2135758 * 2 ^ 59
def prefixEnd_2135758 : Nat := 4983230072969 + 3 ^ 40 * 2135758 * 2
def baseEnd_2135758 : Nat := 731113610456906713801889

theorem tailTrace_2135758 : CollatzResearch.WordTrace tailWord_2135758 prefixEnd_2135758 731113610456906713801889 := by
  unfold tailWord_2135758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737186724565124908950991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51931662531013999514405285 9737186724565124908950991)
  ·
    refine ⟨14605780086847687363426487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9737186724565124908950991 14605780086847687363426487)
    ·
      refine ⟨21908670130271531045139731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14605780086847687363426487 21908670130271531045139731)
      ·
        refine ⟨32863005195407296567709597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21908670130271531045139731 32863005195407296567709597)
        ·
          refine ⟨12323626948277736212891099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32863005195407296567709597 12323626948277736212891099)
          ·
            refine ⟨18485440422416604319336649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12323626948277736212891099 18485440422416604319336649)
            ·
              refine ⟨13864080316812453239502487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18485440422416604319336649 13864080316812453239502487)
              ·
                refine ⟨20796120475218679859253731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13864080316812453239502487 20796120475218679859253731)
                ·
                  refine ⟨31194180712828019788880597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20796120475218679859253731 31194180712828019788880597)
                  ·
                    refine ⟨731113610456906713801889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31194180712828019788880597 731113610456906713801889)
                    ·
                      rfl

theorem cell22_2135758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2135758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135758 prefixEnd_2135758 := by exact prefixLift 2135758
  have htrace : WordTrace (prefixWord ++ tailWord_2135758) baseStart_2135758 baseEnd_2135758 := by
    simpa [prefixWord, tailWord_2135758, baseEnd_2135758] using wordTrace_append hprefix tailTrace_2135758
  have hstable : (prefixWord ++ tailWord_2135758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135758).length < 2 ^ (prefixWord ++ tailWord_2135758).sum := by decide
  have hdescent : baseEnd_2135758 < baseStart_2135758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135854 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2135854 : Nat := 118140960795 + 2135854 * 2 ^ 59
def prefixEnd_2135854 : Nat := 4983230072969 + 3 ^ 40 * 2135854 * 2
def baseEnd_2135854 : Nat := 731146473218794463401595

theorem tailTrace_2135854 : CollatzResearch.WordTrace tailWord_2135854 prefixEnd_2135854 731146473218794463401595 := by
  unfold tailWord_2135854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737624400521650958387827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51933996802782138444735077 9737624400521650958387827)
  ·
    refine ⟨14606436600782476437581741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9737624400521650958387827 14606436600782476437581741)
    ·
      refine ⟨5477413725293428664093153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14606436600782476437581741 5477413725293428664093153)
      ·
        refine ⟨4108060293970071498069865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5477413725293428664093153 4108060293970071498069865)
        ·
          refine ⟨3081045220477553623552399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4108060293970071498069865 3081045220477553623552399)
          ·
            refine ⟨4621567830716330435328599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081045220477553623552399 4621567830716330435328599)
            ·
              refine ⟨6932351746074495652992899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621567830716330435328599 6932351746074495652992899)
              ·
                refine ⟨10398527619111743479489349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6932351746074495652992899 10398527619111743479489349)
                ·
                  refine ⟨1949723928583451902404253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10398527619111743479489349 1949723928583451902404253)
                  ·
                    refine ⟨731146473218794463401595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949723928583451902404253 731146473218794463401595)
                    ·
                      rfl

theorem cell22_2135854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2135854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135854 prefixEnd_2135854 := by exact prefixLift 2135854
  have htrace : WordTrace (prefixWord ++ tailWord_2135854) baseStart_2135854 baseEnd_2135854 := by
    simpa [prefixWord, tailWord_2135854, baseEnd_2135854] using wordTrace_append hprefix tailTrace_2135854
  have hstable : (prefixWord ++ tailWord_2135854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135854).length < 2 ^ (prefixWord ++ tailWord_2135854).sum := by decide
  have hdescent : baseEnd_2135854 < baseStart_2135854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135863 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2135863 : Nat := 118140960795 + 2135863 * 2 ^ 59
def prefixEnd_2135863 : Nat := 4983230072969 + 3 ^ 40 * 2135863 * 2
def baseEnd_2135863 : Nat := 731149554102721439926567

theorem tailTrace_2135863 : CollatzResearch.WordTrace tailWord_2135863 prefixEnd_2135863 731149554102721439926567 := by
  unfold tailWord_2135863
  simp only [CollatzResearch.WordTrace]
  refine ⟨77901323461140602204180243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51934215640760401469453495 77901323461140602204180243)
  ·
    refine ⟨116851985191710903306270365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77901323461140602204180243 116851985191710903306270365)
    ·
      refine ⟨43819494446891588739851387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116851985191710903306270365 43819494446891588739851387)
      ·
        refine ⟨65729241670337383109777081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43819494446891588739851387 65729241670337383109777081)
        ·
          refine ⟨49296931252753037332332811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65729241670337383109777081 49296931252753037332332811)
          ·
            refine ⟨73945396879129555998499217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49296931252753037332332811 73945396879129555998499217)
            ·
              refine ⟨55459047659347166998874413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73945396879129555998499217 55459047659347166998874413)
              ·
                refine ⟨20797142872255187624577905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55459047659347166998874413 20797142872255187624577905)
                ·
                  refine ⟨15597857154191390718433429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20797142872255187624577905 15597857154191390718433429)
                  ·
                    refine ⟨731149554102721439926567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15597857154191390718433429 731149554102721439926567)
                    ·
                      rfl

theorem cell22_2135863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2135863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135863 prefixEnd_2135863 := by exact prefixLift 2135863
  have htrace : WordTrace (prefixWord ++ tailWord_2135863) baseStart_2135863 baseEnd_2135863 := by
    simpa [prefixWord, tailWord_2135863, baseEnd_2135863] using wordTrace_append hprefix tailTrace_2135863
  have hstable : (prefixWord ++ tailWord_2135863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135863).length < 2 ^ (prefixWord ++ tailWord_2135863).sum := by decide
  have hdescent : baseEnd_2135863 < baseStart_2135863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135884 : List Nat := [2, 2, 1, 3, 5, 1, 2, 6]
def baseStart_2135884 : Nat := 118140960795 + 2135884 * 2 ^ 59
def prefixEnd_2135884 : Nat := 4983230072969 + 3 ^ 40 * 2135884 * 2
def baseEnd_2135884 : Nat := 81239638092431598350167

theorem tailTrace_2135884 : CollatzResearch.WordTrace tailWord_2135884 prefixEnd_2135884 81239638092431598350167 := by
  unfold tailWord_2135884
  simp only [CollatzResearch.WordTrace]
  refine ⟨38951044697032261395347353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51934726262709681860463137 38951044697032261395347353)
  ·
    refine ⟨29213283522774196046510515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38951044697032261395347353 29213283522774196046510515)
    ·
      refine ⟨43819925284161294069765773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29213283522774196046510515 43819925284161294069765773)
      ·
        refine ⟨16432471981560485276162165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43819925284161294069765773 16432471981560485276162165)
        ·
          refine ⟨1540544248271295494640203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16432471981560485276162165 1540544248271295494640203)
          ·
            refine ⟨2310816372406943241960305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540544248271295494640203 2310816372406943241960305)
            ·
              refine ⟨1733112279305207431470229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310816372406943241960305 1733112279305207431470229)
              ·
                refine ⟨81239638092431598350167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1733112279305207431470229 81239638092431598350167)
                ·
                  rfl

theorem cell22_2135884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_2135884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135884 prefixEnd_2135884 := by exact prefixLift 2135884
  have htrace : WordTrace (prefixWord ++ tailWord_2135884) baseStart_2135884 baseEnd_2135884 := by
    simpa [prefixWord, tailWord_2135884, baseEnd_2135884] using wordTrace_append hprefix tailTrace_2135884
  have hstable : (prefixWord ++ tailWord_2135884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135884).length < 2 ^ (prefixWord ++ tailWord_2135884).sum := by decide
  have hdescent : baseEnd_2135884 < baseStart_2135884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135916 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_2135916 : Nat := 118140960795 + 2135916 * 2 ^ 59
def prefixEnd_2135916 : Nat := 4983230072969 + 3 ^ 40 * 2135916 * 2
def baseEnd_2135916 : Nat := 731167697085846968351405

theorem tailTrace_2135916 : CollatzResearch.WordTrace tailWord_2135916 prefixEnd_2135916 731167697085846968351405 := by
  unfold tailWord_2135916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38951628264974296127929801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51935504353299061503906401 38951628264974296127929801)
  ·
    refine ⟨29213721198730722095947351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38951628264974296127929801 29213721198730722095947351)
    ·
      refine ⟨43820581798096083143921027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29213721198730722095947351 43820581798096083143921027)
      ·
        refine ⟨65730872697144124715881541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43820581798096083143921027 65730872697144124715881541)
        ·
          refine ⟨12324538630714523384227789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65730872697144124715881541 12324538630714523384227789)
          ·
            refine ⟨4621701986517946269085421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12324538630714523384227789 4621701986517946269085421)
            ·
              refine ⟨1733138244944229850907033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4621701986517946269085421 1733138244944229850907033)
              ·
                refine ⟨1299853683708172388180275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733138244944229850907033 1299853683708172388180275)
                ·
                  refine ⟨1949780525562258582270413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299853683708172388180275 1949780525562258582270413)
                  ·
                    refine ⟨731167697085846968351405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949780525562258582270413 731167697085846968351405)
                    ·
                      rfl

theorem cell22_2135916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_2135916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135916 prefixEnd_2135916 := by exact prefixLift 2135916
  have htrace : WordTrace (prefixWord ++ tailWord_2135916) baseStart_2135916 baseEnd_2135916 := by
    simpa [prefixWord, tailWord_2135916, baseEnd_2135916] using wordTrace_append hprefix tailTrace_2135916
  have hstable : (prefixWord ++ tailWord_2135916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135916).length < 2 ^ (prefixWord ++ tailWord_2135916).sum := by decide
  have hdescent : baseEnd_2135916 < baseStart_2135916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135940 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_2135940 : Nat := 118140960795 + 2135940 * 2 ^ 59
def prefixEnd_2135940 : Nat := 4983230072969 + 3 ^ 40 * 2135940 * 2
def baseEnd_2135940 : Nat := 243725304258772968583777

theorem tailTrace_2135940 : CollatzResearch.WordTrace tailWord_2135940 prefixEnd_2135940 243725304258772968583777 := by
  unfold tailWord_2135940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38952065940930822177366637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51936087921241096236488849 38952065940930822177366637)
  ·
    refine ⟨14607024727849058316512489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38952065940930822177366637 14607024727849058316512489)
    ·
      refine ⟨10955268545886793737384367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14607024727849058316512489 10955268545886793737384367)
      ·
        refine ⟨16432902818830190606076551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10955268545886793737384367 16432902818830190606076551)
        ·
          refine ⟨24649354228245285909114827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16432902818830190606076551 24649354228245285909114827)
          ·
            refine ⟨36974031342367928863672241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24649354228245285909114827 36974031342367928863672241)
            ·
              refine ⟨27730523506775946647754181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36974031342367928863672241 27730523506775946647754181)
              ·
                refine ⟨5199473157520489996453909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27730523506775946647754181 5199473157520489996453909)
                ·
                  refine ⟨243725304258772968583777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5199473157520489996453909 243725304258772968583777)
                  ·
                    rfl

theorem cell22_2135940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_2135940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135940 prefixEnd_2135940 := by exact prefixLift 2135940
  have htrace : WordTrace (prefixWord ++ tailWord_2135940) baseStart_2135940 baseEnd_2135940 := by
    simpa [prefixWord, tailWord_2135940, baseEnd_2135940] using wordTrace_append hprefix tailTrace_2135940
  have hstable : (prefixWord ++ tailWord_2135940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135940).length < 2 ^ (prefixWord ++ tailWord_2135940).sum := by decide
  have hdescent : baseEnd_2135940 < baseStart_2135940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135957 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 4]
def baseStart_2135957 : Nat := 118140960795 + 2135957 * 2 ^ 59
def prefixEnd_2135957 : Nat := 4983230072969 + 3 ^ 40 * 2135957 * 2
def baseEnd_2135957 : Nat := 243727244074578842692093

theorem tailTrace_2135957 : CollatzResearch.WordTrace tailWord_2135957 prefixEnd_2135957 243727244074578842692093 := by
  unfold tailWord_2135957
  simp only [CollatzResearch.WordTrace]
  refine ⟨77904751922800056258102125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51936501281866704172068083 77904751922800056258102125)
  ·
    refine ⟨29214281971050021096788297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77904751922800056258102125 29214281971050021096788297)
    ·
      refine ⟨21910711478287515822591223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29214281971050021096788297 21910711478287515822591223)
      ·
        refine ⟨32866067217431273733886835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21910711478287515822591223 32866067217431273733886835)
        ·
          refine ⟨49299100826146910600830253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32866067217431273733886835 49299100826146910600830253)
          ·
            refine ⟨18487162809805091475311345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49299100826146910600830253 18487162809805091475311345)
            ·
              refine ⟨13865372107353818606483509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18487162809805091475311345 13865372107353818606483509)
              ·
                refine ⟨1299878635064420494357829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13865372107353818606483509 1299878635064420494357829)
                ·
                  refine ⟨243727244074578842692093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1299878635064420494357829 243727244074578842692093)
                  ·
                    rfl

theorem cell22_2135957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_2135957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135957 prefixEnd_2135957 := by exact prefixLift 2135957
  have htrace : WordTrace (prefixWord ++ tailWord_2135957) baseStart_2135957 baseEnd_2135957 := by
    simpa [prefixWord, tailWord_2135957, baseEnd_2135957] using wordTrace_append hprefix tailTrace_2135957
  have hstable : (prefixWord ++ tailWord_2135957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135957).length < 2 ^ (prefixWord ++ tailWord_2135957).sum := by decide
  have hdescent : baseEnd_2135957 < baseStart_2135957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135959 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 1, 4]
def baseStart_2135959 : Nat := 118140960795 + 2135959 * 2 ^ 59
def prefixEnd_2135959 : Nat := 4983230072969 + 3 ^ 40 * 2135959 * 2
def baseEnd_2135959 : Nat := 731182416864609189526273

theorem tailTrace_2135959 : CollatzResearch.WordTrace tailWord_2135959 prefixEnd_2135959 731182416864609189526273 := by
  unfold tailWord_2135959
  simp only [CollatzResearch.WordTrace]
  refine ⟨77904824868792810599674931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51936549912528540399783287 77904824868792810599674931)
  ·
    refine ⟨116857237303189215899512397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77904824868792810599674931 116857237303189215899512397)
    ·
      refine ⟨43821463988695955962317149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116857237303189215899512397 43821463988695955962317149)
      ·
        refine ⟨16433048995760983485868931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43821463988695955962317149 16433048995760983485868931)
        ·
          refine ⟨24649573493641475228803397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16433048995760983485868931 24649573493641475228803397)
          ·
            refine ⟨4621795030057776605400637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24649573493641475228803397 4621795030057776605400637)
            ·
              refine ⟨1733173136271666227025239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4621795030057776605400637 1733173136271666227025239)
              ·
                refine ⟨2599759704407499340537859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733173136271666227025239 2599759704407499340537859)
                ·
                  refine ⟨3899639556611249010806789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2599759704407499340537859 3899639556611249010806789)
                  ·
                    refine ⟨731182416864609189526273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3899639556611249010806789 731182416864609189526273)
                    ·
                      rfl

theorem cell22_2135959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_2135959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135959 prefixEnd_2135959 := by exact prefixLift 2135959
  have htrace : WordTrace (prefixWord ++ tailWord_2135959) baseStart_2135959 baseEnd_2135959 := by
    simpa [prefixWord, tailWord_2135959, baseEnd_2135959] using wordTrace_append hprefix tailTrace_2135959
  have hstable : (prefixWord ++ tailWord_2135959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135959).length < 2 ^ (prefixWord ++ tailWord_2135959).sum := by decide
  have hdescent : baseEnd_2135959 < baseStart_2135959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2135989 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2135989 : Nat := 118140960795 + 2135989 * 2 ^ 59
def prefixEnd_2135989 : Nat := 4983230072969 + 3 ^ 40 * 2135989 * 2
def baseEnd_2135989 : Nat := 731192686477699111276181

theorem tailTrace_2135989 : CollatzResearch.WordTrace tailWord_2135989 prefixEnd_2135989 731192686477699111276181 := by
  unfold tailWord_2135989
  simp only [CollatzResearch.WordTrace]
  refine ⟨77905919058684125723267021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51937279372456083815511347 77905919058684125723267021)
  ·
    refine ⟨29214719647006547146225133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77905919058684125723267021 29214719647006547146225133)
    ·
      refine ⟨10955519867627455179834425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29214719647006547146225133 10955519867627455179834425)
      ·
        refine ⟨8216639900720591384875819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10955519867627455179834425 8216639900720591384875819)
        ·
          refine ⟨12324959851080887077313729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8216639900720591384875819 12324959851080887077313729)
          ·
            refine ⟨9243719888310665307985297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12324959851080887077313729 9243719888310665307985297)
            ·
              refine ⟨6932789916232998980988973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9243719888310665307985297 6932789916232998980988973)
              ·
                refine ⟨2599796218587374617870865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6932789916232998980988973 2599796218587374617870865)
                ·
                  refine ⟨1949847163940530963403149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2599796218587374617870865 1949847163940530963403149)
                  ·
                    refine ⟨731192686477699111276181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949847163940530963403149 731192686477699111276181)
                    ·
                      rfl

theorem cell22_2135989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2135989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2135989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2135989 prefixEnd_2135989 := by exact prefixLift 2135989
  have htrace : WordTrace (prefixWord ++ tailWord_2135989) baseStart_2135989 baseEnd_2135989 := by
    simpa [prefixWord, tailWord_2135989, baseEnd_2135989] using wordTrace_append hprefix tailTrace_2135989
  have hstable : (prefixWord ++ tailWord_2135989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2135989).length < 2 ^ (prefixWord ++ tailWord_2135989).sum := by decide
  have hdescent : baseEnd_2135989 < baseStart_2135989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2135989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136070 : List Nat := [6, 2, 1, 2, 2, 1, 8]
def baseStart_2136070 : Nat := 118140960795 + 2136070 * 2 ^ 59
def prefixEnd_2136070 : Nat := 4983230072969 + 3 ^ 40 * 2136070 * 2
def baseEnd_2136070 : Nat := 27082237571594144444479

theorem tailTrace_2136070 : CollatzResearch.WordTrace tailWord_2136070 prefixEnd_2136070 27082237571594144444479 := by
  unfold tailWord_2136070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434652292855958642405177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51939248914260451037977109 2434652292855958642405177)
  ·
    refine ⟨1825989219641968981803883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2434652292855958642405177 1825989219641968981803883)
    ·
      refine ⟨2738983829462953472705825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825989219641968981803883 2738983829462953472705825)
      ·
        refine ⟨2054237872097215104529369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2738983829462953472705825 2054237872097215104529369)
        ·
          refine ⟨1540678404072911328397027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054237872097215104529369 1540678404072911328397027)
          ·
            refine ⟨2311017606109366992595541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540678404072911328397027 2311017606109366992595541)
            ·
              refine ⟨27082237571594144444479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2311017606109366992595541 27082237571594144444479)
              ·
                rfl

theorem cell22_2136070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 8].length) (baseStart_2136070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136070 prefixEnd_2136070 := by exact prefixLift 2136070
  have htrace : WordTrace (prefixWord ++ tailWord_2136070) baseStart_2136070 baseEnd_2136070 := by
    simpa [prefixWord, tailWord_2136070, baseEnd_2136070] using wordTrace_append hprefix tailTrace_2136070
  have hstable : (prefixWord ++ tailWord_2136070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136070).length < 2 ^ (prefixWord ++ tailWord_2136070).sum := by decide
  have hdescent : baseEnd_2136070 < baseStart_2136070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136107 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 6, 3]
def baseStart_2136107 : Nat := 118140960795 + 2136107 * 2 ^ 59
def prefixEnd_2136107 : Nat := 4983230072969 + 3 ^ 40 * 2136107 * 2
def baseEnd_2136107 : Nat := 731233080289186136825819

theorem tailTrace_2136107 : CollatzResearch.WordTrace tailWord_2136107 prefixEnd_2136107 731233080289186136825819 := by
  unfold tailWord_2136107
  simp only [CollatzResearch.WordTrace]
  refine ⟨77910222872256631876062575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51940148581504421250708383 77910222872256631876062575)
  ·
    refine ⟨116865334308384947814093863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77910222872256631876062575 116865334308384947814093863)
    ·
      refine ⟨175298001462577421721140795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116865334308384947814093863 175298001462577421721140795)
      ·
        refine ⟨262947002193866132581711193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175298001462577421721140795 262947002193866132581711193)
        ·
          refine ⟨197210251645399599436283395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262947002193866132581711193 197210251645399599436283395)
          ·
            refine ⟨295815377468099399154425093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197210251645399599436283395 295815377468099399154425093)
            ·
              refine ⟨55465383275268637341454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 295815377468099399154425093 55465383275268637341454705)
              ·
                refine ⟨41599037456451478006091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55465383275268637341454705 41599037456451478006091029)
                ·
                  refine ⟨1949954880771163031535517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41599037456451478006091029 1949954880771163031535517)
                  ·
                    refine ⟨731233080289186136825819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1949954880771163031535517 731233080289186136825819)
                    ·
                      rfl

theorem cell22_2136107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 3].length) (baseStart_2136107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136107 prefixEnd_2136107 := by exact prefixLift 2136107
  have htrace : WordTrace (prefixWord ++ tailWord_2136107) baseStart_2136107 baseEnd_2136107 := by
    simpa [prefixWord, tailWord_2136107, baseEnd_2136107] using wordTrace_append hprefix tailTrace_2136107
  have hstable : (prefixWord ++ tailWord_2136107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136107).length < 2 ^ (prefixWord ++ tailWord_2136107).sum := by decide
  have hdescent : baseEnd_2136107 < baseStart_2136107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136167 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2136167 : Nat := 118140960795 + 2136167 * 2 ^ 59
def prefixEnd_2136167 : Nat := 4983230072969 + 3 ^ 40 * 2136167 * 2
def baseEnd_2136167 : Nat := 731253619515365980325635

theorem tailTrace_2136167 : CollatzResearch.WordTrace tailWord_2136167 prefixEnd_2136167 731253619515365980325635 := by
  unfold tailWord_2136167
  simp only [CollatzResearch.WordTrace]
  refine ⟨77912411252039262123246755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51941607501359508082164503 77912411252039262123246755)
  ·
    refine ⟨116868616878058893184870133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77912411252039262123246755 116868616878058893184870133)
    ·
      refine ⟨10956432832318021236081575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116868616878058893184870133 10956432832318021236081575)
      ·
        refine ⟨16434649248477031854122363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10956432832318021236081575 16434649248477031854122363)
        ·
          refine ⟨24651973872715547781183545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16434649248477031854122363 24651973872715547781183545)
          ·
            refine ⟨18488980404536660835887659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24651973872715547781183545 18488980404536660835887659)
            ·
              refine ⟨27733470606804991253831489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18488980404536660835887659 27733470606804991253831489)
              ·
                refine ⟨20800102955103743440373617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27733470606804991253831489 20800102955103743440373617)
                ·
                  refine ⟨15600077216327807580280213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20800102955103743440373617 15600077216327807580280213)
                  ·
                    refine ⟨731253619515365980325635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15600077216327807580280213 731253619515365980325635)
                    ·
                      rfl

theorem cell22_2136167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2136167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136167 prefixEnd_2136167 := by exact prefixLift 2136167
  have htrace : WordTrace (prefixWord ++ tailWord_2136167) baseStart_2136167 baseEnd_2136167 := by
    simpa [prefixWord, tailWord_2136167, baseEnd_2136167] using wordTrace_append hprefix tailTrace_2136167
  have hstable : (prefixWord ++ tailWord_2136167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136167).length < 2 ^ (prefixWord ++ tailWord_2136167).sum := by decide
  have hdescent : baseEnd_2136167 < baseStart_2136167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136169 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_2136169 : Nat := 118140960795 + 2136169 * 2 ^ 59
def prefixEnd_2136169 : Nat := 4983230072969 + 3 ^ 40 * 2136169 * 2
def baseEnd_2136169 : Nat := 731254304156238641775629

theorem tailTrace_2136169 : CollatzResearch.WordTrace tailWord_2136169 prefixEnd_2136169 731254304156238641775629 := by
  unfold tailWord_2136169
  simp only [CollatzResearch.WordTrace]
  refine ⟨77912484198032016464819561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51941656132021344309879707 77912484198032016464819561)
  ·
    refine ⟨58434363148524012348614671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77912484198032016464819561 58434363148524012348614671)
    ·
      refine ⟨87651544722786018522922007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58434363148524012348614671 87651544722786018522922007)
      ·
        refine ⟨131477317084179027784383011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87651544722786018522922007 131477317084179027784383011)
        ·
          refine ⟨197215975626268541676574517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131477317084179027784383011 197215975626268541676574517)
          ·
            refine ⟨18488997714962675782178861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197215975626268541676574517 18488997714962675782178861)
            ·
              refine ⟨6933374143111003418317073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18488997714962675782178861 6933374143111003418317073)
              ·
                refine ⟨5200030607333252563737805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6933374143111003418317073 5200030607333252563737805)
                ·
                  refine ⟨1950011477749969711401677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5200030607333252563737805 1950011477749969711401677)
                  ·
                    refine ⟨731254304156238641775629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950011477749969711401677 731254304156238641775629)
                    ·
                      rfl

theorem cell22_2136169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_2136169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136169 prefixEnd_2136169 := by exact prefixLift 2136169
  have htrace : WordTrace (prefixWord ++ tailWord_2136169) baseStart_2136169 baseEnd_2136169 := by
    simpa [prefixWord, tailWord_2136169, baseEnd_2136169] using wordTrace_append hprefix tailTrace_2136169
  have hstable : (prefixWord ++ tailWord_2136169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136169).length < 2 ^ (prefixWord ++ tailWord_2136169).sum := by decide
  have hdescent : baseEnd_2136169 < baseStart_2136169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136199 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 5]
def baseStart_2136199 : Nat := 118140960795 + 2136199 * 2 ^ 59
def prefixEnd_2136199 : Nat := 4983230072969 + 3 ^ 40 * 2136199 * 2
def baseEnd_2136199 : Nat := 243754857923109521175179

theorem tailTrace_2136199 : CollatzResearch.WordTrace tailWord_2136199 prefixEnd_2136199 243754857923109521175179 := by
  unfold tailWord_2136199
  simp only [CollatzResearch.WordTrace]
  refine ⟨77913578387923331588411651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51942385591948887725607767 77913578387923331588411651)
  ·
    refine ⟨116870367581884997382617477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77913578387923331588411651 116870367581884997382617477)
    ·
      refine ⟨21913193921603437009240777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116870367581884997382617477 21913193921603437009240777)
      ·
        refine ⟨16434895441202577756930583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21913193921603437009240777 16434895441202577756930583)
        ·
          refine ⟨24652343161803866635395875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16434895441202577756930583 24652343161803866635395875)
          ·
            refine ⟨36978514742705799953093813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24652343161803866635395875 36978514742705799953093813)
            ·
              refine ⟨3466735757128668745602545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36978514742705799953093813 3466735757128668745602545)
              ·
                refine ⟨2600051817846501559201909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3466735757128668745602545 2600051817846501559201909)
                ·
                  refine ⟨243754857923109521175179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2600051817846501559201909 243754857923109521175179)
                  ·
                    rfl

theorem cell22_2136199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 5].length) (baseStart_2136199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136199 prefixEnd_2136199 := by exact prefixLift 2136199
  have htrace : WordTrace (prefixWord ++ tailWord_2136199) baseStart_2136199 baseEnd_2136199 := by
    simpa [prefixWord, tailWord_2136199, baseEnd_2136199] using wordTrace_append hprefix tailTrace_2136199
  have hstable : (prefixWord ++ tailWord_2136199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136199).length < 2 ^ (prefixWord ++ tailWord_2136199).sum := by decide
  have hdescent : baseEnd_2136199 < baseStart_2136199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136321 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2136321 : Nat := 118140960795 + 2136321 * 2 ^ 59
def prefixEnd_2136321 : Nat := 4983230072969 + 3 ^ 40 * 2136321 * 2
def baseEnd_2136321 : Nat := 731306336862560911975163

theorem tailTrace_2136321 : CollatzResearch.WordTrace tailWord_2136321 prefixEnd_2136321 731306336862560911975163 := by
  unfold tailWord_2136321
  simp only [CollatzResearch.WordTrace]
  refine ⟨77918028093481346424352817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51945352062320897616235211 77918028093481346424352817)
  ·
    refine ⟨58438521070111009818264613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77918028093481346424352817 58438521070111009818264613)
    ·
      refine ⟨10957222700645814340924615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58438521070111009818264613 10957222700645814340924615)
      ·
        refine ⟨16435834050968721511386923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10957222700645814340924615 16435834050968721511386923)
        ·
          refine ⟨24653751076453082267080385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16435834050968721511386923 24653751076453082267080385)
          ·
            refine ⟨18490313307339811700310289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24653751076453082267080385 18490313307339811700310289)
            ·
              refine ⟨13867734980504858775232717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18490313307339811700310289 13867734980504858775232717)
              ·
                refine ⟨5200400617689322040712269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13867734980504858775232717 5200400617689322040712269)
                ·
                  refine ⟨1950150231633495765267101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5200400617689322040712269 1950150231633495765267101)
                  ·
                    refine ⟨731306336862560911975163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950150231633495765267101 731306336862560911975163)
                    ·
                      rfl

theorem cell22_2136321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2136321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136321 prefixEnd_2136321 := by exact prefixLift 2136321
  have htrace : WordTrace (prefixWord ++ tailWord_2136321) baseStart_2136321 baseEnd_2136321 := by
    simpa [prefixWord, tailWord_2136321, baseEnd_2136321] using wordTrace_append hprefix tailTrace_2136321
  have hstable : (prefixWord ++ tailWord_2136321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136321).length < 2 ^ (prefixWord ++ tailWord_2136321).sum := by decide
  have hdescent : baseEnd_2136321 < baseStart_2136321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136385 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 5]
def baseStart_2136385 : Nat := 118140960795 + 2136385 * 2 ^ 59
def prefixEnd_2136385 : Nat := 4983230072969 + 3 ^ 40 * 2136385 * 2
def baseEnd_2136385 : Nat := 243776081790162026124989

theorem tailTrace_2136385 : CollatzResearch.WordTrace tailWord_2136385 prefixEnd_2136385 243776081790162026124989 := by
  unfold tailWord_2136385
  simp only [CollatzResearch.WordTrace]
  refine ⟨77920362365249485354682609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51946908243499656903121739 77920362365249485354682609)
  ·
    refine ⟨58440271773937114016011957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77920362365249485354682609 58440271773937114016011957)
    ·
      refine ⟨5478775478806604439001121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58440271773937114016011957 5478775478806604439001121)
      ·
        refine ⟨4109081609104953329250841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5478775478806604439001121 4109081609104953329250841)
        ·
          refine ⟨3081811206828714996938131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4109081609104953329250841 3081811206828714996938131)
          ·
            refine ⟨4622716810243072495407197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3081811206828714996938131 4622716810243072495407197)
            ·
              refine ⟨1733518803841152185777699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4622716810243072495407197 1733518803841152185777699)
              ·
                refine ⟨2600278205761728278666549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733518803841152185777699 2600278205761728278666549)
                ·
                  refine ⟨243776081790162026124989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2600278205761728278666549 243776081790162026124989)
                  ·
                    rfl

theorem cell22_2136385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_2136385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136385 prefixEnd_2136385 := by exact prefixLift 2136385
  have htrace : WordTrace (prefixWord ++ tailWord_2136385) baseStart_2136385 baseEnd_2136385 := by
    simpa [prefixWord, tailWord_2136385, baseEnd_2136385] using wordTrace_append hprefix tailTrace_2136385
  have hstable : (prefixWord ++ tailWord_2136385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136385).length < 2 ^ (prefixWord ++ tailWord_2136385).sum := by decide
  have hdescent : baseEnd_2136385 < baseStart_2136385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136439 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2136439 : Nat := 118140960795 + 2136439 * 2 ^ 59
def prefixEnd_2136439 : Nat := 4983230072969 + 3 ^ 40 * 2136439 * 2
def baseEnd_2136439 : Nat := 731346730674047937524801

theorem tailTrace_2136439 : CollatzResearch.WordTrace tailWord_2136439 prefixEnd_2136439 731346730674047937524801 := by
  unfold tailWord_2136439
  simp only [CollatzResearch.WordTrace]
  refine ⟨77922331907053852577148371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51948221271369235051432247 77922331907053852577148371)
  ·
    refine ⟨116883497860580778865722557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77922331907053852577148371 116883497860580778865722557)
    ·
      refine ⟨43831311697717792074645959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116883497860580778865722557 43831311697717792074645959)
      ·
        refine ⟨65746967546576688111968939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43831311697717792074645959 65746967546576688111968939)
        ·
          refine ⟨98620451319865032167953409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65746967546576688111968939 98620451319865032167953409)
          ·
            refine ⟨73965338489898774125965057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98620451319865032167953409 73965338489898774125965057)
            ·
              refine ⟨55474003867424080594473793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73965338489898774125965057 55474003867424080594473793)
              ·
                refine ⟨41605502900568060445855345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55474003867424080594473793 41605502900568060445855345)
                ·
                  refine ⟨31204127175426045334391509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41605502900568060445855345 31204127175426045334391509)
                  ·
                    refine ⟨731346730674047937524801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31204127175426045334391509 731346730674047937524801)
                    ·
                      rfl

theorem cell22_2136439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2136439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136439 prefixEnd_2136439 := by exact prefixLift 2136439
  have htrace : WordTrace (prefixWord ++ tailWord_2136439) baseStart_2136439 baseEnd_2136439 := by
    simpa [prefixWord, tailWord_2136439, baseEnd_2136439] using wordTrace_append hprefix tailTrace_2136439
  have hstable : (prefixWord ++ tailWord_2136439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136439).length < 2 ^ (prefixWord ++ tailWord_2136439).sum := by decide
  have hdescent : baseEnd_2136439 < baseStart_2136439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136445 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_2136445 : Nat := 118140960795 + 2136445 * 2 ^ 59
def prefixEnd_2136445 : Nat := 4983230072969 + 3 ^ 40 * 2136445 * 2
def baseEnd_2136445 : Nat := 731348784596665921874783

theorem tailTrace_2136445 : CollatzResearch.WordTrace tailWord_2136445 prefixEnd_2136445 731348784596665921874783 := by
  unfold tailWord_2136445
  simp only [CollatzResearch.WordTrace]
  refine ⟨77922550745032115601866789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51948367163354743734577859 77922550745032115601866789)
  ·
    refine ⟨14610478264693521675350023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77922550745032115601866789 14610478264693521675350023)
    ·
      refine ⟨21915717397040282513025035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14610478264693521675350023 21915717397040282513025035)
      ·
        refine ⟨32873576095560423769537553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21915717397040282513025035 32873576095560423769537553)
        ·
          refine ⟨24655182071670317827153165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32873576095560423769537553 24655182071670317827153165)
          ·
            refine ⟨9245693276876369185182437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24655182071670317827153165 9245693276876369185182437)
            ·
              refine ⟨1733567489414319222221707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9245693276876369185182437 1733567489414319222221707)
              ·
                refine ⟨2600351234121478833332561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733567489414319222221707 2600351234121478833332561)
                ·
                  refine ⟨1950263425591109124999421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600351234121478833332561 1950263425591109124999421)
                  ·
                    refine ⟨731348784596665921874783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950263425591109124999421 731348784596665921874783)
                    ·
                      rfl

theorem cell22_2136445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_2136445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136445 prefixEnd_2136445 := by exact prefixLift 2136445
  have htrace : WordTrace (prefixWord ++ tailWord_2136445) baseStart_2136445 baseEnd_2136445 := by
    simpa [prefixWord, tailWord_2136445, baseEnd_2136445] using wordTrace_append hprefix tailTrace_2136445
  have hstable : (prefixWord ++ tailWord_2136445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136445).length < 2 ^ (prefixWord ++ tailWord_2136445).sum := by decide
  have hdescent : baseEnd_2136445 < baseStart_2136445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136488 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2136488 : Nat := 118140960795 + 2136488 * 2 ^ 59
def prefixEnd_2136488 : Nat := 4983230072969 + 3 ^ 40 * 2136488 * 2
def baseEnd_2136488 : Nat := 731363504375428143049651

theorem tailTrace_2136488 : CollatzResearch.WordTrace tailWord_2136488 prefixEnd_2136488 731363504375428143049651 := by
  unfold tailWord_2136488
  simp only [CollatzResearch.WordTrace]
  refine ⟨38962059541938166972841059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51949412722584222630454745 38962059541938166972841059)
  ·
    refine ⟨58443089312907250459261589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38962059541938166972841059 58443089312907250459261589)
    ·
      refine ⟨2739519811542527365277887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58443089312907250459261589 2739519811542527365277887)
      ·
        refine ⟨4109279717313791047916831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739519811542527365277887 4109279717313791047916831)
        ·
          refine ⟨6163919575970686571875247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109279717313791047916831 6163919575970686571875247)
          ·
            refine ⟨9245879363956029857812871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6163919575970686571875247 9245879363956029857812871)
            ·
              refine ⟨13868819045934044786719307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9245879363956029857812871 13868819045934044786719307)
              ·
                refine ⟨20803228568901067180078961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13868819045934044786719307 20803228568901067180078961)
                ·
                  refine ⟨15602421426675800385059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20803228568901067180078961 15602421426675800385059221)
                  ·
                    refine ⟨731363504375428143049651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15602421426675800385059221 731363504375428143049651)
                    ·
                      rfl

theorem cell22_2136488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2136488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136488 prefixEnd_2136488 := by exact prefixLift 2136488
  have htrace : WordTrace (prefixWord ++ tailWord_2136488) baseStart_2136488 baseEnd_2136488 := by
    simpa [prefixWord, tailWord_2136488, baseEnd_2136488] using wordTrace_append hprefix tailTrace_2136488
  have hstable : (prefixWord ++ tailWord_2136488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136488).length < 2 ^ (prefixWord ++ tailWord_2136488).sum := by decide
  have hdescent : baseEnd_2136488 < baseStart_2136488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136561 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2136561 : Nat := 118140960795 + 2136561 * 2 ^ 59
def prefixEnd_2136561 : Nat := 4983230072969 + 3 ^ 40 * 2136561 * 2
def baseEnd_2136561 : Nat := 731388493767280285974427

theorem tailTrace_2136561 : CollatzResearch.WordTrace tailWord_2136561 prefixEnd_2136561 731388493767280285974427 := by
  unfold tailWord_2136561
  simp only [CollatzResearch.WordTrace]
  refine ⟨77926781612611867413089537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51951187741741244942059691 77926781612611867413089537)
  ·
    refine ⟨58445086209458900559817153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77926781612611867413089537 58445086209458900559817153)
    ·
      refine ⟨43833814657094175419862865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58445086209458900559817153 43833814657094175419862865)
      ·
        refine ⟨32875360992820631564897149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43833814657094175419862865 32875360992820631564897149)
        ·
          refine ⟨12328260372307736836836431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32875360992820631564897149 12328260372307736836836431)
          ·
            refine ⟨18492390558461605255254647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12328260372307736836836431 18492390558461605255254647)
            ·
              refine ⟨27738585837692407882881971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18492390558461605255254647 27738585837692407882881971)
              ·
                refine ⟨41607878756538611824322957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27738585837692407882881971 41607878756538611824322957)
                ·
                  refine ⟨15602954533701979434121109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41607878756538611824322957 15602954533701979434121109)
                  ·
                    refine ⟨731388493767280285974427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15602954533701979434121109 731388493767280285974427)
                    ·
                      rfl

theorem cell22_2136561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2136561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136561 prefixEnd_2136561 := by exact prefixLift 2136561
  have htrace : WordTrace (prefixWord ++ tailWord_2136561) baseStart_2136561 baseEnd_2136561 := by
    simpa [prefixWord, tailWord_2136561, baseEnd_2136561] using wordTrace_append hprefix tailTrace_2136561
  have hstable : (prefixWord ++ tailWord_2136561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136561).length < 2 ^ (prefixWord ++ tailWord_2136561).sum := by decide
  have hdescent : baseEnd_2136561 < baseStart_2136561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136580 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2136580 : Nat := 118140960795 + 2136580 * 2 ^ 59
def prefixEnd_2136580 : Nat := 4983230072969 + 3 ^ 40 * 2136580 * 2
def baseEnd_2136580 : Nat := 731394997855570569749369

theorem tailTrace_2136580 : CollatzResearch.WordTrace tailWord_2136580 prefixEnd_2136580 731394997855570569749369 := by
  unfold tailWord_2136580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38963737299771516829015597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51951649733028689105354129 38963737299771516829015597)
  ·
    refine ⟨14611401487414318810880849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38963737299771516829015597 14611401487414318810880849)
    ·
      refine ⟨10958551115560739108160637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14611401487414318810880849 10958551115560739108160637)
      ·
        refine ⟨4109456668335277165560239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10958551115560739108160637 4109456668335277165560239)
        ·
          refine ⟨6164185002502915748340359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109456668335277165560239 6164185002502915748340359)
          ·
            refine ⟨9246277503754373622510539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164185002502915748340359 9246277503754373622510539)
            ·
              refine ⟨13869416255631560433765809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9246277503754373622510539 13869416255631560433765809)
              ·
                refine ⟨10402062191723670325324357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13869416255631560433765809 10402062191723670325324357)
                ·
                  refine ⟨1950386660948188185998317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10402062191723670325324357 1950386660948188185998317)
                  ·
                    refine ⟨731394997855570569749369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950386660948188185998317 731394997855570569749369)
                    ·
                      rfl

theorem cell22_2136580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2136580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136580 prefixEnd_2136580 := by exact prefixLift 2136580
  have htrace : WordTrace (prefixWord ++ tailWord_2136580) baseStart_2136580 baseEnd_2136580 := by
    simpa [prefixWord, tailWord_2136580, baseEnd_2136580] using wordTrace_append hprefix tailTrace_2136580
  have hstable : (prefixWord ++ tailWord_2136580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136580).length < 2 ^ (prefixWord ++ tailWord_2136580).sum := by decide
  have hdescent : baseEnd_2136580 < baseStart_2136580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136599 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 4]
def baseStart_2136599 : Nat := 118140960795 + 2136599 * 2 ^ 59
def prefixEnd_2136599 : Nat := 4983230072969 + 3 ^ 40 * 2136599 * 2
def baseEnd_2136599 : Nat := 243800500647953617841437

theorem tailTrace_2136599 : CollatzResearch.WordTrace tailWord_2136599 prefixEnd_2136599 243800500647953617841437 := by
  unfold tailWord_2136599
  simp only [CollatzResearch.WordTrace]
  refine ⟨77928167586474199902972851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51952111724316133268648567 77928167586474199902972851)
  ·
    refine ⟨116892251379711299854459277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77928167586474199902972851 116892251379711299854459277)
    ·
      refine ⟨43834594267391737445422229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116892251379711299854459277 43834594267391737445422229)
      ·
        refine ⟨2054746606283987692754167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43834594267391737445422229 2054746606283987692754167)
        ·
          refine ⟨3082119909425981539131251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054746606283987692754167 3082119909425981539131251)
          ·
            refine ⟨4623179864138972308696877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082119909425981539131251 4623179864138972308696877)
            ·
              refine ⟨1733692449052114615761329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4623179864138972308696877 1733692449052114615761329)
              ·
                refine ⟨1300269336789085961820997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733692449052114615761329 1300269336789085961820997)
                ·
                  refine ⟨243800500647953617841437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300269336789085961820997 243800500647953617841437)
                  ·
                    rfl

theorem cell22_2136599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 4].length) (baseStart_2136599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136599 prefixEnd_2136599 := by exact prefixLift 2136599
  have htrace : WordTrace (prefixWord ++ tailWord_2136599) baseStart_2136599 baseEnd_2136599 := by
    simpa [prefixWord, tailWord_2136599, baseEnd_2136599] using wordTrace_append hprefix tailTrace_2136599
  have hstable : (prefixWord ++ tailWord_2136599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136599).length < 2 ^ (prefixWord ++ tailWord_2136599).sum := by decide
  have hdescent : baseEnd_2136599 < baseStart_2136599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136685 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2136685 : Nat := 118140960795 + 2136685 * 2 ^ 59
def prefixEnd_2136685 : Nat := 4983230072969 + 3 ^ 40 * 2136685 * 2
def baseEnd_2136685 : Nat := 731430941501385295874047

theorem tailTrace_2136685 : CollatzResearch.WordTrace tailWord_2136685 prefixEnd_2136685 731430941501385295874047 := by
  unfold tailWord_2136685
  simp only [CollatzResearch.WordTrace]
  refine ⟨77931304264162636590603509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51954202842775091060402339 77931304264162636590603509)
  ·
    refine ⟨7306059774765247180369079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77931304264162636590603509 7306059774765247180369079)
    ·
      refine ⟨10959089662147870770553619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7306059774765247180369079 10959089662147870770553619)
      ·
        refine ⟨16438634493221806155830429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10959089662147870770553619 16438634493221806155830429)
        ·
          refine ⟨6164487934958177308436411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16438634493221806155830429 6164487934958177308436411)
          ·
            refine ⟨9246731902437265962654617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164487934958177308436411 9246731902437265962654617)
            ·
              refine ⟨6935048926827949471990963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9246731902437265962654617 6935048926827949471990963)
              ·
                refine ⟨10402573390241924207986445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6935048926827949471990963 10402573390241924207986445)
                ·
                  refine ⟨3900965021340721577994917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10402573390241924207986445 3900965021340721577994917)
                  ·
                    refine ⟨731430941501385295874047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3900965021340721577994917 731430941501385295874047)
                    ·
                      rfl

theorem cell22_2136685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2136685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136685 prefixEnd_2136685 := by exact prefixLift 2136685
  have htrace : WordTrace (prefixWord ++ tailWord_2136685) baseStart_2136685 baseEnd_2136685 := by
    simpa [prefixWord, tailWord_2136685, baseEnd_2136685] using wordTrace_append hprefix tailTrace_2136685
  have hstable : (prefixWord ++ tailWord_2136685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136685).length < 2 ^ (prefixWord ++ tailWord_2136685).sum := by decide
  have hdescent : baseEnd_2136685 < baseStart_2136685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136700 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_2136700 : Nat := 118140960795 + 2136700 * 2 ^ 59
def prefixEnd_2136700 : Nat := 4983230072969 + 3 ^ 40 * 2136700 * 2
def baseEnd_2136700 : Nat := 243812025435976752249667

theorem tailTrace_2136700 : CollatzResearch.WordTrace tailWord_2136700 prefixEnd_2136700 243812025435976752249667 := by
  unfold tailWord_2136700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38965925679554147076199777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51954567572738862768266369 38965925679554147076199777)
  ·
    refine ⟨29224444259665610307149833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38965925679554147076199777 29224444259665610307149833)
    ·
      refine ⟨21918333194749207730362375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29224444259665610307149833 21918333194749207730362375)
      ·
        refine ⟨32877499792123811595543563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21918333194749207730362375 32877499792123811595543563)
        ·
          refine ⟨49316249688185717393315345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32877499792123811595543563 49316249688185717393315345)
          ·
            refine ⟨36987187266139288044986509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49316249688185717393315345 36987187266139288044986509)
            ·
              refine ⟨13870195224802233016869941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36987187266139288044986509 13870195224802233016869941)
              ·
                refine ⟨1300330802325209345331557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13870195224802233016869941 1300330802325209345331557)
                ·
                  refine ⟨243812025435976752249667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300330802325209345331557 243812025435976752249667)
                  ·
                    rfl

theorem cell22_2136700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_2136700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136700 prefixEnd_2136700 := by exact prefixLift 2136700
  have htrace : WordTrace (prefixWord ++ tailWord_2136700) baseStart_2136700 baseEnd_2136700 := by
    simpa [prefixWord, tailWord_2136700, baseEnd_2136700] using wordTrace_append hprefix tailTrace_2136700
  have hstable : (prefixWord ++ tailWord_2136700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136700).length < 2 ^ (prefixWord ++ tailWord_2136700).sum := by decide
  have hdescent : baseEnd_2136700 < baseStart_2136700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136713 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_2136713 : Nat := 118140960795 + 2136713 * 2 ^ 59
def prefixEnd_2136713 : Nat := 4983230072969 + 3 ^ 40 * 2136713 * 2
def baseEnd_2136713 : Nat := 731440526473602556173961

theorem tailTrace_2136713 : CollatzResearch.WordTrace tailWord_2136713 prefixEnd_2136713 731440526473602556173961 := by
  unfold tailWord_2136713
  simp only [CollatzResearch.WordTrace]
  refine ⟨77932325508061197372622793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51954883672040798248415195 77932325508061197372622793)
  ·
    refine ⟨58449244131045898029467095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77932325508061197372622793 58449244131045898029467095)
    ·
      refine ⟨87673866196568847044200643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58449244131045898029467095 87673866196568847044200643)
      ·
        refine ⟨131510799294853270566300965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87673866196568847044200643 131510799294853270566300965)
        ·
          refine ⟨24658274867784988231181431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131510799294853270566300965 24658274867784988231181431)
          ·
            refine ⟨36987412301677482346772147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24658274867784988231181431 36987412301677482346772147)
            ·
              refine ⟨55481118452516223520158221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36987412301677482346772147 55481118452516223520158221)
              ·
                refine ⟨20805419419693583820059333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55481118452516223520158221 20805419419693583820059333)
                ·
                  refine ⟨3901016141192546966261125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20805419419693583820059333 3901016141192546966261125)
                  ·
                    refine ⟨731440526473602556173961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3901016141192546966261125 731440526473602556173961)
                    ·
                      rfl

theorem cell22_2136713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_2136713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136713 prefixEnd_2136713 := by exact prefixLift 2136713
  have htrace : WordTrace (prefixWord ++ tailWord_2136713) baseStart_2136713 baseEnd_2136713 := by
    simpa [prefixWord, tailWord_2136713, baseEnd_2136713] using wordTrace_append hprefix tailTrace_2136713
  have hstable : (prefixWord ++ tailWord_2136713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136713).length < 2 ^ (prefixWord ++ tailWord_2136713).sum := by decide
  have hdescent : baseEnd_2136713 < baseStart_2136713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136715 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 2, 3]
def baseStart_2136715 : Nat := 118140960795 + 2136715 * 2 ^ 59
def prefixEnd_2136715 : Nat := 4983230072969 + 3 ^ 40 * 2136715 * 2
def baseEnd_2136715 : Nat := 731441211114475217623955

theorem tailTrace_2136715 : CollatzResearch.WordTrace tailWord_2136715 prefixEnd_2136715 731441211114475217623955 := by
  unfold tailWord_2136715
  simp only [CollatzResearch.WordTrace]
  refine ⟨77932398454053951714195599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51954932302702634476130399 77932398454053951714195599)
  ·
    refine ⟨116898597681080927571293399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77932398454053951714195599 116898597681080927571293399)
    ·
      refine ⟨175347896521621391356940099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116898597681080927571293399 175347896521621391356940099)
      ·
        refine ⟨263021844782432087035410149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175347896521621391356940099 263021844782432087035410149)
        ·
          refine ⟨49316595896706016319139403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263021844782432087035410149 49316595896706016319139403)
          ·
            refine ⟨73974893845059024478709105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49316595896706016319139403 73974893845059024478709105)
            ·
              refine ⟨55481170383794268359031829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73974893845059024478709105 55481170383794268359031829)
              ·
                refine ⟨2600679861740356329329617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55481170383794268359031829 2600679861740356329329617)
                ·
                  refine ⟨1950509896305267246997213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2600679861740356329329617 1950509896305267246997213)
                  ·
                    refine ⟨731441211114475217623955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950509896305267246997213 731441211114475217623955)
                    ·
                      rfl

theorem cell22_2136715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3].length) (baseStart_2136715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136715 prefixEnd_2136715 := by exact prefixLift 2136715
  have htrace : WordTrace (prefixWord ++ tailWord_2136715) baseStart_2136715 baseEnd_2136715 := by
    simpa [prefixWord, tailWord_2136715, baseEnd_2136715] using wordTrace_append hprefix tailTrace_2136715
  have hstable : (prefixWord ++ tailWord_2136715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136715).length < 2 ^ (prefixWord ++ tailWord_2136715).sum := by decide
  have hdescent : baseEnd_2136715 < baseStart_2136715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136728 : List Nat := [2, 1, 2, 4, 1, 1, 2, 9]
def baseStart_2136728 : Nat := 118140960795 + 2136728 * 2 ^ 59
def prefixEnd_2136728 : Nat := 4983230072969 + 3 ^ 40 * 2136728 * 2
def baseEnd_2136728 : Nat := 81271740142238613005435

theorem tailTrace_2136728 : CollatzResearch.WordTrace tailWord_2136728 prefixEnd_2136728 81271740142238613005435 := by
  unfold tailWord_2136728
  simp only [CollatzResearch.WordTrace]
  refine ⟨38966436301503427467209419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51955248402004569956279225 38966436301503427467209419)
  ·
    refine ⟨58449654452255141200814129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38966436301503427467209419 58449654452255141200814129)
    ·
      refine ⟨43837240839191355900610597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58449654452255141200814129 43837240839191355900610597)
      ·
        refine ⟨8219482657348379231364487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43837240839191355900610597 8219482657348379231364487)
        ·
          refine ⟨12329223986022568847046731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219482657348379231364487 12329223986022568847046731)
          ·
            refine ⟨18493835979033853270570097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12329223986022568847046731 18493835979033853270570097)
            ·
              refine ⟨13870376984275389952927573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18493835979033853270570097 13870376984275389952927573)
              ·
                refine ⟨81271740142238613005435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13870376984275389952927573 81271740142238613005435)
                ·
                  rfl

theorem cell22_2136728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_2136728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136728 prefixEnd_2136728 := by exact prefixLift 2136728
  have htrace : WordTrace (prefixWord ++ tailWord_2136728) baseStart_2136728 baseEnd_2136728 := by
    simpa [prefixWord, tailWord_2136728, baseEnd_2136728] using wordTrace_append hprefix tailTrace_2136728
  have hstable : (prefixWord ++ tailWord_2136728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136728).length < 2 ^ (prefixWord ++ tailWord_2136728).sum := by decide
  have hdescent : baseEnd_2136728 < baseStart_2136728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136732 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2136732 : Nat := 118140960795 + 2136732 * 2 ^ 59
def prefixEnd_2136732 : Nat := 4983230072969 + 3 ^ 40 * 2136732 * 2
def baseEnd_2136732 : Nat := 731447030561892839948903

theorem tailTrace_2136732 : CollatzResearch.WordTrace tailWord_2136732 prefixEnd_2136732 731447030561892839948903 := by
  unfold tailWord_2136732
  simp only [CollatzResearch.WordTrace]
  refine ⟨38966509247496181808782225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51955345663328242411709633 38966509247496181808782225)
  ·
    refine ⟨29224881935622136356586669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38966509247496181808782225 29224881935622136356586669)
    ·
      refine ⟨10959330725858301133720001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29224881935622136356586669 10959330725858301133720001)
      ·
        refine ⟨8219498044393725850290001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10959330725858301133720001 8219498044393725850290001)
        ·
          refine ⟨6164623533295294387717501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8219498044393725850290001 6164623533295294387717501)
          ·
            refine ⟨2311733824985735395394063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6164623533295294387717501 2311733824985735395394063)
            ·
              refine ⟨3467600737478603093091095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311733824985735395394063 3467600737478603093091095)
              ·
                refine ⟨5201401106217904639636643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3467600737478603093091095 5201401106217904639636643)
                ·
                  refine ⟨7802101659326856959454965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201401106217904639636643 7802101659326856959454965)
                  ·
                    refine ⟨731447030561892839948903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7802101659326856959454965 731447030561892839948903)
                    ·
                      rfl

theorem cell22_2136732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2136732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136732 prefixEnd_2136732 := by exact prefixLift 2136732
  have htrace : WordTrace (prefixWord ++ tailWord_2136732) baseStart_2136732 baseEnd_2136732 := by
    simpa [prefixWord, tailWord_2136732, baseEnd_2136732] using wordTrace_append hprefix tailTrace_2136732
  have hstable : (prefixWord ++ tailWord_2136732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136732).length < 2 ^ (prefixWord ++ tailWord_2136732).sum := by decide
  have hdescent : baseEnd_2136732 < baseStart_2136732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136865 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2136865 : Nat := 118140960795 + 2136865 * 2 ^ 59
def prefixEnd_2136865 : Nat := 4983230072969 + 3 ^ 40 * 2136865 * 2
def baseEnd_2136865 : Nat := 731492559179924826373495

theorem tailTrace_2136865 : CollatzResearch.WordTrace tailWord_2136865 prefixEnd_2136865 731492559179924826373495 := by
  unfold tailWord_2136865
  simp only [CollatzResearch.WordTrace]
  refine ⟨77937869403510527332156049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51958579602340351554770699 77937869403510527332156049)
  ·
    refine ⟨58453402052632895499117037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77937869403510527332156049 58453402052632895499117037)
    ·
      refine ⟨21920025769737335812168889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58453402052632895499117037 21920025769737335812168889)
      ·
        refine ⟨16440019327303001859126667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21920025769737335812168889 16440019327303001859126667)
        ·
          refine ⟨24660028990954502788690001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16440019327303001859126667 24660028990954502788690001)
          ·
            refine ⟨18495021743215877091517501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24660028990954502788690001 18495021743215877091517501)
            ·
              refine ⟨6935633153705953909319063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18495021743215877091517501 6935633153705953909319063)
              ·
                refine ⟨10403449730558930863978595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6935633153705953909319063 10403449730558930863978595)
                ·
                  refine ⟨15605174595838396295967893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10403449730558930863978595 15605174595838396295967893)
                  ·
                    refine ⟨731492559179924826373495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15605174595838396295967893 731492559179924826373495)
                    ·
                      rfl

theorem cell22_2136865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2136865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136865 prefixEnd_2136865 := by exact prefixLift 2136865
  have htrace : WordTrace (prefixWord ++ tailWord_2136865) baseStart_2136865 baseEnd_2136865 := by
    simpa [prefixWord, tailWord_2136865, baseEnd_2136865] using wordTrace_append hprefix tailTrace_2136865
  have hstable : (prefixWord ++ tailWord_2136865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136865).length < 2 ^ (prefixWord ++ tailWord_2136865).sum := by decide
  have hdescent : baseEnd_2136865 < baseStart_2136865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136910 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2136910 : Nat := 118140960795 + 2136910 * 2 ^ 59
def prefixEnd_2136910 : Nat := 4983230072969 + 3 ^ 40 * 2136910 * 2
def baseEnd_2136910 : Nat := 731507963599559708998357

theorem tailTrace_2136910 : CollatzResearch.WordTrace tailWord_2136910 prefixEnd_2136910 731507963599559708998357 := by
  unfold tailWord_2136910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9742438836043437502193023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51959673792231666678362789 9742438836043437502193023)
  ·
    refine ⟨14613658254065156253289535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9742438836043437502193023 14613658254065156253289535)
    ·
      refine ⟨21920487381097734379934303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14613658254065156253289535 21920487381097734379934303)
      ·
        refine ⟨32880731071646601569901455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21920487381097734379934303 32880731071646601569901455)
        ·
          refine ⟨49321096607469902354852183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32880731071646601569901455 49321096607469902354852183)
          ·
            refine ⟨73981644911204853532278275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49321096607469902354852183 73981644911204853532278275)
            ·
              refine ⟨110972467366807280298417413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73981644911204853532278275 110972467366807280298417413)
              ·
                refine ⟨20807337631276365055953265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110972467366807280298417413 20807337631276365055953265)
                ·
                  refine ⟨15605503223457273791964949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20807337631276365055953265 15605503223457273791964949)
                  ·
                    refine ⟨731507963599559708998357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15605503223457273791964949 731507963599559708998357)
                    ·
                      rfl

theorem cell22_2136910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2136910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136910 prefixEnd_2136910 := by exact prefixLift 2136910
  have htrace : WordTrace (prefixWord ++ tailWord_2136910) baseStart_2136910 baseEnd_2136910 := by
    simpa [prefixWord, tailWord_2136910, baseEnd_2136910] using wordTrace_append hprefix tailTrace_2136910
  have hstable : (prefixWord ++ tailWord_2136910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136910).length < 2 ^ (prefixWord ++ tailWord_2136910).sum := by decide
  have hdescent : baseEnd_2136910 < baseStart_2136910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136912 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_2136912 : Nat := 118140960795 + 2136912 * 2 ^ 59
def prefixEnd_2136912 : Nat := 4983230072969 + 3 ^ 40 * 2136912 * 2
def baseEnd_2136912 : Nat := 731508648240432370448351

theorem tailTrace_2136912 : CollatzResearch.WordTrace tailWord_2136912 prefixEnd_2136912 731508648240432370448351 := by
  unfold tailWord_2136912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38969791817170127179558495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51959722422893502906077993 38969791817170127179558495)
  ·
    refine ⟨58454687725755190769337743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38969791817170127179558495 58454687725755190769337743)
    ·
      refine ⟨87682031588632786154006615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58454687725755190769337743 87682031588632786154006615)
      ·
        refine ⟨131523047382949179231009923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87682031588632786154006615 131523047382949179231009923)
        ·
          refine ⟨197284571074423768846514885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131523047382949179231009923 197284571074423768846514885)
          ·
            refine ⟨36990857076454456658721541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197284571074423768846514885 36990857076454456658721541)
            ·
              refine ⟨6935785701835210623510289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36990857076454456658721541 6935785701835210623510289)
              ·
                refine ⟨5201839276376407967632717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935785701835210623510289 5201839276376407967632717)
                ·
                  refine ⟨1950689728641152987862269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5201839276376407967632717 1950689728641152987862269)
                  ·
                    refine ⟨731508648240432370448351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950689728641152987862269 731508648240432370448351)
                    ·
                      rfl

theorem cell22_2136912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_2136912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136912 prefixEnd_2136912 := by exact prefixLift 2136912
  have htrace : WordTrace (prefixWord ++ tailWord_2136912) baseStart_2136912 baseEnd_2136912 := by
    simpa [prefixWord, tailWord_2136912, baseEnd_2136912] using wordTrace_append hprefix tailTrace_2136912
  have hstable : (prefixWord ++ tailWord_2136912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136912).length < 2 ^ (prefixWord ++ tailWord_2136912).sum := by decide
  have hdescent : baseEnd_2136912 < baseStart_2136912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2136929 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 1, 3]
def baseStart_2136929 : Nat := 118140960795 + 2136929 * 2 ^ 59
def prefixEnd_2136929 : Nat := 4983230072969 + 3 ^ 40 * 2136929 * 2
def baseEnd_2136929 : Nat := 731514467687849992773299

theorem tailTrace_2136929 : CollatzResearch.WordTrace tailWord_2136929 prefixEnd_2136929 731514467687849992773299 := by
  unfold tailWord_2136929
  simp only [CollatzResearch.WordTrace]
  refine ⟨77940203675278666262485841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51960135783519110841657227 77940203675278666262485841)
  ·
    refine ⟨58455152756458999696864381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77940203675278666262485841 58455152756458999696864381)
    ·
      refine ⟨21920682283672124886324143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58455152756458999696864381 21920682283672124886324143)
      ·
        refine ⟨32881023425508187329486215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21920682283672124886324143 32881023425508187329486215)
        ·
          refine ⟨49321535138262280994229323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32881023425508187329486215 49321535138262280994229323)
          ·
            refine ⟨73982302707393421491343985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49321535138262280994229323 73982302707393421491343985)
            ·
              refine ⟨55486727030545066118507989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73982302707393421491343985 55486727030545066118507989)
              ·
                refine ⟨1300470164778399987152531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55486727030545066118507989 1300470164778399987152531)
                ·
                  refine ⟨1950705247167599980728797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300470164778399987152531 1950705247167599980728797)
                  ·
                    refine ⟨731514467687849992773299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950705247167599980728797 731514467687849992773299)
                    ·
                      rfl

theorem cell22_2136929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_2136929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2136929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2136929 prefixEnd_2136929 := by exact prefixLift 2136929
  have htrace : WordTrace (prefixWord ++ tailWord_2136929) baseStart_2136929 baseEnd_2136929 := by
    simpa [prefixWord, tailWord_2136929, baseEnd_2136929] using wordTrace_append hprefix tailTrace_2136929
  have hstable : (prefixWord ++ tailWord_2136929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2136929).length < 2 ^ (prefixWord ++ tailWord_2136929).sum := by decide
  have hdescent : baseEnd_2136929 < baseStart_2136929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2136929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137053 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2137053 : Nat := 118140960795 + 2137053 * 2 ^ 59
def prefixEnd_2137053 : Nat := 4983230072969 + 3 ^ 40 * 2137053 * 2
def baseEnd_2137053 : Nat := 731556915421955002672919

theorem tailTrace_2137053 : CollatzResearch.WordTrace tailWord_2137053 prefixEnd_2137053 731556915421955002672919 := by
  unfold tailWord_2137053
  simp only [CollatzResearch.WordTrace]
  refine ⟨77944726326829435439999813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51963150884552956959999875 77944726326829435439999813)
  ·
    refine ⟨14614636186280519144999965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77944726326829435439999813 14614636186280519144999965)
    ·
      refine ⟨5480488569855194679374987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14614636186280519144999965 5480488569855194679374987)
      ·
        refine ⟨8220732854782792019062481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5480488569855194679374987 8220732854782792019062481)
        ·
          refine ⟨6165549641087094014296861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8220732854782792019062481 6165549641087094014296861)
          ·
            refine ⟨2312081115407660255361323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6165549641087094014296861 2312081115407660255361323)
            ·
              refine ⟨3468121673111490383041985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312081115407660255361323 3468121673111490383041985)
              ·
                refine ⟨2601091254833617787281489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3468121673111490383041985 2601091254833617787281489)
                ·
                  refine ⟨1950818441125213340461117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601091254833617787281489 1950818441125213340461117)
                  ·
                    refine ⟨731556915421955002672919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950818441125213340461117 731556915421955002672919)
                    ·
                      rfl

theorem cell22_2137053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2137053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137053 prefixEnd_2137053 := by exact prefixLift 2137053
  have htrace : WordTrace (prefixWord ++ tailWord_2137053) baseStart_2137053 baseEnd_2137053 := by
    simpa [prefixWord, tailWord_2137053, baseEnd_2137053] using wordTrace_append hprefix tailTrace_2137053
  have hstable : (prefixWord ++ tailWord_2137053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137053).length < 2 ^ (prefixWord ++ tailWord_2137053).sum := by decide
  have hdescent : baseEnd_2137053 < baseStart_2137053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137064 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2137064 : Nat := 118140960795 + 2137064 * 2 ^ 59
def prefixEnd_2137064 : Nat := 4983230072969 + 3 ^ 40 * 2137064 * 2
def baseEnd_2137064 : Nat := 731560680946754640647885

theorem tailTrace_2137064 : CollatzResearch.WordTrace tailWord_2137064 prefixEnd_2137064 731560680946754640647885 := by
  unfold tailWord_2137064
  simp only [CollatzResearch.WordTrace]
  refine ⟨38972563764894792159325123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51963418353193056212433497 38972563764894792159325123)
  ·
    refine ⟨58458845647342188238987685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38972563764894792159325123 58458845647342188238987685)
    ·
      refine ⟨10961033558876660294810191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58458845647342188238987685 10961033558876660294810191)
      ·
        refine ⟨16441550338314990442215287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10961033558876660294810191 16441550338314990442215287)
        ·
          refine ⟨24662325507472485663322931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16441550338314990442215287 24662325507472485663322931)
          ·
            refine ⟨36993488261208728494984397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24662325507472485663322931 36993488261208728494984397)
            ·
              refine ⟨13872558097953273185619149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36993488261208728494984397 13872558097953273185619149)
              ·
                refine ⟨5202209286732477444607181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13872558097953273185619149 5202209286732477444607181)
                ·
                  refine ⟨1950828482524679041727693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5202209286732477444607181 1950828482524679041727693)
                  ·
                    refine ⟨731560680946754640647885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950828482524679041727693 731560680946754640647885)
                    ·
                      rfl

theorem cell22_2137064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2137064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137064 prefixEnd_2137064 := by exact prefixLift 2137064
  have htrace : WordTrace (prefixWord ++ tailWord_2137064) baseStart_2137064 baseEnd_2137064 := by
    simpa [prefixWord, tailWord_2137064, baseEnd_2137064] using wordTrace_append hprefix tailTrace_2137064
  have hstable : (prefixWord ++ tailWord_2137064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137064).length < 2 ^ (prefixWord ++ tailWord_2137064).sum := by decide
  have hdescent : baseEnd_2137064 < baseStart_2137064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137098 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_2137098 : Nat := 118140960795 + 2137098 * 2 ^ 59
def prefixEnd_2137098 : Nat := 4983230072969 + 3 ^ 40 * 2137098 * 2
def baseEnd_2137098 : Nat := 731572319841589885297781

theorem tailTrace_2137098 : CollatzResearch.WordTrace tailWord_2137098 prefixEnd_2137098 731572319841589885297781 := by
  unfold tailWord_2137098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19486591902916602031346987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51964245074444272083591965 19486591902916602031346987)
  ·
    refine ⟨29229887854374903047020481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19486591902916602031346987 29229887854374903047020481)
    ·
      refine ⟨21922415890781177285265361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29229887854374903047020481 21922415890781177285265361)
      ·
        refine ⟨16441811918085882963949021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21922415890781177285265361 16441811918085882963949021)
        ·
          refine ⟨6165679469282206111480883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16441811918085882963949021 6165679469282206111480883)
          ·
            refine ⟨9248519203923309167221325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6165679469282206111480883 9248519203923309167221325)
            ·
              refine ⟨3468194701471240937707997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9248519203923309167221325 3468194701471240937707997)
              ·
                refine ⟨1300573013051715351640499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3468194701471240937707997 1300573013051715351640499)
                ·
                  refine ⟨1950859519577573027460749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300573013051715351640499 1950859519577573027460749)
                  ·
                    refine ⟨731572319841589885297781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1950859519577573027460749 731572319841589885297781)
                    ·
                      rfl

theorem cell22_2137098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_2137098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137098 prefixEnd_2137098 := by exact prefixLift 2137098
  have htrace : WordTrace (prefixWord ++ tailWord_2137098) baseStart_2137098 baseEnd_2137098 := by
    simpa [prefixWord, tailWord_2137098, baseEnd_2137098] using wordTrace_append hprefix tailTrace_2137098
  have hstable : (prefixWord ++ tailWord_2137098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137098).length < 2 ^ (prefixWord ++ tailWord_2137098).sum := by decide
  have hdescent : baseEnd_2137098 < baseStart_2137098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137107 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_2137107 : Nat := 118140960795 + 2137107 * 2 ^ 59
def prefixEnd_2137107 : Nat := 4983230072969 + 3 ^ 40 * 2137107 * 2
def baseEnd_2137107 : Nat := 731575400725516861822753

theorem tailTrace_2137107 : CollatzResearch.WordTrace tailWord_2137107 prefixEnd_2137107 731575400725516861822753 := by
  unfold tailWord_2137107
  simp only [CollatzResearch.WordTrace]
  refine ⟨77946695868633802662465575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51964463912422535108310383 77946695868633802662465575)
  ·
    refine ⟨116920043802950703993698363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77946695868633802662465575 116920043802950703993698363)
    ·
      refine ⟨175380065704426055990547545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116920043802950703993698363 175380065704426055990547545)
      ·
        refine ⟨131535049278319541992910659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175380065704426055990547545 131535049278319541992910659)
        ·
          refine ⟨197302573917479312989365989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131535049278319541992910659 197302573917479312989365989)
          ·
            refine ⟨36994232609527371185506123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 197302573917479312989365989 36994232609527371185506123)
            ·
              refine ⟨55491348914291056778259185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36994232609527371185506123 55491348914291056778259185)
              ·
                refine ⟨41618511685718292583694389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55491348914291056778259185 41618511685718292583694389)
                ·
                  refine ⟨3901735470536089929721349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41618511685718292583694389 3901735470536089929721349)
                  ·
                    refine ⟨731575400725516861822753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3901735470536089929721349 731575400725516861822753)
                    ·
                      rfl

theorem cell22_2137107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_2137107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137107 prefixEnd_2137107 := by exact prefixLift 2137107
  have htrace : WordTrace (prefixWord ++ tailWord_2137107) baseStart_2137107 baseEnd_2137107 := by
    simpa [prefixWord, tailWord_2137107, baseEnd_2137107] using wordTrace_append hprefix tailTrace_2137107
  have hstable : (prefixWord ++ tailWord_2137107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137107).length < 2 ^ (prefixWord ++ tailWord_2137107).sum := by decide
  have hdescent : baseEnd_2137107 < baseStart_2137107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137169 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2137169 : Nat := 118140960795 + 2137169 * 2 ^ 59
def prefixEnd_2137169 : Nat := 4983230072969 + 3 ^ 40 * 2137169 * 2
def baseEnd_2137169 : Nat := 731596624592569366772563

theorem tailTrace_2137169 : CollatzResearch.WordTrace tailWord_2137169 prefixEnd_2137169 731596624592569366772563 := by
  unfold tailWord_2137169
  simp only [CollatzResearch.WordTrace]
  refine ⟨77948957194409187251222561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51965971462939458167481707 77948957194409187251222561)
  ·
    refine ⟨58461717895806890438416921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77948957194409187251222561 58461717895806890438416921)
    ·
      refine ⟨43846288421855167828812691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58461717895806890438416921 43846288421855167828812691)
      ·
        refine ⟨65769432632782751743219037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43846288421855167828812691 65769432632782751743219037)
        ·
          refine ⟨24663537237293531903707139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65769432632782751743219037 24663537237293531903707139)
          ·
            refine ⟨36995305855940297855560709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24663537237293531903707139 36995305855940297855560709)
            ·
              refine ⟨6936619847988805847917633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36995305855940297855560709 6936619847988805847917633)
              ·
                refine ⟨5202464885991604385938225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6936619847988805847917633 5202464885991604385938225)
                ·
                  refine ⟨3901848664493703289453669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5202464885991604385938225 3901848664493703289453669)
                  ·
                    refine ⟨731596624592569366772563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3901848664493703289453669 731596624592569366772563)
                    ·
                      rfl

theorem cell22_2137169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2137169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137169 prefixEnd_2137169 := by exact prefixLift 2137169
  have htrace : WordTrace (prefixWord ++ tailWord_2137169) baseStart_2137169 baseEnd_2137169 := by
    simpa [prefixWord, tailWord_2137169, baseEnd_2137169] using wordTrace_append hprefix tailTrace_2137169
  have hstable : (prefixWord ++ tailWord_2137169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137169).length < 2 ^ (prefixWord ++ tailWord_2137169).sum := by decide
  have hdescent : baseEnd_2137169 < baseStart_2137169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137340 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_2137340 : Nat := 118140960795 + 2137340 * 2 ^ 59
def prefixEnd_2137340 : Nat := 4983230072969 + 3 ^ 40 * 2137340 * 2
def baseEnd_2137340 : Nat := 731655161387181920747039

theorem tailTrace_2137340 : CollatzResearch.WordTrace tailWord_2137340 prefixEnd_2137340 731655161387181920747039 := by
  unfold tailWord_2137340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38977597038394841727848737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51970129384526455637131649 38977597038394841727848737)
  ·
    refine ⟨29233197778796131295886553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38977597038394841727848737 29233197778796131295886553)
    ·
      refine ⟨21924898334097098471914915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29233197778796131295886553 21924898334097098471914915)
      ·
        refine ⟨32887347501145647707872373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21924898334097098471914915 32887347501145647707872373)
        ·
          refine ⟨3083188828232404472613035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32887347501145647707872373 3083188828232404472613035)
          ·
            refine ⟨4624783242348606708919553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083188828232404472613035 4624783242348606708919553)
            ·
              refine ⟨3468587431761455031689665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4624783242348606708919553 3468587431761455031689665)
              ·
                refine ⟨2601440573821091273767249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3468587431761455031689665 2601440573821091273767249)
                ·
                  refine ⟨1951080430365818455325437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601440573821091273767249 1951080430365818455325437)
                  ·
                    refine ⟨731655161387181920747039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951080430365818455325437 731655161387181920747039)
                    ·
                      rfl

theorem cell22_2137340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_2137340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137340 prefixEnd_2137340 := by exact prefixLift 2137340
  have htrace : WordTrace (prefixWord ++ tailWord_2137340) baseStart_2137340 baseEnd_2137340 := by
    simpa [prefixWord, tailWord_2137340, baseEnd_2137340] using wordTrace_append hprefix tailTrace_2137340
  have hstable : (prefixWord ++ tailWord_2137340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137340).length < 2 ^ (prefixWord ++ tailWord_2137340).sum := by decide
  have hdescent : baseEnd_2137340 < baseStart_2137340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137342 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2137342 : Nat := 118140960795 + 2137342 * 2 ^ 59
def prefixEnd_2137342 : Nat := 4983230072969 + 3 ^ 40 * 2137342 * 2
def baseEnd_2137342 : Nat := 243885282009351527399011

theorem tailTrace_2137342 : CollatzResearch.WordTrace tailWord_2137342 prefixEnd_2137342 243885282009351527399011 := by
  unfold tailWord_2137342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744408377847804724658785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51970178015188291864846853 9744408377847804724658785)
  ·
    refine ⟨7308306283385853543494089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9744408377847804724658785 7308306283385853543494089)
    ·
      refine ⟨5481229712539390157620567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7308306283385853543494089 5481229712539390157620567)
      ·
        refine ⟨8221844568809085236430851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481229712539390157620567 8221844568809085236430851)
        ·
          refine ⟨12332766853213627854646277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8221844568809085236430851 12332766853213627854646277)
          ·
            refine ⟨2312393784977555222746177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12332766853213627854646277 2312393784977555222746177)
            ·
              refine ⟨1734295338733166417059633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312393784977555222746177 1734295338733166417059633)
              ·
                refine ⟨1300721504049874812794725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1734295338733166417059633 1300721504049874812794725)
                ·
                  refine ⟨243885282009351527399011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300721504049874812794725 243885282009351527399011)
                  ·
                    rfl

theorem cell22_2137342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2137342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137342 prefixEnd_2137342 := by exact prefixLift 2137342
  have htrace : WordTrace (prefixWord ++ tailWord_2137342) baseStart_2137342 baseEnd_2137342 := by
    simpa [prefixWord, tailWord_2137342, baseEnd_2137342] using wordTrace_append hprefix tailTrace_2137342
  have hstable : (prefixWord ++ tailWord_2137342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137342).length < 2 ^ (prefixWord ++ tailWord_2137342).sum := by decide
  have hdescent : baseEnd_2137342 < baseStart_2137342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137349 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_2137349 : Nat := 118140960795 + 2137349 * 2 ^ 59
def prefixEnd_2137349 : Nat := 4983230072969 + 3 ^ 40 * 2137349 * 2
def baseEnd_2137349 : Nat := 731658242271108897272011

theorem tailTrace_2137349 : CollatzResearch.WordTrace tailWord_2137349 prefixEnd_2137349 731658242271108897272011 := by
  unfold tailWord_2137349
  simp only [CollatzResearch.WordTrace]
  refine ⟨77955522333757077992775101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51970348222504718661850067 77955522333757077992775101)
  ·
    refine ⟨29233320875158904247290663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77955522333757077992775101 29233320875158904247290663)
    ·
      refine ⟨43849981312738356370935995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29233320875158904247290663 43849981312738356370935995)
      ·
        refine ⟨65774971969107534556403993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43849981312738356370935995 65774971969107534556403993)
        ·
          refine ⟨49331228976830650917302995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65774971969107534556403993 49331228976830650917302995)
          ·
            refine ⟨73996843465245976375954493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49331228976830650917302995 73996843465245976375954493)
            ·
              refine ⟨27748816299467241140982935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73996843465245976375954493 27748816299467241140982935)
              ·
                refine ⟨41623224449200861711474403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27748816299467241140982935 41623224449200861711474403)
                ·
                  refine ⟨62434836673801292567211605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41623224449200861711474403 62434836673801292567211605)
                  ·
                    refine ⟨731658242271108897272011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62434836673801292567211605 731658242271108897272011)
                    ·
                      rfl

theorem cell22_2137349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_2137349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137349 prefixEnd_2137349 := by exact prefixLift 2137349
  have htrace : WordTrace (prefixWord ++ tailWord_2137349) baseStart_2137349 baseEnd_2137349 := by
    simpa [prefixWord, tailWord_2137349, baseEnd_2137349] using wordTrace_append hprefix tailTrace_2137349
  have hstable : (prefixWord ++ tailWord_2137349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137349).length < 2 ^ (prefixWord ++ tailWord_2137349).sum := by decide
  have hdescent : baseEnd_2137349 < baseStart_2137349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137368 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_2137368 : Nat := 118140960795 + 2137368 * 2 ^ 59
def prefixEnd_2137368 : Nat := 4983230072969 + 3 ^ 40 * 2137368 * 2
def baseEnd_2137368 : Nat := 731664746359399181046953

theorem tailTrace_2137368 : CollatzResearch.WordTrace tailWord_2137368 prefixEnd_2137368 731664746359399181046953 := by
  unfold tailWord_2137368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38978107660344122118858379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51970810213792162825144505 38978107660344122118858379)
  ·
    refine ⟨58467161490516183178287569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38978107660344122118858379 58467161490516183178287569)
    ·
      refine ⟨43850371117887137383715677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58467161490516183178287569 43850371117887137383715677)
      ·
        refine ⟨16443889169207676518893379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43850371117887137383715677 16443889169207676518893379)
        ·
          refine ⟨24665833753811514778340069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16443889169207676518893379 24665833753811514778340069)
          ·
            refine ⟨4624843828839659020938763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24665833753811514778340069 4624843828839659020938763)
            ·
              refine ⟨6937265743259488531408145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624843828839659020938763 6937265743259488531408145)
              ·
                refine ⟨5202949307444616398556109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6937265743259488531408145 5202949307444616398556109)
                ·
                  refine ⟨1951105990291731149458541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5202949307444616398556109 1951105990291731149458541)
                  ·
                    refine ⟨731664746359399181046953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951105990291731149458541 731664746359399181046953)
                    ·
                      rfl

theorem cell22_2137368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_2137368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137368 prefixEnd_2137368 := by exact prefixLift 2137368
  have htrace : WordTrace (prefixWord ++ tailWord_2137368) baseStart_2137368 baseEnd_2137368 := by
    simpa [prefixWord, tailWord_2137368, baseEnd_2137368] using wordTrace_append hprefix tailTrace_2137368
  have hstable : (prefixWord ++ tailWord_2137368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137368).length < 2 ^ (prefixWord ++ tailWord_2137368).sum := by decide
  have hdescent : baseEnd_2137368 < baseStart_2137368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137441 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2137441 : Nat := 118140960795 + 2137441 * 2 ^ 59
def prefixEnd_2137441 : Nat := 4983230072969 + 3 ^ 40 * 2137441 * 2
def baseEnd_2137441 : Nat := 731689735751251323971729

theorem tailTrace_2137441 : CollatzResearch.WordTrace tailWord_2137441 prefixEnd_2137441 731689735751251323971729 := by
  unfold tailWord_2137441
  simp only [CollatzResearch.WordTrace]
  refine ⟨77958877849423777705124177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51972585232949185136749451 77958877849423777705124177)
  ·
    refine ⟨58469158387067833278843133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77958877849423777705124177 58469158387067833278843133)
    ·
      refine ⟨21925934395150437479566175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58469158387067833278843133 21925934395150437479566175)
      ·
        refine ⟨32888901592725656219349263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21925934395150437479566175 32888901592725656219349263)
        ·
          refine ⟨49333352389088484329023895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32888901592725656219349263 49333352389088484329023895)
          ·
            refine ⟨74000028583632726493535843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49333352389088484329023895 74000028583632726493535843)
            ·
              refine ⟨111000042875449089740303765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74000028583632726493535843 111000042875449089740303765)
              ·
                refine ⟨5203127009786676081576739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111000042875449089740303765 5203127009786676081576739)
                ·
                  refine ⟨7804690514680014122365109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5203127009786676081576739 7804690514680014122365109)
                  ·
                    refine ⟨731689735751251323971729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7804690514680014122365109 731689735751251323971729)
                    ·
                      rfl

theorem cell22_2137441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2137441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137441 prefixEnd_2137441 := by exact prefixLift 2137441
  have htrace : WordTrace (prefixWord ++ tailWord_2137441) baseStart_2137441 baseEnd_2137441 := by
    simpa [prefixWord, tailWord_2137441, baseEnd_2137441] using wordTrace_append hprefix tailTrace_2137441
  have hstable : (prefixWord ++ tailWord_2137441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137441).length < 2 ^ (prefixWord ++ tailWord_2137441).sum := by decide
  have hdescent : baseEnd_2137441 < baseStart_2137441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137458 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_2137458 : Nat := 118140960795 + 2137458 * 2 ^ 59
def prefixEnd_2137458 : Nat := 4983230072969 + 3 ^ 40 * 2137458 * 2
def baseEnd_2137458 : Nat := 731695555198668946296677

theorem tailTrace_2137458 : CollatzResearch.WordTrace tailWord_2137458 prefixEnd_2137458 731695555198668946296677 := by
  unfold tailWord_2137458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19489874472590547402123257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51972998593574793072328685 19489874472590547402123257)
  ·
    refine ⟨14617405854442910551592443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19489874472590547402123257 14617405854442910551592443)
    ·
      refine ⟨21926108781664365827388665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14617405854442910551592443 21926108781664365827388665)
      ·
        refine ⟨16444581586248274370541499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21926108781664365827388665 16444581586248274370541499)
        ·
          refine ⟨24666872379372411555812249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16444581586248274370541499 24666872379372411555812249)
          ·
            refine ⟨18500154284529308666859187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24666872379372411555812249 18500154284529308666859187)
            ·
              refine ⟨27750231426793963000288781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18500154284529308666859187 27750231426793963000288781)
              ·
                refine ⟨10406336785047736125108293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27750231426793963000288781 10406336785047736125108293)
                ·
                  refine ⟨1951188147196450523457805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10406336785047736125108293 1951188147196450523457805)
                  ·
                    refine ⟨731695555198668946296677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951188147196450523457805 731695555198668946296677)
                    ·
                      rfl

theorem cell22_2137458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_2137458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137458 prefixEnd_2137458 := by exact prefixLift 2137458
  have htrace : WordTrace (prefixWord ++ tailWord_2137458) baseStart_2137458 baseEnd_2137458 := by
    simpa [prefixWord, tailWord_2137458, baseEnd_2137458] using wordTrace_append hprefix tailTrace_2137458
  have hstable : (prefixWord ++ tailWord_2137458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137458).length < 2 ^ (prefixWord ++ tailWord_2137458).sum := by decide
  have hdescent : baseEnd_2137458 < baseStart_2137458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137475 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 2, 3]
def baseStart_2137475 : Nat := 118140960795 + 2137475 * 2 ^ 59
def prefixEnd_2137475 : Nat := 4983230072969 + 3 ^ 40 * 2137475 * 2
def baseEnd_2137475 : Nat := 731701374646086568621625

theorem tailTrace_2137475 : CollatzResearch.WordTrace tailWord_2137475 prefixEnd_2137475 731701374646086568621625 := by
  unfold tailWord_2137475
  simp only [CollatzResearch.WordTrace]
  refine ⟨77960117931300601511861879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51973411954200401007907919 77960117931300601511861879)
  ·
    refine ⟨116940176896950902267792819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77960117931300601511861879 116940176896950902267792819)
    ·
      refine ⟨175410265345426353401689229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116940176896950902267792819 175410265345426353401689229)
      ·
        refine ⟨65778849504534882525633461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175410265345426353401689229 65778849504534882525633461)
        ·
          refine ⟨6166767141050145236778137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65778849504534882525633461 6166767141050145236778137)
          ·
            refine ⟨4625075355787608927583603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6166767141050145236778137 4625075355787608927583603)
            ·
              refine ⟨6937613033681413391375405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625075355787608927583603 6937613033681413391375405)
              ·
                refine ⟨2601604887630530021765777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6937613033681413391375405 2601604887630530021765777)
                ·
                  refine ⟨1951203665722897516324333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2601604887630530021765777 1951203665722897516324333)
                  ·
                    refine ⟨731701374646086568621625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951203665722897516324333 731701374646086568621625)
                    ·
                      rfl

theorem cell22_2137475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 3].length) (baseStart_2137475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137475 prefixEnd_2137475 := by exact prefixLift 2137475
  have htrace : WordTrace (prefixWord ++ tailWord_2137475) baseStart_2137475 baseEnd_2137475 := by
    simpa [prefixWord, tailWord_2137475, baseEnd_2137475] using wordTrace_append hprefix tailTrace_2137475
  have hstable : (prefixWord ++ tailWord_2137475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137475).length < 2 ^ (prefixWord ++ tailWord_2137475).sum := by decide
  have hdescent : baseEnd_2137475 < baseStart_2137475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137516 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_2137516 : Nat := 118140960795 + 2137516 * 2 ^ 59
def prefixEnd_2137516 : Nat := 4983230072969 + 3 ^ 40 * 2137516 * 2
def baseEnd_2137516 : Nat := 243905136594658709448833

theorem tailTrace_2137516 : CollatzResearch.WordTrace tailWord_2137516 prefixEnd_2137516 243905136594658709448833 := by
  unfold tailWord_2137516
  simp only [CollatzResearch.WordTrace]
  refine ⟨38980806662076032757052201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51974408882768043676069601 38980806662076032757052201)
  ·
    refine ⟨29235604996557024567789151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38980806662076032757052201 29235604996557024567789151)
    ·
      refine ⟨43853407494835536851683727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29235604996557024567789151 43853407494835536851683727)
      ·
        refine ⟨65780111242253305277525591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43853407494835536851683727 65780111242253305277525591)
        ·
          refine ⟨98670166863379957916288387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65780111242253305277525591 98670166863379957916288387)
          ·
            refine ⟨148005250295069936874432581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98670166863379957916288387 148005250295069936874432581)
            ·
              refine ⟨27750984430325613163956109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148005250295069936874432581 27750984430325613163956109)
              ·
                refine ⟨10406619161372104936483541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27750984430325613163956109 10406619161372104936483541)
                ·
                  refine ⟨243905136594658709448833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10406619161372104936483541 243905136594658709448833)
                  ·
                    rfl

theorem cell22_2137516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_2137516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137516 prefixEnd_2137516 := by exact prefixLift 2137516
  have htrace : WordTrace (prefixWord ++ tailWord_2137516) baseStart_2137516 baseEnd_2137516 := by
    simpa [prefixWord, tailWord_2137516, baseEnd_2137516] using wordTrace_append hprefix tailTrace_2137516
  have hstable : (prefixWord ++ tailWord_2137516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137516).length < 2 ^ (prefixWord ++ tailWord_2137516).sum := by decide
  have hdescent : baseEnd_2137516 < baseStart_2137516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137533 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2137533 : Nat := 118140960795 + 2137533 * 2 ^ 59
def prefixEnd_2137533 : Nat := 4983230072969 + 3 ^ 40 * 2137533 * 2
def baseEnd_2137533 : Nat := 243907076410464583557149

theorem tailTrace_2137533 : CollatzResearch.WordTrace tailWord_2137533 prefixEnd_2137533 243907076410464583557149 := by
  unfold tailWord_2137533
  simp only [CollatzResearch.WordTrace]
  refine ⟨77962233365090477417473253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51974822243393651611648835 77962233365090477417473253)
  ·
    refine ⟨14617918755954464515776235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77962233365090477417473253 14617918755954464515776235)
    ·
      refine ⟨21926878133931696773664353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14617918755954464515776235 21926878133931696773664353)
      ·
        refine ⟨16445158600448772580248265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21926878133931696773664353 16445158600448772580248265)
        ·
          refine ⟨12333868950336579435186199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16445158600448772580248265 12333868950336579435186199)
          ·
            refine ⟨18500803425504869152779299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12333868950336579435186199 18500803425504869152779299)
            ·
              refine ⟨27751205138257303729168949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18500803425504869152779299 27751205138257303729168949)
              ·
                refine ⟨2601675481711622224609589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27751205138257303729168949 2601675481711622224609589)
                ·
                  refine ⟨243907076410464583557149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2601675481711622224609589 243907076410464583557149)
                  ·
                    rfl

theorem cell22_2137533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2137533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137533 prefixEnd_2137533 := by exact prefixLift 2137533
  have htrace : WordTrace (prefixWord ++ tailWord_2137533) baseStart_2137533 baseEnd_2137533 := by
    simpa [prefixWord, tailWord_2137533, baseEnd_2137533] using wordTrace_append hprefix tailTrace_2137533
  have hstable : (prefixWord ++ tailWord_2137533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137533).length < 2 ^ (prefixWord ++ tailWord_2137533).sum := by decide
  have hdescent : baseEnd_2137533 < baseStart_2137533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137608 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2137608 : Nat := 118140960795 + 2137608 * 2 ^ 59
def prefixEnd_2137608 : Nat := 4983230072969 + 3 ^ 40 * 2137608 * 2
def baseEnd_2137608 : Nat := 731746903264118555046217

theorem tailTrace_2137608 : CollatzResearch.WordTrace tailWord_2137608 prefixEnd_2137608 731746903264118555046217 := by
  unfold tailWord_2137608
  simp only [CollatzResearch.WordTrace]
  refine ⟨38982484419909382613226739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51976645893212510150968985 38982484419909382613226739)
  ·
    refine ⟨58473726629864073919840109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38982484419909382613226739 58473726629864073919840109)
    ·
      refine ⟨21927647486199027719940041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58473726629864073919840109 21927647486199027719940041)
      ·
        refine ⟨16445735614649270789955031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21927647486199027719940041 16445735614649270789955031)
        ·
          refine ⟨24668603421973906184932547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16445735614649270789955031 24668603421973906184932547)
          ·
            refine ⟨37002905132960859277398821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24668603421973906184932547 37002905132960859277398821)
            ·
              refine ⟨6938044712430161114512279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37002905132960859277398821 6938044712430161114512279)
              ·
                refine ⟨10407067068645241671768419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6938044712430161114512279 10407067068645241671768419)
                ·
                  refine ⟨15610600602967862507652629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10407067068645241671768419 15610600602967862507652629)
                  ·
                    refine ⟨731746903264118555046217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15610600602967862507652629 731746903264118555046217)
                    ·
                      rfl

theorem cell22_2137608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2137608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137608 prefixEnd_2137608 := by exact prefixLift 2137608
  have htrace : WordTrace (prefixWord ++ tailWord_2137608) baseStart_2137608 baseEnd_2137608 := by
    simpa [prefixWord, tailWord_2137608, baseEnd_2137608] using wordTrace_append hprefix tailTrace_2137608
  have hstable : (prefixWord ++ tailWord_2137608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137608).length < 2 ^ (prefixWord ++ tailWord_2137608).sum := by decide
  have hdescent : baseEnd_2137608 < baseStart_2137608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137610 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_2137610 : Nat := 118140960795 + 2137610 * 2 ^ 59
def prefixEnd_2137610 : Nat := 4983230072969 + 3 ^ 40 * 2137610 * 2
def baseEnd_2137610 : Nat := 731747587904991216496211

theorem tailTrace_2137610 : CollatzResearch.WordTrace tailWord_2137610 prefixEnd_2137610 731747587904991216496211 := by
  unfold tailWord_2137610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19491260446452879892006571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51976694523874346378684189 19491260446452879892006571)
  ·
    refine ⟨29236890669679319838009857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19491260446452879892006571 29236890669679319838009857)
    ·
      refine ⟨21927668002259489878507393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29236890669679319838009857 21927668002259489878507393)
      ·
        refine ⟨16445751001694617408880545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21927668002259489878507393 16445751001694617408880545)
        ·
          refine ⟨12334313251270963056660409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16445751001694617408880545 12334313251270963056660409)
          ·
            refine ⟨9250734938453222292495307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12334313251270963056660409 9250734938453222292495307)
            ·
              refine ⟨13876102407679833438742961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9250734938453222292495307 13876102407679833438742961)
              ·
                refine ⟨10407076805759875079057221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13876102407679833438742961 10407076805759875079057221)
                ·
                  refine ⟨1951326901079976577323229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10407076805759875079057221 1951326901079976577323229)
                  ·
                    refine ⟨731747587904991216496211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951326901079976577323229 731747587904991216496211)
                    ·
                      rfl

theorem cell22_2137610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_2137610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137610 prefixEnd_2137610 := by exact prefixLift 2137610
  have htrace : WordTrace (prefixWord ++ tailWord_2137610) baseStart_2137610 baseEnd_2137610 := by
    simpa [prefixWord, tailWord_2137610, baseEnd_2137610] using wordTrace_append hprefix tailTrace_2137610
  have hstable : (prefixWord ++ tailWord_2137610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137610).length < 2 ^ (prefixWord ++ tailWord_2137610).sum := by decide
  have hdescent : baseEnd_2137610 < baseStart_2137610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137700 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2137700 : Nat := 118140960795 + 2137700 * 2 ^ 59
def prefixEnd_2137700 : Nat := 4983230072969 + 3 ^ 40 * 2137700 * 2
def baseEnd_2137700 : Nat := 731778396744260981745935

theorem tailTrace_2137700 : CollatzResearch.WordTrace tailWord_2137700 prefixEnd_2137700 731778396744260981745935 := by
  unfold tailWord_2137700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38984162177742732469401277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51978882903656976625868369 38984162177742732469401277)
  ·
    refine ⟨14619060816653524676025479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38984162177742732469401277 14619060816653524676025479)
    ·
      refine ⟨21928591224980287014038219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14619060816653524676025479 21928591224980287014038219)
      ·
        refine ⟨32892886837470430521057329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21928591224980287014038219 32892886837470430521057329)
        ·
          refine ⟨24669665128102822890792997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32892886837470430521057329 24669665128102822890792997)
          ·
            refine ⟨4625562211519279292023687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24669665128102822890792997 4625562211519279292023687)
            ·
              refine ⟨6938343317278918938035531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625562211519279292023687 6938343317278918938035531)
              ·
                refine ⟨10407514975918378407053297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6938343317278918938035531 10407514975918378407053297)
                ·
                  refine ⟨7805636231938783805289973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10407514975918378407053297 7805636231938783805289973)
                  ·
                    refine ⟨731778396744260981745935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7805636231938783805289973 731778396744260981745935)
                    ·
                      rfl

theorem cell22_2137700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2137700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137700 prefixEnd_2137700 := by exact prefixLift 2137700
  have htrace : WordTrace (prefixWord ++ tailWord_2137700) baseStart_2137700 baseEnd_2137700 := by
    simpa [prefixWord, tailWord_2137700, baseEnd_2137700] using wordTrace_append hprefix tailTrace_2137700
  have hstable : (prefixWord ++ tailWord_2137700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137700).length < 2 ^ (prefixWord ++ tailWord_2137700).sum := by decide
  have hdescent : baseEnd_2137700 < baseStart_2137700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137736 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_2137736 : Nat := 118140960795 + 2137736 * 2 ^ 59
def prefixEnd_2137736 : Nat := 4983230072969 + 3 ^ 40 * 2137736 * 2
def baseEnd_2137736 : Nat := 243930240093322962615275

theorem tailTrace_2137736 : CollatzResearch.WordTrace tailWord_2137736 prefixEnd_2137736 243930240093322962615275 := by
  unfold tailWord_2137736
  simp only [CollatzResearch.WordTrace]
  refine ⟨38984818691677521543556531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51979758255570028724742041 38984818691677521543556531)
  ·
    refine ⟨58477228037516282315334797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38984818691677521543556531 58477228037516282315334797)
    ·
      refine ⟨21928960514068605868250549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58477228037516282315334797 21928960514068605868250549)
      ·
        refine ⟨2055840048193931800148489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21928960514068605868250549 2055840048193931800148489)
        ·
          refine ⟨1541880036145448850111367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2055840048193931800148489 1541880036145448850111367)
          ·
            refine ⟨2312820054218173275167051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541880036145448850111367 2312820054218173275167051)
            ·
              refine ⟨3469230081327259912750577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312820054218173275167051 3469230081327259912750577)
              ·
                refine ⟨2601922560995444934562933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3469230081327259912750577 2601922560995444934562933)
                ·
                  refine ⟨243930240093322962615275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2601922560995444934562933 243930240093322962615275)
                  ·
                    rfl

theorem cell22_2137736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_2137736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137736 prefixEnd_2137736 := by exact prefixLift 2137736
  have htrace : WordTrace (prefixWord ++ tailWord_2137736) baseStart_2137736 baseEnd_2137736 := by
    simpa [prefixWord, tailWord_2137736, baseEnd_2137736] using wordTrace_append hprefix tailTrace_2137736
  have hstable : (prefixWord ++ tailWord_2137736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137736).length < 2 ^ (prefixWord ++ tailWord_2137736).sum := by decide
  have hdescent : baseEnd_2137736 < baseStart_2137736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137743 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_2137743 : Nat := 118140960795 + 2137743 * 2 ^ 59
def prefixEnd_2137743 : Nat := 4983230072969 + 3 ^ 40 * 2137743 * 2
def baseEnd_2137743 : Nat := 731793116523023202920803

theorem tailTrace_2137743 : CollatzResearch.WordTrace tailWord_2137743 prefixEnd_2137743 731793116523023202920803 := by
  unfold tailWord_2137743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77969892694329683282617883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51979928462886455521745255 77969892694329683282617883)
  ·
    refine ⟨116954839041494524923926825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77969892694329683282617883 116954839041494524923926825)
    ·
      refine ⟨87716129281120893692945119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116954839041494524923926825 87716129281120893692945119)
      ·
        refine ⟨131574193921681340539417679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87716129281120893692945119 131574193921681340539417679)
        ·
          refine ⟨197361290882522010809126519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131574193921681340539417679 197361290882522010809126519)
          ·
            refine ⟨296041936323783016213689779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197361290882522010809126519 296041936323783016213689779)
            ·
              refine ⟨444062904485674524320534669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296041936323783016213689779 444062904485674524320534669)
              ·
                refine ⟨166523589182127946620200501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 444062904485674524320534669 166523589182127946620200501)
                ·
                  refine ⟨15611586485824494995643797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166523589182127946620200501 15611586485824494995643797)
                  ·
                    refine ⟨731793116523023202920803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15611586485824494995643797 731793116523023202920803)
                    ·
                      rfl

theorem cell22_2137743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_2137743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137743 prefixEnd_2137743 := by exact prefixLift 2137743
  have htrace : WordTrace (prefixWord ++ tailWord_2137743) baseStart_2137743 baseEnd_2137743 := by
    simpa [prefixWord, tailWord_2137743, baseEnd_2137743] using wordTrace_append hprefix tailTrace_2137743
  have hstable : (prefixWord ++ tailWord_2137743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137743).length < 2 ^ (prefixWord ++ tailWord_2137743).sum := by decide
  have hdescent : baseEnd_2137743 < baseStart_2137743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137760 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_2137760 : Nat := 118140960795 + 2137760 * 2 ^ 59
def prefixEnd_2137760 : Nat := 4983230072969 + 3 ^ 40 * 2137760 * 2
def baseEnd_2137760 : Nat := 731798935970440825245751

theorem tailTrace_2137760 : CollatzResearch.WordTrace tailWord_2137760 prefixEnd_2137760 731798935970440825245751 := by
  unfold tailWord_2137760
  simp only [CollatzResearch.WordTrace]
  refine ⟨38985256367634047592993367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51980341823512063457324489 38985256367634047592993367)
  ·
    refine ⟨58477884551451071389490051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38985256367634047592993367 58477884551451071389490051)
    ·
      refine ⟨87716826827176607084235077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58477884551451071389490051 87716826827176607084235077)
      ·
        refine ⟨16446905030095613828294077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87716826827176607084235077 16446905030095613828294077)
        ·
          refine ⟨6167589386285855185610279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16446905030095613828294077 6167589386285855185610279)
          ·
            refine ⟨9251384079428782778415419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6167589386285855185610279 9251384079428782778415419)
            ·
              refine ⟨13877076119143174167623129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9251384079428782778415419 13877076119143174167623129)
              ·
                refine ⟨10407807089357380625717347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13877076119143174167623129 10407807089357380625717347)
                ·
                  refine ⟨15611710634036070938576021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10407807089357380625717347 15611710634036070938576021)
                  ·
                    refine ⟨731798935970440825245751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15611710634036070938576021 731798935970440825245751)
                    ·
                      rfl

theorem cell22_2137760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_2137760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137760 prefixEnd_2137760 := by exact prefixLift 2137760
  have htrace : WordTrace (prefixWord ++ tailWord_2137760) baseStart_2137760 baseEnd_2137760 := by
    simpa [prefixWord, tailWord_2137760, baseEnd_2137760] using wordTrace_append hprefix tailTrace_2137760
  have hstable : (prefixWord ++ tailWord_2137760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137760).length < 2 ^ (prefixWord ++ tailWord_2137760).sum := by decide
  have hdescent : baseEnd_2137760 < baseStart_2137760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137781 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 4]
def baseStart_2137781 : Nat := 118140960795 + 2137781 * 2 ^ 59
def prefixEnd_2137781 : Nat := 4983230072969 + 3 ^ 40 * 2137781 * 2
def baseEnd_2137781 : Nat := 243935374899867923490229

theorem tailTrace_2137781 : CollatzResearch.WordTrace tailWord_2137781 prefixEnd_2137781 243935374899867923490229 := by
  unfold tailWord_2137781
  simp only [CollatzResearch.WordTrace]
  refine ⟨77971278668192015772501197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51980852445461343848334131 77971278668192015772501197)
  ·
    refine ⟨29239229500572005914687949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77971278668192015772501197 29239229500572005914687949)
    ·
      refine ⟨10964711062714502218007981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29239229500572005914687949 10964711062714502218007981)
      ·
        refine ⟨4111766648517938331752993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10964711062714502218007981 4111766648517938331752993)
        ·
          refine ⟨3083824986388453748814745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4111766648517938331752993 3083824986388453748814745)
          ·
            refine ⟨2312868739791340311611059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3083824986388453748814745 2312868739791340311611059)
            ·
              refine ⟨3469303109687010467416589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312868739791340311611059 3469303109687010467416589)
              ·
                refine ⟨1300988666132628925281221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3469303109687010467416589 1300988666132628925281221)
                ·
                  refine ⟨243935374899867923490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300988666132628925281221 243935374899867923490229)
                  ·
                    rfl

theorem cell22_2137781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_2137781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137781 prefixEnd_2137781 := by exact prefixLift 2137781
  have htrace : WordTrace (prefixWord ++ tailWord_2137781) baseStart_2137781 baseEnd_2137781 := by
    simpa [prefixWord, tailWord_2137781, baseEnd_2137781] using wordTrace_append hprefix tailTrace_2137781
  have hstable : (prefixWord ++ tailWord_2137781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137781).length < 2 ^ (prefixWord ++ tailWord_2137781).sum := by decide
  have hdescent : baseEnd_2137781 < baseStart_2137781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137865 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 6]
def baseStart_2137865 : Nat := 118140960795 + 2137865 * 2 ^ 59
def prefixEnd_2137865 : Nat := 4983230072969 + 3 ^ 40 * 2137865 * 2
def baseEnd_2137865 : Nat := 243944959872085183790143

theorem tailTrace_2137865 : CollatzResearch.WordTrace tailWord_2137865 prefixEnd_2137865 243944959872085183790143 := by
  unfold tailWord_2137865
  simp only [CollatzResearch.WordTrace]
  refine ⟨77974342399887698118559049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51982894933258465412372699 77974342399887698118559049)
  ·
    refine ⟨58480756799915773588919287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77974342399887698118559049 58480756799915773588919287)
    ·
      refine ⟨87721135199873660383378931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58480756799915773588919287 87721135199873660383378931)
      ·
        refine ⟨131581702799810490575068397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87721135199873660383378931 131581702799810490575068397)
        ·
          refine ⟨49343138549928933965650649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131581702799810490575068397 49343138549928933965650649)
          ·
            refine ⟨37007353912446700474237987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49343138549928933965650649 37007353912446700474237987)
            ·
              refine ⟨55511030868670050711356981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37007353912446700474237987 55511030868670050711356981)
              ·
                refine ⟨5204159143937817254189717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55511030868670050711356981 5204159143937817254189717)
                ·
                  refine ⟨243944959872085183790143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5204159143937817254189717 243944959872085183790143)
                  ·
                    rfl

theorem cell22_2137865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_2137865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137865 prefixEnd_2137865 := by exact prefixLift 2137865
  have htrace : WordTrace (prefixWord ++ tailWord_2137865) baseStart_2137865 baseEnd_2137865 := by
    simpa [prefixWord, tailWord_2137865, baseEnd_2137865] using wordTrace_append hprefix tailTrace_2137865
  have hstable : (prefixWord ++ tailWord_2137865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137865).length < 2 ^ (prefixWord ++ tailWord_2137865).sum := by decide
  have hdescent : baseEnd_2137865 < baseStart_2137865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137882 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_2137882 : Nat := 118140960795 + 2137882 * 2 ^ 59
def prefixEnd_2137882 : Nat := 4983230072969 + 3 ^ 40 * 2137882 * 2
def baseEnd_2137882 : Nat := 243946899687891057898459

theorem tailTrace_2137882 : CollatzResearch.WordTrace tailWord_2137882 prefixEnd_2137882 243946899687891057898459 := by
  unfold tailWord_2137882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19493740610206527505481975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51983308293884073347951933 19493740610206527505481975)
  ·
    refine ⟨29240610915309791258222963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19493740610206527505481975 29240610915309791258222963)
    ·
      refine ⟨43860916372964686887334445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29240610915309791258222963 43860916372964686887334445)
      ·
        refine ⟨16447843639861757582750417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43860916372964686887334445 16447843639861757582750417)
        ·
          refine ⟨12335882729896318187062813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16447843639861757582750417 12335882729896318187062813)
          ·
            refine ⟨4625956023711119320148555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12335882729896318187062813 4625956023711119320148555)
            ·
              refine ⟨6938934035566678980222833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625956023711119320148555 6938934035566678980222833)
              ·
                refine ⟨5204200526675009235167125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6938934035566678980222833 5204200526675009235167125)
                ·
                  refine ⟨243946899687891057898459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5204200526675009235167125 243946899687891057898459)
                  ·
                    rfl

theorem cell22_2137882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_2137882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137882 prefixEnd_2137882 := by exact prefixLift 2137882
  have htrace : WordTrace (prefixWord ++ tailWord_2137882) baseStart_2137882 baseEnd_2137882 := by
    simpa [prefixWord, tailWord_2137882, baseEnd_2137882] using wordTrace_append hprefix tailTrace_2137882
  have hstable : (prefixWord ++ tailWord_2137882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137882).length < 2 ^ (prefixWord ++ tailWord_2137882).sum := by decide
  have hdescent : baseEnd_2137882 < baseStart_2137882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2137914 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_2137914 : Nat := 118140960795 + 2137914 * 2 ^ 59
def prefixEnd_2137914 : Nat := 4983230072969 + 3 ^ 40 * 2137914 * 2
def baseEnd_2137914 : Nat := 731851653317635756895279

theorem tailTrace_2137914 : CollatzResearch.WordTrace tailWord_2137914 prefixEnd_2137914 731851653317635756895279 := by
  unfold tailWord_2137914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19494032394177544871773199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51984086384473452991395197 19494032394177544871773199)
  ·
    refine ⟨29241048591266317307659799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19494032394177544871773199 29241048591266317307659799)
    ·
      refine ⟨43861572886899475961489699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29241048591266317307659799 43861572886899475961489699)
      ·
        refine ⟨65792359330349213942234549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43861572886899475961489699 65792359330349213942234549)
        ·
          refine ⟨6168033687220238807084489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65792359330349213942234549 6168033687220238807084489)
          ·
            refine ⟨4626025265415179105313367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6168033687220238807084489 4626025265415179105313367)
            ·
              refine ⟨6939037898122768657970051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626025265415179105313367 6939037898122768657970051)
              ·
                refine ⟨10408556847184152986955077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6939037898122768657970051 10408556847184152986955077)
                ·
                  refine ⟨1951604408847028685054077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10408556847184152986955077 1951604408847028685054077)
                  ·
                    refine ⟨731851653317635756895279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951604408847028685054077 731851653317635756895279)
                    ·
                      rfl

theorem cell22_2137914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_2137914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2137914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2137914 prefixEnd_2137914 := by exact prefixLift 2137914
  have htrace : WordTrace (prefixWord ++ tailWord_2137914) baseStart_2137914 baseEnd_2137914 := by
    simpa [prefixWord, tailWord_2137914, baseEnd_2137914] using wordTrace_append hprefix tailTrace_2137914
  have hstable : (prefixWord ++ tailWord_2137914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2137914).length < 2 ^ (prefixWord ++ tailWord_2137914).sum := by decide
  have hdescent : baseEnd_2137914 < baseStart_2137914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2137914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138047 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_2138047 : Nat := 118140960795 + 2138047 * 2 ^ 59
def prefixEnd_2138047 : Nat := 4983230072969 + 3 ^ 40 * 2138047 * 2
def baseEnd_2138047 : Nat := 731897181935667743319871

theorem tailTrace_2138047 : CollatzResearch.WordTrace tailWord_2138047 prefixEnd_2138047 731897181935667743319871 := by
  unfold tailWord_2138047
  simp only [CollatzResearch.WordTrace]
  refine ⟨77980980485228343201684395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51987320323485562134456263 77980980485228343201684395)
  ·
    refine ⟨116971470727842514802526593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77980980485228343201684395 116971470727842514802526593)
    ·
      refine ⟨87728603045881886101894945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116971470727842514802526593 87728603045881886101894945)
      ·
        refine ⟨65796452284411414576421209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87728603045881886101894945 65796452284411414576421209)
        ·
          refine ⟨49347339213308560932315907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65796452284411414576421209 49347339213308560932315907)
          ·
            refine ⟨74021008819962841398473861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49347339213308560932315907 74021008819962841398473861)
            ·
              refine ⟨13878939153743032762213849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74021008819962841398473861 13878939153743032762213849)
              ·
                refine ⟨10409204365307274571660387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13878939153743032762213849 10409204365307274571660387)
                ·
                  refine ⟨15613806547960911857490581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10409204365307274571660387 15613806547960911857490581)
                  ·
                    refine ⟨731897181935667743319871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15613806547960911857490581 731897181935667743319871)
                    ·
                      rfl

theorem cell22_2138047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_2138047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138047 prefixEnd_2138047 := by exact prefixLift 2138047
  have htrace : WordTrace (prefixWord ++ tailWord_2138047) baseStart_2138047 baseEnd_2138047 := by
    simpa [prefixWord, tailWord_2138047, baseEnd_2138047] using wordTrace_append hprefix tailTrace_2138047
  have hstable : (prefixWord ++ tailWord_2138047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138047).length < 2 ^ (prefixWord ++ tailWord_2138047).sum := by decide
  have hdescent : baseEnd_2138047 < baseStart_2138047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138064 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_2138064 : Nat := 118140960795 + 2138064 * 2 ^ 59
def prefixEnd_2138064 : Nat := 4983230072969 + 3 ^ 40 * 2138064 * 2
def baseEnd_2138064 : Nat := 731903001383085365644819

theorem tailTrace_2138064 : CollatzResearch.WordTrace tailWord_2138064 prefixEnd_2138064 731903001383085365644819 := by
  unfold tailWord_2138064
  simp only [CollatzResearch.WordTrace]
  refine ⟨38990800263083377552526623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51987733684111170070035497 38990800263083377552526623)
  ·
    refine ⟨58486200394625066328789935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38990800263083377552526623 58486200394625066328789935)
    ·
      refine ⟨87729300591937599493184903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58486200394625066328789935 87729300591937599493184903)
      ·
        refine ⟨131593950887906399239777355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87729300591937599493184903 131593950887906399239777355)
        ·
          refine ⟨197390926331859598859666033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131593950887906399239777355 197390926331859598859666033)
          ·
            refine ⟨148043194748894699144749525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197390926331859598859666033 148043194748894699144749525)
            ·
              refine ⟨3469762376927219511205067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148043194748894699144749525 3469762376927219511205067)
              ·
                refine ⟨5204643565390829266807601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469762376927219511205067 5204643565390829266807601)
                ·
                  refine ⟨3903482674043121950105701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5204643565390829266807601 3903482674043121950105701)
                  ·
                    refine ⟨731903001383085365644819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3903482674043121950105701 731903001383085365644819)
                    ·
                      rfl

theorem cell22_2138064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_2138064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138064 prefixEnd_2138064 := by exact prefixLift 2138064
  have htrace : WordTrace (prefixWord ++ tailWord_2138064) baseStart_2138064 baseEnd_2138064 := by
    simpa [prefixWord, tailWord_2138064, baseEnd_2138064] using wordTrace_append hprefix tailTrace_2138064
  have hstable : (prefixWord ++ tailWord_2138064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138064).length < 2 ^ (prefixWord ++ tailWord_2138064).sum := by decide
  have hdescent : baseEnd_2138064 < baseStart_2138064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138083 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 2, 3]
def baseStart_2138083 : Nat := 118140960795 + 2138083 * 2 ^ 59
def prefixEnd_2138083 : Nat := 4983230072969 + 3 ^ 40 * 2138083 * 2
def baseEnd_2138083 : Nat := 731909505471375649419761

theorem tailTrace_2138083 : CollatzResearch.WordTrace tailWord_2138083 prefixEnd_2138083 731909505471375649419761 := by
  unfold tailWord_2138083
  simp only [CollatzResearch.WordTrace]
  refine ⟨77982293513097921349994903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51988195675398614233329935 77982293513097921349994903)
  ·
    refine ⟨116973440269646882024992355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77982293513097921349994903 116973440269646882024992355)
    ·
      refine ⟨175460160404470323037488533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116973440269646882024992355 175460160404470323037488533)
      ·
        refine ⟨8224695018959546392382275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 175460160404470323037488533 8224695018959546392382275)
        ·
          refine ⟨12337042528439319588573413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8224695018959546392382275 12337042528439319588573413)
          ·
            refine ⟨2313195474082372422857515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12337042528439319588573413 2313195474082372422857515)
            ·
              refine ⟨3469793211123558634286273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313195474082372422857515 3469793211123558634286273)
              ·
                refine ⟨2602344908342668975714705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3469793211123558634286273 2602344908342668975714705)
                ·
                  refine ⟨1951758681257001731786029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2602344908342668975714705 1951758681257001731786029)
                  ·
                    refine ⟨731909505471375649419761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951758681257001731786029 731909505471375649419761)
                    ·
                      rfl

theorem cell22_2138083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3].length) (baseStart_2138083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138083 prefixEnd_2138083 := by exact prefixLift 2138083
  have htrace : WordTrace (prefixWord ++ tailWord_2138083) baseStart_2138083 baseEnd_2138083 := by
    simpa [prefixWord, tailWord_2138083, baseEnd_2138083] using wordTrace_append hprefix tailTrace_2138083
  have hstable : (prefixWord ++ tailWord_2138083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138083).length < 2 ^ (prefixWord ++ tailWord_2138083).sum := by decide
  have hdescent : baseEnd_2138083 < baseStart_2138083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138092 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_2138092 : Nat := 118140960795 + 2138092 * 2 ^ 59
def prefixEnd_2138092 : Nat := 4983230072969 + 3 ^ 40 * 2138092 * 2
def baseEnd_2138092 : Nat := 731912586355302625944733

theorem tailTrace_2138092 : CollatzResearch.WordTrace tailWord_2138092 prefixEnd_2138092 731912586355302625944733 := by
  unfold tailWord_2138092
  simp only [CollatzResearch.WordTrace]
  refine ⟨38991310885032657943536265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51988414513376877258048353 38991310885032657943536265)
  ·
    refine ⟨29243483163774493457652199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38991310885032657943536265 29243483163774493457652199)
    ·
      refine ⟨43865224745661740186478299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29243483163774493457652199 43865224745661740186478299)
      ·
        refine ⟨65797837118492610279717449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43865224745661740186478299 65797837118492610279717449)
        ·
          refine ⟨49348377838869457709788087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65797837118492610279717449 49348377838869457709788087)
          ·
            refine ⟨74022566758304186564682131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49348377838869457709788087 74022566758304186564682131)
            ·
              refine ⟨111033850137456279847023197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74022566758304186564682131 111033850137456279847023197)
              ·
                refine ⟨41637693801546104942633699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111033850137456279847023197 41637693801546104942633699)
                ·
                  refine ⟨62456540702319157413950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41637693801546104942633699 62456540702319157413950549)
                  ·
                    refine ⟨731912586355302625944733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62456540702319157413950549 731912586355302625944733)
                    ·
                      rfl

theorem cell22_2138092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_2138092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138092 prefixEnd_2138092 := by exact prefixLift 2138092
  have htrace : WordTrace (prefixWord ++ tailWord_2138092) baseStart_2138092 baseEnd_2138092 := by
    simpa [prefixWord, tailWord_2138092, baseEnd_2138092] using wordTrace_append hprefix tailTrace_2138092
  have hstable : (prefixWord ++ tailWord_2138092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138092).length < 2 ^ (prefixWord ++ tailWord_2138092).sum := by decide
  have hdescent : baseEnd_2138092 < baseStart_2138092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138145 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2138145 : Nat := 118140960795 + 2138145 * 2 ^ 59
def prefixEnd_2138145 : Nat := 4983230072969 + 3 ^ 40 * 2138145 * 2
def baseEnd_2138145 : Nat := 731930729338428154369571

theorem tailTrace_2138145 : CollatzResearch.WordTrace tailWord_2138145 prefixEnd_2138145 731930729338428154369571 := by
  unfold tailWord_2138145
  simp only [CollatzResearch.WordTrace]
  refine ⟨77984554838873305938751889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51989703225915537292501259 77984554838873305938751889)
  ·
    refine ⟨58488416129154979454063917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77984554838873305938751889 58488416129154979454063917)
    ·
      refine ⟨21933156048433117295273969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58488416129154979454063917 21933156048433117295273969)
      ·
        refine ⟨16449867036324837971455477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21933156048433117295273969 16449867036324837971455477)
        ·
          refine ⟨1542175034655453559823951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16449867036324837971455477 1542175034655453559823951)
          ·
            refine ⟨2313262551983180339735927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542175034655453559823951 2313262551983180339735927)
            ·
              refine ⟨3469893827974770509603891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313262551983180339735927 3469893827974770509603891)
              ·
                refine ⟨5204840741962155764405837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3469893827974770509603891 5204840741962155764405837)
                ·
                  refine ⟨1951815278235808411652189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5204840741962155764405837 1951815278235808411652189)
                  ·
                    refine ⟨731930729338428154369571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1951815278235808411652189 731930729338428154369571)
                    ·
                      rfl

theorem cell22_2138145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2138145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138145 prefixEnd_2138145 := by exact prefixLift 2138145
  have htrace : WordTrace (prefixWord ++ tailWord_2138145) baseStart_2138145 baseEnd_2138145 := by
    simpa [prefixWord, tailWord_2138145, baseEnd_2138145] using wordTrace_append hprefix tailTrace_2138145
  have hstable : (prefixWord ++ tailWord_2138145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138145).length < 2 ^ (prefixWord ++ tailWord_2138145).sum := by decide
  have hdescent : baseEnd_2138145 < baseStart_2138145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138158 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_2138158 : Nat := 118140960795 + 2138158 * 2 ^ 59
def prefixEnd_2138158 : Nat := 4983230072969 + 3 ^ 40 * 2138158 * 2
def baseEnd_2138158 : Nat := 243978393168033484598177

theorem tailTrace_2138158 : CollatzResearch.WordTrace tailWord_2138158 prefixEnd_2138158 243978393168033484598177 := by
  unfold tailWord_2138158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748128623478276144871891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51990019325217472772650085 9748128623478276144871891)
  ·
    refine ⟨14622192935217414217307837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9748128623478276144871891 14622192935217414217307837)
    ·
      refine ⟨5483322350706530331490439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14622192935217414217307837 5483322350706530331490439)
      ·
        refine ⟨8224983526059795497235659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5483322350706530331490439 8224983526059795497235659)
        ·
          refine ⟨12337475289089693245853489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8224983526059795497235659 12337475289089693245853489)
          ·
            refine ⟨9253106466817269934390117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12337475289089693245853489 9253106466817269934390117)
            ·
              refine ⟨1734957462528238112698147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9253106466817269934390117 1734957462528238112698147)
              ·
                refine ⟨2602436193792357169047221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734957462528238112698147 2602436193792357169047221)
                ·
                  refine ⟨243978393168033484598177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2602436193792357169047221 243978393168033484598177)
                  ·
                    rfl

theorem cell22_2138158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_2138158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138158 prefixEnd_2138158 := by exact prefixLift 2138158
  have htrace : WordTrace (prefixWord ++ tailWord_2138158) baseStart_2138158 baseEnd_2138158 := by
    simpa [prefixWord, tailWord_2138158, baseEnd_2138158] using wordTrace_append hprefix tailTrace_2138158
  have hstable : (prefixWord ++ tailWord_2138158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138158).length < 2 ^ (prefixWord ++ tailWord_2138158).sum := by decide
  have hdescent : baseEnd_2138158 < baseStart_2138158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138186 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_2138186 : Nat := 118140960795 + 2138186 * 2 ^ 59
def prefixEnd_2138186 : Nat := 4983230072969 + 3 ^ 40 * 2138186 * 2
def baseEnd_2138186 : Nat := 243981588158772571364815

theorem tailTrace_2138186 : CollatzResearch.WordTrace tailWord_2138186 prefixEnd_2138186 243981588158772571364815 := by
  unfold tailWord_2138186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496512557931192485248603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51990700154483179960662941 19496512557931192485248603)
  ·
    refine ⟨29244768836896788727872905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19496512557931192485248603 29244768836896788727872905)
    ·
      refine ⟨21933576627672591545904679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29244768836896788727872905 21933576627672591545904679)
      ·
        refine ⟨32900364941508887318857019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21933576627672591545904679 32900364941508887318857019)
        ·
          refine ⟨49350547412263330978285529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32900364941508887318857019 49350547412263330978285529)
          ·
            refine ⟨37012910559197498233714147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49350547412263330978285529 37012910559197498233714147)
            ·
              refine ⟨55519365838796247350571221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37012910559197498233714147 55519365838796247350571221)
              ·
                refine ⟨1301235136846787047279013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55519365838796247350571221 1301235136846787047279013)
                ·
                  refine ⟨243981588158772571364815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301235136846787047279013 243981588158772571364815)
                  ·
                    rfl

theorem cell22_2138186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_2138186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138186 prefixEnd_2138186 := by exact prefixLift 2138186
  have htrace : WordTrace (prefixWord ++ tailWord_2138186) baseStart_2138186 baseEnd_2138186 := by
    simpa [prefixWord, tailWord_2138186, baseEnd_2138186] using wordTrace_append hprefix tailTrace_2138186
  have hstable : (prefixWord ++ tailWord_2138186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138186).length < 2 ^ (prefixWord ++ tailWord_2138186).sum := by decide
  have hdescent : baseEnd_2138186 < baseStart_2138186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138218 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2138218 : Nat := 118140960795 + 2138218 * 2 ^ 59
def prefixEnd_2138218 : Nat := 4983230072969 + 3 ^ 40 * 2138218 * 2
def baseEnd_2138218 : Nat := 731955718730280297294347

theorem tailTrace_2138218 : CollatzResearch.WordTrace tailWord_2138218 prefixEnd_2138218 731955718730280297294347 := by
  unfold tailWord_2138218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19496804341902209851539827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51991478245072559604106205 19496804341902209851539827)
  ·
    refine ⟨29245206512853314777309741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19496804341902209851539827 29245206512853314777309741)
    ·
      refine ⟨10966952442319993041491153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29245206512853314777309741 10966952442319993041491153)
      ·
        refine ⟨8225214331739994781118365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10966952442319993041491153 8225214331739994781118365)
        ·
          refine ⟨3084455374402498042919387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8225214331739994781118365 3084455374402498042919387)
          ·
            refine ⟨4626683061603747064379081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084455374402498042919387 4626683061603747064379081)
            ·
              refine ⟨3470012296202810298284311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4626683061603747064379081 3470012296202810298284311)
              ·
                refine ⟨5205018444304215447426467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470012296202810298284311 5205018444304215447426467)
                ·
                  refine ⟨7807527666456323171139701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205018444304215447426467 7807527666456323171139701)
                  ·
                    refine ⟨731955718730280297294347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7807527666456323171139701 731955718730280297294347)
                    ·
                      rfl

theorem cell22_2138218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2138218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138218 prefixEnd_2138218 := by exact prefixLift 2138218
  have htrace : WordTrace (prefixWord ++ tailWord_2138218) baseStart_2138218 baseEnd_2138218 := by
    simpa [prefixWord, tailWord_2138218, baseEnd_2138218] using wordTrace_append hprefix tailTrace_2138218
  have hstable : (prefixWord ++ tailWord_2138218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138218).length < 2 ^ (prefixWord ++ tailWord_2138218).sum := by decide
  have hdescent : baseEnd_2138218 < baseStart_2138218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138231 : List Nat := [1, 1, 3, 1, 1, 6, 3, 6]
def baseStart_2138231 : Nat := 118140960795 + 2138231 * 2 ^ 59
def prefixEnd_2138231 : Nat := 4983230072969 + 3 ^ 40 * 2138231 * 2
def baseEnd_2138231 : Nat := 81328907655105844079923

theorem tailTrace_2138231 : CollatzResearch.WordTrace tailWord_2138231 prefixEnd_2138231 81328907655105844079923 := by
  unfold tailWord_2138231
  simp only [CollatzResearch.WordTrace]
  refine ⟨77987691516561742626382547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51991794344374495084255031 77987691516561742626382547)
  ·
    refine ⟨116981537274842613939573821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77987691516561742626382547 116981537274842613939573821)
    ·
      refine ⟨43868076478065980227340183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116981537274842613939573821 43868076478065980227340183)
      ·
        refine ⟨65802114717098970341010275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43868076478065980227340183 65802114717098970341010275)
        ·
          refine ⟨98703172075648455511515413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65802114717098970341010275 98703172075648455511515413)
          ·
            refine ⟨4626711191046021352102285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98703172075648455511515413 4626711191046021352102285)
            ·
              refine ⟨1735016696642258007038357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4626711191046021352102285 1735016696642258007038357)
              ·
                refine ⟨81328907655105844079923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1735016696642258007038357 81328907655105844079923)
                ·
                  rfl

theorem cell22_2138231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 6].length) (baseStart_2138231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138231 prefixEnd_2138231 := by exact prefixLift 2138231
  have htrace : WordTrace (prefixWord ++ tailWord_2138231) baseStart_2138231 baseEnd_2138231 := by
    simpa [prefixWord, tailWord_2138231, baseEnd_2138231] using wordTrace_append hprefix tailTrace_2138231
  have hstable : (prefixWord ++ tailWord_2138231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138231).length < 2 ^ (prefixWord ++ tailWord_2138231).sum := by decide
  have hdescent : baseEnd_2138231 < baseStart_2138231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138233 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_2138233 : Nat := 118140960795 + 2138233 * 2 ^ 59
def prefixEnd_2138233 : Nat := 4983230072969 + 3 ^ 40 * 2138233 * 2
def baseEnd_2138233 : Nat := 731960853536825258169301

theorem tailTrace_2138233 : CollatzResearch.WordTrace tailWord_2138233 prefixEnd_2138233 731960853536825258169301 := by
  unfold tailWord_2138233
  simp only [CollatzResearch.WordTrace]
  refine ⟨77987764462554496967955353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51991842975036331311970235 77987764462554496967955353)
  ·
    refine ⟨58490823346915872725966515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77987764462554496967955353 58490823346915872725966515)
    ·
      refine ⟨87736235020373809088949773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58490823346915872725966515 87736235020373809088949773)
      ·
        refine ⟨32901088132640178408356165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87736235020373809088949773 32901088132640178408356165)
        ·
          refine ⟨6168954024870033451566781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32901088132640178408356165 6168954024870033451566781)
          ·
            refine ⟨2313357759326262544337543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6168954024870033451566781 2313357759326262544337543)
            ·
              refine ⟨3470036638989393816506315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313357759326262544337543 3470036638989393816506315)
              ·
                refine ⟨5205054958484090724759473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470036638989393816506315 5205054958484090724759473)
                ·
                  refine ⟨3903791218863068043569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5205054958484090724759473 3903791218863068043569605)
                  ·
                    refine ⟨731960853536825258169301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3903791218863068043569605 731960853536825258169301)
                    ·
                      rfl

theorem cell22_2138233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_2138233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138233 prefixEnd_2138233 := by exact prefixLift 2138233
  have htrace : WordTrace (prefixWord ++ tailWord_2138233) baseStart_2138233 baseEnd_2138233 := by
    simpa [prefixWord, tailWord_2138233, baseEnd_2138233] using wordTrace_append hprefix tailTrace_2138233
  have hstable : (prefixWord ++ tailWord_2138233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138233).length < 2 ^ (prefixWord ++ tailWord_2138233).sum := by decide
  have hdescent : baseEnd_2138233 < baseStart_2138233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138282 : List Nat := [3, 1, 5, 1, 3, 1, 2, 6]
def baseStart_2138282 : Nat := 118140960795 + 2138282 * 2 ^ 59
def prefixEnd_2138282 : Nat := 4983230072969 + 3 ^ 40 * 2138282 * 2
def baseEnd_2138282 : Nat := 81330847470911718188239

theorem tailTrace_2138282 : CollatzResearch.WordTrace tailWord_2138282 prefixEnd_2138282 81330847470911718188239 := by
  unfold tailWord_2138282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19497387909844244584122275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51993034426251318890992733 19497387909844244584122275)
  ·
    refine ⟨29246081864766366876183413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19497387909844244584122275 29246081864766366876183413)
    ·
      refine ⟨2741820174821846894642195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29246081864766366876183413 2741820174821846894642195)
      ·
        refine ⟨4112730262232770341963293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2741820174821846894642195 4112730262232770341963293)
        ·
          refine ⟨1542273848337288878236235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4112730262232770341963293 1542273848337288878236235)
          ·
            refine ⟨2313410772505933317354353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542273848337288878236235 2313410772505933317354353)
            ·
              refine ⟨1735058079379449988015765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313410772505933317354353 1735058079379449988015765)
              ·
                refine ⟨81330847470911718188239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1735058079379449988015765 81330847470911718188239)
                ·
                  rfl

theorem cell22_2138282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_2138282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138282 prefixEnd_2138282 := by exact prefixLift 2138282
  have htrace : WordTrace (prefixWord ++ tailWord_2138282) baseStart_2138282 baseEnd_2138282 := by
    simpa [prefixWord, tailWord_2138282, baseEnd_2138282] using wordTrace_append hprefix tailTrace_2138282
  have hstable : (prefixWord ++ tailWord_2138282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138282).length < 2 ^ (prefixWord ++ tailWord_2138282).sum := by decide
  have hdescent : baseEnd_2138282 < baseStart_2138282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138321 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 6]
def baseStart_2138321 : Nat := 118140960795 + 2138321 * 2 ^ 59
def prefixEnd_2138321 : Nat := 4983230072969 + 3 ^ 40 * 2138321 * 2
def baseEnd_2138321 : Nat := 243996992578407453989677

theorem tailTrace_2138321 : CollatzResearch.WordTrace tailWord_2138321 prefixEnd_2138321 243996992578407453989677 := by
  unfold tailWord_2138321
  simp only [CollatzResearch.WordTrace]
  refine ⟨77990974086235687997158817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51993982724157125331439211 77990974086235687997158817)
  ·
    refine ⟨58493230564676765997869113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77990974086235687997158817 58493230564676765997869113)
    ·
      refine ⟨43869922923507574498401835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58493230564676765997869113 43869922923507574498401835)
      ·
        refine ⟨65804884385261361747602753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43869922923507574498401835 65804884385261361747602753)
        ·
          refine ⟨49353663288946021310702065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65804884385261361747602753 49353663288946021310702065)
          ·
            refine ⟨37015247466709515983026549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49353663288946021310702065 37015247466709515983026549)
            ·
              refine ⟨3470179450004017123408739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37015247466709515983026549 3470179450004017123408739)
              ·
                refine ⟨5205269175006025685113109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3470179450004017123408739 5205269175006025685113109)
                ·
                  refine ⟨243996992578407453989677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5205269175006025685113109 243996992578407453989677)
                  ·
                    rfl

theorem cell22_2138321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_2138321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138321 prefixEnd_2138321 := by exact prefixLift 2138321
  have htrace : WordTrace (prefixWord ++ tailWord_2138321) baseStart_2138321 baseEnd_2138321 := by
    simpa [prefixWord, tailWord_2138321, baseEnd_2138321] using wordTrace_append hprefix tailTrace_2138321
  have hstable : (prefixWord ++ tailWord_2138321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138321).length < 2 ^ (prefixWord ++ tailWord_2138321).sum := by decide
  have hdescent : baseEnd_2138321 < baseStart_2138321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138336 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_2138336 : Nat := 118140960795 + 2138336 * 2 ^ 59
def prefixEnd_2138336 : Nat := 4983230072969 + 3 ^ 40 * 2138336 * 2
def baseEnd_2138336 : Nat := 731996112541767322843985

theorem tailTrace_2138336 : CollatzResearch.WordTrace tailWord_2138336 prefixEnd_2138336 731996112541767322843985 := by
  unfold tailWord_2138336
  simp only [CollatzResearch.WordTrace]
  refine ⟨38995760590590672779477431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51994347454120897039303241 38995760590590672779477431)
  ·
    refine ⟨58493640885886009169216147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38995760590590672779477431 58493640885886009169216147)
    ·
      refine ⟨87740461328829013753824221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58493640885886009169216147 87740461328829013753824221)
      ·
        refine ⟨32902672998310880157684083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87740461328829013753824221 32902672998310880157684083)
        ·
          refine ⟨49354009497466320236526125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32902672998310880157684083 49354009497466320236526125)
          ·
            refine ⟨18507753561549870088697297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49354009497466320236526125 18507753561549870088697297)
            ·
              refine ⟨13880815171162402566522973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18507753561549870088697297 13880815171162402566522973)
              ·
                refine ⟨5205305689185900962446115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13880815171162402566522973 5205305689185900962446115)
                ·
                  refine ⟨7807958533778851443669173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5205305689185900962446115 7807958533778851443669173)
                  ·
                    refine ⟨731996112541767322843985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7807958533778851443669173 731996112541767322843985)
                    ·
                      rfl

theorem cell22_2138336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_2138336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138336 prefixEnd_2138336 := by exact prefixLift 2138336
  have htrace : WordTrace (prefixWord ++ tailWord_2138336) baseStart_2138336 baseEnd_2138336 := by
    simpa [prefixWord, tailWord_2138336, baseEnd_2138336] using wordTrace_append hprefix tailTrace_2138336
  have hstable : (prefixWord ++ tailWord_2138336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138336).length < 2 ^ (prefixWord ++ tailWord_2138336).sum := by decide
  have hdescent : baseEnd_2138336 < baseStart_2138336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138396 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2138396 : Nat := 118140960795 + 2138396 * 2 ^ 59
def prefixEnd_2138396 : Nat := 4983230072969 + 3 ^ 40 * 2138396 * 2
def baseEnd_2138396 : Nat := 732016651767947166343801

theorem tailTrace_2138396 : CollatzResearch.WordTrace tailWord_2138396 prefixEnd_2138396 732016651767947166343801 := by
  unfold tailWord_2138396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38996854780481987903069521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51995806373975983870759361 38996854780481987903069521)
  ·
    refine ⟨29247641085361490927302141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38996854780481987903069521 29247641085361490927302141)
    ·
      refine ⟨10967865407010559097738303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29247641085361490927302141 10967865407010559097738303)
      ·
        refine ⟨16451798110515838646607455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10967865407010559097738303 16451798110515838646607455)
        ·
          refine ⟨24677697165773757969911183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16451798110515838646607455 24677697165773757969911183)
          ·
            refine ⟨37016545748660636954866775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24677697165773757969911183 37016545748660636954866775)
            ·
              refine ⟨55524818622990955432300163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37016545748660636954866775 55524818622990955432300163)
              ·
                refine ⟨83287227934486433148450245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55524818622990955432300163 83287227934486433148450245)
                ·
                  refine ⟨15616355237716206215334421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83287227934486433148450245 15616355237716206215334421)
                  ·
                    refine ⟨732016651767947166343801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15616355237716206215334421 732016651767947166343801)
                    ·
                      rfl

theorem cell22_2138396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2138396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138396 prefixEnd_2138396 := by exact prefixLift 2138396
  have htrace : WordTrace (prefixWord ++ tailWord_2138396) baseStart_2138396 baseEnd_2138396 := by
    simpa [prefixWord, tailWord_2138396, baseEnd_2138396] using wordTrace_append hprefix tailTrace_2138396
  have hstable : (prefixWord ++ tailWord_2138396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138396).length < 2 ^ (prefixWord ++ tailWord_2138396).sum := by decide
  have hdescent : baseEnd_2138396 < baseStart_2138396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138415 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 1, 3]
def baseStart_2138415 : Nat := 118140960795 + 2138415 * 2 ^ 59
def prefixEnd_2138415 : Nat := 4983230072969 + 3 ^ 40 * 2138415 * 2
def baseEnd_2138415 : Nat := 732023155856237450118743

theorem tailTrace_2138415 : CollatzResearch.WordTrace tailWord_2138415 prefixEnd_2138415 732023155856237450118743 := by
  unfold tailWord_2138415
  simp only [CollatzResearch.WordTrace]
  refine ⟨77994402547895142051080699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51996268365263428034053799 77994402547895142051080699)
  ·
    refine ⟨116991603821842713076621049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77994402547895142051080699 116991603821842713076621049)
    ·
      refine ⟨87743702866382034807465787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116991603821842713076621049 87743702866382034807465787)
      ·
        refine ⟨131615554299573052211198681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87743702866382034807465787 131615554299573052211198681)
        ·
          refine ⟨98711665724679789158399011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131615554299573052211198681 98711665724679789158399011)
          ·
            refine ⟨148067498587019683737598517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98711665724679789158399011 148067498587019683737598517)
            ·
              refine ⟨13881327992533095350399861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 148067498587019683737598517 13881327992533095350399861)
              ·
                refine ⟨1301374499299977689099987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13881327992533095350399861 1301374499299977689099987)
                ·
                  refine ⟨1952061748949966533649981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301374499299977689099987 1952061748949966533649981)
                  ·
                    refine ⟨732023155856237450118743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952061748949966533649981 732023155856237450118743)
                    ·
                      rfl

theorem cell22_2138415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_2138415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138415 prefixEnd_2138415 := by exact prefixLift 2138415
  have htrace : WordTrace (prefixWord ++ tailWord_2138415) baseStart_2138415 baseEnd_2138415 := by
    simpa [prefixWord, tailWord_2138415, baseEnd_2138415] using wordTrace_append hprefix tailTrace_2138415
  have hstable : (prefixWord ++ tailWord_2138415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138415).length < 2 ^ (prefixWord ++ tailWord_2138415).sum := by decide
  have hdescent : baseEnd_2138415 < baseStart_2138415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138456 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_2138456 : Nat := 118140960795 + 2138456 * 2 ^ 59
def prefixEnd_2138456 : Nat := 4983230072969 + 3 ^ 40 * 2138456 * 2
def baseEnd_2138456 : Nat := 244012396998042336614539

theorem tailTrace_2138456 : CollatzResearch.WordTrace tailWord_2138456 prefixEnd_2138456 244012396998042336614539 := by
  unfold tailWord_2138456
  simp only [CollatzResearch.WordTrace]
  refine ⟨38997948970373303026661611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51997265293831070702215481 38997948970373303026661611)
  ·
    refine ⟨58496923455559954539992417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38997948970373303026661611 58496923455559954539992417)
    ·
      refine ⟨43872692591669965904994313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58496923455559954539992417 43872692591669965904994313)
      ·
        refine ⟨32904519443752474428745735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43872692591669965904994313 32904519443752474428745735)
        ·
          refine ⟨49356779165628711643118603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32904519443752474428745735 49356779165628711643118603)
          ·
            refine ⟨74035168748443067464677905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49356779165628711643118603 74035168748443067464677905)
            ·
              refine ⟨55526376561332300598508429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74035168748443067464677905 55526376561332300598508429)
              ·
                refine ⟨20822391210499612724440661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55526376561332300598508429 20822391210499612724440661)
                ·
                  refine ⟨244012396998042336614539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20822391210499612724440661 244012396998042336614539)
                  ·
                    rfl

theorem cell22_2138456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_2138456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138456 prefixEnd_2138456 := by exact prefixLift 2138456
  have htrace : WordTrace (prefixWord ++ tailWord_2138456) baseStart_2138456 baseEnd_2138456 := by
    simpa [prefixWord, tailWord_2138456, baseEnd_2138456] using wordTrace_append hprefix tailTrace_2138456
  have hstable : (prefixWord ++ tailWord_2138456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138456).length < 2 ^ (prefixWord ++ tailWord_2138456).sum := by decide
  have hdescent : baseEnd_2138456 < baseStart_2138456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138503 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2138503 : Nat := 118140960795 + 2138503 * 2 ^ 59
def prefixEnd_2138503 : Nat := 4983230072969 + 3 ^ 40 * 2138503 * 2
def baseEnd_2138503 : Nat := 732053280054634553918473

theorem tailTrace_2138503 : CollatzResearch.WordTrace tailWord_2138503 prefixEnd_2138503 732053280054634553918473 := by
  unfold tailWord_2138503
  simp only [CollatzResearch.WordTrace]
  refine ⟨77997612171576333080284163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51998408114384222053522775 77997612171576333080284163)
  ·
    refine ⟨116996418257364499620426245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77997612171576333080284163 116996418257364499620426245)
    ·
      refine ⟨21936828423255843678829921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116996418257364499620426245 21936828423255843678829921)
      ·
        refine ⟨16452621317441882759122441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21936828423255843678829921 16452621317441882759122441)
        ·
          refine ⟨12339465988081412069341831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16452621317441882759122441 12339465988081412069341831)
          ·
            refine ⟨18509198982122118104012747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12339465988081412069341831 18509198982122118104012747)
            ·
              refine ⟨27763798473183177156019121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18509198982122118104012747 27763798473183177156019121)
              ·
                refine ⟨20822848854887382867014341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27763798473183177156019121 20822848854887382867014341)
                ·
                  refine ⟨3904284160291384287565189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20822848854887382867014341 3904284160291384287565189)
                  ·
                    refine ⟨732053280054634553918473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904284160291384287565189 732053280054634553918473)
                    ·
                      rfl

theorem cell22_2138503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2138503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138503 prefixEnd_2138503 := by exact prefixLift 2138503
  have htrace : WordTrace (prefixWord ++ tailWord_2138503) baseStart_2138503 baseEnd_2138503 := by
    simpa [prefixWord, tailWord_2138503, baseEnd_2138503] using wordTrace_append hprefix tailTrace_2138503
  have hstable : (prefixWord ++ tailWord_2138503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138503).length < 2 ^ (prefixWord ++ tailWord_2138503).sum := by decide
  have hdescent : baseEnd_2138503 < baseStart_2138503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138520 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_2138520 : Nat := 118140960795 + 2138520 * 2 ^ 59
def prefixEnd_2138520 : Nat := 4983230072969 + 3 ^ 40 * 2138520 * 2
def baseEnd_2138520 : Nat := 732059099502052176243421

theorem tailTrace_2138520 : CollatzResearch.WordTrace tailWord_2138520 prefixEnd_2138520 732059099502052176243421 := by
  unfold tailWord_2138520
  simp only [CollatzResearch.WordTrace]
  refine ⟨38999116106257372491826507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51998821475009829989102009 38999116106257372491826507)
  ·
    refine ⟨58498674159386058737739761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38999116106257372491826507 58498674159386058737739761)
    ·
      refine ⟨43874005619539544053304821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58498674159386058737739761 43874005619539544053304821)
      ·
        refine ⟨4113188026831832254997327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43874005619539544053304821 4113188026831832254997327)
        ·
          refine ⟨6169782040247748382495991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113188026831832254997327 6169782040247748382495991)
          ·
            refine ⟨9254673060371622573743987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6169782040247748382495991 9254673060371622573743987)
            ·
              refine ⟨13882009590557433860615981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9254673060371622573743987 13882009590557433860615981)
              ·
                refine ⟨5205753596459037697730993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13882009590557433860615981 5205753596459037697730993)
                ·
                  refine ⟨3904315197344278273298245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5205753596459037697730993 3904315197344278273298245)
                  ·
                    refine ⟨732059099502052176243421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904315197344278273298245 732059099502052176243421)
                    ·
                      rfl

theorem cell22_2138520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_2138520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138520 prefixEnd_2138520 := by exact prefixLift 2138520
  have htrace : WordTrace (prefixWord ++ tailWord_2138520) baseStart_2138520 baseEnd_2138520 := by
    simpa [prefixWord, tailWord_2138520, baseEnd_2138520] using wordTrace_append hprefix tailTrace_2138520
  have hstable : (prefixWord ++ tailWord_2138520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138520).length < 2 ^ (prefixWord ++ tailWord_2138520).sum := by decide
  have hdescent : baseEnd_2138520 < baseStart_2138520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138541 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2138541 : Nat := 118140960795 + 2138541 * 2 ^ 59
def prefixEnd_2138541 : Nat := 4983230072969 + 3 ^ 40 * 2138541 * 2
def baseEnd_2138541 : Nat := 244022096077071707156119

theorem tailTrace_2138541 : CollatzResearch.WordTrace tailWord_2138541 prefixEnd_2138541 244022096077071707156119 := by
  unfold tailWord_2138541
  simp only [CollatzResearch.WordTrace]
  refine ⟨77998998145438665570167477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51999332096959110380111651 77998998145438665570167477)
  ·
    refine ⟨7312406076134874897203201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77998998145438665570167477 7312406076134874897203201)
    ·
      refine ⟨5484304557101156172902401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7312406076134874897203201 5484304557101156172902401)
      ·
        refine ⟨4113228417825867129676801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5484304557101156172902401 4113228417825867129676801)
        ·
          refine ⟨3084921313369400347257601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4113228417825867129676801 3084921313369400347257601)
          ·
            refine ⟨2313690985027050260443201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3084921313369400347257601 2313690985027050260443201)
            ·
              refine ⟨1735268238770287695332401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313690985027050260443201 1735268238770287695332401)
              ·
                refine ⟨1301451179077715771499301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735268238770287695332401 1301451179077715771499301)
                ·
                  refine ⟨244022096077071707156119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301451179077715771499301 244022096077071707156119)
                  ·
                    rfl

theorem cell22_2138541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2138541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138541 prefixEnd_2138541 := by exact prefixLift 2138541
  have htrace : WordTrace (prefixWord ++ tailWord_2138541) baseStart_2138541 baseEnd_2138541 := by
    simpa [prefixWord, tailWord_2138541, baseEnd_2138541] using wordTrace_append hprefix tailTrace_2138541
  have hstable : (prefixWord ++ tailWord_2138541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138541).length < 2 ^ (prefixWord ++ tailWord_2138541).sum := by decide
  have hdescent : baseEnd_2138541 < baseStart_2138541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138625 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 6]
def baseStart_2138625 : Nat := 118140960795 + 2138625 * 2 ^ 59
def prefixEnd_2138625 : Nat := 4983230072969 + 3 ^ 40 * 2138625 * 2
def baseEnd_2138625 : Nat := 244031681049288967456033

theorem tailTrace_2138625 : CollatzResearch.WordTrace tailWord_2138625 prefixEnd_2138625 244031681049288967456033 := by
  unfold tailWord_2138625
  simp only [CollatzResearch.WordTrace]
  refine ⟨78002061877134347916225329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52001374584756231944150219 78002061877134347916225329)
  ·
    refine ⟨58501546407850760937168997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78002061877134347916225329 58501546407850760937168997)
    ·
      refine ⟨10969039951472017675719187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58501546407850760937168997 10969039951472017675719187)
      ·
        refine ⟨16453559927208026513578781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10969039951472017675719187 16453559927208026513578781)
        ·
          refine ⟨6170084972703009942592043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16453559927208026513578781 6170084972703009942592043)
          ·
            refine ⟨9255127459054514913888065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170084972703009942592043 9255127459054514913888065)
            ·
              refine ⟨6941345594290886185416049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9255127459054514913888065 6941345594290886185416049)
              ·
                refine ⟨5206009195718164639062037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6941345594290886185416049 5206009195718164639062037)
                ·
                  refine ⟨244031681049288967456033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5206009195718164639062037 244031681049288967456033)
                  ·
                    rfl

theorem cell22_2138625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_2138625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138625 prefixEnd_2138625 := by exact prefixLift 2138625
  have htrace : WordTrace (prefixWord ++ tailWord_2138625) baseStart_2138625 baseEnd_2138625 := by
    simpa [prefixWord, tailWord_2138625, baseEnd_2138625] using wordTrace_append hprefix tailTrace_2138625
  have hstable : (prefixWord ++ tailWord_2138625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138625).length < 2 ^ (prefixWord ++ tailWord_2138625).sum := by decide
  have hdescent : baseEnd_2138625 < baseStart_2138625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138644 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2138644 : Nat := 118140960795 + 2138644 * 2 ^ 59
def prefixEnd_2138644 : Nat := 4983230072969 + 3 ^ 40 * 2138644 * 2
def baseEnd_2138644 : Nat := 732101547236157186143041

theorem tailTrace_2138644 : CollatzResearch.WordTrace tailWord_2138644 prefixEnd_2138644 732101547236157186143041 := by
  unfold tailWord_2138644
  simp only [CollatzResearch.WordTrace]
  refine ⟨39001377432032757080583493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52001836576043676107444657 39001377432032757080583493)
  ·
    refine ⟨7312758268506141952609405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39001377432032757080583493 7312758268506141952609405)
    ·
      refine ⟨2742284350689803232228527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7312758268506141952609405 2742284350689803232228527)
      ·
        refine ⟨4113426526034704848342791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742284350689803232228527 4113426526034704848342791)
        ·
          refine ⟨6170139789052057272514187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113426526034704848342791 6170139789052057272514187)
          ·
            refine ⟨9255209683578085908771281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170139789052057272514187 9255209683578085908771281)
            ·
              refine ⟨6941407262683564431578461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9255209683578085908771281 6941407262683564431578461)
              ·
                refine ⟨2603027723506336661841923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6941407262683564431578461 2603027723506336661841923)
                ·
                  refine ⟨3904541585259504992762885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603027723506336661841923 3904541585259504992762885)
                  ·
                    refine ⟨732101547236157186143041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3904541585259504992762885 732101547236157186143041)
                    ·
                      rfl

theorem cell22_2138644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2138644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138644 prefixEnd_2138644 := by exact prefixLift 2138644
  have htrace : WordTrace (prefixWord ++ tailWord_2138644) baseStart_2138644 baseEnd_2138644 := by
    simpa [prefixWord, tailWord_2138644, baseEnd_2138644] using wordTrace_append hprefix tailTrace_2138644
  have hstable : (prefixWord ++ tailWord_2138644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138644).length < 2 ^ (prefixWord ++ tailWord_2138644).sum := by decide
  have hdescent : baseEnd_2138644 < baseStart_2138644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138657 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2138657 : Nat := 118140960795 + 2138657 * 2 ^ 59
def prefixEnd_2138657 : Nat := 4983230072969 + 3 ^ 40 * 2138657 * 2
def baseEnd_2138657 : Nat := 732105997401829485568001

theorem tailTrace_2138657 : CollatzResearch.WordTrace tailWord_2138657 prefixEnd_2138657 732105997401829485568001 := by
  unfold tailWord_2138657
  simp only [CollatzResearch.WordTrace]
  refine ⟨78003229013018417381390225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52002152675345611587593483 78003229013018417381390225)
  ·
    refine ⟨58502421759763813036042669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78003229013018417381390225 58502421759763813036042669)
    ·
      refine ⟨21938408159911429888516001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58502421759763813036042669 21938408159911429888516001)
      ·
        refine ⟨16453806119933572416387001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21938408159911429888516001 16453806119933572416387001)
        ·
          refine ⟨12340354589950179312290251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16453806119933572416387001 12340354589950179312290251)
          ·
            refine ⟨18510531884925268968435377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12340354589950179312290251 18510531884925268968435377)
            ·
              refine ⟨13882898913693951726326533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18510531884925268968435377 13882898913693951726326533)
              ·
                refine ⟨2603043546317615948686225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13882898913693951726326533 2603043546317615948686225)
                ·
                  refine ⟨1952282659738211961514669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603043546317615948686225 1952282659738211961514669)
                  ·
                    refine ⟨732105997401829485568001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952282659738211961514669 732105997401829485568001)
                    ·
                      rfl

theorem cell22_2138657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2138657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138657 prefixEnd_2138657 := by exact prefixLift 2138657
  have htrace : WordTrace (prefixWord ++ tailWord_2138657) baseStart_2138657 baseEnd_2138657 := by
    simpa [prefixWord, tailWord_2138657, baseEnd_2138657] using wordTrace_append hprefix tailTrace_2138657
  have hstable : (prefixWord ++ tailWord_2138657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138657).length < 2 ^ (prefixWord ++ tailWord_2138657).sum := by decide
  have hdescent : baseEnd_2138657 < baseStart_2138657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138659 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 4]
def baseStart_2138659 : Nat := 118140960795 + 2138659 * 2 ^ 59
def prefixEnd_2138659 : Nat := 4983230072969 + 3 ^ 40 * 2138659 * 2
def baseEnd_2138659 : Nat := 244035560680900715672665

theorem tailTrace_2138659 : CollatzResearch.WordTrace tailWord_2138659 prefixEnd_2138659 244035560680900715672665 := by
  unfold tailWord_2138659
  simp only [CollatzResearch.WordTrace]
  refine ⟨78003301959011171722963031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52002201306007447815308687 78003301959011171722963031)
  ·
    refine ⟨117004952938516757584444547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78003301959011171722963031 117004952938516757584444547)
    ·
      refine ⟨175507429407775136376666821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117004952938516757584444547 175507429407775136376666821)
      ·
        refine ⟨32907643013957838070625029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175507429407775136376666821 32907643013957838070625029)
        ·
          refine ⟨6170183065117094638242193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32907643013957838070625029 6170183065117094638242193)
          ·
            refine ⟨4627637298837820978681645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6170183065117094638242193 4627637298837820978681645)
            ·
              refine ⟨1735363987064182867005617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4627637298837820978681645 1735363987064182867005617)
              ·
                refine ⟨1301522990298137150254213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735363987064182867005617 1301522990298137150254213)
                ·
                  refine ⟨244035560680900715672665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301522990298137150254213 244035560680900715672665)
                  ·
                    rfl

theorem cell22_2138659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 4].length) (baseStart_2138659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138659 prefixEnd_2138659 := by exact prefixLift 2138659
  have htrace : WordTrace (prefixWord ++ tailWord_2138659) baseStart_2138659 baseEnd_2138659 := by
    simpa [prefixWord, tailWord_2138659, baseEnd_2138659] using wordTrace_append hprefix tailTrace_2138659
  have hstable : (prefixWord ++ tailWord_2138659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138659).length < 2 ^ (prefixWord ++ tailWord_2138659).sum := by decide
  have hdescent : baseEnd_2138659 < baseStart_2138659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138674 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2138674 : Nat := 118140960795 + 2138674 * 2 ^ 59
def prefixEnd_2138674 : Nat := 4983230072969 + 3 ^ 40 * 2138674 * 2
def baseEnd_2138674 : Nat := 732111816849247107892949

theorem tailTrace_2138674 : CollatzResearch.WordTrace tailWord_2138674 prefixEnd_2138674 732111816849247107892949 := by
  unfold tailWord_2138674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19500962263489207321189769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52002566035971219523172717 19500962263489207321189769)
  ·
    refine ⟨14625721697616905490892327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19500962263489207321189769 14625721697616905490892327)
    ·
      refine ⟨21938582546425358236338491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14625721697616905490892327 21938582546425358236338491)
      ·
        refine ⟨32907873819638037354507737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21938582546425358236338491 32907873819638037354507737)
        ·
          refine ⟨24680905364728528015880803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32907873819638037354507737 24680905364728528015880803)
          ·
            refine ⟨37021358047092792023821205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24680905364728528015880803 37021358047092792023821205)
            ·
              refine ⟨1735376158457474626116619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37021358047092792023821205 1735376158457474626116619)
              ·
                refine ⟨2603064237686211939174929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735376158457474626116619 2603064237686211939174929)
                ·
                  refine ⟨1952298178264658954381197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603064237686211939174929 1952298178264658954381197)
                  ·
                    refine ⟨732111816849247107892949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952298178264658954381197 732111816849247107892949)
                    ·
                      rfl

theorem cell22_2138674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2138674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138674 prefixEnd_2138674 := by exact prefixLift 2138674
  have htrace : WordTrace (prefixWord ++ tailWord_2138674) baseStart_2138674 baseEnd_2138674 := by
    simpa [prefixWord, tailWord_2138674, baseEnd_2138674] using wordTrace_append hprefix tailTrace_2138674
  have hstable : (prefixWord ++ tailWord_2138674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138674).length < 2 ^ (prefixWord ++ tailWord_2138674).sum := by decide
  have hdescent : baseEnd_2138674 < baseStart_2138674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138777 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 4]
def baseStart_2138777 : Nat := 118140960795 + 2138777 * 2 ^ 59
def prefixEnd_2138777 : Nat := 4983230072969 + 3 ^ 40 * 2138777 * 2
def baseEnd_2138777 : Nat := 244049025284729724189211

theorem tailTrace_2138777 : CollatzResearch.WordTrace tailWord_2138777 prefixEnd_2138777 244049025284729724189211 := by
  unfold tailWord_2138777
  simp only [CollatzResearch.WordTrace]
  refine ⟨78007605772583677875758585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52005070515055785250505723 78007605772583677875758585)
  ·
    refine ⟨58505704329437758406818939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78007605772583677875758585 58505704329437758406818939)
    ·
      refine ⟨87758556494156637610228409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58505704329437758406818939 87758556494156637610228409)
      ·
        refine ⟨65818917370617478207671307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87758556494156637610228409 65818917370617478207671307)
        ·
          refine ⟨98728376055926217311506961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65818917370617478207671307 98728376055926217311506961)
          ·
            refine ⟨74046282041944662983630221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98728376055926217311506961 74046282041944662983630221)
            ·
              refine ⟨27767355765729248618861333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74046282041944662983630221 27767355765729248618861333)
              ·
                refine ⟨1301594801518558529009125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27767355765729248618861333 1301594801518558529009125)
                ·
                  refine ⟨244049025284729724189211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301594801518558529009125 244049025284729724189211)
                  ·
                    rfl

theorem cell22_2138777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_2138777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138777 prefixEnd_2138777 := by exact prefixLift 2138777
  have htrace : WordTrace (prefixWord ++ tailWord_2138777) baseStart_2138777 baseEnd_2138777 := by
    simpa [prefixWord, tailWord_2138777, baseEnd_2138777] using wordTrace_append hprefix tailTrace_2138777
  have hstable : (prefixWord ++ tailWord_2138777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138777).length < 2 ^ (prefixWord ++ tailWord_2138777).sum := by decide
  have hdescent : baseEnd_2138777 < baseStart_2138777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138884 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_2138884 : Nat := 118140960795 + 2138884 * 2 ^ 59
def prefixEnd_2138884 : Nat := 4983230072969 + 3 ^ 40 * 2138884 * 2
def baseEnd_2138884 : Nat := 244061234713625520047435

theorem tailTrace_2138884 : CollatzResearch.WordTrace tailWord_2138884 prefixEnd_2138884 244061234713625520047435 := by
  unfold tailWord_2138884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39005754191598017574951853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52007672255464023433269137 39005754191598017574951853)
  ·
    refine ⟨14627157821849256590606945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39005754191598017574951853 14627157821849256590606945)
    ·
      refine ⟨10970368366386942442955209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14627157821849256590606945 10970368366386942442955209)
      ·
        refine ⟨8227776274790206832216407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10970368366386942442955209 8227776274790206832216407)
        ·
          refine ⟨12341664412185310248324611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227776274790206832216407 12341664412185310248324611)
          ·
            refine ⟨18512496618277965372486917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12341664412185310248324611 18512496618277965372486917)
            ·
              refine ⟨3471093115927118507341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18512496618277965372486917 3471093115927118507341297)
              ·
                refine ⟨2603319836945338880505973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3471093115927118507341297 2603319836945338880505973)
                ·
                  refine ⟨244061234713625520047435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2603319836945338880505973 244061234713625520047435)
                  ·
                    rfl

theorem cell22_2138884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_2138884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138884 prefixEnd_2138884 := by exact prefixLift 2138884
  have htrace : WordTrace (prefixWord ++ tailWord_2138884) baseStart_2138884 baseEnd_2138884 := by
    simpa [prefixWord, tailWord_2138884, baseEnd_2138884] using wordTrace_append hprefix tailTrace_2138884
  have hstable : (prefixWord ++ tailWord_2138884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138884).length < 2 ^ (prefixWord ++ tailWord_2138884).sum := by decide
  have hdescent : baseEnd_2138884 < baseStart_2138884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138888 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2138888 : Nat := 118140960795 + 2138888 * 2 ^ 59
def prefixEnd_2138888 : Nat := 4983230072969 + 3 ^ 40 * 2138888 * 2
def baseEnd_2138888 : Nat := 732185073422621883042293

theorem tailTrace_2138888 : CollatzResearch.WordTrace tailWord_2138888 prefixEnd_2138888 732185073422621883042293 := by
  unfold tailWord_2138888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39005827137590771916524659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52007769516787695888699545 39005827137590771916524659)
  ·
    refine ⟨58508740706386157874786989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39005827137590771916524659 58508740706386157874786989)
    ·
      refine ⟨21940777764894809203045121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58508740706386157874786989 21940777764894809203045121)
      ·
        refine ⟨16455583323671106902283841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21940777764894809203045121 16455583323671106902283841)
        ·
          refine ⟨12341687492753330176712881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16455583323671106902283841 12341687492753330176712881)
          ·
            refine ⟨9256265619564997632534661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12341687492753330176712881 9256265619564997632534661)
            ·
              refine ⟨1735549803668437056100249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9256265619564997632534661 1735549803668437056100249)
              ·
                refine ⟨1301662352751327792075187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735549803668437056100249 1301662352751327792075187)
                ·
                  refine ⟨1952493529126991688112781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301662352751327792075187 1952493529126991688112781)
                  ·
                    refine ⟨732185073422621883042293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952493529126991688112781 732185073422621883042293)
                    ·
                      rfl

theorem cell22_2138888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2138888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138888 prefixEnd_2138888 := by exact prefixLift 2138888
  have htrace : WordTrace (prefixWord ++ tailWord_2138888) baseStart_2138888 baseEnd_2138888 := by
    simpa [prefixWord, tailWord_2138888, baseEnd_2138888] using wordTrace_append hprefix tailTrace_2138888
  have hstable : (prefixWord ++ tailWord_2138888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138888).length < 2 ^ (prefixWord ++ tailWord_2138888).sum := by decide
  have hdescent : baseEnd_2138888 < baseStart_2138888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138897 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2138897 : Nat := 118140960795 + 2138897 * 2 ^ 59
def prefixEnd_2138897 : Nat := 4983230072969 + 3 ^ 40 * 2138897 * 2
def baseEnd_2138897 : Nat := 732188154306548859567265

theorem tailTrace_2138897 : CollatzResearch.WordTrace tailWord_2138897 prefixEnd_2138897 732188154306548859567265 := by
  unfold tailWord_2138897
  simp only [CollatzResearch.WordTrace]
  refine ⟨78011982532148938370126945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52007988354765958913417963 78011982532148938370126945)
  ·
    refine ⟨58508986899111703777595209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78011982532148938370126945 58508986899111703777595209)
    ·
      refine ⟨43881740174333777833196407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58508986899111703777595209 43881740174333777833196407)
      ·
        refine ⟨65822610261500666749794611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43881740174333777833196407 65822610261500666749794611)
        ·
          refine ⟨98733915392251000124691917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65822610261500666749794611 98733915392251000124691917)
          ·
            refine ⟨37025218272094125046759469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98733915392251000124691917 37025218272094125046759469)
            ·
              refine ⟨13884456852035296892534801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37025218272094125046759469 13884456852035296892534801)
              ·
                refine ⟨10413342639026472669401101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13884456852035296892534801 10413342639026472669401101)
                ·
                  refine ⟨3905003489634927251025413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10413342639026472669401101 3905003489634927251025413)
                  ·
                    refine ⟨732188154306548859567265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905003489634927251025413 732188154306548859567265)
                    ·
                      rfl

theorem cell22_2138897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2138897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138897 prefixEnd_2138897 := by exact prefixLift 2138897
  have htrace : WordTrace (prefixWord ++ tailWord_2138897) baseStart_2138897 baseEnd_2138897 := by
    simpa [prefixWord, tailWord_2138897, baseEnd_2138897] using wordTrace_append hprefix tailTrace_2138897
  have hstable : (prefixWord ++ tailWord_2138897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138897).length < 2 ^ (prefixWord ++ tailWord_2138897).sum := by decide
  have hdescent : baseEnd_2138897 < baseStart_2138897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138912 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_2138912 : Nat := 118140960795 + 2138912 * 2 ^ 59
def prefixEnd_2138912 : Nat := 4983230072969 + 3 ^ 40 * 2138912 * 2
def baseEnd_2138912 : Nat := 244064429704364606814073

theorem tailTrace_2138912 : CollatzResearch.WordTrace tailWord_2138912 prefixEnd_2138912 244064429704364606814073 := by
  unfold tailWord_2138912
  simp only [CollatzResearch.WordTrace]
  refine ⟨39006264813547297965961495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52008353084729730621281993 39006264813547297965961495)
  ·
    refine ⟨58509397220320946948942243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39006264813547297965961495 58509397220320946948942243)
    ·
      refine ⟨87764095830481420423413365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58509397220320946948942243 87764095830481420423413365)
      ·
        refine ⟨8227883984107633164695003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87764095830481420423413365 8227883984107633164695003)
        ·
          refine ⟨12341825976161449747042505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227883984107633164695003 12341825976161449747042505)
          ·
            refine ⟨9256369482121087310281879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12341825976161449747042505 9256369482121087310281879)
            ·
              refine ⟨13884554223181630965422819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9256369482121087310281879 13884554223181630965422819)
              ·
                refine ⟨20826831334772446448134229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13884554223181630965422819 20826831334772446448134229)
                ·
                  refine ⟨244064429704364606814073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20826831334772446448134229 244064429704364606814073)
                  ·
                    rfl

theorem cell22_2138912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_2138912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138912 prefixEnd_2138912 := by exact prefixLift 2138912
  have htrace : WordTrace (prefixWord ++ tailWord_2138912) baseStart_2138912 baseEnd_2138912 := by
    simpa [prefixWord, tailWord_2138912, baseEnd_2138912] using wordTrace_append hprefix tailTrace_2138912
  have hstable : (prefixWord ++ tailWord_2138912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138912).length < 2 ^ (prefixWord ++ tailWord_2138912).sum := by decide
  have hdescent : baseEnd_2138912 < baseStart_2138912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138914 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2138914 : Nat := 118140960795 + 2138914 * 2 ^ 59
def prefixEnd_2138914 : Nat := 4983230072969 + 3 ^ 40 * 2138914 * 2
def baseEnd_2138914 : Nat := 732193973753966481892213

theorem tailTrace_2138914 : CollatzResearch.WordTrace tailWord_2138914 prefixEnd_2138914 732193973753966481892213 := by
  unfold tailWord_2138914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19503150643271837568373949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52008401715391566848997197 19503150643271837568373949)
  ·
    refine ⟨7313681491226939088140231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19503150643271837568373949 7313681491226939088140231)
    ·
      refine ⟨10970522236840408632210347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7313681491226939088140231 10970522236840408632210347)
      ·
        refine ⟨16455783355260612948315521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10970522236840408632210347 16455783355260612948315521)
        ·
          refine ⟨12341837516445459711236641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16455783355260612948315521 12341837516445459711236641)
          ·
            refine ⟨9256378137334094783427481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12341837516445459711236641 9256378137334094783427481)
            ·
              refine ⟨6942283603000571087570611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9256378137334094783427481 6942283603000571087570611)
              ·
                refine ⟨10413425404500856631355917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6942283603000571087570611 10413425404500856631355917)
                ·
                  refine ⟨3905034526687821236758469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10413425404500856631355917 3905034526687821236758469)
                  ·
                    refine ⟨732193973753966481892213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905034526687821236758469 732193973753966481892213)
                    ·
                      rfl

theorem cell22_2138914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2138914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138914 prefixEnd_2138914 := by exact prefixLift 2138914
  have htrace : WordTrace (prefixWord ++ tailWord_2138914) baseStart_2138914 baseEnd_2138914 := by
    simpa [prefixWord, tailWord_2138914, baseEnd_2138914] using wordTrace_append hprefix tailTrace_2138914
  have hstable : (prefixWord ++ tailWord_2138914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138914).length < 2 ^ (prefixWord ++ tailWord_2138914).sum := by decide
  have hdescent : baseEnd_2138914 < baseStart_2138914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138931 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 1, 4]
def baseStart_2138931 : Nat := 118140960795 + 2138931 * 2 ^ 59
def prefixEnd_2138931 : Nat := 4983230072969 + 3 ^ 40 * 2138931 * 2
def baseEnd_2138931 : Nat := 732199793201384104217161

theorem tailTrace_2138931 : CollatzResearch.WordTrace tailWord_2138931 prefixEnd_2138931 732199793201384104217161 := by
  unfold tailWord_2138931
  simp only [CollatzResearch.WordTrace]
  refine ⟨78013222614025762176864647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52008815076017174784576431 78013222614025762176864647)
  ·
    refine ⟨117019833921038643265296971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78013222614025762176864647 117019833921038643265296971)
    ·
      refine ⟨175529750881557964897945457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117019833921038643265296971 175529750881557964897945457)
      ·
        refine ⟨131647313161168473673459093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175529750881557964897945457 131647313161168473673459093)
        ·
          refine ⟨6170967804429772203443395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131647313161168473673459093 6170967804429772203443395)
          ·
            refine ⟨9256451706644658305165093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170967804429772203443395 9256451706644658305165093)
            ·
              refine ⟨1735584694995873432218455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9256451706644658305165093 1735584694995873432218455)
              ·
                refine ⟨2603377042493810148327683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735584694995873432218455 2603377042493810148327683)
                ·
                  refine ⟨3905065563740715222491525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603377042493810148327683 3905065563740715222491525)
                  ·
                    refine ⟨732199793201384104217161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905065563740715222491525 732199793201384104217161)
                    ·
                      rfl

theorem cell22_2138931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 4].length) (baseStart_2138931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138931 prefixEnd_2138931 := by exact prefixLift 2138931
  have htrace : WordTrace (prefixWord ++ tailWord_2138931) baseStart_2138931 baseEnd_2138931 := by
    simpa [prefixWord, tailWord_2138931, baseEnd_2138931] using wordTrace_append hprefix tailTrace_2138931
  have hstable : (prefixWord ++ tailWord_2138931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138931).length < 2 ^ (prefixWord ++ tailWord_2138931).sum := by decide
  have hdescent : baseEnd_2138931 < baseStart_2138931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2138961 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2138961 : Nat := 118140960795 + 2138961 * 2 ^ 59
def prefixEnd_2138961 : Nat := 4983230072969 + 3 ^ 40 * 2138961 * 2
def baseEnd_2138961 : Nat := 732210062814474025967069

theorem tailTrace_2138961 : CollatzResearch.WordTrace tailWord_2138961 prefixEnd_2138961 732210062814474025967069 := by
  unfold tailWord_2138961
  simp only [CollatzResearch.WordTrace]
  refine ⟨78014316803917077300456737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52009544535944718200304491 78014316803917077300456737)
  ·
    refine ⟨58510737602937807975342553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78014316803917077300456737 58510737602937807975342553)
    ·
      refine ⟨43883053202203355981506915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58510737602937807975342553 43883053202203355981506915)
      ·
        refine ⟨65824579803305033972260373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43883053202203355981506915 65824579803305033972260373)
        ·
          refine ⟨3085527178279923467449705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65824579803305033972260373 3085527178279923467449705)
          ·
            refine ⟨2314145383709942600587279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085527178279923467449705 2314145383709942600587279)
            ·
              refine ⟨3471218075564913900880919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314145383709942600587279 3471218075564913900880919)
              ·
                refine ⟨5206827113347370851321379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471218075564913900880919 5206827113347370851321379)
                ·
                  refine ⟨7810240670021056276982069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5206827113347370851321379 7810240670021056276982069)
                  ·
                    refine ⟨732210062814474025967069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7810240670021056276982069 732210062814474025967069)
                    ·
                      rfl

theorem cell22_2138961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2138961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2138961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2138961 prefixEnd_2138961 := by exact prefixLift 2138961
  have htrace : WordTrace (prefixWord ++ tailWord_2138961) baseStart_2138961 baseEnd_2138961 := by
    simpa [prefixWord, tailWord_2138961, baseEnd_2138961] using wordTrace_append hprefix tailTrace_2138961
  have hstable : (prefixWord ++ tailWord_2138961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2138961).length < 2 ^ (prefixWord ++ tailWord_2138961).sum := by decide
  have hdescent : baseEnd_2138961 < baseStart_2138961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2138961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139057 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 1, 3]
def baseStart_2139057 : Nat := 118140960795 + 2139057 * 2 ^ 59
def prefixEnd_2139057 : Nat := 4983230072969 + 3 ^ 40 * 2139057 * 2
def baseEnd_2139057 : Nat := 732242925576361775566775

theorem tailTrace_2139057 : CollatzResearch.WordTrace tailWord_2139057 prefixEnd_2139057 732242925576361775566775 := by
  unfold tailWord_2139057
  simp only [CollatzResearch.WordTrace]
  refine ⟨78017818211569285695951425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52011878807712857130634283 78017818211569285695951425)
  ·
    refine ⟨58513363658676964271963569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78017818211569285695951425 58513363658676964271963569)
    ·
      refine ⟨43885022744007723203972677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58513363658676964271963569 43885022744007723203972677)
      ·
        refine ⟨8228441764501448100744877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43885022744007723203972677 8228441764501448100744877)
        ·
          refine ⟨3085665661688043037779329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8228441764501448100744877 3085665661688043037779329)
          ·
            refine ⟨2314249246266032278334497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3085665661688043037779329 2314249246266032278334497)
            ·
              refine ⟨1735686934699524208750873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314249246266032278334497 1735686934699524208750873)
              ·
                refine ⟨1301765201024643156563155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735686934699524208750873 1301765201024643156563155)
                ·
                  refine ⟨1952647801536964734844733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301765201024643156563155 1952647801536964734844733)
                  ·
                    refine ⟨732242925576361775566775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952647801536964734844733 732242925576361775566775)
                    ·
                      rfl

theorem cell22_2139057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_2139057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139057 prefixEnd_2139057 := by exact prefixLift 2139057
  have htrace : WordTrace (prefixWord ++ tailWord_2139057) baseStart_2139057 baseEnd_2139057 := by
    simpa [prefixWord, tailWord_2139057, baseEnd_2139057] using wordTrace_append hprefix tailTrace_2139057
  have hstable : (prefixWord ++ tailWord_2139057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139057).length < 2 ^ (prefixWord ++ tailWord_2139057).sum := by decide
  have hdescent : baseEnd_2139057 < baseStart_2139057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139079 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2139079 : Nat := 118140960795 + 2139079 * 2 ^ 59
def prefixEnd_2139079 : Nat := 4983230072969 + 3 ^ 40 * 2139079 * 2
def baseEnd_2139079 : Nat := 732250456625961051516707

theorem tailTrace_2139079 : CollatzResearch.WordTrace tailWord_2139079 prefixEnd_2139079 732250456625961051516707 := by
  unfold tailWord_2139079
  simp only [CollatzResearch.WordTrace]
  refine ⟨78018620617489583453252291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52012413744993055635501527 78018620617489583453252291)
  ·
    refine ⟨117027930926234375179878437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78018620617489583453252291 117027930926234375179878437)
    ·
      refine ⟨21942737048668945346227207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117027930926234375179878437 21942737048668945346227207)
      ·
        refine ⟨32914105573003418019340811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21942737048668945346227207 32914105573003418019340811)
        ·
          refine ⟨49371158359505127029011217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32914105573003418019340811 49371158359505127029011217)
          ·
            refine ⟨37028368769628845271758413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49371158359505127029011217 37028368769628845271758413)
            ·
              refine ⟨13885638288610816976909405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37028368769628845271758413 13885638288610816976909405)
              ·
                refine ⟨5207114358229056366341027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13885638288610816976909405 5207114358229056366341027)
                ·
                  refine ⟨7810671537343584549511541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5207114358229056366341027 7810671537343584549511541)
                  ·
                    refine ⟨732250456625961051516707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7810671537343584549511541 732250456625961051516707)
                    ·
                      rfl

theorem cell22_2139079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2139079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139079 prefixEnd_2139079 := by exact prefixLift 2139079
  have htrace : WordTrace (prefixWord ++ tailWord_2139079) baseStart_2139079 baseEnd_2139079 := by
    simpa [prefixWord, tailWord_2139079, baseEnd_2139079] using wordTrace_append hprefix tailTrace_2139079
  have hstable : (prefixWord ++ tailWord_2139079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139079).length < 2 ^ (prefixWord ++ tailWord_2139079).sum := by decide
  have hdescent : baseEnd_2139079 < baseStart_2139079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139098 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_2139098 : Nat := 118140960795 + 2139098 * 2 ^ 59
def prefixEnd_2139098 : Nat := 4983230072969 + 3 ^ 40 * 2139098 * 2
def baseEnd_2139098 : Nat := 244085653571417111763883

theorem tailTrace_2139098 : CollatzResearch.WordTrace tailWord_2139098 prefixEnd_2139098 244085653571417111763883 := by
  unfold tailWord_2139098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19504828401105187424548487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52012875736280499798795965 19504828401105187424548487)
  ·
    refine ⟨29257242601657781136822731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19504828401105187424548487 29257242601657781136822731)
    ·
      refine ⟨43885863902486671705234097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29257242601657781136822731 43885863902486671705234097)
      ·
        refine ⟨32914397926865003778925573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43885863902486671705234097 32914397926865003778925573)
        ·
          refine ⟨6171449611287188208548545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32914397926865003778925573 6171449611287188208548545)
          ·
            refine ⟨4628587208465391156411409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6171449611287188208548545 4628587208465391156411409)
            ·
              refine ⟨3471440406349043367308557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628587208465391156411409 3471440406349043367308557)
              ·
                refine ⟨1301790152380891262740709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3471440406349043367308557 1301790152380891262740709)
                ·
                  refine ⟨244085653571417111763883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301790152380891262740709 244085653571417111763883)
                  ·
                    rfl

theorem cell22_2139098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_2139098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139098 prefixEnd_2139098 := by exact prefixLift 2139098
  have htrace : WordTrace (prefixWord ++ tailWord_2139098) baseStart_2139098 baseEnd_2139098 := by
    simpa [prefixWord, tailWord_2139098, baseEnd_2139098] using wordTrace_append hprefix tailTrace_2139098
  have hstable : (prefixWord ++ tailWord_2139098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139098).length < 2 ^ (prefixWord ++ tailWord_2139098).sum := by decide
  have hdescent : baseEnd_2139098 < baseStart_2139098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139141 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_2139141 : Nat := 118140960795 + 2139141 * 2 ^ 59
def prefixEnd_2139141 : Nat := 4983230072969 + 3 ^ 40 * 2139141 * 2
def baseEnd_2139141 : Nat := 732271680493013556466517

theorem tailTrace_2139141 : CollatzResearch.WordTrace tailWord_2139141 prefixEnd_2139141 732271680493013556466517 := by
  unfold tailWord_2139141
  simp only [CollatzResearch.WordTrace]
  refine ⟨78020881943264968042009277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52013921295509978694672851 78020881943264968042009277)
  ·
    refine ⟨29257830728724363015753479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78020881943264968042009277 29257830728724363015753479)
    ·
      refine ⟨43886746093086544523630219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29257830728724363015753479 43886746093086544523630219)
      ·
        refine ⟨65830119139629816785445329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43886746093086544523630219 65830119139629816785445329)
        ·
          refine ⟨49372589354722362589083997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65830119139629816785445329 49372589354722362589083997)
          ·
            refine ⟨18514721008020885970906499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49372589354722362589083997 18514721008020885970906499)
            ·
              refine ⟨27772081512031328956359749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18514721008020885970906499 27772081512031328956359749)
              ·
                refine ⟨5207265283505874179317453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27772081512031328956359749 5207265283505874179317453)
                ·
                  refine ⟨1952724481314702817244045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5207265283505874179317453 1952724481314702817244045)
                  ·
                    refine ⟨732271680493013556466517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952724481314702817244045 732271680493013556466517)
                    ·
                      rfl

theorem cell22_2139141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_2139141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139141 prefixEnd_2139141 := by exact prefixLift 2139141
  have htrace : WordTrace (prefixWord ++ tailWord_2139141) baseStart_2139141 baseEnd_2139141 := by
    simpa [prefixWord, tailWord_2139141, baseEnd_2139141] using wordTrace_append hprefix tailTrace_2139141
  have hstable : (prefixWord ++ tailWord_2139141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139141).length < 2 ^ (prefixWord ++ tailWord_2139141).sum := by decide
  have hdescent : baseEnd_2139141 < baseStart_2139141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139175 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2139175 : Nat := 118140960795 + 2139175 * 2 ^ 59
def prefixEnd_2139175 : Nat := 4983230072969 + 3 ^ 40 * 2139175 * 2
def baseEnd_2139175 : Nat := 732283319387848801116413

theorem tailTrace_2139175 : CollatzResearch.WordTrace tailWord_2139175 prefixEnd_2139175 732283319387848801116413 := by
  unfold tailWord_2139175
  simp only [CollatzResearch.WordTrace]
  refine ⟨78022122025141791848746979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52014748016761194565831319 78022122025141791848746979)
  ·
    refine ⟨117033183037712687773120469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78022122025141791848746979 117033183037712687773120469)
    ·
      refine ⟨2742965227446391119682511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 117033183037712687773120469 2742965227446391119682511)
      ·
        refine ⟨4114447841169586679523767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742965227446391119682511 4114447841169586679523767)
        ·
          refine ⟨6171671761754380019285651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114447841169586679523767 6171671761754380019285651)
          ·
            refine ⟨9257507642631570028928477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6171671761754380019285651 9257507642631570028928477)
            ·
              refine ⟨3471565365986838760848179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9257507642631570028928477 3471565365986838760848179)
              ·
                refine ⟨5207348048980258141272269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471565365986838760848179 5207348048980258141272269)
                ·
                  refine ⟨1952755518367596802977101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5207348048980258141272269 1952755518367596802977101)
                  ·
                    refine ⟨732283319387848801116413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952755518367596802977101 732283319387848801116413)
                    ·
                      rfl

theorem cell22_2139175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2139175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139175 prefixEnd_2139175 := by exact prefixLift 2139175
  have htrace : WordTrace (prefixWord ++ tailWord_2139175) baseStart_2139175 baseEnd_2139175 := by
    simpa [prefixWord, tailWord_2139175, baseEnd_2139175] using wordTrace_append hprefix tailTrace_2139175
  have hstable : (prefixWord ++ tailWord_2139175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139175).length < 2 ^ (prefixWord ++ tailWord_2139175).sum := by decide
  have hdescent : baseEnd_2139175 < baseStart_2139175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139199 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 8]
def baseStart_2139199 : Nat := 118140960795 + 2139199 * 2 ^ 59
def prefixEnd_2139199 : Nat := 4983230072969 + 3 ^ 40 * 2139199 * 2
def baseEnd_2139199 : Nat := 244097178359440246172113

theorem tailTrace_2139199 : CollatzResearch.WordTrace tailWord_2139199 prefixEnd_2139199 244097178359440246172113 := by
  unfold tailWord_2139199
  simp only [CollatzResearch.WordTrace]
  refine ⟨78022997377054843947620651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52015331584703229298413767 78022997377054843947620651)
  ·
    refine ⟨117034496065582265921430977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78022997377054843947620651 117034496065582265921430977)
    ·
      refine ⟨87775872049186699441073233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117034496065582265921430977 87775872049186699441073233)
      ·
        refine ⟨65831904036890024580804925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87775872049186699441073233 65831904036890024580804925)
        ·
          refine ⟨24686964013833759217801847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65831904036890024580804925 24686964013833759217801847)
          ·
            refine ⟨37030446020750638826702771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24686964013833759217801847 37030446020750638826702771)
            ·
              refine ⟨55545669031125958240054157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37030446020750638826702771 55545669031125958240054157)
              ·
                refine ⟨20829625886672234340020309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55545669031125958240054157 20829625886672234340020309)
                ·
                  refine ⟨244097178359440246172113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20829625886672234340020309 244097178359440246172113)
                  ·
                    rfl

theorem cell22_2139199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_2139199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139199 prefixEnd_2139199 := by exact prefixLift 2139199
  have htrace : WordTrace (prefixWord ++ tailWord_2139199) baseStart_2139199 baseEnd_2139199 := by
    simpa [prefixWord, tailWord_2139199, baseEnd_2139199] using wordTrace_append hprefix tailTrace_2139199
  have hstable : (prefixWord ++ tailWord_2139199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139199).length < 2 ^ (prefixWord ++ tailWord_2139199).sum := by decide
  have hdescent : baseEnd_2139199 < baseStart_2139199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139222 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2139222 : Nat := 118140960795 + 2139222 * 2 ^ 59
def prefixEnd_2139222 : Nat := 4983230072969 + 3 ^ 40 * 2139222 * 2
def baseEnd_2139222 : Nat := 244099802816118781730423

theorem tailTrace_2139222 : CollatzResearch.WordTrace tailWord_2139222 prefixEnd_2139222 244099802816118781730423 := by
  unfold tailWord_2139222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876489765998219929731745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52015890837314345917138613 4876489765998219929731745)
  ·
    refine ⟨3657367324498664947298809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4876489765998219929731745 3657367324498664947298809)
    ·
      refine ⟨2743025493373998710474107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3657367324498664947298809 2743025493373998710474107)
      ·
        refine ⟨4114538240060998065711161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743025493373998710474107 4114538240060998065711161)
        ·
          refine ⟨3085903680045748549283371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4114538240060998065711161 3085903680045748549283371)
          ·
            refine ⟨4628855520068622823925057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3085903680045748549283371 4628855520068622823925057)
            ·
              refine ⟨3471641640051467117943793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628855520068622823925057 3471641640051467117943793)
              ·
                refine ⟨2603731230038600338457845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3471641640051467117943793 2603731230038600338457845)
                ·
                  refine ⟨244099802816118781730423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2603731230038600338457845 244099802816118781730423)
                  ·
                    rfl

theorem cell22_2139222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2139222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139222 prefixEnd_2139222 := by exact prefixLift 2139222
  have htrace : WordTrace (prefixWord ++ tailWord_2139222) baseStart_2139222 baseEnd_2139222 := by
    simpa [prefixWord, tailWord_2139222, baseEnd_2139222] using wordTrace_append hprefix tailTrace_2139222
  have hstable : (prefixWord ++ tailWord_2139222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139222).length < 2 ^ (prefixWord ++ tailWord_2139222).sum := by decide
  have hdescent : baseEnd_2139222 < baseStart_2139222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139248 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_2139248 : Nat := 118140960795 + 2139248 * 2 ^ 59
def prefixEnd_2139248 : Nat := 4983230072969 + 3 ^ 40 * 2139248 * 2
def baseEnd_2139248 : Nat := 732308308779700944041189

theorem tailTrace_2139248 : CollatzResearch.WordTrace tailWord_2139248 prefixEnd_2139248 732308308779700944041189 := by
  unfold tailWord_2139248
  simp only [CollatzResearch.WordTrace]
  refine ⟨39012392276938662658077199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52016523035918216877436265 39012392276938662658077199)
  ·
    refine ⟨58518588415407993987115799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39012392276938662658077199 58518588415407993987115799)
    ·
      refine ⟨87777882623111990980673699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58518588415407993987115799 87777882623111990980673699)
      ·
        refine ⟨131666823934667986471010549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87777882623111990980673699 131666823934667986471010549)
        ·
          refine ⟨12343764743875123731657239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131666823934667986471010549 12343764743875123731657239)
          ·
            refine ⟨18515647115812685597485859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12343764743875123731657239 18515647115812685597485859)
            ·
              refine ⟨27773470673719028396228789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18515647115812685597485859 27773470673719028396228789)
              ·
                refine ⟨2603762875661158912146449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27773470673719028396228789 2603762875661158912146449)
                ·
                  refine ⟨1952822156745869184109837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603762875661158912146449 1952822156745869184109837)
                  ·
                    refine ⟨732308308779700944041189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952822156745869184109837 732308308779700944041189)
                    ·
                      rfl

theorem cell22_2139248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_2139248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139248 prefixEnd_2139248 := by exact prefixLift 2139248
  have htrace : WordTrace (prefixWord ++ tailWord_2139248) baseStart_2139248 baseEnd_2139248 := by
    simpa [prefixWord, tailWord_2139248, baseEnd_2139248] using wordTrace_append hprefix tailTrace_2139248
  have hstable : (prefixWord ++ tailWord_2139248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139248).length < 2 ^ (prefixWord ++ tailWord_2139248).sum := by decide
  have hdescent : baseEnd_2139248 < baseStart_2139248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139282 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2139282 : Nat := 118140960795 + 2139282 * 2 ^ 59
def prefixEnd_2139282 : Nat := 4983230072969 + 3 ^ 40 * 2139282 * 2
def baseEnd_2139282 : Nat := 732319947674536188691085

theorem tailTrace_2139282 : CollatzResearch.WordTrace tailWord_2139282 prefixEnd_2139282 732319947674536188691085 := by
  unfold tailWord_2139282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506506158938537280723025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52017349757169432748594733 19506506158938537280723025)
  ·
    refine ⟨14629879619203902960542269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19506506158938537280723025 14629879619203902960542269)
    ·
      refine ⟨5486204857201463610203351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14629879619203902960542269 5486204857201463610203351)
      ·
        refine ⟨8229307285802195415305027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5486204857201463610203351 8229307285802195415305027)
        ·
          refine ⟨12343960928703293122957541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8229307285802195415305027 12343960928703293122957541)
          ·
            refine ⟨2314492674131867460554539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12343960928703293122957541 2314492674131867460554539)
            ·
              refine ⟨3471739011197801190831809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314492674131867460554539 3471739011197801190831809)
              ·
                refine ⟨2603804258398350893123857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3471739011197801190831809 2603804258398350893123857)
                ·
                  refine ⟨1952853193798763169842893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2603804258398350893123857 1952853193798763169842893)
                  ·
                    refine ⟨732319947674536188691085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1952853193798763169842893 732319947674536188691085)
                    ·
                      rfl

theorem cell22_2139282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2139282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139282 prefixEnd_2139282 := by exact prefixLift 2139282
  have htrace : WordTrace (prefixWord ++ tailWord_2139282) baseStart_2139282 baseEnd_2139282 := by
    simpa [prefixWord, tailWord_2139282, baseEnd_2139282] using wordTrace_append hprefix tailTrace_2139282
  have hstable : (prefixWord ++ tailWord_2139282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139282).length < 2 ^ (prefixWord ++ tailWord_2139282).sum := by decide
  have hdescent : baseEnd_2139282 < baseStart_2139282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139370 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2139370 : Nat := 118140960795 + 2139370 * 2 ^ 59
def prefixEnd_2139370 : Nat := 4983230072969 + 3 ^ 40 * 2139370 * 2
def baseEnd_2139370 : Nat := 732350071872933292490815

theorem tailTrace_2139370 : CollatzResearch.WordTrace tailWord_2139370 prefixEnd_2139370 732350071872933292490815 := by
  unfold tailWord_2139370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507308564858835038023891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52019489506290226768063709 19507308564858835038023891)
  ·
    refine ⟨29260962847288252557035837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19507308564858835038023891 29260962847288252557035837)
    ·
      refine ⟨10972861067733094708888439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29260962847288252557035837 10972861067733094708888439)
      ·
        refine ⟨16459291601599642063332659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10972861067733094708888439 16459291601599642063332659)
        ·
          refine ⟨24688937402399463094998989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16459291601599642063332659 24688937402399463094998989)
          ·
            refine ⟨9258351525899798660624621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24688937402399463094998989 9258351525899798660624621)
            ·
              refine ⟨3471881822212424497734233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9258351525899798660624621 3471881822212424497734233)
              ·
                refine ⟨2603911366659318373300675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3471881822212424497734233 2603911366659318373300675)
                ·
                  refine ⟨3905867049988977559951013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2603911366659318373300675 3905867049988977559951013)
                  ·
                    refine ⟨732350071872933292490815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905867049988977559951013 732350071872933292490815)
                    ·
                      rfl

theorem cell22_2139370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2139370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139370 prefixEnd_2139370 := by exact prefixLift 2139370
  have htrace : WordTrace (prefixWord ++ tailWord_2139370) baseStart_2139370 baseEnd_2139370 := by
    simpa [prefixWord, tailWord_2139370, baseEnd_2139370] using wordTrace_append hprefix tailTrace_2139370
  have hstable : (prefixWord ++ tailWord_2139370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139370).length < 2 ^ (prefixWord ++ tailWord_2139370).sum := by decide
  have hdescent : baseEnd_2139370 < baseStart_2139370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139411 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_2139411 : Nat := 118140960795 + 2139411 * 2 ^ 59
def prefixEnd_2139411 : Nat := 4983230072969 + 3 ^ 40 * 2139411 * 2
def baseEnd_2139411 : Nat := 732364107010822852215689

theorem tailTrace_2139411 : CollatzResearch.WordTrace tailWord_2139411 prefixEnd_2139411 732364107010822852215689 := by
  unfold tailWord_2139411
  simp only [CollatzResearch.WordTrace]
  refine ⟨78030729652286804154338087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52020486434857869436225391 78030729652286804154338087)
  ·
    refine ⟨117046094478430206231507131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78030729652286804154338087 117046094478430206231507131)
    ·
      refine ⟨175569141717645309347260697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117046094478430206231507131 175569141717645309347260697)
      ·
        refine ⟨131676856288233982010445523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175569141717645309347260697 131676856288233982010445523)
        ·
          refine ⟨197515284432350973015668285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131676856288233982010445523 197515284432350973015668285)
          ·
            refine ⟨74068231662131614880875607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197515284432350973015668285 74068231662131614880875607)
            ·
              refine ⟨111102347493197422321313411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74068231662131614880875607 111102347493197422321313411)
              ·
                refine ⟨166653521239796133481970117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111102347493197422321313411 166653521239796133481970117)
                ·
                  refine ⟨31247535232461775027869397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166653521239796133481970117 31247535232461775027869397)
                  ·
                    refine ⟨732364107010822852215689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31247535232461775027869397 732364107010822852215689)
                    ·
                      rfl

theorem cell22_2139411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_2139411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139411 prefixEnd_2139411 := by exact prefixLift 2139411
  have htrace : WordTrace (prefixWord ++ tailWord_2139411) baseStart_2139411 baseEnd_2139411 := by
    simpa [prefixWord, tailWord_2139411, baseEnd_2139411] using wordTrace_append hprefix tailTrace_2139411
  have hstable : (prefixWord ++ tailWord_2139411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139411).length < 2 ^ (prefixWord ++ tailWord_2139411).sum := by decide
  have hdescent : baseEnd_2139411 < baseStart_2139411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139432 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2139432 : Nat := 118140960795 + 2139432 * 2 ^ 59
def prefixEnd_2139432 : Nat := 4983230072969 + 3 ^ 40 * 2139432 * 2
def baseEnd_2139432 : Nat := 732371295739985797440625

theorem tailTrace_2139432 : CollatzResearch.WordTrace tailWord_2139432 prefixEnd_2139432 732371295739985797440625 := by
  unfold tailWord_2139432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39015747792605362370426275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52020997056807149827235033 39015747792605362370426275)
  ·
    refine ⟨58523621688908043555639413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39015747792605362370426275 58523621688908043555639413)
    ·
      refine ⟨5486589533335129083341195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58523621688908043555639413 5486589533335129083341195)
      ·
        refine ⟨8229884300002693625011793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5486589533335129083341195 8229884300002693625011793)
        ·
          refine ⟨6172413225002020218758845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8229884300002693625011793 6172413225002020218758845)
          ·
            refine ⟨2314654959375757582034567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6172413225002020218758845 2314654959375757582034567)
            ·
              refine ⟨3471982439063636373051851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314654959375757582034567 3471982439063636373051851)
              ·
                refine ⟨5207973658595454559577777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3471982439063636373051851 5207973658595454559577777)
                ·
                  refine ⟨3905980243946590919683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5207973658595454559577777 3905980243946590919683333)
                  ·
                    refine ⟨732371295739985797440625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3905980243946590919683333 732371295739985797440625)
                    ·
                      rfl

theorem cell22_2139432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2139432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139432 prefixEnd_2139432 := by exact prefixLift 2139432
  have htrace : WordTrace (prefixWord ++ tailWord_2139432) baseStart_2139432 baseEnd_2139432 := by
    simpa [prefixWord, tailWord_2139432, baseEnd_2139432] using wordTrace_append hprefix tailTrace_2139432
  have hstable : (prefixWord ++ tailWord_2139432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139432).length < 2 ^ (prefixWord ++ tailWord_2139432).sum := by decide
  have hdescent : baseEnd_2139432 < baseStart_2139432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139473 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2139473 : Nat := 118140960795 + 2139473 * 2 ^ 59
def prefixEnd_2139473 : Nat := 4983230072969 + 3 ^ 40 * 2139473 * 2
def baseEnd_2139473 : Nat := 732385330877875357165499

theorem tailTrace_2139473 : CollatzResearch.WordTrace tailWord_2139473 prefixEnd_2139473 732385330877875357165499 := by
  unfold tailWord_2139473
  simp only [CollatzResearch.WordTrace]
  refine ⟨78032990978062188743095073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52021993985374792495396715 78032990978062188743095073)
  ·
    refine ⟨58524743233546641557321305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78032990978062188743095073 58524743233546641557321305)
    ·
      refine ⟨43893557425159981167990979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58524743233546641557321305 43893557425159981167990979)
      ·
        refine ⟨65840336137739971751986469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43893557425159981167990979 65840336137739971751986469)
        ·
          refine ⟨12345063025826244703497463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65840336137739971751986469 12345063025826244703497463)
          ·
            refine ⟨18517594538739367055246195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12345063025826244703497463 18517594538739367055246195)
            ·
              refine ⟨27776391808109050582869293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18517594538739367055246195 27776391808109050582869293)
              ·
                refine ⟨10416146928040893968575985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27776391808109050582869293 10416146928040893968575985)
                ·
                  refine ⟨7812110196030670476431989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10416146928040893968575985 7812110196030670476431989)
                  ·
                    refine ⟨732385330877875357165499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7812110196030670476431989 732385330877875357165499)
                    ·
                      rfl

theorem cell22_2139473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2139473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139473 prefixEnd_2139473 := by exact prefixLift 2139473
  have htrace : WordTrace (prefixWord ++ tailWord_2139473) baseStart_2139473 baseEnd_2139473 := by
    simpa [prefixWord, tailWord_2139473, baseEnd_2139473] using wordTrace_append hprefix tailTrace_2139473
  have hstable : (prefixWord ++ tailWord_2139473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139473).length < 2 ^ (prefixWord ++ tailWord_2139473).sum := by decide
  have hdescent : baseEnd_2139473 < baseStart_2139473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139475 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 5]
def baseStart_2139475 : Nat := 118140960795 + 2139475 * 2 ^ 59
def prefixEnd_2139475 : Nat := 4983230072969 + 3 ^ 40 * 2139475 * 2
def baseEnd_2139475 : Nat := 244128671839582672871831

theorem tailTrace_2139475 : CollatzResearch.WordTrace tailWord_2139475 prefixEnd_2139475 244128671839582672871831 := by
  unfold tailWord_2139475
  simp only [CollatzResearch.WordTrace]
  refine ⟨78033063924054943084667879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52022042616036628723111919 78033063924054943084667879)
  ·
    refine ⟨117049595886082414627001819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78033063924054943084667879 117049595886082414627001819)
    ·
      refine ⟨175574393829123621940502729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117049595886082414627001819 175574393829123621940502729)
      ·
        refine ⟨131680795371842716455377047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175574393829123621940502729 131680795371842716455377047)
        ·
          refine ⟨197521193057764074683065571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131680795371842716455377047 197521193057764074683065571)
          ·
            refine ⟨296281789586646112024598357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197521193057764074683065571 296281789586646112024598357)
            ·
              refine ⟨1736026110859254562644131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 296281789586646112024598357 1736026110859254562644131)
              ·
                refine ⟨2604039166288881843966197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736026110859254562644131 2604039166288881843966197)
                ·
                  refine ⟨244128671839582672871831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2604039166288881843966197 244128671839582672871831)
                  ·
                    rfl

theorem cell22_2139475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 5].length) (baseStart_2139475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139475 prefixEnd_2139475 := by exact prefixLift 2139475
  have htrace : WordTrace (prefixWord ++ tailWord_2139475) baseStart_2139475 baseEnd_2139475 := by
    simpa [prefixWord, tailWord_2139475, baseEnd_2139475] using wordTrace_append hprefix tailTrace_2139475
  have hstable : (prefixWord ++ tailWord_2139475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139475).length < 2 ^ (prefixWord ++ tailWord_2139475).sum := by decide
  have hdescent : baseEnd_2139475 < baseStart_2139475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139496 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2139496 : Nat := 118140960795 + 2139496 * 2 ^ 59
def prefixEnd_2139496 : Nat := 4983230072969 + 3 ^ 40 * 2139496 * 2
def baseEnd_2139496 : Nat := 732393204247910963840429

theorem tailTrace_2139496 : CollatzResearch.WordTrace tailWord_2139496 prefixEnd_2139496 732393204247910963840429 := by
  unfold tailWord_2139496
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016914928489431835591171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52022553237985909114121561 39016914928489431835591171)
  ·
    refine ⟨58525372392734147753386757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39016914928489431835591171 58525372392734147753386757)
    ·
      refine ⟨10973507323637652703760017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58525372392734147753386757 10973507323637652703760017)
      ·
        refine ⟨8230130492728239527820013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10973507323637652703760017 8230130492728239527820013)
        ·
          refine ⟨3086298934773089822932505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8230130492728239527820013 3086298934773089822932505)
          ·
            refine ⟨2314724201079817367199379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3086298934773089822932505 2314724201079817367199379)
            ·
              refine ⟨3472086301619726050799069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314724201079817367199379 3472086301619726050799069)
              ·
                refine ⟨1302032363107397269049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3472086301619726050799069 1302032363107397269049651)
                ·
                  refine ⟨1953048544661095903574477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302032363107397269049651 1953048544661095903574477)
                  ·
                    refine ⟨732393204247910963840429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953048544661095903574477 732393204247910963840429)
                    ·
                      rfl

theorem cell22_2139496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2139496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139496 prefixEnd_2139496 := by exact prefixLift 2139496
  have htrace : WordTrace (prefixWord ++ tailWord_2139496) baseStart_2139496 baseEnd_2139496 := by
    simpa [prefixWord, tailWord_2139496, baseEnd_2139496] using wordTrace_append hprefix tailTrace_2139496
  have hstable : (prefixWord ++ tailWord_2139496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139496).length < 2 ^ (prefixWord ++ tailWord_2139496).sum := by decide
  have hdescent : baseEnd_2139496 < baseStart_2139496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139505 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_2139505 : Nat := 118140960795 + 2139505 * 2 ^ 59
def prefixEnd_2139505 : Nat := 4983230072969 + 3 ^ 40 * 2139505 * 2
def baseEnd_2139505 : Nat := 732396285131837940365401

theorem tailTrace_2139505 : CollatzResearch.WordTrace tailWord_2139505 prefixEnd_2139505 732396285131837940365401 := by
  unfold tailWord_2139505
  simp only [CollatzResearch.WordTrace]
  refine ⟨78034158113946258208259969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52022772075964172138839979 78034158113946258208259969)
  ·
    refine ⟨58525618585459693656194977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78034158113946258208259969 58525618585459693656194977)
    ·
      refine ⟨43894213939094770242146233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58525618585459693656194977 43894213939094770242146233)
      ·
        refine ⟨32920660454321077681609675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43894213939094770242146233 32920660454321077681609675)
        ·
          refine ⟨49380990681481616522414513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32920660454321077681609675 49380990681481616522414513)
          ·
            refine ⟨37035743011111212391810885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49380990681481616522414513 37035743011111212391810885)
            ·
              refine ⟨6944201814583352323464541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37035743011111212391810885 6944201814583352323464541)
              ·
                refine ⟨2604075680468757121299203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6944201814583352323464541 2604075680468757121299203)
                ·
                  refine ⟨3906113520703135681948805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604075680468757121299203 3906113520703135681948805)
                  ·
                    refine ⟨732396285131837940365401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906113520703135681948805 732396285131837940365401)
                    ·
                      rfl

theorem cell22_2139505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_2139505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139505 prefixEnd_2139505 := by exact prefixLift 2139505
  have htrace : WordTrace (prefixWord ++ tailWord_2139505) baseStart_2139505 baseEnd_2139505 := by
    simpa [prefixWord, tailWord_2139505, baseEnd_2139505] using wordTrace_append hprefix tailTrace_2139505
  have hstable : (prefixWord ++ tailWord_2139505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139505).length < 2 ^ (prefixWord ++ tailWord_2139505).sum := by decide
  have hdescent : baseEnd_2139505 < baseStart_2139505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139520 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_2139520 : Nat := 118140960795 + 2139520 * 2 ^ 59
def prefixEnd_2139520 : Nat := 4983230072969 + 3 ^ 40 * 2139520 * 2
def baseEnd_2139520 : Nat := 244133806646127633746785

theorem tailTrace_2139520 : CollatzResearch.WordTrace tailWord_2139520 prefixEnd_2139520 244133806646127633746785 := by
  unfold tailWord_2139520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39017352604445957885028007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52023136805927943846704009 39017352604445957885028007)
  ·
    refine ⟨58526028906668936827542011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39017352604445957885028007 58526028906668936827542011)
    ·
      refine ⟨87789043360003405241313017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58526028906668936827542011 87789043360003405241313017)
      ·
        refine ⟨65841782520002553930984763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87789043360003405241313017 65841782520002553930984763)
        ·
          refine ⟨98762673780003830896477145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65841782520002553930984763 98762673780003830896477145)
          ·
            refine ⟨74072005335002873172357859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98762673780003830896477145 74072005335002873172357859)
            ·
              refine ⟨111108008002504309758536789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74072005335002873172357859 111108008002504309758536789)
              ·
                refine ⟨1302046968779347379982853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 111108008002504309758536789 1302046968779347379982853)
                ·
                  refine ⟨244133806646127633746785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302046968779347379982853 244133806646127633746785)
                  ·
                    rfl

theorem cell22_2139520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_2139520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139520 prefixEnd_2139520 := by exact prefixLift 2139520
  have htrace : WordTrace (prefixWord ++ tailWord_2139520) baseStart_2139520 baseEnd_2139520 := by
    simpa [prefixWord, tailWord_2139520, baseEnd_2139520] using wordTrace_append hprefix tailTrace_2139520
  have hstable : (prefixWord ++ tailWord_2139520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139520).length < 2 ^ (prefixWord ++ tailWord_2139520).sum := by decide
  have hdescent : baseEnd_2139520 < baseStart_2139520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139565 : List Nat := [1, 5, 2, 2, 1, 11]
def baseStart_2139565 : Nat := 118140960795 + 2139565 * 2 ^ 59
def prefixEnd_2139565 : Nat := 4983230072969 + 3 ^ 40 * 2139565 * 2
def baseEnd_2139565 : Nat := 9042183016765651652657

theorem tailTrace_2139565 : CollatzResearch.WordTrace tailWord_2139565 prefixEnd_2139565 9042183016765651652657 := by
  unfold tailWord_2139565
  simp only [CollatzResearch.WordTrace]
  refine ⟨78036346493728888455444149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52024230995819258970296099 78036346493728888455444149)
  ·
    refine ⟨7315907483787083292697889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78036346493728888455444149 7315907483787083292697889)
    ·
      refine ⟨5486930612840312469523417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7315907483787083292697889 5486930612840312469523417)
      ·
        refine ⟨4115197959630234352142563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5486930612840312469523417 4115197959630234352142563)
        ·
          refine ⟨6172796939445351528213845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115197959630234352142563 6172796939445351528213845)
          ·
            refine ⟨9042183016765651652657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6172796939445351528213845 9042183016765651652657)
            ·
              rfl

theorem cell22_2139565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 11].length) (baseStart_2139565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139565 prefixEnd_2139565 := by exact prefixLift 2139565
  have htrace : WordTrace (prefixWord ++ tailWord_2139565) baseStart_2139565 baseEnd_2139565 := by
    simpa [prefixWord, tailWord_2139565, baseEnd_2139565] using wordTrace_append hprefix tailTrace_2139565
  have hstable : (prefixWord ++ tailWord_2139565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139565).length < 2 ^ (prefixWord ++ tailWord_2139565).sum := by decide
  have hdescent : baseEnd_2139565 < baseStart_2139565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139593 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 9]
def baseStart_2139593 : Nat := 118140960795 + 2139593 * 2 ^ 59
def prefixEnd_2139593 : Nat := 4983230072969 + 3 ^ 40 * 2139593 * 2
def baseEnd_2139593 : Nat := 244142136443411681388377

theorem tailTrace_2139593 : CollatzResearch.WordTrace tailWord_2139593 prefixEnd_2139593 244142136443411681388377 := by
  unfold tailWord_2139593
  simp only [CollatzResearch.WordTrace]
  refine ⟨78037367737627449237463433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52024911825084966158308955 78037367737627449237463433)
  ·
    refine ⟨58528025803220586928097575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78037367737627449237463433 58528025803220586928097575)
    ·
      refine ⟨87792038704830880392146363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58528025803220586928097575 87792038704830880392146363)
      ·
        refine ⟨131688058057246320588219545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87792038704830880392146363 131688058057246320588219545)
        ·
          refine ⟨98766043542934740441164659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131688058057246320588219545 98766043542934740441164659)
          ·
            refine ⟨148149065314402110661746989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98766043542934740441164659 148149065314402110661746989)
            ·
              refine ⟨55555899492900791498155121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148149065314402110661746989 55555899492900791498155121)
              ·
                refine ⟨41666924619675593623616341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55555899492900791498155121 41666924619675593623616341)
                ·
                  refine ⟨244142136443411681388377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41666924619675593623616341 244142136443411681388377)
                  ·
                    rfl

theorem cell22_2139593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_2139593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139593 prefixEnd_2139593 := by exact prefixLift 2139593
  have htrace : WordTrace (prefixWord ++ tailWord_2139593) baseStart_2139593 baseEnd_2139593 := by
    simpa [prefixWord, tailWord_2139593, baseEnd_2139593] using wordTrace_append hprefix tailTrace_2139593
  have hstable : (prefixWord ++ tailWord_2139593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139593).length < 2 ^ (prefixWord ++ tailWord_2139593).sum := by decide
  have hdescent : baseEnd_2139593 < baseStart_2139593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139657 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_2139657 : Nat := 118140960795 + 2139657 * 2 ^ 59
def prefixEnd_2139657 : Nat := 4983230072969 + 3 ^ 40 * 2139657 * 2
def baseEnd_2139657 : Nat := 732448317838160210564935

theorem tailTrace_2139657 : CollatzResearch.WordTrace tailWord_2139657 prefixEnd_2139657 732448317838160210564935 := by
  unfold tailWord_2139657
  simp only [CollatzResearch.WordTrace]
  refine ⟨78039702009395588167793225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52026468006263725445195483 78039702009395588167793225)
  ·
    refine ⟨58529776507046691125844919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78039702009395588167793225 58529776507046691125844919)
    ·
      refine ⟨87794664760570036688767379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58529776507046691125844919 87794664760570036688767379)
      ·
        refine ⟨131691997140855055033151069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87794664760570036688767379 131691997140855055033151069)
        ·
          refine ⟨49384498927820645637431651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131691997140855055033151069 49384498927820645637431651)
          ·
            refine ⟨74076748391730968456147477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49384498927820645637431651 74076748391730968456147477)
            ·
              refine ⟨3472347580862389146381913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74076748391730968456147477 3472347580862389146381913)
              ·
                refine ⟨2604260685646791859786435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3472347580862389146381913 2604260685646791859786435)
                ·
                  refine ⟨3906391028470187789679653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2604260685646791859786435 3906391028470187789679653)
                  ·
                    refine ⟨732448317838160210564935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906391028470187789679653 732448317838160210564935)
                    ·
                      rfl

theorem cell22_2139657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_2139657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139657 prefixEnd_2139657 := by exact prefixLift 2139657
  have htrace : WordTrace (prefixWord ++ tailWord_2139657) baseStart_2139657 baseEnd_2139657 := by
    simpa [prefixWord, tailWord_2139657, baseEnd_2139657] using wordTrace_append hprefix tailTrace_2139657
  have hstable : (prefixWord ++ tailWord_2139657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139657).length < 2 ^ (prefixWord ++ tailWord_2139657).sum := by decide
  have hdescent : baseEnd_2139657 < baseStart_2139657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139704 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_2139704 : Nat := 118140960795 + 2139704 * 2 ^ 59
def prefixEnd_2139704 : Nat := 4983230072969 + 3 ^ 40 * 2139704 * 2
def baseEnd_2139704 : Nat := 732464406898667754639791

theorem tailTrace_2139704 : CollatzResearch.WordTrace tailWord_2139704 prefixEnd_2139704 732464406898667754639791 := by
  unfold tailWord_2139704
  simp only [CollatzResearch.WordTrace]
  refine ⟨39020708120112657597377083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52027610826816876796502777 39020708120112657597377083)
  ·
    refine ⟨58531062180168986396065625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39020708120112657597377083 58531062180168986396065625)
    ·
      refine ⟨43898296635126739797049219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58531062180168986396065625 43898296635126739797049219)
      ·
        refine ⟨65847444952690109695573829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43898296635126739797049219 65847444952690109695573829)
        ·
          refine ⟨12346395928629395567920093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65847444952690109695573829 12346395928629395567920093)
          ·
            refine ⟨4629898473236023337970035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12346395928629395567920093 4629898473236023337970035)
            ·
              refine ⟨6944847709854035006955053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4629898473236023337970035 6944847709854035006955053)
              ·
                refine ⟨2604317891195263127608145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6944847709854035006955053 2604317891195263127608145)
                ·
                  refine ⟨1953238418396447345706109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604317891195263127608145 1953238418396447345706109)
                  ·
                    refine ⟨732464406898667754639791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953238418396447345706109 732464406898667754639791)
                    ·
                      rfl

theorem cell22_2139704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_2139704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139704 prefixEnd_2139704 := by exact prefixLift 2139704
  have htrace : WordTrace (prefixWord ++ tailWord_2139704) baseStart_2139704 baseEnd_2139704 := by
    simpa [prefixWord, tailWord_2139704, baseEnd_2139704] using wordTrace_append hprefix tailTrace_2139704
  have hstable : (prefixWord ++ tailWord_2139704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139704).length < 2 ^ (prefixWord ++ tailWord_2139704).sum := by decide
  have hdescent : baseEnd_2139704 < baseStart_2139704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139719 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2139719 : Nat := 118140960795 + 2139719 * 2 ^ 59
def prefixEnd_2139719 : Nat := 4983230072969 + 3 ^ 40 * 2139719 * 2
def baseEnd_2139719 : Nat := 732469541705212715514745

theorem tailTrace_2139719 : CollatzResearch.WordTrace tailWord_2139719 prefixEnd_2139719 732469541705212715514745 := by
  unfold tailWord_2139719
  simp only [CollatzResearch.WordTrace]
  refine ⟨78041963335170972756550211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52027975556780648504366807 78041963335170972756550211)
  ·
    refine ⟨117062945002756459134825317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78041963335170972756550211 117062945002756459134825317)
    ·
      refine ⟨21949302188016836087779747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117062945002756459134825317 21949302188016836087779747)
      ·
        refine ⟨32923953282025254131669621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21949302188016836087779747 32923953282025254131669621)
        ·
          refine ⟨3086620620189867574844027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32923953282025254131669621 3086620620189867574844027)
          ·
            refine ⟨4629930930284801362266041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086620620189867574844027 4629930930284801362266041)
            ·
              refine ⟨3472448197713601021699531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4629930930284801362266041 3472448197713601021699531)
              ·
                refine ⟨5208672296570401532549297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3472448197713601021699531 5208672296570401532549297)
                ·
                  refine ⟨3906504222427801149411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5208672296570401532549297 3906504222427801149411973)
                  ·
                    refine ⟨732469541705212715514745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906504222427801149411973 732469541705212715514745)
                    ·
                      rfl

theorem cell22_2139719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2139719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139719 prefixEnd_2139719 := by exact prefixLift 2139719
  have htrace : WordTrace (prefixWord ++ tailWord_2139719) baseStart_2139719 baseEnd_2139719 := by
    simpa [prefixWord, tailWord_2139719, baseEnd_2139719] using wordTrace_append hprefix tailTrace_2139719
  have hstable : (prefixWord ++ tailWord_2139719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139719).length < 2 ^ (prefixWord ++ tailWord_2139719).sum := by decide
  have hdescent : baseEnd_2139719 < baseStart_2139719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139734 : List Nat := [5, 2, 2, 2, 11]
def baseStart_2139734 : Nat := 118140960795 + 2139734 * 2 ^ 59
def prefixEnd_2139734 : Nat := 4983230072969 + 3 ^ 40 * 2139734 * 2
def baseEnd_2139734 : Nat := 3014299080295299079793

theorem tailTrace_2139734 : CollatzResearch.WordTrace tailWord_2139734 prefixEnd_2139734 3014299080295299079793 := by
  unfold tailWord_2139734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877656901882289394896641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52028340286744420212230837 4877656901882289394896641)
  ·
    refine ⟨3658242676411717046172481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4877656901882289394896641 3658242676411717046172481)
    ·
      refine ⟨2743682007308787784629361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658242676411717046172481 2743682007308787784629361)
      ·
        refine ⟨2057761505481590838472021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2743682007308787784629361 2057761505481590838472021)
        ·
          refine ⟨3014299080295299079793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2057761505481590838472021 3014299080295299079793)
          ·
            rfl

theorem cell22_2139734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 11].length) (baseStart_2139734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139734 prefixEnd_2139734 := by exact prefixLift 2139734
  have htrace : WordTrace (prefixWord ++ tailWord_2139734) baseStart_2139734 baseEnd_2139734 := by
    simpa [prefixWord, tailWord_2139734, baseEnd_2139734] using wordTrace_append hprefix tailTrace_2139734
  have hstable : (prefixWord ++ tailWord_2139734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139734).length < 2 ^ (prefixWord ++ tailWord_2139734).sum := by decide
  have hdescent : baseEnd_2139734 < baseStart_2139734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
