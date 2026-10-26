import V185TrunkScan23Chunk0189

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1125227 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4]
def baseStart_1125227 : Nat := 118140960795 + 1125227 * 2 ^ 59
def prefixEnd_1125227 : Nat := 4983230072969 + 3 ^ 40 * 1125227 * 2
def baseEnd_1125227 : Nat := 577782296416774277887681

theorem tailTrace_1125227 : CollatzResearch.WordTrace tailWord_1125227 prefixEnd_1125227 577782296416774277887681 := by
  unfold tailWord_1125227
  simp only [CollatzResearch.WordTrace]
  refine ⟨41040400294502227316997935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27360266863001484877998623 41040400294502227316997935)
  ·
    refine ⟨61560600441753340975496903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41040400294502227316997935 61560600441753340975496903)
    ·
      refine ⟨92340900662630011463245355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61560600441753340975496903 92340900662630011463245355)
      ·
        refine ⟨138511350993945017194868033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92340900662630011463245355 138511350993945017194868033)
        ·
          refine ⟨103883513245458762896151025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138511350993945017194868033 103883513245458762896151025)
          ·
            refine ⟨77912634934094072172113269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103883513245458762896151025 77912634934094072172113269)
            ·
              refine ⟨7304309525071319266135619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77912634934094072172113269 7304309525071319266135619)
              ·
                refine ⟨10956464287606978899203429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7304309525071319266135619 10956464287606978899203429)
                ·
                  refine ⟨2054337053926308543600643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10956464287606978899203429 2054337053926308543600643)
                  ·
                    refine ⟨3081505580889462815400965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2054337053926308543600643 3081505580889462815400965)
                    ·
                      refine ⟨577782296416774277887681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3081505580889462815400965 577782296416774277887681)
                      ·
                        rfl

theorem cell23_1125227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4].length) (baseStart_1125227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125227 prefixEnd_1125227 := by exact prefixLift 1125227
  have htrace : WordTrace (prefixWord ++ tailWord_1125227) baseStart_1125227 baseEnd_1125227 := by
    simpa [prefixWord, tailWord_1125227, baseEnd_1125227] using wordTrace_append hprefix tailTrace_1125227
  have hstable : (prefixWord ++ tailWord_1125227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125227).length < 2 ^ (prefixWord ++ tailWord_1125227).sum := by decide
  have hdescent : baseEnd_1125227 < baseStart_1125227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125244 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_1125244 : Nat := 118140960795 + 1125244 * 2 ^ 59
def prefixEnd_1125244 : Nat := 4983230072969 + 3 ^ 40 * 1125244 * 2
def baseEnd_1125244 : Nat := 577791025587900711375103

theorem tailTrace_1125244 : CollatzResearch.WordTrace tailWord_1125244 prefixEnd_1125244 577791025587900711375103 := by
  unfold tailWord_1125244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20520510167720319610183393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27360680223627092813577857 20520510167720319610183393)
  ·
    refine ⟨15390382625790239707637545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20520510167720319610183393 15390382625790239707637545)
    ·
      refine ⟨11542786969342679780728159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15390382625790239707637545 11542786969342679780728159)
      ·
        refine ⟨17314180454014019671092239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11542786969342679780728159 17314180454014019671092239)
        ·
          refine ⟨25971270681021029506638359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17314180454014019671092239 25971270681021029506638359)
          ·
            refine ⟨38956906021531544259957539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25971270681021029506638359 38956906021531544259957539)
            ·
              refine ⟨58435359032297316389936309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38956906021531544259957539 58435359032297316389936309)
              ·
                refine ⟨5478314909277873411556529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58435359032297316389936309 5478314909277873411556529)
                ·
                  refine ⟨4108736181958405058667397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478314909277873411556529 4108736181958405058667397)
                  ·
                    refine ⟨770388034117200948500137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108736181958405058667397 770388034117200948500137)
                    ·
                      refine ⟨577791025587900711375103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770388034117200948500137 577791025587900711375103)
                      ·
                        rfl

theorem cell23_1125244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_1125244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125244 prefixEnd_1125244 := by exact prefixLift 1125244
  have htrace : WordTrace (prefixWord ++ tailWord_1125244) baseStart_1125244 baseEnd_1125244 := by
    simpa [prefixWord, tailWord_1125244, baseEnd_1125244] using wordTrace_append hprefix tailTrace_1125244
  have hstable : (prefixWord ++ tailWord_1125244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125244).length < 2 ^ (prefixWord ++ tailWord_1125244).sum := by decide
  have hdescent : baseEnd_1125244 < baseStart_1125244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125247 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_1125247 : Nat := 118140960795 + 1125247 * 2 ^ 59
def prefixEnd_1125247 : Nat := 4983230072969 + 3 ^ 40 * 1125247 * 2
def baseEnd_1125247 : Nat := 577792566029864199637589

theorem tailTrace_1125247 : CollatzResearch.WordTrace tailWord_1125247 prefixEnd_1125247 577792566029864199637589 := by
  unfold tailWord_1125247
  simp only [CollatzResearch.WordTrace]
  refine ⟨41041129754429770732725995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27360753169619847155150663 41041129754429770732725995)
  ·
    refine ⟨61561694631644656099088993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41041129754429770732725995 61561694631644656099088993)
    ·
      refine ⟨46171270973733492074316745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61561694631644656099088993 46171270973733492074316745)
      ·
        refine ⟨34628453230300119055737559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46171270973733492074316745 34628453230300119055737559)
        ·
          refine ⟨51942679845450178583606339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34628453230300119055737559 51942679845450178583606339)
          ·
            refine ⟨77914019768175267875409509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51942679845450178583606339 77914019768175267875409509)
            ·
              refine ⟨14608878706532862726639283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77914019768175267875409509 14608878706532862726639283)
              ·
                refine ⟨21913318059799294089958925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14608878706532862726639283 21913318059799294089958925)
                ·
                  refine ⟨8217494272424735283734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21913318059799294089958925 8217494272424735283734597)
                  ·
                    refine ⟨1540780176079637865700237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8217494272424735283734597 1540780176079637865700237)
                    ·
                      refine ⟨577792566029864199637589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540780176079637865700237 577792566029864199637589)
                      ·
                        rfl

theorem cell23_1125247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_1125247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125247 prefixEnd_1125247 := by exact prefixLift 1125247
  have htrace : WordTrace (prefixWord ++ tailWord_1125247) baseStart_1125247 baseEnd_1125247 := by
    simpa [prefixWord, tailWord_1125247, baseEnd_1125247] using wordTrace_append hprefix tailTrace_1125247
  have hstable : (prefixWord ++ tailWord_1125247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125247).length < 2 ^ (prefixWord ++ tailWord_1125247).sum := by decide
  have hdescent : baseEnd_1125247 < baseStart_1125247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125271 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 1, 4]
def baseStart_1125271 : Nat := 118140960795 + 1125271 * 2 ^ 59
def prefixEnd_1125271 : Nat := 4983230072969 + 3 ^ 40 * 1125271 * 2
def baseEnd_1125271 : Nat := 192601629855190701912493

theorem tailTrace_1125271 : CollatzResearch.WordTrace tailWord_1125271 prefixEnd_1125271 192601629855190701912493 := by
  unfold tailWord_1125271
  simp only [CollatzResearch.WordTrace]
  refine ⟨41042005106342822831599667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27361336737561881887733111 41042005106342822831599667)
  ·
    refine ⟨61563007659514234247399501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41042005106342822831599667 61563007659514234247399501)
    ·
      refine ⟨23086127872317837842774813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61563007659514234247399501 23086127872317837842774813)
      ·
        refine ⟨8657297952119189191040555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23086127872317837842774813 8657297952119189191040555)
        ·
          refine ⟨12985946928178783786560833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657297952119189191040555 12985946928178783786560833)
          ·
            refine ⟨9739460196134087839920625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12985946928178783786560833 9739460196134087839920625)
            ·
              refine ⟨7304595147100565879940469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9739460196134087839920625 7304595147100565879940469)
              ·
                refine ⟨684805795040678051244419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7304595147100565879940469 684805795040678051244419)
                ·
                  refine ⟨1027208692561017076866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684805795040678051244419 1027208692561017076866629)
                  ·
                    refine ⟨192601629855190701912493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027208692561017076866629 192601629855190701912493)
                    ·
                      rfl

theorem cell23_1125271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_1125271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125271 prefixEnd_1125271 := by exact prefixLift 1125271
  have htrace : WordTrace (prefixWord ++ tailWord_1125271) baseStart_1125271 baseEnd_1125271 := by
    simpa [prefixWord, tailWord_1125271, baseEnd_1125271] using wordTrace_append hprefix tailTrace_1125271
  have hstable : (prefixWord ++ tailWord_1125271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125271).length < 2 ^ (prefixWord ++ tailWord_1125271).sum := by decide
  have hdescent : baseEnd_1125271 < baseStart_1125271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125281 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1125281 : Nat := 118140960795 + 1125281 * 2 ^ 59
def prefixEnd_1125281 : Nat := 4983230072969 + 3 ^ 40 * 1125281 * 2
def baseEnd_1125281 : Nat := 577810024372117066612433

theorem tailTrace_1125281 : CollatzResearch.WordTrace tailWord_1125281 prefixEnd_1125281 577810024372117066612433 := by
  unfold tailWord_1125281
  simp only [CollatzResearch.WordTrace]
  refine ⟨41042369836306594539463697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27361579890871063026309131 41042369836306594539463697)
  ·
    refine ⟨30781777377229945904597773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41042369836306594539463697 30781777377229945904597773)
    ·
      refine ⟨11543166516461229714224165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30781777377229945904597773 11543166516461229714224165)
      ·
        refine ⟨2164343721836480571417031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11543166516461229714224165 2164343721836480571417031)
        ·
          refine ⟨3246515582754720857125547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164343721836480571417031 3246515582754720857125547)
          ·
            refine ⟨4869773374132081285688321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246515582754720857125547 4869773374132081285688321)
            ·
              refine ⟨3652330030599060964266241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869773374132081285688321 3652330030599060964266241)
              ·
                refine ⟨2739247522949295723199681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652330030599060964266241 2739247522949295723199681)
                ·
                  refine ⟨2054435642211971792399761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739247522949295723199681 2054435642211971792399761)
                  ·
                    refine ⟨1540826731658978844299821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2054435642211971792399761 1540826731658978844299821)
                    ·
                      refine ⟨577810024372117066612433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540826731658978844299821 577810024372117066612433)
                      ·
                        rfl

theorem cell23_1125281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1125281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125281 prefixEnd_1125281 := by exact prefixLift 1125281
  have htrace : WordTrace (prefixWord ++ tailWord_1125281) baseStart_1125281 baseEnd_1125281 := by
    simpa [prefixWord, tailWord_1125281, baseEnd_1125281] using wordTrace_append hprefix tailTrace_1125281
  have hstable : (prefixWord ++ tailWord_1125281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125281).length < 2 ^ (prefixWord ++ tailWord_1125281).sum := by decide
  have hdescent : baseEnd_1125281 < baseStart_1125281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125284 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1125284 : Nat := 118140960795 + 1125284 * 2 ^ 59
def prefixEnd_1125284 : Nat := 4983230072969 + 3 ^ 40 * 1125284 * 2
def baseEnd_1125284 : Nat := 64201284979342283874991

theorem tailTrace_1125284 : CollatzResearch.WordTrace tailWord_1125284 prefixEnd_1125284 64201284979342283874991 := by
  unfold tailWord_1125284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20521239627647863025911453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27361652836863817367881937 20521239627647863025911453)
  ·
    refine ⟨7695464860367948634716795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20521239627647863025911453 7695464860367948634716795)
    ·
      refine ⟨11543197290551922952075193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7695464860367948634716795 11543197290551922952075193)
      ·
        refine ⟨8657397967913942214056395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11543197290551922952075193 8657397967913942214056395)
        ·
          refine ⟨12986096951870913321084593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657397967913942214056395 12986096951870913321084593)
          ·
            refine ⟨9739572713903184990813445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12986096951870913321084593 9739572713903184990813445)
            ·
              refine ⟨1826169883856847185777521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9739572713903184990813445 1826169883856847185777521)
              ·
                refine ⟨1369627412892635389333141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826169883856847185777521 1369627412892635389333141)
                ·
                  refine ⟨64201284979342283874991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1369627412892635389333141 64201284979342283874991)
                  ·
                    rfl

theorem cell23_1125284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1125284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125284 prefixEnd_1125284 := by exact prefixLift 1125284
  have htrace : WordTrace (prefixWord ++ tailWord_1125284) baseStart_1125284 baseEnd_1125284 := by
    simpa [prefixWord, tailWord_1125284, baseEnd_1125284] using wordTrace_append hprefix tailTrace_1125284
  have hstable : (prefixWord ++ tailWord_1125284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125284).length < 2 ^ (prefixWord ++ tailWord_1125284).sum := by decide
  have hdescent : baseEnd_1125284 < baseStart_1125284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125354 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1125354 : Nat := 118140960795 + 1125354 * 2 ^ 59
def prefixEnd_1125354 : Nat := 4983230072969 + 3 ^ 40 * 1125354 * 2
def baseEnd_1125354 : Nat := 577847508459895280999597

theorem tailTrace_1125354 : CollatzResearch.WordTrace tailWord_1125354 prefixEnd_1125354 577847508459895280999597 := by
  unfold tailWord_1125354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261258091260532001717779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27363354910028085337914077 10261258091260532001717779)
  ·
    refine ⟨15391887136890798002576669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10261258091260532001717779 15391887136890798002576669)
    ·
      refine ⟨5771957676334049250966251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15391887136890798002576669 5771957676334049250966251)
      ·
        refine ⟨8657936514501073876449377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771957676334049250966251 8657936514501073876449377)
        ·
          refine ⟨6493452385875805407337033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8657936514501073876449377 6493452385875805407337033)
          ·
            refine ⟨4870089289406854055502775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6493452385875805407337033 4870089289406854055502775)
            ·
              refine ⟨7305133934110281083254163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870089289406854055502775 7305133934110281083254163)
              ·
                refine ⟨10957700901165421624881245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305133934110281083254163 10957700901165421624881245)
                ·
                  refine ⟨4109137837937033109330467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10957700901165421624881245 4109137837937033109330467)
                  ·
                    refine ⟨6163706756905549663995701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109137837937033109330467 6163706756905549663995701)
                    ·
                      refine ⟨577847508459895280999597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6163706756905549663995701 577847508459895280999597)
                      ·
                        rfl

theorem cell23_1125354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1125354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125354 prefixEnd_1125354 := by exact prefixLift 1125354
  have htrace : WordTrace (prefixWord ++ tailWord_1125354) baseStart_1125354 baseEnd_1125354 := by
    simpa [prefixWord, tailWord_1125354, baseEnd_1125354] using wordTrace_append hprefix tailTrace_1125354
  have hstable : (prefixWord ++ tailWord_1125354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125354).length < 2 ^ (prefixWord ++ tailWord_1125354).sum := by decide
  have hdescent : baseEnd_1125354 < baseStart_1125354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125361 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1125361 : Nat := 118140960795 + 1125361 * 2 ^ 59
def prefixEnd_1125361 : Nat := 4983230072969 + 3 ^ 40 * 1125361 * 2
def baseEnd_1125361 : Nat := 192617034274825584537355

theorem tailTrace_1125361 : CollatzResearch.WordTrace tailWord_1125361 prefixEnd_1125361 192617034274825584537355 := by
  unfold tailWord_1125361
  simp only [CollatzResearch.WordTrace]
  refine ⟨41045287676016768202375937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27363525117344512134917291 41045287676016768202375937)
  ·
    refine ⟨30783965757012576151781953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41045287676016768202375937 30783965757012576151781953)
    ·
      refine ⟨23087974317759432113836465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30783965757012576151781953 23087974317759432113836465)
      ·
        refine ⟨17315980738319574085377349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23087974317759432113836465 17315980738319574085377349)
        ·
          refine ⟨3246746388434920141008253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17315980738319574085377349 3246746388434920141008253)
          ·
            refine ⟨1217529895663095052878095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3246746388434920141008253 1217529895663095052878095)
            ·
              refine ⟨1826294843494642579317143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217529895663095052878095 1826294843494642579317143)
              ·
                refine ⟨2739442265241963868975715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826294843494642579317143 2739442265241963868975715)
                ·
                  refine ⟨4109163397862945803463573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739442265241963868975715 4109163397862945803463573)
                  ·
                    refine ⟨192617034274825584537355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4109163397862945803463573 192617034274825584537355)
                    ·
                      rfl

theorem cell23_1125361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1125361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125361 prefixEnd_1125361 := by exact prefixLift 1125361
  have htrace : WordTrace (prefixWord ++ tailWord_1125361) baseStart_1125361 baseEnd_1125361 := by
    simpa [prefixWord, tailWord_1125361, baseEnd_1125361] using wordTrace_append hprefix tailTrace_1125361
  have hstable : (prefixWord ++ tailWord_1125361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125361).length < 2 ^ (prefixWord ++ tailWord_1125361).sum := by decide
  have hdescent : baseEnd_1125361 < baseStart_1125361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125365 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1125365 : Nat := 118140960795 + 1125365 * 2 ^ 59
def prefixEnd_1125365 : Nat := 4983230072969 + 3 ^ 40 * 1125365 * 2
def baseEnd_1125365 : Nat := 192617718915698245987349

theorem tailTrace_1125365 : CollatzResearch.WordTrace tailWord_1125365 prefixEnd_1125365 192617718915698245987349 := by
  unfold tailWord_1125365
  simp only [CollatzResearch.WordTrace]
  refine ⟨41045433568002276885521549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27363622378668184590347699 41045433568002276885521549)
  ·
    refine ⟨15392037588000853832070581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41045433568002276885521549 15392037588000853832070581)
    ·
      refine ⟨1443003523875080046756617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15392037588000853832070581 1443003523875080046756617)
      ·
        refine ⟨1082252642906310035067463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443003523875080046756617 1082252642906310035067463)
        ·
          refine ⟨1623378964359465052601195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082252642906310035067463 1623378964359465052601195)
          ·
            refine ⟨2435068446539197578901793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623378964359465052601195 2435068446539197578901793)
            ·
              refine ⟨1826301334904398184176345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435068446539197578901793 1826301334904398184176345)
              ·
                refine ⟨1369726001178298638132259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826301334904398184176345 1369726001178298638132259)
                ·
                  refine ⟨2054589001767447957198389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369726001178298638132259 2054589001767447957198389)
                  ·
                    refine ⟨192617718915698245987349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2054589001767447957198389 192617718915698245987349)
                    ·
                      rfl

theorem cell23_1125365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1125365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125365 prefixEnd_1125365 := by exact prefixLift 1125365
  have htrace : WordTrace (prefixWord ++ tailWord_1125365) baseStart_1125365 baseEnd_1125365 := by
    simpa [prefixWord, tailWord_1125365, baseEnd_1125365] using wordTrace_append hprefix tailTrace_1125365
  have hstable : (prefixWord ++ tailWord_1125365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125365).length < 2 ^ (prefixWord ++ tailWord_1125365).sum := by decide
  have hdescent : baseEnd_1125365 < baseStart_1125365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125401 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 3]
def baseStart_1125401 : Nat := 118140960795 + 1125401 * 2 ^ 59
def prefixEnd_1125401 : Nat := 4983230072969 + 3 ^ 40 * 1125401 * 2
def baseEnd_1125401 : Nat := 577871642050656597111881

theorem tailTrace_1125401 : CollatzResearch.WordTrace tailWord_1125401 prefixEnd_1125401 577871642050656597111881 := by
  unfold tailWord_1125401
  simp only [CollatzResearch.WordTrace]
  refine ⟨41046746595871855033832057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27364497730581236689221371 41046746595871855033832057)
  ·
    refine ⟨30785059946903891275374043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41046746595871855033832057 30785059946903891275374043)
    ·
      refine ⟨46177589920355836913061065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30785059946903891275374043 46177589920355836913061065)
      ·
        refine ⟨34633192440266877684795799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46177589920355836913061065 34633192440266877684795799)
        ·
          refine ⟨51949788660400316527193699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34633192440266877684795799 51949788660400316527193699)
          ·
            refine ⟨77924682990600474790790549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51949788660400316527193699 77924682990600474790790549)
            ·
              refine ⟨3652719515184397255818307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77924682990600474790790549 3652719515184397255818307)
              ·
                refine ⟨5479079272776595883727461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652719515184397255818307 5479079272776595883727461)
                ·
                  refine ⟨1027327363645611728198899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5479079272776595883727461 1027327363645611728198899)
                  ·
                    refine ⟨1540991045468417592298349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027327363645611728198899 1540991045468417592298349)
                    ·
                      refine ⟨577871642050656597111881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1540991045468417592298349 577871642050656597111881)
                      ·
                        rfl

theorem cell23_1125401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_1125401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125401 prefixEnd_1125401 := by exact prefixLift 1125401
  have htrace : WordTrace (prefixWord ++ tailWord_1125401) baseStart_1125401 baseEnd_1125401 := by
    simpa [prefixWord, tailWord_1125401, baseEnd_1125401] using wordTrace_append hprefix tailTrace_1125401
  have hstable : (prefixWord ++ tailWord_1125401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125401).length < 2 ^ (prefixWord ++ tailWord_1125401).sum := by decide
  have hdescent : baseEnd_1125401 < baseStart_1125401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125402 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2]
def baseStart_1125402 : Nat := 118140960795 + 1125402 * 2 ^ 59
def prefixEnd_1125402 : Nat := 4983230072969 + 3 ^ 40 * 1125402 * 2
def baseEnd_1125402 : Nat := 577872155531311093199377

theorem tailTrace_1125402 : CollatzResearch.WordTrace tailWord_1125402 prefixEnd_1125402 577872155531311093199377 := by
  unfold tailWord_1125402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261695767217058051154615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27364522045912154803078973 10261695767217058051154615)
  ·
    refine ⟨15392543650825587076731923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10261695767217058051154615 15392543650825587076731923)
    ·
      refine ⟨23088815476238380615097885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15392543650825587076731923 23088815476238380615097885)
      ·
        refine ⟨8658305803589392730661707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23088815476238380615097885 8658305803589392730661707)
        ·
          refine ⟨12987458705384089095992561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8658305803589392730661707 12987458705384089095992561)
          ·
            refine ⟨9740594029038066821994421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12987458705384089095992561 9740594029038066821994421)
            ·
              refine ⟨913180690222318764561977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9740594029038066821994421 913180690222318764561977)
              ·
                refine ⟨684885517666739073421483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913180690222318764561977 684885517666739073421483)
                ·
                  refine ⟨1027328276500108610132225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684885517666739073421483 1027328276500108610132225)
                  ·
                    refine ⟨770496207375081457599169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1027328276500108610132225 770496207375081457599169)
                    ·
                      refine ⟨577872155531311093199377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770496207375081457599169 577872155531311093199377)
                      ·
                        rfl

theorem cell23_1125402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_1125402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125402 prefixEnd_1125402 := by exact prefixLift 1125402
  have htrace : WordTrace (prefixWord ++ tailWord_1125402) baseStart_1125402 baseEnd_1125402 := by
    simpa [prefixWord, tailWord_1125402, baseEnd_1125402] using wordTrace_append hprefix tailTrace_1125402
  have hstable : (prefixWord ++ tailWord_1125402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125402).length < 2 ^ (prefixWord ++ tailWord_1125402).sum := by decide
  have hdescent : baseEnd_1125402 < baseStart_1125402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125464 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 7]
def baseStart_1125464 : Nat := 118140960795 + 1125464 * 2 ^ 59
def prefixEnd_1125464 : Nat := 4983230072969 + 3 ^ 40 * 1125464 * 2
def baseEnd_1125464 : Nat := 64211554592432205624899

theorem tailTrace_1125464 : CollatzResearch.WordTrace tailWord_1125464 prefixEnd_1125464 64211554592432205624899 := by
  unfold tailWord_1125464
  simp only [CollatzResearch.WordTrace]
  refine ⟨20524522197321808396687723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27366029596429077862250297 20524522197321808396687723)
  ·
    refine ⟨30786783295982712595031585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20524522197321808396687723 30786783295982712595031585)
    ·
      refine ⟨23090087471987034446273689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30786783295982712595031585 23090087471987034446273689)
      ·
        refine ⟨17317565603990275834705267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23090087471987034446273689 17317565603990275834705267)
        ·
          refine ⟨25976348405985413752057901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17317565603990275834705267 25976348405985413752057901)
          ·
            refine ⟨9741130652244530157021713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25976348405985413752057901 9741130652244530157021713)
            ·
              refine ⟨7305847989183397617766285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9741130652244530157021713 7305847989183397617766285)
              ·
                refine ⟨2739692995943774106662357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7305847989183397617766285 2739692995943774106662357)
                ·
                  refine ⟨64211554592432205624899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2739692995943774106662357 64211554592432205624899)
                  ·
                    rfl

theorem cell23_1125464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_1125464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125464 prefixEnd_1125464 := by exact prefixLift 1125464
  have htrace : WordTrace (prefixWord ++ tailWord_1125464) baseStart_1125464 baseEnd_1125464 := by
    simpa [prefixWord, tailWord_1125464, baseEnd_1125464] using wordTrace_append hprefix tailTrace_1125464
  have hstable : (prefixWord ++ tailWord_1125464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125464).length < 2 ^ (prefixWord ++ tailWord_1125464).sum := by decide
  have hdescent : baseEnd_1125464 < baseStart_1125464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125504 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1125504 : Nat := 118140960795 + 1125504 * 2 ^ 59
def prefixEnd_1125504 : Nat := 4983230072969 + 3 ^ 40 * 1125504 * 2
def baseEnd_1125504 : Nat := 577924530558069694123907

theorem tailTrace_1125504 : CollatzResearch.WordTrace tailWord_1125504 prefixEnd_1125504 577924530558069694123907 := by
  unfold tailWord_1125504
  simp only [CollatzResearch.WordTrace]
  refine ⟨20525251657249351812415783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27367002209665802416554377 20525251657249351812415783)
  ·
    refine ⟨30787877485874027718623675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20525251657249351812415783 30787877485874027718623675)
    ·
      refine ⟨46181816228811041577935513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30787877485874027718623675 46181816228811041577935513)
      ·
        refine ⟨34636362171608281183451635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46181816228811041577935513 34636362171608281183451635)
        ·
          refine ⟨51954543257412421775177453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34636362171608281183451635 51954543257412421775177453)
          ·
            refine ⟨19482953721529658165691545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51954543257412421775177453 19482953721529658165691545)
            ·
              refine ⟨14612215291147243624268659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19482953721529658165691545 14612215291147243624268659)
              ·
                refine ⟨21918322936720865436402989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14612215291147243624268659 21918322936720865436402989)
                ·
                  refine ⟨8219371101270324538651121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21918322936720865436402989 8219371101270324538651121)
                  ·
                    refine ⟨6164528325952743403988341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8219371101270324538651121 6164528325952743403988341)
                    ·
                      refine ⟨577924530558069694123907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6164528325952743403988341 577924530558069694123907)
                      ·
                        rfl

theorem cell23_1125504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1125504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125504 prefixEnd_1125504 := by exact prefixLift 1125504
  have htrace : WordTrace (prefixWord ++ tailWord_1125504) baseStart_1125504 baseEnd_1125504 := by
    simpa [prefixWord, tailWord_1125504, baseEnd_1125504] using wordTrace_append hprefix tailTrace_1125504
  have hstable : (prefixWord ++ tailWord_1125504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125504).length < 2 ^ (prefixWord ++ tailWord_1125504).sum := by decide
  have hdescent : baseEnd_1125504 < baseStart_1125504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125509 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_1125509 : Nat := 118140960795 + 1125509 * 2 ^ 59
def prefixEnd_1125509 : Nat := 4983230072969 + 3 ^ 40 * 1125509 * 2
def baseEnd_1125509 : Nat := 577927097961342174561385

theorem tailTrace_1125509 : CollatzResearch.WordTrace tailWord_1125509 prefixEnd_1125509 577927097961342174561385 := by
  unfold tailWord_1125509
  simp only [CollatzResearch.WordTrace]
  refine ⟨41050685679480589478763581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27367123786320392985842387 41050685679480589478763581)
  ·
    refine ⟨15394007129805221054536343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41050685679480589478763581 15394007129805221054536343)
    ·
      refine ⟨23091010694707831581804515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15394007129805221054536343 23091010694707831581804515)
      ·
        refine ⟨34636516042061747372706773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23091010694707831581804515 34636516042061747372706773)
        ·
          refine ⟨811793344735822204047815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34636516042061747372706773 811793344735822204047815)
          ·
            refine ⟨1217690017103733306071723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811793344735822204047815 1217690017103733306071723)
            ·
              refine ⟨1826535025655599959107585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217690017103733306071723 1826535025655599959107585)
              ·
                refine ⟨1369901269241699969330689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826535025655599959107585 1369901269241699969330689)
                ·
                  refine ⟨1027425951931274976998017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1369901269241699969330689 1027425951931274976998017)
                  ·
                    refine ⟨770569463948456232748513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1027425951931274976998017 770569463948456232748513)
                    ·
                      refine ⟨577927097961342174561385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770569463948456232748513 577927097961342174561385)
                      ·
                        rfl

theorem cell23_1125509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_1125509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125509 prefixEnd_1125509 := by exact prefixLift 1125509
  have htrace : WordTrace (prefixWord ++ tailWord_1125509) baseStart_1125509 baseEnd_1125509 := by
    simpa [prefixWord, tailWord_1125509, baseEnd_1125509] using wordTrace_append hprefix tailTrace_1125509
  have hstable : (prefixWord ++ tailWord_1125509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125509).length < 2 ^ (prefixWord ++ tailWord_1125509).sum := by decide
  have hdescent : baseEnd_1125509 < baseStart_1125509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125551 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_1125551 : Nat := 118140960795 + 1125551 * 2 ^ 59
def prefixEnd_1125551 : Nat := 4983230072969 + 3 ^ 40 * 1125551 * 2
def baseEnd_1125551 : Nat := 577948664148831010236191

theorem tailTrace_1125551 : CollatzResearch.WordTrace tailWord_1125551 prefixEnd_1125551 577948664148831010236191 := by
  unfold tailWord_1125551
  simp only [CollatzResearch.WordTrace]
  refine ⟨41052217545328430651792507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27368145030218953767861671 41052217545328430651792507)
  ·
    refine ⟨61578326317992645977688761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41052217545328430651792507 61578326317992645977688761)
    ·
      refine ⟨46183744738494484483266571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61578326317992645977688761 46183744738494484483266571)
      ·
        refine ⟨69275617107741726724899857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46183744738494484483266571 69275617107741726724899857)
        ·
          refine ⟨51956712830806295043674893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69275617107741726724899857 51956712830806295043674893)
          ·
            refine ⟨19483767311552360641378085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51956712830806295043674893 19483767311552360641378085)
            ·
              refine ⟨3653206370916067620258391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19483767311552360641378085 3653206370916067620258391)
              ·
                refine ⟨5479809556374101430387587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653206370916067620258391 5479809556374101430387587)
                ·
                  refine ⟨8219714334561152145581381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479809556374101430387587 8219714334561152145581381)
                  ·
                    refine ⟨1541196437730216027296509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8219714334561152145581381 1541196437730216027296509)
                    ·
                      refine ⟨577948664148831010236191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1541196437730216027296509 577948664148831010236191)
                      ·
                        rfl

theorem cell23_1125551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_1125551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125551 prefixEnd_1125551 := by exact prefixLift 1125551
  have htrace : WordTrace (prefixWord ++ tailWord_1125551) baseStart_1125551 baseEnd_1125551 := by
    simpa [prefixWord, tailWord_1125551, baseEnd_1125551] using wordTrace_append hprefix tailTrace_1125551
  have hstable : (prefixWord ++ tailWord_1125551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125551).length < 2 ^ (prefixWord ++ tailWord_1125551).sum := by decide
  have hdescent : baseEnd_1125551 < baseStart_1125551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125641 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_1125641 : Nat := 118140960795 + 1125641 * 2 ^ 59
def prefixEnd_1125641 : Nat := 4983230072969 + 3 ^ 40 * 1125641 * 2
def baseEnd_1125641 : Nat := 577994877407735658110777

theorem tailTrace_1125641 : CollatzResearch.WordTrace tailWord_1125641 prefixEnd_1125641 577994877407735658110777 := by
  unfold tailWord_1125641
  simp only [CollatzResearch.WordTrace]
  refine ⟨41055500115002376022568777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27370333410001584015045851 41055500115002376022568777)
  ·
    refine ⟨30791625086251782016926583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41055500115002376022568777 30791625086251782016926583)
    ·
      refine ⟨46187437629377673025389875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30791625086251782016926583 46187437629377673025389875)
      ·
        refine ⟨69281156444066509538084813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46187437629377673025389875 69281156444066509538084813)
        ·
          refine ⟨25980433666524941076781805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69281156444066509538084813 25980433666524941076781805)
          ·
            refine ⟨9742662624946852903793177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25980433666524941076781805 9742662624946852903793177)
            ·
              refine ⟨7306996968710139677844883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9742662624946852903793177 7306996968710139677844883)
              ·
                refine ⟨10960495453065209516767325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306996968710139677844883 10960495453065209516767325)
                ·
                  refine ⟨4110185794899453568787747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10960495453065209516767325 4110185794899453568787747)
                  ·
                    refine ⟨6165278692349180353181621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110185794899453568787747 6165278692349180353181621)
                    ·
                      refine ⟨577994877407735658110777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6165278692349180353181621 577994877407735658110777)
                      ·
                        rfl

theorem cell23_1125641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_1125641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125641 prefixEnd_1125641 := by exact prefixLift 1125641
  have htrace : WordTrace (prefixWord ++ tailWord_1125641) baseStart_1125641 baseEnd_1125641 := by
    simpa [prefixWord, tailWord_1125641, baseEnd_1125641] using wordTrace_append hprefix tailTrace_1125641
  have hstable : (prefixWord ++ tailWord_1125641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125641).length < 2 ^ (prefixWord ++ tailWord_1125641).sum := by decide
  have hdescent : baseEnd_1125641 < baseStart_1125641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125668 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1125668 : Nat := 118140960795 + 1125668 * 2 ^ 59
def prefixEnd_1125668 : Nat := 4983230072969 + 3 ^ 40 * 1125668 * 2
def baseEnd_1125668 : Nat := 578008741385407052473153

theorem tailTrace_1125668 : CollatzResearch.WordTrace tailWord_1125668 prefixEnd_1125668 578008741385407052473153 := by
  unfold tailWord_1125668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528242442952279816900829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27370989923936373089201105 20528242442952279816900829)
  ·
    refine ⟨7698090916107104931337811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20528242442952279816900829 7698090916107104931337811)
    ·
      refine ⟨11547136374160657397006717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698090916107104931337811 11547136374160657397006717)
      ·
        refine ⟨4330176140310246523877519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11547136374160657397006717 4330176140310246523877519)
        ·
          refine ⟨6495264210465369785816279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330176140310246523877519 6495264210465369785816279)
          ·
            refine ⟨9742896315698054678724419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495264210465369785816279 9742896315698054678724419)
            ·
              refine ⟨14614344473547082018086629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9742896315698054678724419 14614344473547082018086629)
              ·
                refine ⟨2740189588790077878391243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14614344473547082018086629 2740189588790077878391243)
                ·
                  refine ⟨4110284383185116817586865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740189588790077878391243 4110284383185116817586865)
                  ·
                    refine ⟨3082713287388837613190149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110284383185116817586865 3082713287388837613190149)
                    ·
                      refine ⟨578008741385407052473153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3082713287388837613190149 578008741385407052473153)
                      ·
                        rfl

theorem cell23_1125668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1125668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125668 prefixEnd_1125668 := by exact prefixLift 1125668
  have htrace : WordTrace (prefixWord ++ tailWord_1125668) baseStart_1125668 baseEnd_1125668 := by
    simpa [prefixWord, tailWord_1125668, baseEnd_1125668] using wordTrace_append hprefix tailTrace_1125668
  have hstable : (prefixWord ++ tailWord_1125668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125668).length < 2 ^ (prefixWord ++ tailWord_1125668).sum := by decide
  have hdescent : baseEnd_1125668 < baseStart_1125668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125672 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1125672 : Nat := 118140960795 + 1125672 * 2 ^ 59
def prefixEnd_1125672 : Nat := 4983230072969 + 3 ^ 40 * 1125672 * 2
def baseEnd_1125672 : Nat := 578010795308025036823135

theorem tailTrace_1125672 : CollatzResearch.WordTrace tailWord_1125672 prefixEnd_1125672 578010795308025036823135 := by
  unfold tailWord_1125672
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528315388945034158473635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27371087185260045544631513 20528315388945034158473635)
  ·
    refine ⟨30792473083417551237710453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20528315388945034158473635 30792473083417551237710453)
    ·
      refine ⟨2886794351570395428535355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30792473083417551237710453 2886794351570395428535355)
      ·
        refine ⟨4330191527355593142803033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886794351570395428535355 4330191527355593142803033)
        ·
          refine ⟨3247643645516694857102275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4330191527355593142803033 3247643645516694857102275)
          ·
            refine ⟨4871465468275042285653413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247643645516694857102275 4871465468275042285653413)
            ·
              refine ⟨913399775301570428560015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4871465468275042285653413 913399775301570428560015)
              ·
                refine ⟨1370099662952355642840023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913399775301570428560015 1370099662952355642840023)
                ·
                  refine ⟨2055149494428533464260035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370099662952355642840023 2055149494428533464260035)
                  ·
                    refine ⟨3082724241642800196390053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055149494428533464260035 3082724241642800196390053)
                    ·
                      refine ⟨578010795308025036823135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3082724241642800196390053 578010795308025036823135)
                      ·
                        rfl

theorem cell23_1125672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1125672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125672 prefixEnd_1125672 := by exact prefixLift 1125672
  have htrace : WordTrace (prefixWord ++ tailWord_1125672) baseStart_1125672 baseEnd_1125672 := by
    simpa [prefixWord, tailWord_1125672, baseEnd_1125672] using wordTrace_append hprefix tailTrace_1125672
  have hstable : (prefixWord ++ tailWord_1125672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125672).length < 2 ^ (prefixWord ++ tailWord_1125672).sum := by decide
  have hdescent : baseEnd_1125672 < baseStart_1125672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125682 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_1125682 : Nat := 118140960795 + 1125682 * 2 ^ 59
def prefixEnd_1125682 : Nat := 4983230072969 + 3 ^ 40 * 1125682 * 2
def baseEnd_1125682 : Nat := 192671976704856665899363

theorem tailTrace_1125682 : CollatzResearch.WordTrace tailWord_1125682 prefixEnd_1125682 192671976704856665899363 := by
  unfold tailWord_1125682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264248876963460006202825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27371330338569226683207533 10264248876963460006202825)
  ·
    refine ⟨7698186657722595004652119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10264248876963460006202825 7698186657722595004652119)
    ·
      refine ⟨11547279986583892506978179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698186657722595004652119 11547279986583892506978179)
      ·
        refine ⟨17320919979875838760467269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11547279986583892506978179 17320919979875838760467269)
        ·
          refine ⟨3247672496226719767587613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17320919979875838760467269 3247672496226719767587613)
          ·
            refine ⟨1217877186085019912845355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3247672496226719767587613 1217877186085019912845355)
            ·
              refine ⟨1826815779127529869268033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217877186085019912845355 1826815779127529869268033)
              ·
                refine ⟨1370111834345647401951025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826815779127529869268033 1370111834345647401951025)
                ·
                  refine ⟨1027583875759235551463269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370111834345647401951025 1027583875759235551463269)
                  ·
                    refine ⟨192671976704856665899363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027583875759235551463269 192671976704856665899363)
                    ·
                      rfl

theorem cell23_1125682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_1125682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125682 prefixEnd_1125682 := by exact prefixLift 1125682
  have htrace : WordTrace (prefixWord ++ tailWord_1125682) baseStart_1125682 baseEnd_1125682 := by
    simpa [prefixWord, tailWord_1125682, baseEnd_1125682] using wordTrace_append hprefix tailTrace_1125682
  have hstable : (prefixWord ++ tailWord_1125682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125682).length < 2 ^ (prefixWord ++ tailWord_1125682).sum := by decide
  have hdescent : baseEnd_1125682 < baseStart_1125682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125689 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1125689 : Nat := 118140960795 + 1125689 * 2 ^ 59
def prefixEnd_1125689 : Nat := 4983230072969 + 3 ^ 40 * 1125689 * 2
def baseEnd_1125689 : Nat := 578019524479151470310557

theorem tailTrace_1125689 : CollatzResearch.WordTrace tailWord_1125689 prefixEnd_1125689 578019524479151470310557 := by
  unfold tailWord_1125689
  simp only [CollatzResearch.WordTrace]
  refine ⟨41057250818828480220316121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27371500545885653480210747 41057250818828480220316121)
  ·
    refine ⟨30792938114121360165237091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41057250818828480220316121 30792938114121360165237091)
    ·
      refine ⟨46189407171182040247855637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30792938114121360165237091 46189407171182040247855637)
      ·
        refine ⟨2165128461149158136618233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46189407171182040247855637 2165128461149158136618233)
        ·
          refine ⟨1623846345861868602463675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165128461149158136618233 1623846345861868602463675)
          ·
            refine ⟨2435769518792802903695513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623846345861868602463675 2435769518792802903695513)
            ·
              refine ⟨1826827139094602177771635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2435769518792802903695513 1826827139094602177771635)
              ·
                refine ⟨2740240708641903266657453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826827139094602177771635 2740240708641903266657453)
                ·
                  refine ⟨1027590265740713724996545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2740240708641903266657453 1027590265740713724996545)
                  ·
                    refine ⟨770692699305535293747409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1027590265740713724996545 770692699305535293747409)
                    ·
                      refine ⟨578019524479151470310557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770692699305535293747409 578019524479151470310557)
                      ·
                        rfl

theorem cell23_1125689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1125689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125689 prefixEnd_1125689 := by exact prefixLift 1125689
  have htrace : WordTrace (prefixWord ++ tailWord_1125689) baseStart_1125689 baseEnd_1125689 := by
    simpa [prefixWord, tailWord_1125689, baseEnd_1125689] using wordTrace_append hprefix tailTrace_1125689
  have hstable : (prefixWord ++ tailWord_1125689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125689).length < 2 ^ (prefixWord ++ tailWord_1125689).sum := by decide
  have hdescent : baseEnd_1125689 < baseStart_1125689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125701 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_1125701 : Nat := 118140960795 + 1125701 * 2 ^ 59
def prefixEnd_1125701 : Nat := 4983230072969 + 3 ^ 40 * 1125701 * 2
def baseEnd_1125701 : Nat := 578025686247005423360501

theorem tailTrace_1125701 : CollatzResearch.WordTrace tailWord_1125701 prefixEnd_1125701 578025686247005423360501 := by
  unfold tailWord_1125701
  simp only [CollatzResearch.WordTrace]
  refine ⟨41057688494785006269752957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27371792329856670846501971 41057688494785006269752957)
  ·
    refine ⟨15396633185544377351157359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41057688494785006269752957 15396633185544377351157359)
    ·
      refine ⟨23094949778316566026736039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396633185544377351157359 23094949778316566026736039)
      ·
        refine ⟨34642424667474849040104059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23094949778316566026736039 34642424667474849040104059)
        ·
          refine ⟨51963637001212273560156089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34642424667474849040104059 51963637001212273560156089)
          ·
            refine ⟨38972727750909205170117067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51963637001212273560156089 38972727750909205170117067)
            ·
              refine ⟨58459091626363807755175601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38972727750909205170117067 58459091626363807755175601)
              ·
                refine ⟨43844318719772855816381701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58459091626363807755175601 43844318719772855816381701)
                ·
                  refine ⟨8220809759957410465571569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43844318719772855816381701 8220809759957410465571569)
                  ·
                    refine ⟨6165607319968057849178677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8220809759957410465571569 6165607319968057849178677)
                    ·
                      refine ⟨578025686247005423360501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6165607319968057849178677 578025686247005423360501)
                      ·
                        rfl

theorem cell23_1125701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_1125701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125701 prefixEnd_1125701 := by exact prefixLift 1125701
  have htrace : WordTrace (prefixWord ++ tailWord_1125701) baseStart_1125701 baseEnd_1125701 := by
    simpa [prefixWord, tailWord_1125701, baseEnd_1125701] using wordTrace_append hprefix tailTrace_1125701
  have hstable : (prefixWord ++ tailWord_1125701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125701).length < 2 ^ (prefixWord ++ tailWord_1125701).sum := by decide
  have hdescent : baseEnd_1125701 < baseStart_1125701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125705 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 3]
def baseStart_1125705 : Nat := 118140960795 + 1125705 * 2 ^ 59
def prefixEnd_1125705 : Nat := 4983230072969 + 3 ^ 40 * 1125705 * 2
def baseEnd_1125705 : Nat := 578027740169623407710483

theorem tailTrace_1125705 : CollatzResearch.WordTrace tailWord_1125705 prefixEnd_1125705 578027740169623407710483 := by
  unfold tailWord_1125705
  simp only [CollatzResearch.WordTrace]
  refine ⟨41057834386770514952898569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27371889591180343301932379 41057834386770514952898569)
  ·
    refine ⟨30793375790077886214673927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41057834386770514952898569 30793375790077886214673927)
    ·
      refine ⟨46190063685116829322010891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30793375790077886214673927 46190063685116829322010891)
      ·
        refine ⟨69285095527675243983016337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46190063685116829322010891 69285095527675243983016337)
        ·
          refine ⟨51963821645756432987262253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69285095527675243983016337 51963821645756432987262253)
          ·
            refine ⟨19486433117158662370223345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51963821645756432987262253 19486433117158662370223345)
            ·
              refine ⟨14614824837868996777667509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19486433117158662370223345 14614824837868996777667509)
              ·
                refine ⟨1370139828550218447906329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14614824837868996777667509 1370139828550218447906329)
                ·
                  refine ⟨1027604871412663835929747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370139828550218447906329 1027604871412663835929747)
                  ·
                    refine ⟨1541407307118995753894621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027604871412663835929747 1541407307118995753894621)
                    ·
                      refine ⟨578027740169623407710483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1541407307118995753894621 578027740169623407710483)
                      ·
                        rfl

theorem cell23_1125705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_1125705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125705 prefixEnd_1125705 := by exact prefixLift 1125705
  have htrace : WordTrace (prefixWord ++ tailWord_1125705) baseStart_1125705 baseEnd_1125705 := by
    simpa [prefixWord, tailWord_1125705, baseEnd_1125705] using wordTrace_append hprefix tailTrace_1125705
  have hstable : (prefixWord ++ tailWord_1125705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125705).length < 2 ^ (prefixWord ++ tailWord_1125705).sum := by decide
  have hdescent : baseEnd_1125705 < baseStart_1125705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125711 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_1125711 : Nat := 118140960795 + 1125711 * 2 ^ 59
def prefixEnd_1125711 : Nat := 4983230072969 + 3 ^ 40 * 1125711 * 2
def baseEnd_1125711 : Nat := 578030821053550384235455

theorem tailTrace_1125711 : CollatzResearch.WordTrace tailWord_1125711 prefixEnd_1125711 578030821053550384235455 := by
  unfold tailWord_1125711
  simp only [CollatzResearch.WordTrace]
  refine ⟨41058053224748777977616987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27372035483165851985077991 41058053224748777977616987)
  ·
    refine ⟨61587079837123166966425481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41058053224748777977616987 61587079837123166966425481)
    ·
      refine ⟨46190309877842375224819111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61587079837123166966425481 46190309877842375224819111)
      ·
        refine ⟨69285464816763562837228667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46190309877842375224819111 69285464816763562837228667)
        ·
          refine ⟨103928197225145344255843001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69285464816763562837228667 103928197225145344255843001)
          ·
            refine ⟨77946147918859008191882251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103928197225145344255843001 77946147918859008191882251)
            ·
              refine ⟨116919221878288512287823377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77946147918859008191882251 116919221878288512287823377)
              ·
                refine ⟨87689416408716384215867533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116919221878288512287823377 87689416408716384215867533)
                ·
                  refine ⟨32883531153268644080950325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87689416408716384215867533 32883531153268644080950325)
                  ·
                    refine ⟨3082831045618935382589093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32883531153268644080950325 3082831045618935382589093)
                    ·
                      refine ⟨578030821053550384235455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3082831045618935382589093 578030821053550384235455)
                      ·
                        rfl

theorem cell23_1125711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_1125711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125711 prefixEnd_1125711 := by exact prefixLift 1125711
  have htrace : WordTrace (prefixWord ++ tailWord_1125711) baseStart_1125711 baseEnd_1125711 := by
    simpa [prefixWord, tailWord_1125711, baseEnd_1125711] using wordTrace_append hprefix tailTrace_1125711
  have hstable : (prefixWord ++ tailWord_1125711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125711).length < 2 ^ (prefixWord ++ tailWord_1125711).sum := by decide
  have hdescent : baseEnd_1125711 < baseStart_1125711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125721 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_1125721 : Nat := 118140960795 + 1125721 * 2 ^ 59
def prefixEnd_1125721 : Nat := 4983230072969 + 3 ^ 40 * 1125721 * 2
def baseEnd_1125721 : Nat := 192678651953365115036803

theorem tailTrace_1125721 : CollatzResearch.WordTrace tailWord_1125721 prefixEnd_1125721 192678651953365115036803 := by
  unfold tailWord_1125721
  simp only [CollatzResearch.WordTrace]
  refine ⟨41058417954712549685481017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27372278636475033123654011 41058417954712549685481017)
  ·
    refine ⟨30793813466034412264110763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41058417954712549685481017 30793813466034412264110763)
    ·
      refine ⟨46190720199051618396166145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30793813466034412264110763 46190720199051618396166145)
      ·
        refine ⟨34643040149288713797124609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46190720199051618396166145 34643040149288713797124609)
        ·
          refine ⟨25982280111966535347843457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34643040149288713797124609 25982280111966535347843457)
          ·
            refine ⟨19486710083974901510882593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25982280111966535347843457 19486710083974901510882593)
            ·
              refine ⟨14615032562981176133161945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19486710083974901510882593 14615032562981176133161945)
              ·
                refine ⟨10961274422235882099871459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14615032562981176133161945 10961274422235882099871459)
                ·
                  refine ⟨16441911633353823149807189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10961274422235882099871459 16441911633353823149807189)
                  ·
                    refine ⟨192678651953365115036803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16441911633353823149807189 192678651953365115036803)
                    ·
                      rfl

theorem cell23_1125721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_1125721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125721 prefixEnd_1125721 := by exact prefixLift 1125721
  have htrace : WordTrace (prefixWord ++ tailWord_1125721) baseStart_1125721 baseEnd_1125721 := by
    simpa [prefixWord, tailWord_1125721, baseEnd_1125721] using wordTrace_append hprefix tailTrace_1125721
  have hstable : (prefixWord ++ tailWord_1125721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125721).length < 2 ^ (prefixWord ++ tailWord_1125721).sum := by decide
  have hdescent : baseEnd_1125721 < baseStart_1125721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125732 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_1125732 : Nat := 118140960795 + 1125732 * 2 ^ 59
def prefixEnd_1125732 : Nat := 4983230072969 + 3 ^ 40 * 1125732 * 2
def baseEnd_1125732 : Nat := 578041604147294802072859

theorem tailTrace_1125732 : CollatzResearch.WordTrace tailWord_1125732 prefixEnd_1125732 578041604147294802072859 := by
  unfold tailWord_1125732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20529409578836349282065725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27372546105115132376087633 20529409578836349282065725)
  ·
    refine ⟨7698528592063630980774647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20529409578836349282065725 7698528592063630980774647)
    ·
      refine ⟨11547792888095446471161971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698528592063630980774647 11547792888095446471161971)
      ·
        refine ⟨17321689332143169706742957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11547792888095446471161971 17321689332143169706742957)
        ·
          refine ⟨6495633499553688640028609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17321689332143169706742957 6495633499553688640028609)
          ·
            refine ⟨4871725124665266480021457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6495633499553688640028609 4871725124665266480021457)
            ·
              refine ⟨3653793843498949860016093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871725124665266480021457 3653793843498949860016093)
              ·
                refine ⟨1370172691312106197506035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3653793843498949860016093 1370172691312106197506035)
                ·
                  refine ⟨2055259036968159296259053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370172691312106197506035 2055259036968159296259053)
                  ·
                    refine ⟨770722138863059736097145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2055259036968159296259053 770722138863059736097145)
                    ·
                      refine ⟨578041604147294802072859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770722138863059736097145 578041604147294802072859)
                      ·
                        rfl

theorem cell23_1125732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_1125732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125732 prefixEnd_1125732 := by exact prefixLift 1125732
  have htrace : WordTrace (prefixWord ++ tailWord_1125732) baseStart_1125732 baseEnd_1125732 := by
    simpa [prefixWord, tailWord_1125732, baseEnd_1125732] using wordTrace_append hprefix tailTrace_1125732
  have hstable : (prefixWord ++ tailWord_1125732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125732).length < 2 ^ (prefixWord ++ tailWord_1125732).sum := by decide
  have hdescent : baseEnd_1125732 < baseStart_1125732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125835 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4]
def baseStart_1125835 : Nat := 118140960795 + 1125835 * 2 ^ 59
def prefixEnd_1125835 : Nat := 4983230072969 + 3 ^ 40 * 1125835 * 2
def baseEnd_1125835 : Nat := 578094492654707899084885

theorem tailTrace_1125835 : CollatzResearch.WordTrace tailWord_1125835 prefixEnd_1125835 578094492654707899084885 := by
  unfold tailWord_1125835
  simp only [CollatzResearch.WordTrace]
  refine ⟨41062575876299547155130959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27375050584199698103420639 41062575876299547155130959)
  ·
    refine ⟨61593863814449320732696439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41062575876299547155130959 61593863814449320732696439)
    ·
      refine ⟨92390795721673981099044659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61593863814449320732696439 92390795721673981099044659)
      ·
        refine ⟨138586193582510971648566989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92390795721673981099044659 138586193582510971648566989)
        ·
          refine ⟨51969822593441614368212621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138586193582510971648566989 51969822593441614368212621)
          ·
            refine ⟨19488683472540605388079733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51969822593441614368212621 19488683472540605388079733)
            ·
              refine ⟨1827064075550681755132475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19488683472540605388079733 1827064075550681755132475)
              ·
                refine ⟨2740596113326022632698713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827064075550681755132475 2740596113326022632698713)
                ·
                  refine ⟨2055447084994516974524035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2740596113326022632698713 2055447084994516974524035)
                  ·
                    refine ⟨3083170627491775461786053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055447084994516974524035 3083170627491775461786053)
                    ·
                      refine ⟨578094492654707899084885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3083170627491775461786053 578094492654707899084885)
                      ·
                        rfl

theorem cell23_1125835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4].length) (baseStart_1125835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125835 prefixEnd_1125835 := by exact prefixLift 1125835
  have htrace : WordTrace (prefixWord ++ tailWord_1125835) baseStart_1125835 baseEnd_1125835 := by
    simpa [prefixWord, tailWord_1125835, baseEnd_1125835] using wordTrace_append hprefix tailTrace_1125835
  have hstable : (prefixWord ++ tailWord_1125835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125835).length < 2 ^ (prefixWord ++ tailWord_1125835).sum := by decide
  have hdescent : baseEnd_1125835 < baseStart_1125835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125845 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1125845 : Nat := 118140960795 + 1125845 * 2 ^ 59
def prefixEnd_1125845 : Nat := 4983230072969 + 3 ^ 40 * 1125845 * 2
def baseEnd_1125845 : Nat := 192699875820417619986613

theorem tailTrace_1125845 : CollatzResearch.WordTrace tailWord_1125845 prefixEnd_1125845 192699875820417619986613 := by
  unfold tailWord_1125845
  simp only [CollatzResearch.WordTrace]
  refine ⟨41062940606263318862994989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27375293737508879241996659 41062940606263318862994989)
  ·
    refine ⟨15398602727348744573623121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41062940606263318862994989 15398602727348744573623121)
    ·
      refine ⟨11548952045511558430217341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15398602727348744573623121 11548952045511558430217341)
      ·
        refine ⟨4330857017066834411331503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11548952045511558430217341 4330857017066834411331503)
        ·
          refine ⟨6496285525600251616997255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330857017066834411331503 6496285525600251616997255)
          ·
            refine ⟨9744428288400377425495883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496285525600251616997255 9744428288400377425495883)
            ·
              refine ⟨14616642432600566138243825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9744428288400377425495883 14616642432600566138243825)
              ·
                refine ⟨10962481824450424603682869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14616642432600566138243825 10962481824450424603682869)
                ·
                  refine ⟨1027732671042227306595269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10962481824450424603682869 1027732671042227306595269)
                  ·
                    refine ⟨192699875820417619986613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1027732671042227306595269 192699875820417619986613)
                    ·
                      rfl

theorem cell23_1125845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1125845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125845 prefixEnd_1125845 := by exact prefixLift 1125845
  have htrace : WordTrace (prefixWord ++ tailWord_1125845) baseStart_1125845 baseEnd_1125845 := by
    simpa [prefixWord, tailWord_1125845, baseEnd_1125845] using wordTrace_append hprefix tailTrace_1125845
  have hstable : (prefixWord ++ tailWord_1125845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125845).length < 2 ^ (prefixWord ++ tailWord_1125845).sum := by decide
  have hdescent : baseEnd_1125845 < baseStart_1125845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125848 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1125848 : Nat := 118140960795 + 1125848 * 2 ^ 59
def prefixEnd_1125848 : Nat := 4983230072969 + 3 ^ 40 * 1125848 * 2
def baseEnd_1125848 : Nat := 578101167903216348222325

theorem tailTrace_1125848 : CollatzResearch.WordTrace tailWord_1125848 prefixEnd_1125848 578101167903216348222325 := by
  unfold tailWord_1125848
  simp only [CollatzResearch.WordTrace]
  refine ⟨20531525012626225187677099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27375366683501633583569465 20531525012626225187677099)
  ·
    refine ⟨30797287518939337781515649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20531525012626225187677099 30797287518939337781515649)
    ·
      refine ⟨23097965639204503336136737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30797287518939337781515649 23097965639204503336136737)
      ·
        refine ⟨17323474229403377502102553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23097965639204503336136737 17323474229403377502102553)
        ·
          refine ⟨12992605672052533126576915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17323474229403377502102553 12992605672052533126576915)
          ·
            refine ⟨19488908508078799689865373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12992605672052533126576915 19488908508078799689865373)
            ·
              refine ⟨7308340690529549883699515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19488908508078799689865373 7308340690529549883699515)
              ·
                refine ⟨10962511035794324825549273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308340690529549883699515 10962511035794324825549273)
                ·
                  refine ⟨8221883276845743619161955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10962511035794324825549273 8221883276845743619161955)
                  ·
                    refine ⟨12332824915268615428742933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8221883276845743619161955 12332824915268615428742933)
                    ·
                      refine ⟨578101167903216348222325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12332824915268615428742933 578101167903216348222325)
                      ·
                        rfl

theorem cell23_1125848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1125848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125848 prefixEnd_1125848 := by exact prefixLift 1125848
  have htrace : WordTrace (prefixWord ++ tailWord_1125848) baseStart_1125848 baseEnd_1125848 := by
    simpa [prefixWord, tailWord_1125848, baseEnd_1125848] using wordTrace_append hprefix tailTrace_1125848
  have hstable : (prefixWord ++ tailWord_1125848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125848).length < 2 ^ (prefixWord ++ tailWord_1125848).sum := by decide
  have hdescent : baseEnd_1125848 < baseStart_1125848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125855 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1125855 : Nat := 118140960795 + 1125855 * 2 ^ 59
def prefixEnd_1125855 : Nat := 4983230072969 + 3 ^ 40 * 1125855 * 2
def baseEnd_1125855 : Nat := 578104762267797820834793

theorem tailTrace_1125855 : CollatzResearch.WordTrace tailWord_1125855 prefixEnd_1125855 578104762267797820834793 := by
  unfold tailWord_1125855
  simp only [CollatzResearch.WordTrace]
  refine ⟨41063305336227090570859019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27375536890818060380572679 41063305336227090570859019)
  ·
    refine ⟨61594958004340635856288529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41063305336227090570859019 61594958004340635856288529)
    ·
      refine ⟨46196218503255476892216397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61594958004340635856288529 46196218503255476892216397)
      ·
        refine ⟨17323581938720803834581149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46196218503255476892216397 17323581938720803834581149)
        ·
          refine ⟨6496343227020301437967931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17323581938720803834581149 6496343227020301437967931)
          ·
            refine ⟨9744514840530452156951897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496343227020301437967931 9744514840530452156951897)
            ·
              refine ⟨7308386130397839117713923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9744514840530452156951897 7308386130397839117713923)
              ·
                refine ⟨10962579195596758676570885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308386130397839117713923 10962579195596758676570885)
                ·
                  refine ⟨2055483599174392251857041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10962579195596758676570885 2055483599174392251857041)
                  ·
                    refine ⟨1541612699380794188892781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2055483599174392251857041 1541612699380794188892781)
                    ·
                      refine ⟨578104762267797820834793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1541612699380794188892781 578104762267797820834793)
                      ·
                        rfl

theorem cell23_1125855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1125855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125855 prefixEnd_1125855 := by exact prefixLift 1125855
  have htrace : WordTrace (prefixWord ++ tailWord_1125855) baseStart_1125855 baseEnd_1125855 := by
    simpa [prefixWord, tailWord_1125855, baseEnd_1125855] using wordTrace_append hprefix tailTrace_1125855
  have hstable : (prefixWord ++ tailWord_1125855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125855).length < 2 ^ (prefixWord ++ tailWord_1125855).sum := by decide
  have hdescent : baseEnd_1125855 < baseStart_1125855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125905 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_1125905 : Nat := 118140960795 + 1125905 * 2 ^ 59
def prefixEnd_1125905 : Nat := 4983230072969 + 3 ^ 40 * 1125905 * 2
def baseEnd_1125905 : Nat := 192710145433507541736521

theorem tailTrace_1125905 : CollatzResearch.WordTrace tailWord_1125905 prefixEnd_1125905 192710145433507541736521 := by
  unfold tailWord_1125905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41065128986045949110179169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27376752657363966073452779 41065128986045949110179169)
  ·
    refine ⟨30798846739534461832634377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41065128986045949110179169 30798846739534461832634377)
    ·
      refine ⟨23099135054650846374475783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30798846739534461832634377 23099135054650846374475783)
      ·
        refine ⟨34648702581976269561713675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23099135054650846374475783 34648702581976269561713675)
        ·
          refine ⟨51973053872964404342570513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34648702581976269561713675 51973053872964404342570513)
          ·
            refine ⟨38979790404723303256927885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51973053872964404342570513 38979790404723303256927885)
            ·
              refine ⟨14617421401771238721347957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38979790404723303256927885 14617421401771238721347957)
              ·
                refine ⟨1370383256416053630126371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14617421401771238721347957 1370383256416053630126371)
                ·
                  refine ⟨2055574884624080445189557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370383256416053630126371 2055574884624080445189557)
                  ·
                    refine ⟨192710145433507541736521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2055574884624080445189557 192710145433507541736521)
                    ·
                      rfl

theorem cell23_1125905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_1125905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125905 prefixEnd_1125905 := by exact prefixLift 1125905
  have htrace : WordTrace (prefixWord ++ tailWord_1125905) baseStart_1125905 baseEnd_1125905 := by
    simpa [prefixWord, tailWord_1125905, baseEnd_1125905] using wordTrace_append hprefix tailTrace_1125905
  have hstable : (prefixWord ++ tailWord_1125905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125905).length < 2 ^ (prefixWord ++ tailWord_1125905).sum := by decide
  have hdescent : baseEnd_1125905 < baseStart_1125905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125919 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 1, 1, 3]
def baseStart_1125919 : Nat := 118140960795 + 1125919 * 2 ^ 59
def prefixEnd_1125919 : Nat := 4983230072969 + 3 ^ 40 * 1125919 * 2
def baseEnd_1125919 : Nat := 578137625029685570434499

theorem tailTrace_1125919 : CollatzResearch.WordTrace tailWord_1125919 prefixEnd_1125919 578137625029685570434499 := by
  unfold tailWord_1125919
  simp only [CollatzResearch.WordTrace]
  refine ⟨41065639607995229501188811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27377093071996819667459207 41065639607995229501188811)
  ·
    refine ⟨61598459411992844251783217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41065639607995229501188811 61598459411992844251783217)
    ·
      refine ⟨46198844558994633188837413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61598459411992844251783217 46198844558994633188837413)
      ·
        refine ⟨8662283354811493722907015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46198844558994633188837413 8662283354811493722907015)
        ·
          refine ⟨12993425032217240584360523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662283354811493722907015 12993425032217240584360523)
          ·
            refine ⟨19490137548325860876540785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993425032217240584360523 19490137548325860876540785)
            ·
              refine ⟨14617603161244395657405589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19490137548325860876540785 14617603161244395657405589)
              ·
                refine ⟨685200148183331046440887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14617603161244395657405589 685200148183331046440887)
                ·
                  refine ⟨1027800222274996569661331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685200148183331046440887 1027800222274996569661331)
                  ·
                    refine ⟨1541700333412494854491997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027800222274996569661331 1541700333412494854491997)
                    ·
                      refine ⟨578137625029685570434499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1541700333412494854491997 578137625029685570434499)
                      ·
                        rfl

theorem cell23_1125919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_1125919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125919 prefixEnd_1125919 := by exact prefixLift 1125919
  have htrace : WordTrace (prefixWord ++ tailWord_1125919) baseStart_1125919 baseEnd_1125919 := by
    simpa [prefixWord, tailWord_1125919, baseEnd_1125919] using wordTrace_append hprefix tailTrace_1125919
  have hstable : (prefixWord ++ tailWord_1125919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125919).length < 2 ^ (prefixWord ++ tailWord_1125919).sum := by decide
  have hdescent : baseEnd_1125919 < baseStart_1125919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125925 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_1125925 : Nat := 118140960795 + 1125925 * 2 ^ 59
def prefixEnd_1125925 : Nat := 4983230072969 + 3 ^ 40 * 1125925 * 2
def baseEnd_1125925 : Nat := 578140705913612546959471

theorem tailTrace_1125925 : CollatzResearch.WordTrace tailWord_1125925 prefixEnd_1125925 578140705913612546959471 := by
  unfold tailWord_1125925
  simp only [CollatzResearch.WordTrace]
  refine ⟨41065858445973492525907229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27377238963982328350604819 41065858445973492525907229)
  ·
    refine ⟨15399696917240059697215211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41065858445973492525907229 15399696917240059697215211)
    ·
      refine ⟨23099545375860089545822817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15399696917240059697215211 23099545375860089545822817)
      ·
        refine ⟨17324659031895067159367113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23099545375860089545822817 17324659031895067159367113)
        ·
          refine ⟨12993494273921300369525335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17324659031895067159367113 12993494273921300369525335)
          ·
            refine ⟨19490241410881950554288003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993494273921300369525335 19490241410881950554288003)
            ·
              refine ⟨29235362116322925831432005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19490241410881950554288003 29235362116322925831432005)
              ·
                refine ⟨5481630396810548593393501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29235362116322925831432005 5481630396810548593393501)
                ·
                  refine ⟨2055611398803955722522563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5481630396810548593393501 2055611398803955722522563)
                  ·
                    refine ⟨3083417098205933583783845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2055611398803955722522563 3083417098205933583783845)
                    ·
                      refine ⟨578140705913612546959471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3083417098205933583783845 578140705913612546959471)
                      ·
                        rfl

theorem cell23_1125925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_1125925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125925 prefixEnd_1125925 := by exact prefixLift 1125925
  have htrace : WordTrace (prefixWord ++ tailWord_1125925) baseStart_1125925 baseEnd_1125925 := by
    simpa [prefixWord, tailWord_1125925, baseEnd_1125925] using wordTrace_append hprefix tailTrace_1125925
  have hstable : (prefixWord ++ tailWord_1125925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125925).length < 2 ^ (prefixWord ++ tailWord_1125925).sum := by decide
  have hdescent : baseEnd_1125925 < baseStart_1125925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125965 : List Nat := [1, 6, 1, 1, 14]
def baseStart_1125965 : Nat := 118140960795 + 1125965 * 2 ^ 59
def prefixEnd_1125965 : Nat := 4983230072969 + 3 ^ 40 * 1125965 * 2
def baseEnd_1125965 : Nat := 793088127763775569903

theorem tailTrace_1125965 : CollatzResearch.WordTrace tailWord_1125965 prefixEnd_1125965 793088127763775569903 := by
  unfold tailWord_1125965
  simp only [CollatzResearch.WordTrace]
  refine ⟨41067317365828579357363349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27378211577219052904908899 41067317365828579357363349)
  ·
    refine ⟨1925030501523214657376407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41067317365828579357363349 1925030501523214657376407)
    ·
      refine ⟨2887545752284821986064611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925030501523214657376407 2887545752284821986064611)
      ·
        refine ⟨4331318628427232979096917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2887545752284821986064611 4331318628427232979096917)
        ·
          refine ⟨793088127763775569903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 4331318628427232979096917 793088127763775569903)
          ·
            rfl

theorem cell23_1125965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 14].length) (baseStart_1125965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1125965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1125965 prefixEnd_1125965 := by exact prefixLift 1125965
  have htrace : WordTrace (prefixWord ++ tailWord_1125965) baseStart_1125965 baseEnd_1125965 := by
    simpa [prefixWord, tailWord_1125965, baseEnd_1125965] using wordTrace_append hprefix tailTrace_1125965
  have hstable : (prefixWord ++ tailWord_1125965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125965).length < 2 ^ (prefixWord ++ tailWord_1125965).sum := by decide
  have hdescent : baseEnd_1125965 < baseStart_1125965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126025 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_1126025 : Nat := 118140960795 + 1126025 * 2 ^ 59
def prefixEnd_1126025 : Nat := 4983230072969 + 3 ^ 40 * 1126025 * 2
def baseEnd_1126025 : Nat := 192730684659687385236337

theorem tailTrace_1126025 : CollatzResearch.WordTrace tailWord_1126025 prefixEnd_1126025 192730684659687385236337 := by
  unfold tailWord_1126025
  simp only [CollatzResearch.WordTrace]
  refine ⟨41069505745611209604547529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27379670497074139736365019 41069505745611209604547529)
  ·
    refine ⟨30802129309208407203410647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41069505745611209604547529 30802129309208407203410647)
    ·
      refine ⟨46203193963812610805115971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30802129309208407203410647 46203193963812610805115971)
      ·
        refine ⟨69304790945718916207673957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46203193963812610805115971 69304790945718916207673957)
        ·
          refine ⟨12994648302322296788938867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69304790945718916207673957 12994648302322296788938867)
          ·
            refine ⟨19491972453483445183408301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12994648302322296788938867 19491972453483445183408301)
            ·
              refine ⟨7309489670056291943778113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19491972453483445183408301 7309489670056291943778113)
              ·
                refine ⟨5482117252542218957833585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7309489670056291943778113 5482117252542218957833585)
                ·
                  refine ⟨4111587939406664218375189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5482117252542218957833585 4111587939406664218375189)
                  ·
                    refine ⟨192730684659687385236337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4111587939406664218375189 192730684659687385236337)
                    ·
                      rfl

theorem cell23_1126025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_1126025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126025 prefixEnd_1126025 := by exact prefixLift 1126025
  have htrace : WordTrace (prefixWord ++ tailWord_1126025) baseStart_1126025 baseEnd_1126025 := by
    simpa [prefixWord, tailWord_1126025, baseEnd_1126025] using wordTrace_append hprefix tailTrace_1126025
  have hstable : (prefixWord ++ tailWord_1126025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126025).length < 2 ^ (prefixWord ++ tailWord_1126025).sum := by decide
  have hdescent : baseEnd_1126025 < baseStart_1126025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126026 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1126026 : Nat := 118140960795 + 1126026 * 2 ^ 59
def prefixEnd_1126026 : Nat := 4983230072969 + 3 ^ 40 * 1126026 * 2
def baseEnd_1126026 : Nat := 578192567459716651796507

theorem tailTrace_1126026 : CollatzResearch.WordTrace tailWord_1126026 prefixEnd_1126026 578192567459716651796507 := by
  unfold tailWord_1126026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267385554651896693833483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27379694812405057850222621 10267385554651896693833483)
  ·
    refine ⟨15401078331977845040750225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10267385554651896693833483 15401078331977845040750225)
    ·
      refine ⟨11550808748983383780562669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15401078331977845040750225 11550808748983383780562669)
      ·
        refine ⟨4331553280868768917711001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11550808748983383780562669 4331553280868768917711001)
        ·
          refine ⟨3248664960651576688283251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4331553280868768917711001 3248664960651576688283251)
          ·
            refine ⟨4872997440977365032424877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248664960651576688283251 4872997440977365032424877)
            ·
              refine ⟨1827374040366511887159329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4872997440977365032424877 1827374040366511887159329)
              ·
                refine ⟨1370530530274883915369497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827374040366511887159329 1370530530274883915369497)
                ·
                  refine ⟨1027897897706162936527123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370530530274883915369497 1027897897706162936527123)
                  ·
                    refine ⟨1541846846559244404790685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1027897897706162936527123 1541846846559244404790685)
                    ·
                      refine ⟨578192567459716651796507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1541846846559244404790685 578192567459716651796507)
                      ·
                        rfl

theorem cell23_1126026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1126026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126026 prefixEnd_1126026 := by exact prefixLift 1126026
  have htrace : WordTrace (prefixWord ++ tailWord_1126026) baseStart_1126026 baseEnd_1126026 := by
    simpa [prefixWord, tailWord_1126026, baseEnd_1126026] using wordTrace_append hprefix tailTrace_1126026
  have hstable : (prefixWord ++ tailWord_1126026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126026).length < 2 ^ (prefixWord ++ tailWord_1126026).sum := by decide
  have hdescent : baseEnd_1126026 < baseStart_1126026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2]
def baseStart_1126032 : Nat := 118140960795 + 1126032 * 2 ^ 59
def prefixEnd_1126032 : Nat := 4983230072969 + 3 ^ 40 * 1126032 * 2
def baseEnd_1126032 : Nat := 578195648343643628321479

theorem tailTrace_1126032 : CollatzResearch.WordTrace tailWord_1126032 prefixEnd_1126032 578195648343643628321479 := by
  unfold tailWord_1126032
  simp only [CollatzResearch.WordTrace]
  refine ⟨20534880528292924900026175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27379840704390566533368233 20534880528292924900026175)
  ·
    refine ⟨30802320792439387350039263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20534880528292924900026175 30802320792439387350039263)
    ·
      refine ⟨46203481188659081025058895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30802320792439387350039263 46203481188659081025058895)
      ·
        refine ⟨69305221782988621537588343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46203481188659081025058895 69305221782988621537588343)
        ·
          refine ⟨103957832674482932306382515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69305221782988621537588343 103957832674482932306382515)
          ·
            refine ⟨155936749011724398459573773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103957832674482932306382515 155936749011724398459573773)
            ·
              refine ⟨58476280879396649422340165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155936749011724398459573773 58476280879396649422340165)
              ·
                refine ⟨10964302664886871766688781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58476280879396649422340165 10964302664886871766688781)
                ·
                  refine ⟨4111613499332576912508293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10964302664886871766688781 4111613499332576912508293)
                  ·
                    refine ⟨770927531124858171095305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4111613499332576912508293 770927531124858171095305)
                    ·
                      refine ⟨578195648343643628321479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770927531124858171095305 578195648343643628321479)
                      ·
                        rfl

theorem cell23_1126032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2].length) (baseStart_1126032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126032 prefixEnd_1126032 := by exact prefixLift 1126032
  have htrace : WordTrace (prefixWord ++ tailWord_1126032) baseStart_1126032 baseEnd_1126032 := by
    simpa [prefixWord, tailWord_1126032, baseEnd_1126032] using wordTrace_append hprefix tailTrace_1126032
  have hstable : (prefixWord ++ tailWord_1126032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126032).length < 2 ^ (prefixWord ++ tailWord_1126032).sum := by decide
  have hdescent : baseEnd_1126032 < baseStart_1126032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126069 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1126069 : Nat := 118140960795 + 1126069 * 2 ^ 59
def prefixEnd_1126069 : Nat := 4983230072969 + 3 ^ 40 * 1126069 * 2
def baseEnd_1126069 : Nat := 578214647127859983558809

theorem tailTrace_1126069 : CollatzResearch.WordTrace tailWord_1126069 prefixEnd_1126069 578214647127859983558809 := by
  unfold tailWord_1126069
  simp only [CollatzResearch.WordTrace]
  refine ⟨41071110557451805119149261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27380740371634536746099507 41071110557451805119149261)
  ·
    refine ⟨15401666459044426919680973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41071110557451805119149261 15401666459044426919680973)
    ·
      refine ⟨5775624922141660094880365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15401666459044426919680973 5775624922141660094880365)
      ·
        refine ⟨2165859345803122535580137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5775624922141660094880365 2165859345803122535580137)
        ·
          refine ⟨1624394509352341901685103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165859345803122535580137 1624394509352341901685103)
          ·
            refine ⟨2436591764028512852527655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624394509352341901685103 2436591764028512852527655)
            ·
              refine ⟨3654887646042769278791483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436591764028512852527655 3654887646042769278791483)
              ·
                refine ⟨5482331469064153918187225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654887646042769278791483 5482331469064153918187225)
                ·
                  refine ⟨4111748601798115438640419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5482331469064153918187225 4111748601798115438640419)
                  ·
                    refine ⟨6167622902697173157960629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4111748601798115438640419 6167622902697173157960629)
                    ·
                      refine ⟨578214647127859983558809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6167622902697173157960629 578214647127859983558809)
                      ·
                        rfl

theorem cell23_1126069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1126069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126069 prefixEnd_1126069 := by exact prefixLift 1126069
  have htrace : WordTrace (prefixWord ++ tailWord_1126069) baseStart_1126069 baseEnd_1126069 := by
    simpa [prefixWord, tailWord_1126069, baseEnd_1126069] using wordTrace_append hprefix tailTrace_1126069
  have hstable : (prefixWord ++ tailWord_1126069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126069).length < 2 ^ (prefixWord ++ tailWord_1126069).sum := by decide
  have hdescent : baseEnd_1126069 < baseStart_1126069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126100 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1126100 : Nat := 118140960795 + 1126100 * 2 ^ 59
def prefixEnd_1126100 : Nat := 4983230072969 + 3 ^ 40 * 1126100 * 2
def baseEnd_1126100 : Nat := 578230565028149362271167

theorem tailTrace_1126100 : CollatzResearch.WordTrace tailWord_1126100 prefixEnd_1126100 578230565028149362271167 := by
  unfold tailWord_1126100
  simp only [CollatzResearch.WordTrace]
  refine ⟨20536120610169748706763877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27381494146892998275685169 20536120610169748706763877)
  ·
    refine ⟨3850522614406827882518227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20536120610169748706763877 3850522614406827882518227)
    ·
      refine ⟨5775783921610241823777341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3850522614406827882518227 5775783921610241823777341)
      ·
        refine ⟨2165918970603840683916503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5775783921610241823777341 2165918970603840683916503)
        ·
          refine ⟨3248878455905761025874755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165918970603840683916503 3248878455905761025874755)
          ·
            refine ⟨4873317683858641538812133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248878455905761025874755 4873317683858641538812133)
            ·
              refine ⟨913747065723495288527275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4873317683858641538812133 913747065723495288527275)
              ·
                refine ⟨1370620598585242932790913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913747065723495288527275 1370620598585242932790913)
                ·
                  refine ⟨1027965448938932199593185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370620598585242932790913 1027965448938932199593185)
                  ·
                    refine ⟨770974086704199149694889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1027965448938932199593185 770974086704199149694889)
                    ·
                      refine ⟨578230565028149362271167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 770974086704199149694889 578230565028149362271167)
                      ·
                        rfl

theorem cell23_1126100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1126100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126100 prefixEnd_1126100 := by exact prefixLift 1126100
  have htrace : WordTrace (prefixWord ++ tailWord_1126100) baseStart_1126100 baseEnd_1126100 := by
    simpa [prefixWord, tailWord_1126100, baseEnd_1126100] using wordTrace_append hprefix tailTrace_1126100
  have hstable : (prefixWord ++ tailWord_1126100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126100).length < 2 ^ (prefixWord ++ tailWord_1126100).sum := by decide
  have hdescent : baseEnd_1126100 < baseStart_1126100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126122 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1126122 : Nat := 118140960795 + 1126122 * 2 ^ 59
def prefixEnd_1126122 : Nat := 4983230072969 + 3 ^ 40 * 1126122 * 2
def baseEnd_1126122 : Nat := 578241861602548276196065

theorem tailTrace_1126122 : CollatzResearch.WordTrace tailWord_1126122 prefixEnd_1126122 578241861602548276196065 := by
  unfold tailWord_1126122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268260906564948792707155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27382029084173196780552413 10268260906564948792707155)
  ·
    refine ⟨15402391359847423189060733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10268260906564948792707155 15402391359847423189060733)
    ·
      refine ⟨5775896759942783695897775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15402391359847423189060733 5775896759942783695897775)
      ·
        refine ⟨8663845139914175543846663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775896759942783695897775 8663845139914175543846663)
        ·
          refine ⟨12995767709871263315769995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8663845139914175543846663 12995767709871263315769995)
          ·
            refine ⟨19493651564806894973654993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12995767709871263315769995 19493651564806894973654993)
            ·
              refine ⟨14620238673605171230241245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19493651564806894973654993 14620238673605171230241245)
              ·
                refine ⟨5482589502601939211340467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14620238673605171230241245 5482589502601939211340467)
                ·
                  refine ⟨8223884253902908817010701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482589502601939211340467 8223884253902908817010701)
                  ·
                    refine ⟨3083956595213590806379013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8223884253902908817010701 3083956595213590806379013)
                    ·
                      refine ⟨578241861602548276196065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3083956595213590806379013 578241861602548276196065)
                      ·
                        rfl

theorem cell23_1126122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1126122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126122 prefixEnd_1126122 := by exact prefixLift 1126122
  have htrace : WordTrace (prefixWord ++ tailWord_1126122) baseStart_1126122 baseEnd_1126122 := by
    simpa [prefixWord, tailWord_1126122, baseEnd_1126122] using wordTrace_append hprefix tailTrace_1126122
  have hstable : (prefixWord ++ tailWord_1126122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126122).length < 2 ^ (prefixWord ++ tailWord_1126122).sum := by decide
  have hdescent : baseEnd_1126122 < baseStart_1126122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126196 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1126196 : Nat := 118140960795 + 1126196 * 2 ^ 59
def prefixEnd_1126196 : Nat := 4983230072969 + 3 ^ 40 * 1126196 * 2
def baseEnd_1126196 : Nat := 64253317685664554074525

theorem tailTrace_1126196 : CollatzResearch.WordTrace tailWord_1126196 prefixEnd_1126196 64253317685664554074525 := by
  unfold tailWord_1126196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20537871313995852904511221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27383828418661137206014961 20537871313995852904511221)
  ·
    refine ⟨1925425435687111209797927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20537871313995852904511221 1925425435687111209797927)
    ·
      refine ⟨2888138153530666814696891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925425435687111209797927 2888138153530666814696891)
      ·
        refine ⟨4332207230296000222045337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888138153530666814696891 4332207230296000222045337)
        ·
          refine ⟨3249155422722000166534003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332207230296000222045337 3249155422722000166534003)
          ·
            refine ⟨4873733134083000249801005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249155422722000166534003 4873733134083000249801005)
            ·
              refine ⟨1827649925281125093675377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4873733134083000249801005 1827649925281125093675377)
              ·
                refine ⟨1370737443960843820256533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827649925281125093675377 1370737443960843820256533)
                ·
                  refine ⟨64253317685664554074525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1370737443960843820256533 64253317685664554074525)
                  ·
                    rfl

theorem cell23_1126196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1126196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126196 prefixEnd_1126196 := by exact prefixLift 1126196
  have htrace : WordTrace (prefixWord ++ tailWord_1126196) baseStart_1126196 baseEnd_1126196 := by
    simpa [prefixWord, tailWord_1126196, baseEnd_1126196] using wordTrace_append hprefix tailTrace_1126196
  have hstable : (prefixWord ++ tailWord_1126196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126196).length < 2 ^ (prefixWord ++ tailWord_1126196).sum := by decide
  have hdescent : baseEnd_1126196 < baseStart_1126196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126226 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1126226 : Nat := 118140960795 + 1126226 * 2 ^ 59
def prefixEnd_1126226 : Nat := 4983230072969 + 3 ^ 40 * 1126226 * 2
def baseEnd_1126226 : Nat := 192765087863538623098529

theorem tailTrace_1126226 : CollatzResearch.WordTrace tailWord_1126226 prefixEnd_1126226 192765087863538623098529 := by
  unfold tailWord_1126226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10269209204470755233153633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27384557878588680621743021 10269209204470755233153633)
  ·
    refine ⟨7701906903353066424865225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10269209204470755233153633 7701906903353066424865225)
    ·
      refine ⟨5776430177514799818648919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7701906903353066424865225 5776430177514799818648919)
      ·
        refine ⟨8664645266272199727973379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776430177514799818648919 8664645266272199727973379)
        ·
          refine ⟨12996967899408299591960069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8664645266272199727973379 12996967899408299591960069)
          ·
            refine ⟨2436931481139056173492513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12996967899408299591960069 2436931481139056173492513)
            ·
              refine ⟨1827698610854292130119385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436931481139056173492513 1827698610854292130119385)
              ·
                refine ⟨1370773958140719097589539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827698610854292130119385 1370773958140719097589539)
                ·
                  refine ⟨2056160937211078646384309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370773958140719097589539 2056160937211078646384309)
                  ·
                    refine ⟨192765087863538623098529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2056160937211078646384309 192765087863538623098529)
                    ·
                      rfl

theorem cell23_1126226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1126226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126226 prefixEnd_1126226 := by exact prefixLift 1126226
  have htrace : WordTrace (prefixWord ++ tailWord_1126226) baseStart_1126226 baseEnd_1126226 := by
    simpa [prefixWord, tailWord_1126226, baseEnd_1126226] using wordTrace_append hprefix tailTrace_1126226
  have hstable : (prefixWord ++ tailWord_1126226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126226).length < 2 ^ (prefixWord ++ tailWord_1126226).sum := by decide
  have hdescent : baseEnd_1126226 < baseStart_1126226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126239 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 4, 4]
def baseStart_1126239 : Nat := 118140960795 + 1126239 * 2 ^ 59
def prefixEnd_1126239 : Nat := 4983230072969 + 3 ^ 40 * 1126239 * 2
def baseEnd_1126239 : Nat := 192767312946374772811009

theorem tailTrace_1126239 : CollatzResearch.WordTrace tailWord_1126239 prefixEnd_1126239 192767312946374772811009 := by
  unfold tailWord_1126239
  simp only [CollatzResearch.WordTrace]
  refine ⟨41077310966835924152837771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27384873977890616101891847 41077310966835924152837771)
  ·
    refine ⟨61615966450253886229256657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41077310966835924152837771 61615966450253886229256657)
    ·
      refine ⟨46211974837690414671942493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61615966450253886229256657 46211974837690414671942493)
      ·
        refine ⟨17329490564133905501978435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46211974837690414671942493 17329490564133905501978435)
        ·
          refine ⟨25994235846200858252967653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17329490564133905501978435 25994235846200858252967653)
          ·
            refine ⟨4873919221162660922431435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25994235846200858252967653 4873919221162660922431435)
            ·
              refine ⟨7310878831743991383647153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4873919221162660922431435 7310878831743991383647153)
              ·
                refine ⟨5483159123807993537735365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7310878831743991383647153 5483159123807993537735365)
                ·
                  refine ⟨1028092335713998788325381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5483159123807993537735365 1028092335713998788325381)
                  ·
                    refine ⟨192767312946374772811009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1028092335713998788325381 192767312946374772811009)
                    ·
                      rfl

theorem cell23_1126239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_1126239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126239 prefixEnd_1126239 := by exact prefixLift 1126239
  have htrace : WordTrace (prefixWord ++ tailWord_1126239) baseStart_1126239 baseEnd_1126239 := by
    simpa [prefixWord, tailWord_1126239, baseEnd_1126239] using wordTrace_append hprefix tailTrace_1126239
  have hstable : (prefixWord ++ tailWord_1126239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126239).length < 2 ^ (prefixWord ++ tailWord_1126239).sum := by decide
  have hdescent : baseEnd_1126239 < baseStart_1126239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126240 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 1, 1, 3]
def baseStart_1126240 : Nat := 118140960795 + 1126240 * 2 ^ 59
def prefixEnd_1126240 : Nat := 4983230072969 + 3 ^ 40 * 1126240 * 2
def baseEnd_1126240 : Nat := 578302452319778814520523

theorem tailTrace_1126240 : CollatzResearch.WordTrace tailWord_1126240 prefixEnd_1126240 578302452319778814520523 := by
  unfold tailWord_1126240
  simp only [CollatzResearch.WordTrace]
  refine ⟨20538673719916150661812087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27384898293221534215749449 20538673719916150661812087)
  ·
    refine ⟨30808010579874225992718131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20538673719916150661812087 30808010579874225992718131)
    ·
      refine ⟨46212015869811338989077197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30808010579874225992718131 46212015869811338989077197)
      ·
        refine ⟨17329505951179252120903949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46212015869811338989077197 17329505951179252120903949)
        ·
          refine ⟨6498564731692219545338981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17329505951179252120903949 6498564731692219545338981)
          ·
            refine ⟨1218480887192291164751059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6498564731692219545338981 1218480887192291164751059)
            ·
              refine ⟨1827721330788436747126589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218480887192291164751059 1827721330788436747126589)
              ·
                refine ⟨685395499045663780172471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1827721330788436747126589 685395499045663780172471)
                ·
                  refine ⟨1028093248568495670258707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685395499045663780172471 1028093248568495670258707)
                  ·
                    refine ⟨1542139872852743505388061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028093248568495670258707 1542139872852743505388061)
                    ·
                      refine ⟨578302452319778814520523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542139872852743505388061 578302452319778814520523)
                      ·
                        rfl

theorem cell23_1126240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_1126240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126240 prefixEnd_1126240 := by exact prefixLift 1126240
  have htrace : WordTrace (prefixWord ++ tailWord_1126240) baseStart_1126240 baseEnd_1126240 := by
    simpa [prefixWord, tailWord_1126240, baseEnd_1126240] using wordTrace_append hprefix tailTrace_1126240
  have hstable : (prefixWord ++ tailWord_1126240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126240).length < 2 ^ (prefixWord ++ tailWord_1126240).sum := by decide
  have hdescent : baseEnd_1126240 < baseStart_1126240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126250 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1126250 : Nat := 118140960795 + 1126250 * 2 ^ 59
def prefixEnd_1126250 : Nat := 4983230072969 + 3 ^ 40 * 1126250 * 2
def baseEnd_1126250 : Nat := 578307587126323775395477

theorem tailTrace_1126250 : CollatzResearch.WordTrace tailWord_1126250 prefixEnd_1126250 578307587126323775395477 := by
  unfold tailWord_1126250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10269428042449018257872051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27385141446530715354325469 10269428042449018257872051)
  ·
    refine ⟨15404142063673527386808077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10269428042449018257872051 15404142063673527386808077)
    ·
      refine ⟨5776553273877572770053029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15404142063673527386808077 5776553273877572770053029)
      ·
        refine ⟨1083103738852044894384943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5776553273877572770053029 1083103738852044894384943)
        ·
          refine ⟨1624655608278067341577415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083103738852044894384943 1624655608278067341577415)
          ·
            refine ⟨2436983412417101012366123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624655608278067341577415 2436983412417101012366123)
            ·
              refine ⟨3655475118625651518549185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436983412417101012366123 3655475118625651518549185)
              ·
                refine ⟨2741606338969238638911889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655475118625651518549185 2741606338969238638911889)
                ·
                  refine ⟨2056204754226928979183917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2741606338969238638911889 2056204754226928979183917)
                  ·
                    refine ⟨771076782835098367193969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056204754226928979183917 771076782835098367193969)
                    ·
                      refine ⟨578307587126323775395477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771076782835098367193969 578307587126323775395477)
                      ·
                        rfl

theorem cell23_1126250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1126250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126250 prefixEnd_1126250 := by exact prefixLift 1126250
  have htrace : WordTrace (prefixWord ++ tailWord_1126250) baseStart_1126250 baseEnd_1126250 := by
    simpa [prefixWord, tailWord_1126250, baseEnd_1126250] using wordTrace_append hprefix tailTrace_1126250
  have hstable : (prefixWord ++ tailWord_1126250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126250).length < 2 ^ (prefixWord ++ tailWord_1126250).sum := by decide
  have hdescent : baseEnd_1126250 < baseStart_1126250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126252 : List Nat := [2, 2, 1, 1, 4, 2, 11]
def baseStart_1126252 : Nat := 118140960795 + 1126252 * 2 ^ 59
def prefixEnd_1126252 : Nat := 4983230072969 + 3 ^ 40 * 1126252 * 2
def baseEnd_1126252 : Nat := 7139612519600404537907

theorem tailTrace_1126252 : CollatzResearch.WordTrace tailWord_1126252 prefixEnd_1126252 7139612519600404537907 := by
  unfold tailWord_1126252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20538892557894413686530505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27385190077192551582040673 20538892557894413686530505)
  ·
    refine ⟨15404169418420810264897879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20538892557894413686530505 15404169418420810264897879)
    ·
      refine ⟨23106254127631215397346819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15404169418420810264897879 23106254127631215397346819)
      ·
        refine ⟨34659381191446823096020229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23106254127631215397346819 34659381191446823096020229)
        ·
          refine ⟨6498633973396279330503793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34659381191446823096020229 6498633973396279330503793)
          ·
            refine ⟨4873975480047209497877845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6498633973396279330503793 4873975480047209497877845)
            ·
              refine ⟨7139612519600404537907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4873975480047209497877845 7139612519600404537907)
              ·
                rfl

theorem cell23_1126252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 11].length) (baseStart_1126252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126252 prefixEnd_1126252 := by exact prefixLift 1126252
  have htrace : WordTrace (prefixWord ++ tailWord_1126252) baseStart_1126252 baseEnd_1126252 := by
    simpa [prefixWord, tailWord_1126252, baseEnd_1126252] using wordTrace_append hprefix tailTrace_1126252
  have hstable : (prefixWord ++ tailWord_1126252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126252).length < 2 ^ (prefixWord ++ tailWord_1126252).sum := by decide
  have hdescent : baseEnd_1126252 < baseStart_1126252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126272 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1126272 : Nat := 118140960795 + 1126272 * 2 ^ 59
def prefixEnd_1126272 : Nat := 4983230072969 + 3 ^ 40 * 1126272 * 2
def baseEnd_1126272 : Nat := 578318883700722689320375

theorem tailTrace_1126272 : CollatzResearch.WordTrace tailWord_1126272 prefixEnd_1126272 578318883700722689320375 := by
  unfold tailWord_1126272
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539257287858185394394535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27385676383810913859192713 20539257287858185394394535)
  ·
    refine ⟨30808885931787278091591803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20539257287858185394394535 30808885931787278091591803)
    ·
      refine ⟨46213328897680917137387705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30808885931787278091591803 46213328897680917137387705)
      ·
        refine ⟨34659996673260687853040779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46213328897680917137387705 34659996673260687853040779)
        ·
          refine ⟨51989995009891031779561169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34659996673260687853040779 51989995009891031779561169)
          ·
            refine ⟨38992496257418273834670877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51989995009891031779561169 38992496257418273834670877)
            ·
              refine ⟨14622186096531852688001579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38992496257418273834670877 14622186096531852688001579)
              ·
                refine ⟨21933279144797779032002369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14622186096531852688001579 21933279144797779032002369)
                ·
                  refine ⟨16449959358598334274001777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21933279144797779032002369 16449959358598334274001777)
                  ·
                    refine ⟨12337469518948750705501333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16449959358598334274001777 12337469518948750705501333)
                    ·
                      refine ⟨578318883700722689320375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12337469518948750705501333 578318883700722689320375)
                      ·
                        rfl

theorem cell23_1126272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1126272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126272 prefixEnd_1126272 := by exact prefixLift 1126272
  have htrace : WordTrace (prefixWord ++ tailWord_1126272) baseStart_1126272 baseEnd_1126272 := by
    simpa [prefixWord, tailWord_1126272, baseEnd_1126272] using wordTrace_append hprefix tailTrace_1126272
  have hstable : (prefixWord ++ tailWord_1126272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126272).length < 2 ^ (prefixWord ++ tailWord_1126272).sum := by decide
  have hdescent : baseEnd_1126272 < baseStart_1126272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126280 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_1126280 : Nat := 118140960795 + 1126280 * 2 ^ 59
def prefixEnd_1126280 : Nat := 4983230072969 + 3 ^ 40 * 1126280 * 2
def baseEnd_1126280 : Nat := 578322991545958658020339

theorem tailTrace_1126280 : CollatzResearch.WordTrace tailWord_1126280 prefixEnd_1126280 578322991545958658020339 := by
  unfold tailWord_1126280
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539403179843694077540147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27385870906458258770053529 20539403179843694077540147)
  ·
    refine ⟨30809104769765541116310221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20539403179843694077540147 30809104769765541116310221)
    ·
      refine ⟨11553414288662077918616333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30809104769765541116310221 11553414288662077918616333)
      ·
        refine ⟨4332530358248279219481125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11553414288662077918616333 4332530358248279219481125)
        ·
          refine ⟨812349442171552353652711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4332530358248279219481125 812349442171552353652711)
          ·
            refine ⟨1218524163257328530479067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812349442171552353652711 1218524163257328530479067)
            ·
              refine ⟨1827786244885992795718601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218524163257328530479067 1827786244885992795718601)
              ·
                refine ⟨1370839683664494596788951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1827786244885992795718601 1370839683664494596788951)
                ·
                  refine ⟨2056259525496741895183427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370839683664494596788951 2056259525496741895183427)
                  ·
                    refine ⟨3084389288245112842775141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056259525496741895183427 3084389288245112842775141)
                    ·
                      refine ⟨578322991545958658020339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3084389288245112842775141 578322991545958658020339)
                      ·
                        rfl

theorem cell23_1126280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_1126280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126280 prefixEnd_1126280 := by exact prefixLift 1126280
  have htrace : WordTrace (prefixWord ++ tailWord_1126280) baseStart_1126280 baseEnd_1126280 := by
    simpa [prefixWord, tailWord_1126280, baseEnd_1126280] using wordTrace_append hprefix tailTrace_1126280
  have hstable : (prefixWord ++ tailWord_1126280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126280).length < 2 ^ (prefixWord ++ tailWord_1126280).sum := by decide
  have hdescent : baseEnd_1126280 < baseStart_1126280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126300 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1126300 : Nat := 118140960795 + 1126300 * 2 ^ 59
def prefixEnd_1126300 : Nat := 4983230072969 + 3 ^ 40 * 1126300 * 2
def baseEnd_1126300 : Nat := 578333261159048579770247

theorem tailTrace_1126300 : CollatzResearch.WordTrace tailWord_1126300 prefixEnd_1126300 578333261159048579770247 := by
  unfold tailWord_1126300
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539767909807465785404177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27386357213076621047205569 20539767909807465785404177)
  ·
    refine ⟨15404825932355599339053133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20539767909807465785404177 15404825932355599339053133)
    ·
      refine ⟨5776809724633349752144925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15404825932355599339053133 5776809724633349752144925)
      ·
        refine ⟨2166303646737506157054347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5776809724633349752144925 2166303646737506157054347)
        ·
          refine ⟨3249455470106259235581521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166303646737506157054347 3249455470106259235581521)
          ·
            refine ⟨2437091602579694426686141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249455470106259235581521 2437091602579694426686141)
            ·
              refine ⟨913909350967385410007303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2437091602579694426686141 913909350967385410007303)
              ·
                refine ⟨1370864026451078115010955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913909350967385410007303 1370864026451078115010955)
                ·
                  refine ⟨2056296039676617172516433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370864026451078115010955 2056296039676617172516433)
                  ·
                    refine ⟨1542222029757462879387325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2056296039676617172516433 1542222029757462879387325)
                    ·
                      refine ⟨578333261159048579770247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542222029757462879387325 578333261159048579770247)
                      ·
                        rfl

theorem cell23_1126300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1126300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126300 prefixEnd_1126300 := by exact prefixLift 1126300
  have htrace : WordTrace (prefixWord ++ tailWord_1126300) baseStart_1126300 baseEnd_1126300 := by
    simpa [prefixWord, tailWord_1126300, baseEnd_1126300] using wordTrace_append hprefix tailTrace_1126300
  have hstable : (prefixWord ++ tailWord_1126300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126300).length < 2 ^ (prefixWord ++ tailWord_1126300).sum := by decide
  have hdescent : baseEnd_1126300 < baseStart_1126300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126329 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_1126329 : Nat := 118140960795 + 1126329 * 2 ^ 59
def prefixEnd_1126329 : Nat := 4983230072969 + 3 ^ 40 * 1126329 * 2
def baseEnd_1126329 : Nat := 192782717366009655435871

theorem tailTrace_1126329 : CollatzResearch.WordTrace tailWord_1126329 prefixEnd_1126329 192782717366009655435871 := by
  unfold tailWord_1126329
  simp only [CollatzResearch.WordTrace]
  refine ⟨41080593536509869523614041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27387062357673246349076027 41080593536509869523614041)
  ·
    refine ⟨30810445152382402142710531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41080593536509869523614041 30810445152382402142710531)
    ·
      refine ⟨46215667728573603214065797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30810445152382402142710531 46215667728573603214065797)
      ·
        refine ⟨8665437699107550602637337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46215667728573603214065797 8665437699107550602637337)
        ·
          refine ⟨6499078274330662951978003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8665437699107550602637337 6499078274330662951978003)
          ·
            refine ⟨9748617411495994427967005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499078274330662951978003 9748617411495994427967005)
            ·
              refine ⟨3655731529310997910487627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9748617411495994427967005 3655731529310997910487627)
              ·
                refine ⟨5483597293966496865731441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655731529310997910487627 5483597293966496865731441)
                ·
                  refine ⟨4112697970474872649298581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5483597293966496865731441 4112697970474872649298581)
                  ·
                    refine ⟨192782717366009655435871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4112697970474872649298581 192782717366009655435871)
                    ·
                      rfl

theorem cell23_1126329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_1126329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126329 prefixEnd_1126329 := by exact prefixLift 1126329
  have htrace : WordTrace (prefixWord ++ tailWord_1126329) baseStart_1126329 baseEnd_1126329 := by
    simpa [prefixWord, tailWord_1126329, baseEnd_1126329] using wordTrace_append hprefix tailTrace_1126329
  have hstable : (prefixWord ++ tailWord_1126329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126329).length < 2 ^ (prefixWord ++ tailWord_1126329).sum := by decide
  have hdescent : baseEnd_1126329 < baseStart_1126329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126357 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1126357 : Nat := 118140960795 + 1126357 * 2 ^ 59
def prefixEnd_1126357 : Nat := 4983230072969 + 3 ^ 40 * 1126357 * 2
def baseEnd_1126357 : Nat := 578362529556354856757485

theorem tailTrace_1126357 : CollatzResearch.WordTrace tailWord_1126357 prefixEnd_1126357 578362529556354856757485 := by
  unfold tailWord_1126357
  simp only [CollatzResearch.WordTrace]
  refine ⟨41081614780408430305633325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27387743186938953537088883 41081614780408430305633325)
  ·
    refine ⟨15405605542653161364612497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41081614780408430305633325 15405605542653161364612497)
    ·
      refine ⟨11554204156989871023459373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15405605542653161364612497 11554204156989871023459373)
      ·
        refine ⟨4332826558871201633797265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11554204156989871023459373 4332826558871201633797265)
        ·
          refine ⟨3249619919153401225347949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332826558871201633797265 3249619919153401225347949)
          ·
            refine ⟨1218607469682525459505481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3249619919153401225347949 1218607469682525459505481)
            ·
              refine ⟨913955602261894094629111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218607469682525459505481 913955602261894094629111)
              ·
                refine ⟨1370933403392841141943667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913955602261894094629111 1370933403392841141943667)
                ·
                  refine ⟨2056400105089261712915501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1370933403392841141943667 2056400105089261712915501)
                  ·
                    refine ⟨771150039408473142343313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2056400105089261712915501 771150039408473142343313)
                    ·
                      refine ⟨578362529556354856757485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771150039408473142343313 578362529556354856757485)
                      ·
                        rfl

theorem cell23_1126357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1126357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126357 prefixEnd_1126357 := by exact prefixLift 1126357
  have htrace : WordTrace (prefixWord ++ tailWord_1126357) baseStart_1126357 baseEnd_1126357 := by
    simpa [prefixWord, tailWord_1126357, baseEnd_1126357] using wordTrace_append hprefix tailTrace_1126357
  have hstable : (prefixWord ++ tailWord_1126357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126357).length < 2 ^ (prefixWord ++ tailWord_1126357).sum := by decide
  have hdescent : baseEnd_1126357 < baseStart_1126357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126410 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_1126410 : Nat := 118140960795 + 1126410 * 2 ^ 59
def prefixEnd_1126410 : Nat := 4983230072969 + 3 ^ 40 * 1126410 * 2
def baseEnd_1126410 : Nat := 64265527114560349932749

theorem tailTrace_1126410 : CollatzResearch.WordTrace tailWord_1126410 prefixEnd_1126410 64265527114560349932749 := by
  unfold tailWord_1126410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10270886962304105089328171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27389031899477613571541789 10270886962304105089328171)
  ·
    refine ⟨15406330443456157633992257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10270886962304105089328171 15406330443456157633992257)
    ·
      refine ⟨11554747832592118225494193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15406330443456157633992257 11554747832592118225494193)
      ·
        refine ⟨8666060874444088669120645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11554747832592118225494193 8666060874444088669120645)
        ·
          refine ⟨1624886413958266625460121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8666060874444088669120645 1624886413958266625460121)
          ·
            refine ⟨1218664810468699969095091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1624886413958266625460121 1218664810468699969095091)
            ·
              refine ⟨1827997215703049953642637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218664810468699969095091 1827997215703049953642637)
              ·
                refine ⟨685498955888643732615989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1827997215703049953642637 685498955888643732615989)
                ·
                  refine ⟨64265527114560349932749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 685498955888643732615989 64265527114560349932749)
                  ·
                    rfl

theorem cell23_1126410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_1126410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126410 prefixEnd_1126410 := by exact prefixLift 1126410
  have htrace : WordTrace (prefixWord ++ tailWord_1126410) baseStart_1126410 baseEnd_1126410 := by
    simpa [prefixWord, tailWord_1126410, baseEnd_1126410] using wordTrace_append hprefix tailTrace_1126410
  have hstable : (prefixWord ++ tailWord_1126410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126410).length < 2 ^ (prefixWord ++ tailWord_1126410).sum := by decide
  have hdescent : baseEnd_1126410 < baseStart_1126410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126423 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 2, 5]
def baseStart_1126423 : Nat := 118140960795 + 1126423 * 2 ^ 59
def prefixEnd_1126423 : Nat := 4983230072969 + 3 ^ 40 * 1126423 * 2
def baseEnd_1126423 : Nat := 192798806426517199510727

theorem tailTrace_1126423 : CollatzResearch.WordTrace tailWord_1126423 prefixEnd_1126423 192798806426517199510727 := by
  unfold tailWord_1126423
  simp only [CollatzResearch.WordTrace]
  refine ⟨41084021998169323577535923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27389347998779549051690615 41084021998169323577535923)
  ·
    refine ⟨61626032997253985366303885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41084021998169323577535923 61626032997253985366303885)
    ·
      refine ⟨23109762373970244512363957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61626032997253985366303885 23109762373970244512363957)
      ·
        refine ⟨2166540222559710423034121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23109762373970244512363957 2166540222559710423034121)
        ·
          refine ⟨1624905166919782817275591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166540222559710423034121 1624905166919782817275591)
          ·
            refine ⟨2437357750379674225913387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624905166919782817275591 2437357750379674225913387)
            ·
              refine ⟨3656036625569511338870081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437357750379674225913387 3656036625569511338870081)
              ·
                refine ⟨2742027469177133504152561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656036625569511338870081 2742027469177133504152561)
                ·
                  refine ⟨2056520601882850128114421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742027469177133504152561 2056520601882850128114421)
                  ·
                    refine ⟨192798806426517199510727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2056520601882850128114421 192798806426517199510727)
                    ·
                      rfl

theorem cell23_1126423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_1126423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126423 prefixEnd_1126423 := by exact prefixLift 1126423
  have htrace : WordTrace (prefixWord ++ tailWord_1126423) baseStart_1126423 baseEnd_1126423 := by
    simpa [prefixWord, tailWord_1126423, baseEnd_1126423] using wordTrace_append hprefix tailTrace_1126423
  have hstable : (prefixWord ++ tailWord_1126423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126423).length < 2 ^ (prefixWord ++ tailWord_1126423).sum := by decide
  have hdescent : baseEnd_1126423 < baseStart_1126423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126426 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1126426 : Nat := 118140960795 + 1126426 * 2 ^ 59
def prefixEnd_1126426 : Nat := 4983230072969 + 3 ^ 40 * 1126426 * 2
def baseEnd_1126426 : Nat := 578397959721515086794667

theorem tailTrace_1126426 : CollatzResearch.WordTrace tailWord_1126426 prefixEnd_1126426 578397959721515086794667 := by
  unfold tailWord_1126426
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271032854289613772473783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27389420944772303393263421 10271032854289613772473783)
  ·
    refine ⟨15406549281434420658710675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10271032854289613772473783 15406549281434420658710675)
    ·
      refine ⟨23109823922151630988066013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15406549281434420658710675 23109823922151630988066013)
      ·
        refine ⟨8666183970806861620524755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23109823922151630988066013 8666183970806861620524755)
        ·
          refine ⟨12999275956210292430787133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8666183970806861620524755 12999275956210292430787133)
          ·
            refine ⟨4874728483578859661545175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12999275956210292430787133 4874728483578859661545175)
            ·
              refine ⟨7312092725368289492317763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874728483578859661545175 7312092725368289492317763)
              ·
                refine ⟨10968139088052434238476645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312092725368289492317763 10968139088052434238476645)
                ·
                  refine ⟨2056526079009831419714371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10968139088052434238476645 2056526079009831419714371)
                  ·
                    refine ⟨3084789118514747129571557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056526079009831419714371 3084789118514747129571557)
                    ·
                      refine ⟨578397959721515086794667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3084789118514747129571557 578397959721515086794667)
                      ·
                        rfl

theorem cell23_1126426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1126426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126426 prefixEnd_1126426 := by exact prefixLift 1126426
  have htrace : WordTrace (prefixWord ++ tailWord_1126426) baseStart_1126426 baseEnd_1126426 := by
    simpa [prefixWord, tailWord_1126426, baseEnd_1126426] using wordTrace_append hprefix tailTrace_1126426
  have hstable : (prefixWord ++ tailWord_1126426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126426).length < 2 ^ (prefixWord ++ tailWord_1126426).sum := by decide
  have hdescent : baseEnd_1126426 < baseStart_1126426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126469 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_1126469 : Nat := 118140960795 + 1126469 * 2 ^ 59
def prefixEnd_1126469 : Nat := 4983230072969 + 3 ^ 40 * 1126469 * 2
def baseEnd_1126469 : Nat := 578420039389658418556969

theorem tailTrace_1126469 : CollatzResearch.WordTrace tailWord_1126469 prefixEnd_1126469 578420039389658418556969 := by
  unfold tailWord_1126469
  simp only [CollatzResearch.WordTrace]
  refine ⟨41085699756002673433710461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27390466504001782289140307 41085699756002673433710461)
  ·
    refine ⟨15407137408501002537641423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41085699756002673433710461 15407137408501002537641423)
    ·
      refine ⟨23110706112751503806462135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15407137408501002537641423 23110706112751503806462135)
      ·
        refine ⟨34666059169127255709693203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23110706112751503806462135 34666059169127255709693203)
        ·
          refine ⟨51999088753690883564539805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34666059169127255709693203 51999088753690883564539805)
          ·
            refine ⟨19499658282634081336702427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51999088753690883564539805 19499658282634081336702427)
            ·
              refine ⟨29249487423951122005053641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19499658282634081336702427 29249487423951122005053641)
              ·
                refine ⟨21937115567963341503790231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29249487423951122005053641 21937115567963341503790231)
                ·
                  refine ⟨32905673351945012255685347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21937115567963341503790231 32905673351945012255685347)
                  ·
                    refine ⟨49358510027917518383528021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32905673351945012255685347 49358510027917518383528021)
                    ·
                      refine ⟨578420039389658418556969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 49358510027917518383528021 578420039389658418556969)
                      ·
                        rfl

theorem cell23_1126469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_1126469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126469 prefixEnd_1126469 := by exact prefixLift 1126469
  have htrace : WordTrace (prefixWord ++ tailWord_1126469) baseStart_1126469 baseEnd_1126469 := by
    simpa [prefixWord, tailWord_1126469, baseEnd_1126469] using wordTrace_append hprefix tailTrace_1126469
  have hstable : (prefixWord ++ tailWord_1126469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126469).length < 2 ^ (prefixWord ++ tailWord_1126469).sum := by decide
  have hdescent : baseEnd_1126469 < baseStart_1126469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126494 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1126494 : Nat := 118140960795 + 1126494 * 2 ^ 59
def prefixEnd_1126494 : Nat := 4983230072969 + 3 ^ 40 * 1126494 * 2
def baseEnd_1126494 : Nat := 578432876406020820744355

theorem tailTrace_1126494 : CollatzResearch.WordTrace tailWord_1126494 prefixEnd_1126494 578432876406020820744355 := by
  unfold tailWord_1126494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135826447614012837921317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27391074387274735135580357 5135826447614012837921317)
  ·
    refine ⟨962967458927627407110247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5135826447614012837921317 962967458927627407110247)
    ·
      refine ⟨1444451188391441110665371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962967458927627407110247 1444451188391441110665371)
      ·
        refine ⟨2166676782587161665998057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444451188391441110665371 2166676782587161665998057)
        ·
          refine ⟨1625007586940371249498543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166676782587161665998057 1625007586940371249498543)
          ·
            refine ⟨2437511380410556874247815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625007586940371249498543 2437511380410556874247815)
            ·
              refine ⟨3656267070615835311371723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437511380410556874247815 3656267070615835311371723)
              ·
                refine ⟨5484400605923752967057585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656267070615835311371723 5484400605923752967057585)
                ·
                  refine ⟨4113300454442814725293189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5484400605923752967057585 4113300454442814725293189)
                  ·
                    refine ⟨771243835208027760992473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4113300454442814725293189 771243835208027760992473)
                    ·
                      refine ⟨578432876406020820744355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771243835208027760992473 578432876406020820744355)
                      ·
                        rfl

theorem cell23_1126494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1126494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126494 prefixEnd_1126494 := by exact prefixLift 1126494
  have htrace : WordTrace (prefixWord ++ tailWord_1126494) baseStart_1126494 baseEnd_1126494 := by
    simpa [prefixWord, tailWord_1126494, baseEnd_1126494] using wordTrace_append hprefix tailTrace_1126494
  have hstable : (prefixWord ++ tailWord_1126494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126494).length < 2 ^ (prefixWord ++ tailWord_1126494).sum := by decide
  have hdescent : baseEnd_1126494 < baseStart_1126494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126496 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_1126496 : Nat := 118140960795 + 1126496 * 2 ^ 59
def prefixEnd_1126496 : Nat := 4983230072969 + 3 ^ 40 * 1126496 * 2
def baseEnd_1126496 : Nat := 192811301122443270973115

theorem tailTrace_1126496 : CollatzResearch.WordTrace tailWord_1126496 prefixEnd_1126496 192811301122443270973115 := by
  unfold tailWord_1126496
  simp only [CollatzResearch.WordTrace]
  refine ⟨20543342263452428522471671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27391123017936571363295561 20543342263452428522471671)
  ·
    refine ⟨30815013395178642783707507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20543342263452428522471671 30815013395178642783707507)
    ·
      refine ⟨46222520092767964175561261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30815013395178642783707507 46222520092767964175561261)
      ·
        refine ⟨17333445034787986565835473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46222520092767964175561261 17333445034787986565835473)
        ·
          refine ⟨13000083776090989924376605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17333445034787986565835473 13000083776090989924376605)
          ·
            refine ⟨4875031416034121221641227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13000083776090989924376605 4875031416034121221641227)
            ·
              refine ⟨7312547124051181832461841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4875031416034121221641227 7312547124051181832461841)
              ·
                refine ⟨5484410343038386374346381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7312547124051181832461841 5484410343038386374346381)
                ·
                  refine ⟨2056653878639394890379893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5484410343038386374346381 2056653878639394890379893)
                  ·
                    refine ⟨192811301122443270973115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2056653878639394890379893 192811301122443270973115)
                    ·
                      rfl

theorem cell23_1126496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_1126496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126496 prefixEnd_1126496 := by exact prefixLift 1126496
  have htrace : WordTrace (prefixWord ++ tailWord_1126496) baseStart_1126496 baseEnd_1126496 := by
    simpa [prefixWord, tailWord_1126496, baseEnd_1126496] using wordTrace_append hprefix tailTrace_1126496
  have hstable : (prefixWord ++ tailWord_1126496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126496).length < 2 ^ (prefixWord ++ tailWord_1126496).sum := by decide
  have hdescent : baseEnd_1126496 < baseStart_1126496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126503 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_1126503 : Nat := 118140960795 + 1126503 * 2 ^ 59
def prefixEnd_1126503 : Nat := 4983230072969 + 3 ^ 40 * 1126503 * 2
def baseEnd_1126503 : Nat := 578437497731911285531813

theorem tailTrace_1126503 : CollatzResearch.WordTrace tailWord_1126503 prefixEnd_1126503 578437497731911285531813 := by
  unfold tailWord_1126503
  simp only [CollatzResearch.WordTrace]
  refine ⟨41086939837879497240448163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27391293225252998160298775 41086939837879497240448163)
  ·
    refine ⟨61630409756819245860672245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41086939837879497240448163 61630409756819245860672245)
    ·
      refine ⟨5777850914701804299438023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61630409756819245860672245 5777850914701804299438023)
      ·
        refine ⟨8666776372052706449157035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5777850914701804299438023 8666776372052706449157035)
        ·
          refine ⟨13000164558079059673735553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8666776372052706449157035 13000164558079059673735553)
          ·
            refine ⟨9750123418559294755301665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13000164558079059673735553 9750123418559294755301665)
            ·
              refine ⟨7312592563919471066476249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750123418559294755301665 7312592563919471066476249)
              ·
                refine ⟨5484444422939603299857187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7312592563919471066476249 5484444422939603299857187)
                ·
                  refine ⟨8226666634409404949785781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484444422939603299857187 8226666634409404949785781)
                  ·
                    refine ⟨771249996975881714042417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8226666634409404949785781 771249996975881714042417)
                    ·
                      refine ⟨578437497731911285531813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771249996975881714042417 578437497731911285531813)
                      ·
                        rfl

theorem cell23_1126503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_1126503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126503 prefixEnd_1126503 := by exact prefixLift 1126503
  have htrace : WordTrace (prefixWord ++ tailWord_1126503) baseStart_1126503 baseEnd_1126503 := by
    simpa [prefixWord, tailWord_1126503, baseEnd_1126503] using wordTrace_append hprefix tailTrace_1126503
  have hstable : (prefixWord ++ tailWord_1126503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126503).length < 2 ^ (prefixWord ++ tailWord_1126503).sum := by decide
  have hdescent : baseEnd_1126503 < baseStart_1126503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126510 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1126510 : Nat := 118140960795 + 1126510 * 2 ^ 59
def prefixEnd_1126510 : Nat := 4983230072969 + 3 ^ 40 * 1126510 * 2
def baseEnd_1126510 : Nat := 578441092096492758144281

theorem tailTrace_1126510 : CollatzResearch.WordTrace tailWord_1126510 prefixEnd_1126510 578441092096492758144281 := by
  unfold tailWord_1126510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135899393606767179494123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27391463432569424957301989 5135899393606767179494123)
  ·
    refine ⟨7703849090410150769241185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5135899393606767179494123 7703849090410150769241185)
    ·
      refine ⟨5777886817807613076930889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7703849090410150769241185 5777886817807613076930889)
      ·
        refine ⟨4333415113355709807698167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5777886817807613076930889 4333415113355709807698167)
        ·
          refine ⟨6500122670033564711547251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333415113355709807698167 6500122670033564711547251)
          ·
            refine ⟨9750184005050347067320877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500122670033564711547251 9750184005050347067320877)
            ·
              refine ⟨3656319001893880150245329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9750184005050347067320877 3656319001893880150245329)
              ·
                refine ⟨2742239251420410112683997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656319001893880150245329 2742239251420410112683997)
                ·
                  refine ⟨1028339719282653792256499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2742239251420410112683997 1028339719282653792256499)
                  ·
                    refine ⟨1542509578923980688384749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028339719282653792256499 1542509578923980688384749)
                    ·
                      refine ⟨578441092096492758144281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542509578923980688384749 578441092096492758144281)
                      ·
                        rfl

theorem cell23_1126510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1126510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126510 prefixEnd_1126510 := by exact prefixLift 1126510
  have htrace : WordTrace (prefixWord ++ tailWord_1126510) baseStart_1126510 baseEnd_1126510 := by
    simpa [prefixWord, tailWord_1126510, baseEnd_1126510] using wordTrace_append hprefix tailTrace_1126510
  have hstable : (prefixWord ++ tailWord_1126510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126510).length < 2 ^ (prefixWord ++ tailWord_1126510).sum := by decide
  have hdescent : baseEnd_1126510 < baseStart_1126510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126556 : List Nat := [2, 2, 3, 2, 1, 1, 2, 10]
def baseStart_1126556 : Nat := 118140960795 + 1126556 * 2 ^ 59
def prefixEnd_1126556 : Nat := 4983230072969 + 3 ^ 40 * 1126556 * 2
def baseEnd_1126556 : Nat := 21424618970614799191447

theorem tailTrace_1126556 : CollatzResearch.WordTrace tailWord_1126556 prefixEnd_1126556 21424618970614799191447 := by
  unfold tailWord_1126556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20544436453343743646063761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27392581937791658194751681 20544436453343743646063761)
  ·
    refine ⟨15408327340007807734547821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20544436453343743646063761 15408327340007807734547821)
    ·
      refine ⟨5778122752502927900455433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15408327340007807734547821 5778122752502927900455433)
      ·
        refine ⟨4333592064377195925341575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778122752502927900455433 4333592064377195925341575)
        ·
          refine ⟨6500388096565793888012363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333592064377195925341575 6500388096565793888012363)
          ·
            refine ⟨9750582144848690832018545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500388096565793888012363 9750582144848690832018545)
            ·
              refine ⟨7312936608636518124013909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750582144848690832018545 7312936608636518124013909)
              ·
                refine ⟨21424618970614799191447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7312936608636518124013909 21424618970614799191447)
                ·
                  rfl

theorem cell23_1126556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 10].length) (baseStart_1126556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126556 prefixEnd_1126556 := by exact prefixLift 1126556
  have htrace : WordTrace (prefixWord ++ tailWord_1126556) baseStart_1126556 baseEnd_1126556 := by
    simpa [prefixWord, tailWord_1126556, baseEnd_1126556] using wordTrace_append hprefix tailTrace_1126556
  have hstable : (prefixWord ++ tailWord_1126556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126556).length < 2 ^ (prefixWord ++ tailWord_1126556).sum := by decide
  have hdescent : baseEnd_1126556 < baseStart_1126556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126567 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1126567 : Nat := 118140960795 + 1126567 * 2 ^ 59
def prefixEnd_1126567 : Nat := 4983230072969 + 3 ^ 40 * 1126567 * 2
def baseEnd_1126567 : Nat := 578470360493799035131519

theorem tailTrace_1126567 : CollatzResearch.WordTrace tailWord_1126567 prefixEnd_1126567 578470360493799035131519 := by
  unfold tailWord_1126567
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089274109647636170777955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27392849406431757447185303 41089274109647636170777955)
  ·
    refine ⟨61633911164471454256166933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41089274109647636170777955 61633911164471454256166933)
    ·
      refine ⟨2889089585834599418257825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61633911164471454256166933 2889089585834599418257825)
      ·
        refine ⟨2166817189375949563693369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2889089585834599418257825 2166817189375949563693369)
        ·
          refine ⟨1625112892031962172770027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2166817189375949563693369 1625112892031962172770027)
          ·
            refine ⟨2437669338047943259155041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625112892031962172770027 2437669338047943259155041)
            ·
              refine ⟨1828252003535957444366281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437669338047943259155041 1828252003535957444366281)
              ·
                refine ⟨1371189002651968083274711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828252003535957444366281 1371189002651968083274711)
                ·
                  refine ⟨2056783503977952124912067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371189002651968083274711 2056783503977952124912067)
                  ·
                    refine ⟨3085175255966928187368101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2056783503977952124912067 3085175255966928187368101)
                    ·
                      refine ⟨578470360493799035131519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3085175255966928187368101 578470360493799035131519)
                      ·
                        rfl

theorem cell23_1126567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1126567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126567 prefixEnd_1126567 := by exact prefixLift 1126567
  have htrace : WordTrace (prefixWord ++ tailWord_1126567) baseStart_1126567 baseEnd_1126567 := by
    simpa [prefixWord, tailWord_1126567, baseEnd_1126567] using wordTrace_append hprefix tailTrace_1126567
  have hstable : (prefixWord ++ tailWord_1126567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126567).length < 2 ^ (prefixWord ++ tailWord_1126567).sum := by decide
  have hdescent : baseEnd_1126567 < baseStart_1126567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126573 : List Nat := [1, 5, 2, 1, 2, 2, 1, 9]
def baseStart_1126573 : Nat := 118140960795 + 1126573 * 2 ^ 59
def prefixEnd_1126573 : Nat := 4983230072969 + 3 ^ 40 * 1126573 * 2
def baseEnd_1126573 : Nat := 21424942273249111542833

theorem tailTrace_1126573 : CollatzResearch.WordTrace tailWord_1126573 prefixEnd_1126573 21424942273249111542833 := by
  unfold tailWord_1126573
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089492947625899195496373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27392995298417266130330915 41089492947625899195496373)
  ·
    refine ⟨3852139963839928049577785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41089492947625899195496373 3852139963839928049577785)
    ·
      refine ⟨2889104972879946037183339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3852139963839928049577785 2889104972879946037183339)
      ·
        refine ⟨4333657459319919055775009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889104972879946037183339 4333657459319919055775009)
        ·
          refine ⟨3250243094489939291831257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333657459319919055775009 3250243094489939291831257)
          ·
            refine ⟨2437682320867454468873443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250243094489939291831257 2437682320867454468873443)
            ·
              refine ⟨3656523481301181703310165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437682320867454468873443 3656523481301181703310165)
              ·
                refine ⟨21424942273249111542833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3656523481301181703310165 21424942273249111542833)
                ·
                  rfl

theorem cell23_1126573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 9].length) (baseStart_1126573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126573 prefixEnd_1126573 := by exact prefixLift 1126573
  have htrace : WordTrace (prefixWord ++ tailWord_1126573) baseStart_1126573 baseEnd_1126573 := by
    simpa [prefixWord, tailWord_1126573, baseEnd_1126573] using wordTrace_append hprefix tailTrace_1126573
  have hstable : (prefixWord ++ tailWord_1126573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126573).length < 2 ^ (prefixWord ++ tailWord_1126573).sum := by decide
  have hdescent : baseEnd_1126573 < baseStart_1126573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126590 : List Nat := [4, 2, 1, 1, 5, 1, 9]
def baseStart_1126590 : Nat := 118140960795 + 1126590 * 2 ^ 59
def prefixEnd_1126590 : Nat := 4983230072969 + 3 ^ 40 * 1126590 * 2
def baseEnd_1126590 : Nat := 7141755191961141298073

theorem tailTrace_1126590 : CollatzResearch.WordTrace tailWord_1126590 prefixEnd_1126590 7141755191961141298073 := by
  unfold tailWord_1126590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136264123570538887358153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27393408659042874065910149 5136264123570538887358153)
  ·
    refine ⟨3852198092677904165518615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5136264123570538887358153 3852198092677904165518615)
    ·
      refine ⟨5778297139016856248277923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852198092677904165518615 5778297139016856248277923)
      ·
        refine ⟨8667445708525284372416885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778297139016856248277923 8667445708525284372416885)
        ·
          refine ⟨812573035174245409914083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8667445708525284372416885 812573035174245409914083)
          ·
            refine ⟨1218859552761368114871125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812573035174245409914083 1218859552761368114871125)
            ·
              refine ⟨7141755191961141298073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1218859552761368114871125 7141755191961141298073)
              ·
                rfl

theorem cell23_1126590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 9].length) (baseStart_1126590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126590 prefixEnd_1126590 := by exact prefixLift 1126590
  have htrace : WordTrace (prefixWord ++ tailWord_1126590) baseStart_1126590 baseEnd_1126590 := by
    simpa [prefixWord, tailWord_1126590, baseEnd_1126590] using wordTrace_append hprefix tailTrace_1126590
  have hstable : (prefixWord ++ tailWord_1126590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126590).length < 2 ^ (prefixWord ++ tailWord_1126590).sum := by decide
  have hdescent : baseEnd_1126590 < baseStart_1126590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126600 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_1126600 : Nat := 118140960795 + 1126600 * 2 ^ 59
def prefixEnd_1126600 : Nat := 4983230072969 + 3 ^ 40 * 1126600 * 2
def baseEnd_1126600 : Nat := 578487305355397406018867

theorem tailTrace_1126600 : CollatzResearch.WordTrace tailWord_1126600 prefixEnd_1126600 578487305355397406018867 := by
  unfold tailWord_1126600
  simp only [CollatzResearch.WordTrace]
  refine ⟨20545238859264041403364627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27393651812352055204486169 20545238859264041403364627)
  ·
    refine ⟨30817858288896062105046941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20545238859264041403364627 30817858288896062105046941)
    ·
      refine ⟨11556696858336023289392603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30817858288896062105046941 11556696858336023289392603)
      ·
        refine ⟨17335045287504034934088905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556696858336023289392603 17335045287504034934088905)
        ·
          refine ⟨13001283965628026200566679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17335045287504034934088905 13001283965628026200566679)
          ·
            refine ⟨19501925948442039300850019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001283965628026200566679 19501925948442039300850019)
            ·
              refine ⟨29252888922663058951275029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19501925948442039300850019 29252888922663058951275029)
              ·
                refine ⟨1371229168249830888341017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29252888922663058951275029 1371229168249830888341017)
                ·
                  refine ⟨1028421876187373166255763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371229168249830888341017 1028421876187373166255763)
                  ·
                    refine ⟨1542632814281059749383645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028421876187373166255763 1542632814281059749383645)
                    ·
                      refine ⟨578487305355397406018867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542632814281059749383645 578487305355397406018867)
                      ·
                        rfl

theorem cell23_1126600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_1126600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126600 prefixEnd_1126600 := by exact prefixLift 1126600
  have htrace : WordTrace (prefixWord ++ tailWord_1126600) baseStart_1126600 baseEnd_1126600 := by
    simpa [prefixWord, tailWord_1126600, baseEnd_1126600] using wordTrace_append hprefix tailTrace_1126600
  have hstable : (prefixWord ++ tailWord_1126600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126600).length < 2 ^ (prefixWord ++ tailWord_1126600).sum := by decide
  have hdescent : baseEnd_1126600 < baseStart_1126600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126617 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 2, 1, 3]
def baseStart_1126617 : Nat := 118140960795 + 1126617 * 2 ^ 59
def prefixEnd_1126617 : Nat := 4983230072969 + 3 ^ 40 * 1126617 * 2
def baseEnd_1126617 : Nat := 578496034526523839506289

theorem tailTrace_1126617 : CollatzResearch.WordTrace tailWord_1126617 prefixEnd_1126617 578496034526523839506289 := by
  unfold tailWord_1126617
  simp only [CollatzResearch.WordTrace]
  refine ⟨41091097759466494710098105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27394065172977663140065403 41091097759466494710098105)
  ·
    refine ⟨30818323319599871032573579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41091097759466494710098105 30818323319599871032573579)
    ·
      refine ⟨46227484979399806548860369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30818323319599871032573579 46227484979399806548860369)
      ·
        refine ⟨34670613734549854911645277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46227484979399806548860369 34670613734549854911645277)
        ·
          refine ⟨13001480150456195591866979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34670613734549854911645277 13001480150456195591866979)
          ·
            refine ⟨19502220225684293387800469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001480150456195591866979 19502220225684293387800469)
            ·
              refine ⟨914166573078951252553147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19502220225684293387800469 914166573078951252553147)
              ·
                refine ⟨1371249859618426878829721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914166573078951252553147 1371249859618426878829721)
                ·
                  refine ⟨1028437394713820159122291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1371249859618426878829721 1028437394713820159122291)
                  ·
                    refine ⟨1542656092070730238683437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028437394713820159122291 1542656092070730238683437)
                    ·
                      refine ⟨578496034526523839506289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542656092070730238683437 578496034526523839506289)
                      ·
                        rfl

theorem cell23_1126617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_1126617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126617 prefixEnd_1126617 := by exact prefixLift 1126617
  have htrace : WordTrace (prefixWord ++ tailWord_1126617) baseStart_1126617 baseEnd_1126617 := by
    simpa [prefixWord, tailWord_1126617, baseEnd_1126617] using wordTrace_append hprefix tailTrace_1126617
  have hstable : (prefixWord ++ tailWord_1126617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126617).length < 2 ^ (prefixWord ++ tailWord_1126617).sum := by decide
  have hdescent : baseEnd_1126617 < baseStart_1126617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126640 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2]
def baseStart_1126640 : Nat := 118140960795 + 1126640 * 2 ^ 59
def prefixEnd_1126640 : Nat := 4983230072969 + 3 ^ 40 * 1126640 * 2
def baseEnd_1126640 : Nat := 578507844581577249518683

theorem tailTrace_1126640 : CollatzResearch.WordTrace tailWord_1126640 prefixEnd_1126640 578507844581577249518683 := by
  unfold tailWord_1126640
  simp only [CollatzResearch.WordTrace]
  refine ⟨20545968319191584819092687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27394624425588779758790249 20545968319191584819092687)
  ·
    refine ⟨30818952478787377228639031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20545968319191584819092687 30818952478787377228639031)
    ·
      refine ⟨46228428718181065842958547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30818952478787377228639031 46228428718181065842958547)
      ·
        refine ⟨69342643077271598764437821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46228428718181065842958547 69342643077271598764437821)
        ·
          refine ⟨26003491153976849536664183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69342643077271598764437821 26003491153976849536664183)
          ·
            refine ⟨39005236730965274304996275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26003491153976849536664183 39005236730965274304996275)
            ·
              refine ⟨58507855096447911457494413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39005236730965274304996275 58507855096447911457494413)
              ·
                refine ⟨21940445661167966796560405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58507855096447911457494413 21940445661167966796560405)
                ·
                  refine ⟨1028458390367248443588769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21940445661167966796560405 1028458390367248443588769)
                  ·
                    refine ⟨771343792775436332691577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1028458390367248443588769 771343792775436332691577)
                    ·
                      refine ⟨578507844581577249518683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771343792775436332691577 578507844581577249518683)
                      ·
                        rfl

theorem cell23_1126640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 2, 2].length) (baseStart_1126640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126640 prefixEnd_1126640 := by exact prefixLift 1126640
  have htrace : WordTrace (prefixWord ++ tailWord_1126640) baseStart_1126640 baseEnd_1126640 := by
    simpa [prefixWord, tailWord_1126640, baseEnd_1126640] using wordTrace_append hprefix tailTrace_1126640
  have hstable : (prefixWord ++ tailWord_1126640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126640).length < 2 ^ (prefixWord ++ tailWord_1126640).sum := by decide
  have hdescent : baseEnd_1126640 < baseStart_1126640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126656 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1126656 : Nat := 118140960795 + 1126656 * 2 ^ 59
def prefixEnd_1126656 : Nat := 4983230072969 + 3 ^ 40 * 1126656 * 2
def baseEnd_1126656 : Nat := 578516060272049186918609

theorem tailTrace_1126656 : CollatzResearch.WordTrace tailWord_1126656 prefixEnd_1126656 578516060272049186918609 := by
  unfold tailWord_1126656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20546260103162602185383911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27395013470883469580511881 20546260103162602185383911)
  ·
    refine ⟨30819390154743903278075867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20546260103162602185383911 30819390154743903278075867)
    ·
      refine ⟨46229085232115854917113801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30819390154743903278075867 46229085232115854917113801)
      ·
        refine ⟨34671813924086891187835351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46229085232115854917113801 34671813924086891187835351)
        ·
          refine ⟨52007720886130336781753027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34671813924086891187835351 52007720886130336781753027)
          ·
            refine ⟨78011581329195505172629541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52007720886130336781753027 78011581329195505172629541)
            ·
              refine ⟨14627171499224157219868039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78011581329195505172629541 14627171499224157219868039)
              ·
                refine ⟨21940757248836235829802059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14627171499224157219868039 21940757248836235829802059)
                ·
                  refine ⟨32911135873254353744703089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21940757248836235829802059 32911135873254353744703089)
                  ·
                    refine ⟨24683351904940765308527317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32911135873254353744703089 24683351904940765308527317)
                    ·
                      refine ⟨578516060272049186918609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24683351904940765308527317 578516060272049186918609)
                      ·
                        rfl

theorem cell23_1126656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1126656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126656 prefixEnd_1126656 := by exact prefixLift 1126656
  have htrace : WordTrace (prefixWord ++ tailWord_1126656) baseStart_1126656 baseEnd_1126656 := by
    simpa [prefixWord, tailWord_1126656, baseEnd_1126656] using wordTrace_append hprefix tailTrace_1126656
  have hstable : (prefixWord ++ tailWord_1126656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126656).length < 2 ^ (prefixWord ++ tailWord_1126656).sum := by decide
  have hdescent : baseEnd_1126656 < baseStart_1126656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126673 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_1126673 : Nat := 118140960795 + 1126673 * 2 ^ 59
def prefixEnd_1126673 : Nat := 4983230072969 + 3 ^ 40 * 1126673 * 2
def baseEnd_1126673 : Nat := 578524789443175620406031

theorem tailTrace_1126673 : CollatzResearch.WordTrace tailWord_1126673 prefixEnd_1126673 578524789443175620406031 := by
  unfold tailWord_1126673
  simp only [CollatzResearch.WordTrace]
  refine ⟨41093140247263616274136673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27395426831509077516091115 41093140247263616274136673)
  ·
    refine ⟨30819855185447712205602505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41093140247263616274136673 30819855185447712205602505)
    ·
      refine ⟨23114891389085784154201879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30819855185447712205602505 23114891389085784154201879)
      ·
        refine ⟨34672337083628676231302819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23114891389085784154201879 34672337083628676231302819)
        ·
          refine ⟨52008505625443014346954229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34672337083628676231302819 52008505625443014346954229)
          ·
            refine ⟨4875797402385282595026959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52008505625443014346954229 4875797402385282595026959)
            ·
              refine ⟨7313696103577923892540439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4875797402385282595026959 7313696103577923892540439)
              ·
                refine ⟨10970544155366885838810659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7313696103577923892540439 10970544155366885838810659)
                ·
                  refine ⟨16455816233050328758215989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10970544155366885838810659 16455816233050328758215989)
                  ·
                    refine ⟨1542732771848468321082749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16455816233050328758215989 1542732771848468321082749)
                    ·
                      refine ⟨578524789443175620406031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542732771848468321082749 578524789443175620406031)
                      ·
                        rfl

theorem cell23_1126673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_1126673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126673 prefixEnd_1126673 := by exact prefixLift 1126673
  have htrace : WordTrace (prefixWord ++ tailWord_1126673) baseStart_1126673 baseEnd_1126673 := by
    simpa [prefixWord, tailWord_1126673, baseEnd_1126673] using wordTrace_append hprefix tailTrace_1126673
  have hstable : (prefixWord ++ tailWord_1126673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126673).length < 2 ^ (prefixWord ++ tailWord_1126673).sum := by decide
  have hdescent : baseEnd_1126673 < baseStart_1126673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126695 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1126695 : Nat := 118140960795 + 1126695 * 2 ^ 59
def prefixEnd_1126695 : Nat := 4983230072969 + 3 ^ 40 * 1126695 * 2
def baseEnd_1126695 : Nat := 578536086017574534330931

theorem tailTrace_1126695 : CollatzResearch.WordTrace tailWord_1126695 prefixEnd_1126695 578536086017574534330931 := by
  unfold tailWord_1126695
  simp only [CollatzResearch.WordTrace]
  refine ⟨41093942653183914031437539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27395961768789276020958359 41093942653183914031437539)
  ·
    refine ⟨61640913979775871047156309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41093942653183914031437539 61640913979775871047156309)
    ·
      refine ⟨722354460700498488833863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 61640913979775871047156309 722354460700498488833863)
      ·
        refine ⟨1083531691050747733250795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722354460700498488833863 1083531691050747733250795)
        ·
          refine ⟨1625297536576121599876193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083531691050747733250795 1625297536576121599876193)
          ·
            refine ⟨1218973152432091199907145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625297536576121599876193 1218973152432091199907145)
            ·
              refine ⟨914229864324068399930359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218973152432091199907145 914229864324068399930359)
              ·
                refine ⟨1371344796486102599895539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914229864324068399930359 1371344796486102599895539)
                ·
                  refine ⟨2057017194729153899843309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371344796486102599895539 2057017194729153899843309)
                  ·
                    refine ⟨771381448023432712441241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057017194729153899843309 771381448023432712441241)
                    ·
                      refine ⟨578536086017574534330931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771381448023432712441241 578536086017574534330931)
                      ·
                        rfl

theorem cell23_1126695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1126695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126695 prefixEnd_1126695 := by exact prefixLift 1126695
  have htrace : WordTrace (prefixWord ++ tailWord_1126695) baseStart_1126695 baseEnd_1126695 := by
    simpa [prefixWord, tailWord_1126695, baseEnd_1126695] using wordTrace_append hprefix tailTrace_1126695
  have hstable : (prefixWord ++ tailWord_1126695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126695).length < 2 ^ (prefixWord ++ tailWord_1126695).sum := by decide
  have hdescent : baseEnd_1126695 < baseStart_1126695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126743 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1126743 : Nat := 118140960795 + 1126743 * 2 ^ 59
def prefixEnd_1126743 : Nat := 4983230072969 + 3 ^ 40 * 1126743 * 2
def baseEnd_1126743 : Nat := 578560733088990346530709

theorem tailTrace_1126743 : CollatzResearch.WordTrace tailWord_1126743 prefixEnd_1126743 578560733088990346530709 := by
  unfold tailWord_1126743
  simp only [CollatzResearch.WordTrace]
  refine ⟨41095693357010018229184883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27397128904673345486123255 41095693357010018229184883)
  ·
    refine ⟨61643540035515027343777325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41095693357010018229184883 61643540035515027343777325)
    ·
      refine ⟨23116327513318135253916497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61643540035515027343777325 23116327513318135253916497)
      ·
        refine ⟨17337245634988601440437373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23116327513318135253916497 17337245634988601440437373)
        ·
          refine ⟨6501467113120725540164015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17337245634988601440437373 6501467113120725540164015)
          ·
            refine ⟨9752200669681088310246023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6501467113120725540164015 9752200669681088310246023)
            ·
              refine ⟨14628301004521632465369035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9752200669681088310246023 14628301004521632465369035)
              ·
                refine ⟨21942451506782448698053553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14628301004521632465369035 21942451506782448698053553)
                ·
                  refine ⟨16456838630086836523540165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21942451506782448698053553 16456838630086836523540165)
                  ·
                    refine ⟨3085657243141281848163781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16456838630086836523540165 3085657243141281848163781)
                    ·
                      refine ⟨578560733088990346530709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3085657243141281848163781 578560733088990346530709)
                      ·
                        rfl

theorem cell23_1126743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1126743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126743 prefixEnd_1126743 := by exact prefixLift 1126743
  have htrace : WordTrace (prefixWord ++ tailWord_1126743) baseStart_1126743 baseEnd_1126743 := by
    simpa [prefixWord, tailWord_1126743, baseEnd_1126743] using wordTrace_append hprefix tailTrace_1126743
  have hstable : (prefixWord ++ tailWord_1126743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126743).length < 2 ^ (prefixWord ++ tailWord_1126743).sum := by decide
  have hdescent : baseEnd_1126743 < baseStart_1126743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126763 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3]
def baseStart_1126763 : Nat := 118140960795 + 1126763 * 2 ^ 59
def prefixEnd_1126763 : Nat := 4983230072969 + 3 ^ 40 * 1126763 * 2
def baseEnd_1126763 : Nat := 578571002702080268280617

theorem tailTrace_1126763 : CollatzResearch.WordTrace tailWord_1126763 prefixEnd_1126763 578571002702080268280617 := by
  unfold tailWord_1126763
  simp only [CollatzResearch.WordTrace]
  refine ⟨41096422816937561644912943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27397615211291707763275295 41096422816937561644912943)
  ·
    refine ⟨61644634225406342467369415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41096422816937561644912943 61644634225406342467369415)
    ·
      refine ⟨92466951338109513701054123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61644634225406342467369415 92466951338109513701054123)
      ·
        refine ⟨138700427007164270551581185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92466951338109513701054123 138700427007164270551581185)
        ·
          refine ⟨104025320255373202913685889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138700427007164270551581185 104025320255373202913685889)
          ·
            refine ⟨78018990191529902185264417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104025320255373202913685889 78018990191529902185264417)
            ·
              refine ⟨58514242643647426638948313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78018990191529902185264417 58514242643647426638948313)
              ·
                refine ⟨43885681982735569979211235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58514242643647426638948313 43885681982735569979211235)
                ·
                  refine ⟨65828522974103354968816853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43885681982735569979211235 65828522974103354968816853)
                  ·
                    refine ⟨1542856007205547382081645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65828522974103354968816853 1542856007205547382081645)
                    ·
                      refine ⟨578571002702080268280617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1542856007205547382081645 578571002702080268280617)
                      ·
                        rfl

theorem cell23_1126763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 3].length) (baseStart_1126763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126763 prefixEnd_1126763 := by exact prefixLift 1126763
  have htrace : WordTrace (prefixWord ++ tailWord_1126763) baseStart_1126763 baseEnd_1126763 := by
    simpa [prefixWord, tailWord_1126763, baseEnd_1126763] using wordTrace_append hprefix tailTrace_1126763
  have hstable : (prefixWord ++ tailWord_1126763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126763).length < 2 ^ (prefixWord ++ tailWord_1126763).sum := by decide
  have hdescent : baseEnd_1126763 < baseStart_1126763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126783 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 5, 5]
def baseStart_1126783 : Nat := 118140960795 + 1126783 * 2 ^ 59
def prefixEnd_1126783 : Nat := 4983230072969 + 3 ^ 40 * 1126783 * 2
def baseEnd_1126783 : Nat := 192860424105056730010175

theorem tailTrace_1126783 : CollatzResearch.WordTrace tailWord_1126783 prefixEnd_1126783 192860424105056730010175 := by
  unfold tailWord_1126783
  simp only [CollatzResearch.WordTrace]
  refine ⟨41097152276865105060641003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27398101517910070040427335 41097152276865105060641003)
  ·
    refine ⟨61645728415297657590961505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41097152276865105060641003 61645728415297657590961505)
    ·
      refine ⟨46234296311473243193221129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61645728415297657590961505 46234296311473243193221129)
      ·
        refine ⟨34675722233604932394915847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46234296311473243193221129 34675722233604932394915847)
        ·
          refine ⟨52013583350407398592373771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34675722233604932394915847 52013583350407398592373771)
          ·
            refine ⟨78020375025611097888560657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52013583350407398592373771 78020375025611097888560657)
            ·
              refine ⟨58515281269208323416420493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78020375025611097888560657 58515281269208323416420493)
              ·
                refine ⟨21943230475953121281157685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58515281269208323416420493 21943230475953121281157685)
                ·
                  refine ⟨2057177857120605120108533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21943230475953121281157685 2057177857120605120108533)
                  ·
                    refine ⟨192860424105056730010175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2057177857120605120108533 192860424105056730010175)
                    ·
                      rfl

theorem cell23_1126783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_1126783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126783 prefixEnd_1126783 := by exact prefixLift 1126783
  have htrace : WordTrace (prefixWord ++ tailWord_1126783) baseStart_1126783 baseEnd_1126783 := by
    simpa [prefixWord, tailWord_1126783, baseEnd_1126783] using wordTrace_append hprefix tailTrace_1126783
  have hstable : (prefixWord ++ tailWord_1126783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126783).length < 2 ^ (prefixWord ++ tailWord_1126783).sum := by decide
  have hdescent : baseEnd_1126783 < baseStart_1126783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126807 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_1126807 : Nat := 118140960795 + 1126807 * 2 ^ 59
def prefixEnd_1126807 : Nat := 4983230072969 + 3 ^ 40 * 1126807 * 2
def baseEnd_1126807 : Nat := 578593595850878096130415

theorem tailTrace_1126807 : CollatzResearch.WordTrace tailWord_1126807 prefixEnd_1126807 578593595850878096130415 := by
  unfold tailWord_1126807
  simp only [CollatzResearch.WordTrace]
  refine ⟨41098027628778157159514675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27398685085852104773009783 41098027628778157159514675)
  ·
    refine ⟨61647041443167235739272013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41098027628778157159514675 61647041443167235739272013)
    ·
      refine ⟨23117640541187713402227005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61647041443167235739272013 23117640541187713402227005)
      ·
        refine ⟨8669115202945392525835127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23117640541187713402227005 8669115202945392525835127)
        ·
          refine ⟨13003672804418088788752691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669115202945392525835127 13003672804418088788752691)
          ·
            refine ⟨19505509206627133183129037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13003672804418088788752691 19505509206627133183129037)
            ·
              refine ⟨7314565952485174943673389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19505509206627133183129037 7314565952485174943673389)
              ·
                refine ⟨2742962232181940603877521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7314565952485174943673389 2742962232181940603877521)
                ·
                  refine ⟨2057221674136455452908141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742962232181940603877521 2057221674136455452908141)
                  ·
                    refine ⟨771458127801170794840553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057221674136455452908141 771458127801170794840553)
                    ·
                      refine ⟨578593595850878096130415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771458127801170794840553 578593595850878096130415)
                      ·
                        rfl

theorem cell23_1126807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_1126807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126807 prefixEnd_1126807 := by exact prefixLift 1126807
  have htrace : WordTrace (prefixWord ++ tailWord_1126807) baseStart_1126807 baseEnd_1126807 := by
    simpa [prefixWord, tailWord_1126807, baseEnd_1126807] using wordTrace_append hprefix tailTrace_1126807
  have hstable : (prefixWord ++ tailWord_1126807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126807).length < 2 ^ (prefixWord ++ tailWord_1126807).sum := by decide
  have hdescent : baseEnd_1126807 < baseStart_1126807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126853 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_1126853 : Nat := 118140960795 + 1126853 * 2 ^ 59
def prefixEnd_1126853 : Nat := 4983230072969 + 3 ^ 40 * 1126853 * 2
def baseEnd_1126853 : Nat := 578617215960984916155203

theorem tailTrace_1126853 : CollatzResearch.WordTrace tailWord_1126853 prefixEnd_1126853 578617215960984916155203 := by
  unfold tailWord_1126853
  simp only [CollatzResearch.WordTrace]
  refine ⟨41099705386611507015689213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27399803591074338010459475 41099705386611507015689213)
  ·
    refine ⟨15412389519979315130883455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41099705386611507015689213 15412389519979315130883455)
    ·
      refine ⟨23118584279968972696325183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15412389519979315130883455 23118584279968972696325183)
      ·
        refine ⟨34677876419953459044487775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23118584279968972696325183 34677876419953459044487775)
        ·
          refine ⟨52016814629930188566731663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34677876419953459044487775 52016814629930188566731663)
          ·
            refine ⟨78025221944895282850097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52016814629930188566731663 78025221944895282850097495)
            ·
              refine ⟨117037832917342924275146243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78025221944895282850097495 117037832917342924275146243)
              ·
                refine ⟨175556749376014386412719365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117037832917342924275146243 175556749376014386412719365)
                ·
                  refine ⟨32916890508002697452384881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175556749376014386412719365 32916890508002697452384881)
                  ·
                    refine ⟨24687667881002023089288661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32916890508002697452384881 24687667881002023089288661)
                    ·
                      refine ⟨578617215960984916155203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24687667881002023089288661 578617215960984916155203)
                      ·
                        rfl

theorem cell23_1126853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_1126853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126853 prefixEnd_1126853 := by exact prefixLift 1126853
  have htrace : WordTrace (prefixWord ++ tailWord_1126853) baseStart_1126853 baseEnd_1126853 := by
    simpa [prefixWord, tailWord_1126853, baseEnd_1126853] using wordTrace_append hprefix tailTrace_1126853
  have hstable : (prefixWord ++ tailWord_1126853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126853).length < 2 ^ (prefixWord ++ tailWord_1126853).sum := by decide
  have hdescent : baseEnd_1126853 < baseStart_1126853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126901 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1126901 : Nat := 118140960795 + 1126901 * 2 ^ 59
def prefixEnd_1126901 : Nat := 4983230072969 + 3 ^ 40 * 1126901 * 2
def baseEnd_1126901 : Nat := 578641863032400728354983

theorem tailTrace_1126901 : CollatzResearch.WordTrace tailWord_1126901 prefixEnd_1126901 578641863032400728354983 := by
  unfold tailWord_1126901
  simp only [CollatzResearch.WordTrace]
  refine ⟨41101456090437611213436557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27400970726958407475624371 41101456090437611213436557)
  ·
    refine ⟨15413046033914104205038709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41101456090437611213436557 15413046033914104205038709)
    ·
      refine ⟨1444973065679447269222379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15413046033914104205038709 1444973065679447269222379)
      ·
        refine ⟨2167459598519170903833569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444973065679447269222379 2167459598519170903833569)
        ·
          refine ⟨1625594698889378177875177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167459598519170903833569 1625594698889378177875177)
          ·
            refine ⟨1219196024167033633406383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625594698889378177875177 1219196024167033633406383)
            ·
              refine ⟨1828794036250550450109575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219196024167033633406383 1828794036250550450109575)
              ·
                refine ⟨2743191054375825675164363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828794036250550450109575 2743191054375825675164363)
                ·
                  refine ⟨4114786581563738512746545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743191054375825675164363 4114786581563738512746545)
                  ·
                    refine ⟨3086089936172803884559909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4114786581563738512746545 3086089936172803884559909)
                    ·
                      refine ⟨578641863032400728354983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3086089936172803884559909 578641863032400728354983)
                      ·
                        rfl

theorem cell23_1126901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1126901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126901 prefixEnd_1126901 := by exact prefixLift 1126901
  have htrace : WordTrace (prefixWord ++ tailWord_1126901) baseStart_1126901 baseEnd_1126901 := by
    simpa [prefixWord, tailWord_1126901, baseEnd_1126901] using wordTrace_append hprefix tailTrace_1126901
  have hstable : (prefixWord ++ tailWord_1126901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126901).length < 2 ^ (prefixWord ++ tailWord_1126901).sum := by decide
  have hdescent : baseEnd_1126901 < baseStart_1126901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126997 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1126997 : Nat := 118140960795 + 1126997 * 2 ^ 59
def prefixEnd_1126997 : Nat := 4983230072969 + 3 ^ 40 * 1126997 * 2
def baseEnd_1126997 : Nat := 192897052391744117584847

theorem tailTrace_1126997 : CollatzResearch.WordTrace tailWord_1126997 prefixEnd_1126997 192897052391744117584847 := by
  unfold tailWord_1126997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41104957498089819608931245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27403304998726546405954163 41104957498089819608931245)
  ·
    refine ⟨15414359061783682353349217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41104957498089819608931245 15414359061783682353349217)
    ·
      refine ⟨11560769296337761765011913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15414359061783682353349217 11560769296337761765011913)
      ·
        refine ⟨8670576972253321323758935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11560769296337761765011913 8670576972253321323758935)
        ·
          refine ⟨13005865458379981985638403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670576972253321323758935 13005865458379981985638403)
          ·
            refine ⟨19508798187569972978457605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13005865458379981985638403 19508798187569972978457605)
            ·
              refine ⟨3657899660169369933460801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19508798187569972978457605 3657899660169369933460801)
              ·
                refine ⟨2743424745127027450095601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657899660169369933460801 2743424745127027450095601)
                ·
                  refine ⟨2057568558845270587571701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2743424745127027450095601 2057568558845270587571701)
                  ·
                    refine ⟨192897052391744117584847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2057568558845270587571701 192897052391744117584847)
                    ·
                      rfl

theorem cell23_1126997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1126997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1126997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1126997 prefixEnd_1126997 := by exact prefixLift 1126997
  have htrace : WordTrace (prefixWord ++ tailWord_1126997) baseStart_1126997 baseEnd_1126997 := by
    simpa [prefixWord, tailWord_1126997, baseEnd_1126997] using wordTrace_append hprefix tailTrace_1126997
  have hstable : (prefixWord ++ tailWord_1126997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126997).length < 2 ^ (prefixWord ++ tailWord_1126997).sum := by decide
  have hdescent : baseEnd_1126997 < baseStart_1126997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127054 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1127054 : Nat := 118140960795 + 1127054 * 2 ^ 59
def prefixEnd_1127054 : Nat := 4983230072969 + 3 ^ 40 * 1127054 * 2
def baseEnd_1127054 : Nat := 578720425572538629741779

theorem tailTrace_1127054 : CollatzResearch.WordTrace tailWord_1127054 prefixEnd_1127054 578720425572538629741779 := by
  unfold tailWord_1127054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138379557360414792969527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27404690972588878895837477 5138379557360414792969527)
  ·
    refine ⟨7707569336040622189454291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5138379557360414792969527 7707569336040622189454291)
    ·
      refine ⟨11561354004060933284181437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7707569336040622189454291 11561354004060933284181437)
      ·
        refine ⟨4335507751522849981568039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11561354004060933284181437 4335507751522849981568039)
        ·
          refine ⟨6503261627284274972352059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335507751522849981568039 6503261627284274972352059)
          ·
            refine ⟨9754892440926412458528089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6503261627284274972352059 9754892440926412458528089)
            ·
              refine ⟨7316169330694809343896067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754892440926412458528089 7316169330694809343896067)
              ·
                refine ⟨10974253996042214015844101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316169330694809343896067 10974253996042214015844101)
                ·
                  refine ⟨2057672624257915127970769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10974253996042214015844101 2057672624257915127970769)
                  ·
                    refine ⟨1543254468193436345978077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2057672624257915127970769 1543254468193436345978077)
                    ·
                      refine ⟨578720425572538629741779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1543254468193436345978077 578720425572538629741779)
                      ·
                        rfl

theorem cell23_1127054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1127054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127054 prefixEnd_1127054 := by exact prefixLift 1127054
  have htrace : WordTrace (prefixWord ++ tailWord_1127054) baseStart_1127054 baseEnd_1127054 := by
    simpa [prefixWord, tailWord_1127054, baseEnd_1127054] using wordTrace_append hprefix tailTrace_1127054
  have hstable : (prefixWord ++ tailWord_1127054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127054).length < 2 ^ (prefixWord ++ tailWord_1127054).sum := by decide
  have hdescent : baseEnd_1127054 < baseStart_1127054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127095 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 1, 4]
def baseStart_1127095 : Nat := 118140960795 + 1127095 * 2 ^ 59
def prefixEnd_1127095 : Nat := 4983230072969 + 3 ^ 40 * 1127095 * 2
def baseEnd_1127095 : Nat := 192913826093124323109697

theorem tailTrace_1127095 : CollatzResearch.WordTrace tailWord_1127095 prefixEnd_1127095 192913826093124323109697 := by
  unfold tailWord_1127095
  simp only [CollatzResearch.WordTrace]
  refine ⟨41108531851734782345998739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27405687901156521563999159 41108531851734782345998739)
  ·
    refine ⟨61662797777602173518998109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41108531851734782345998739 61662797777602173518998109)
    ·
      refine ⟨23123549166600815069624291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61662797777602173518998109 23123549166600815069624291)
      ·
        refine ⟨34685323749901222604436437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23123549166600815069624291 34685323749901222604436437)
        ·
          refine ⟨812937275388309904791479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34685323749901222604436437 812937275388309904791479)
          ·
            refine ⟨1219405913082464857187219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812937275388309904791479 1219405913082464857187219)
            ·
              refine ⟨1829108869623697285780829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219405913082464857187219 1829108869623697285780829)
              ·
                refine ⟨685915826108886482167811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1829108869623697285780829 685915826108886482167811)
                ·
                  refine ⟨1028873739163329723251717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685915826108886482167811 1028873739163329723251717)
                  ·
                    refine ⟨192913826093124323109697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1028873739163329723251717 192913826093124323109697)
                    ·
                      rfl

theorem cell23_1127095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_1127095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127095 prefixEnd_1127095 := by exact prefixLift 1127095
  have htrace : WordTrace (prefixWord ++ tailWord_1127095) baseStart_1127095 baseEnd_1127095 := by
    simpa [prefixWord, tailWord_1127095, baseEnd_1127095] using wordTrace_append hprefix tailTrace_1127095
  have hstable : (prefixWord ++ tailWord_1127095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127095).length < 2 ^ (prefixWord ++ tailWord_1127095).sum := by decide
  have hdescent : baseEnd_1127095 < baseStart_1127095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127104 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_1127104 : Nat := 118140960795 + 1127104 * 2 ^ 59
def prefixEnd_1127104 : Nat := 4983230072969 + 3 ^ 40 * 1127104 * 2
def baseEnd_1127104 : Nat := 192915366535087811372183

theorem tailTrace_1127104 : CollatzResearch.WordTrace tailWord_1127104 prefixEnd_1127104 192915366535087811372183 := by
  unfold tailWord_1127104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20554430054351088441538183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27405906739134784588717577 20554430054351088441538183)
  ·
    refine ⟨30831645081526632662307275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20554430054351088441538183 30831645081526632662307275)
    ·
      refine ⟨46247467622289948993460913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30831645081526632662307275 46247467622289948993460913)
      ·
        refine ⟨34685600716717461745095685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46247467622289948993460913 34685600716717461745095685)
        ·
          refine ⟨6503550134384524077205441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34685600716717461745095685 6503550134384524077205441)
          ·
            refine ⟨4877662600788393057904081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6503550134384524077205441 4877662600788393057904081)
            ·
              refine ⟨3658246950591294793428061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4877662600788393057904081 3658246950591294793428061)
              ·
                refine ⟨1371842606471735547535523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3658246950591294793428061 1371842606471735547535523)
                ·
                  refine ⟨2057763909707603321303285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371842606471735547535523 2057763909707603321303285)
                  ·
                    refine ⟨192915366535087811372183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2057763909707603321303285 192915366535087811372183)
                    ·
                      rfl

theorem cell23_1127104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_1127104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127104 prefixEnd_1127104 := by exact prefixLift 1127104
  have htrace : WordTrace (prefixWord ++ tailWord_1127104) baseStart_1127104 baseEnd_1127104 := by
    simpa [prefixWord, tailWord_1127104, baseEnd_1127104] using wordTrace_append hprefix tailTrace_1127104
  have hstable : (prefixWord ++ tailWord_1127104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127104).length < 2 ^ (prefixWord ++ tailWord_1127104).sum := by decide
  have hdescent : baseEnd_1127104 < baseStart_1127104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127118 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_1127118 : Nat := 118140960795 + 1127118 * 2 ^ 59
def prefixEnd_1127118 : Nat := 4983230072969 + 3 ^ 40 * 1127118 * 2
def baseEnd_1127118 : Nat := 578753288334426379341485

theorem tailTrace_1127118 : CollatzResearch.WordTrace tailWord_1127118 prefixEnd_1127118 578753288334426379341485 := by
  unfold tailWord_1127118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138671341331432159260751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27406247153767638182724005 5138671341331432159260751)
  ·
    refine ⟨7708007011997148238891127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5138671341331432159260751 7708007011997148238891127)
    ·
      refine ⟨11562010517995722358336691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7708007011997148238891127 11562010517995722358336691)
      ·
        refine ⟨17343015776993583537505037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11562010517995722358336691 17343015776993583537505037)
        ·
          refine ⟨6503630916372593826564389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17343015776993583537505037 6503630916372593826564389)
          ·
            refine ⟨1219430796819861342480823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6503630916372593826564389 1219430796819861342480823)
            ·
              refine ⟨1829146195229792013721235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219430796819861342480823 1829146195229792013721235)
              ·
                refine ⟨2743719292844688020581853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829146195229792013721235 2743719292844688020581853)
                ·
                  refine ⟨1028894734816758007718195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2743719292844688020581853 1028894734816758007718195)
                  ·
                    refine ⟨1543342102225137011577293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1028894734816758007718195 1543342102225137011577293)
                    ·
                      refine ⟨578753288334426379341485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1543342102225137011577293 578753288334426379341485)
                      ·
                        rfl

theorem cell23_1127118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_1127118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127118 prefixEnd_1127118 := by exact prefixLift 1127118
  have htrace : WordTrace (prefixWord ++ tailWord_1127118) baseStart_1127118 baseEnd_1127118 := by
    simpa [prefixWord, tailWord_1127118, baseEnd_1127118] using wordTrace_append hprefix tailTrace_1127118
  have hstable : (prefixWord ++ tailWord_1127118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127118).length < 2 ^ (prefixWord ++ tailWord_1127118).sum := by decide
  have hdescent : baseEnd_1127118 < baseStart_1127118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127125 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 6]
def baseStart_1127125 : Nat := 118140960795 + 1127125 * 2 ^ 59
def prefixEnd_1127125 : Nat := 4983230072969 + 3 ^ 40 * 1127125 * 2
def baseEnd_1127125 : Nat := 64306320299889761328217

theorem tailTrace_1127125 : CollatzResearch.WordTrace tailWord_1127125 prefixEnd_1127125 64306320299889761328217 := by
  unfold tailWord_1127125
  simp only [CollatzResearch.WordTrace]
  refine ⟨41109626041626097469590829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27406417361084064979727219 41109626041626097469590829)
  ·
    refine ⟨15416109765609786551096561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41109626041626097469590829 15416109765609786551096561)
    ·
      refine ⟨11562082324207339913322421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15416109765609786551096561 11562082324207339913322421)
      ·
        refine ⟨1083945217894438116873977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11562082324207339913322421 1083945217894438116873977)
        ·
          refine ⟨812958913420828587655483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083945217894438116873977 812958913420828587655483)
          ·
            refine ⟨1219438370131242881483225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812958913420828587655483 1219438370131242881483225)
            ·
              refine ⟨914578777598432161112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219438370131242881483225 914578777598432161112419)
              ·
                refine ⟨1371868166397648241668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914578777598432161112419 1371868166397648241668629)
                ·
                  refine ⟨64306320299889761328217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1371868166397648241668629 64306320299889761328217)
                  ·
                    rfl

theorem cell23_1127125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_1127125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127125 prefixEnd_1127125 := by exact prefixLift 1127125
  have htrace : WordTrace (prefixWord ++ tailWord_1127125) baseStart_1127125 baseEnd_1127125 := by
    simpa [prefixWord, tailWord_1127125, baseEnd_1127125] using wordTrace_append hprefix tailTrace_1127125
  have hstable : (prefixWord ++ tailWord_1127125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127125).length < 2 ^ (prefixWord ++ tailWord_1127125).sum := by decide
  have hdescent : baseEnd_1127125 < baseStart_1127125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127141 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1127141 : Nat := 118140960795 + 1127141 * 2 ^ 59
def prefixEnd_1127141 : Nat := 4983230072969 + 3 ^ 40 * 1127141 * 2
def baseEnd_1127141 : Nat := 578765098389479789353879

theorem tailTrace_1127141 : CollatzResearch.WordTrace tailWord_1127141 prefixEnd_1127141 578765098389479789353879 := by
  unfold tailWord_1127141
  simp only [CollatzResearch.WordTrace]
  refine ⟨41110209609568132202173277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27406806406378754801448851 41110209609568132202173277)
  ·
    refine ⟨15416328603588049575814979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41110209609568132202173277 15416328603588049575814979)
    ·
      refine ⟨23124492905382074363722469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15416328603588049575814979 23124492905382074363722469)
      ·
        refine ⟨4335842419759138943197963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23124492905382074363722469 4335842419759138943197963)
        ·
          refine ⟨6503763629638708414796945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335842419759138943197963 6503763629638708414796945)
          ·
            refine ⟨4877822722229031311097709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6503763629638708414796945 4877822722229031311097709)
            ·
              refine ⟨1829183520835886741661641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4877822722229031311097709 1829183520835886741661641)
              ·
                refine ⟨1371887640626915056246231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829183520835886741661641 1371887640626915056246231)
                ·
                  refine ⟨2057831460940372584369347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371887640626915056246231 2057831460940372584369347)
                  ·
                    refine ⟨3086747191410558876554021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2057831460940372584369347 3086747191410558876554021)
                    ·
                      refine ⟨578765098389479789353879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3086747191410558876554021 578765098389479789353879)
                      ·
                        rfl

theorem cell23_1127141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1127141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127141 prefixEnd_1127141 := by exact prefixLift 1127141
  have htrace : WordTrace (prefixWord ++ tailWord_1127141) baseStart_1127141 baseEnd_1127141 := by
    simpa [prefixWord, tailWord_1127141, baseEnd_1127141] using wordTrace_append hprefix tailTrace_1127141
  have hstable : (prefixWord ++ tailWord_1127141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127141).length < 2 ^ (prefixWord ++ tailWord_1127141).sum := by decide
  have hdescent : baseEnd_1127141 < baseStart_1127141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127154 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1127154 : Nat := 118140960795 + 1127154 * 2 ^ 59
def prefixEnd_1127154 : Nat := 4983230072969 + 3 ^ 40 * 1127154 * 2
def baseEnd_1127154 : Nat := 578771773637988238491319

theorem tailTrace_1127154 : CollatzResearch.WordTrace tailWord_1127154 prefixEnd_1127154 578771773637988238491319 := by
  unfold tailWord_1127154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10277670939630258855599129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27407122505680690281597677 10277670939630258855599129)
  ·
    refine ⟨7708253204722694141699347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10277670939630258855599129 7708253204722694141699347)
    ·
      refine ⟨11562379807084041212549021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7708253204722694141699347 11562379807084041212549021)
      ·
        refine ⟨4335892427656515454705883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11562379807084041212549021 4335892427656515454705883)
        ·
          refine ⟨6503838641484773182058825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335892427656515454705883 6503838641484773182058825)
          ·
            refine ⟨4877878981113579886544119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6503838641484773182058825 4877878981113579886544119)
            ·
              refine ⟨7316818471670369829816179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877878981113579886544119 7316818471670369829816179)
              ·
                refine ⟨10975227707505554744724269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316818471670369829816179 10975227707505554744724269)
                ·
                  refine ⟨4115710390314583029271601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10975227707505554744724269 4115710390314583029271601)
                  ·
                    refine ⟨3086782792735937271953701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4115710390314583029271601 3086782792735937271953701)
                    ·
                      refine ⟨578771773637988238491319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3086782792735937271953701 578771773637988238491319)
                      ·
                        rfl

theorem cell23_1127154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1127154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127154 prefixEnd_1127154 := by exact prefixLift 1127154
  have htrace : WordTrace (prefixWord ++ tailWord_1127154) baseStart_1127154 baseEnd_1127154 := by
    simpa [prefixWord, tailWord_1127154, baseEnd_1127154] using wordTrace_append hprefix tailTrace_1127154
  have hstable : (prefixWord ++ tailWord_1127154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127154).length < 2 ^ (prefixWord ++ tailWord_1127154).sum := by decide
  have hdescent : baseEnd_1127154 < baseStart_1127154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127158 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1127158 : Nat := 118140960795 + 1127158 * 2 ^ 59
def prefixEnd_1127158 : Nat := 4983230072969 + 3 ^ 40 * 1127158 * 2
def baseEnd_1127158 : Nat := 578773827560606222841301

theorem tailTrace_1127158 : CollatzResearch.WordTrace tailWord_1127158 prefixEnd_1127158 578773827560606222841301 := by
  unfold tailWord_1127158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569426853156659006596383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27407219767004362737028085 2569426853156659006596383)
  ·
    refine ⟨3854140279734988509894575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569426853156659006596383 3854140279734988509894575)
    ·
      refine ⟨5781210419602482764841863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3854140279734988509894575 5781210419602482764841863)
      ·
        refine ⟨8671815629403724147262795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5781210419602482764841863 8671815629403724147262795)
        ·
          refine ⟨13007723444105586220894193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671815629403724147262795 13007723444105586220894193)
          ·
            refine ⟨9755792583079189665670645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007723444105586220894193 9755792583079189665670645)
            ·
              refine ⟨914605554663674031156623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9755792583079189665670645 914605554663674031156623)
              ·
                refine ⟨1371908331995511046734935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914605554663674031156623 1371908331995511046734935)
                ·
                  refine ⟨2057862497993266570102403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371908331995511046734935 2057862497993266570102403)
                  ·
                    refine ⟨3086793746989899855153605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2057862497993266570102403 3086793746989899855153605)
                    ·
                      refine ⟨578773827560606222841301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3086793746989899855153605 578773827560606222841301)
                      ·
                        rfl

theorem cell23_1127158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1127158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127158 prefixEnd_1127158 := by exact prefixLift 1127158
  have htrace : WordTrace (prefixWord ++ tailWord_1127158) baseStart_1127158 baseEnd_1127158 := by
    simpa [prefixWord, tailWord_1127158, baseEnd_1127158] using wordTrace_append hprefix tailTrace_1127158
  have hstable : (prefixWord ++ tailWord_1127158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127158).length < 2 ^ (prefixWord ++ tailWord_1127158).sum := by decide
  have hdescent : baseEnd_1127158 < baseStart_1127158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127177 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_1127177 : Nat := 118140960795 + 1127177 * 2 ^ 59
def prefixEnd_1127177 : Nat := 4983230072969 + 3 ^ 40 * 1127177 * 2
def baseEnd_1127177 : Nat := 192927861231013882834571

theorem tailTrace_1127177 : CollatzResearch.WordTrace tailWord_1127177 prefixEnd_1127177 192927861231013882834571 := by
  unfold tailWord_1127177
  simp only [CollatzResearch.WordTrace]
  refine ⟨41111522637437710350483785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27407681758291806900322523 41111522637437710350483785)
  ·
    refine ⟨30833641978078282762862839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41111522637437710350483785 30833641978078282762862839)
    ·
      refine ⟨46250462967117424144294259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30833641978078282762862839 46250462967117424144294259)
      ·
        refine ⟨69375694450676136216441389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46250462967117424144294259 69375694450676136216441389)
        ·
          refine ⟨26015885419003551081165521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69375694450676136216441389 26015885419003551081165521)
          ·
            refine ⟨19511914064252663310874141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26015885419003551081165521 19511914064252663310874141)
            ·
              refine ⟨7316967774094748741577803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19511914064252663310874141 7316967774094748741577803)
              ·
                refine ⟨10975451661142123112366705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316967774094748741577803 10975451661142123112366705)
                ·
                  refine ⟨8231588745856592334275029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10975451661142123112366705 8231588745856592334275029)
                  ·
                    refine ⟨192927861231013882834571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8231588745856592334275029 192927861231013882834571)
                    ·
                      rfl

theorem cell23_1127177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_1127177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127177 prefixEnd_1127177 := by exact prefixLift 1127177
  have htrace : WordTrace (prefixWord ++ tailWord_1127177) baseStart_1127177 baseEnd_1127177 := by
    simpa [prefixWord, tailWord_1127177, baseEnd_1127177] using wordTrace_append hprefix tailTrace_1127177
  have hstable : (prefixWord ++ tailWord_1127177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127177).length < 2 ^ (prefixWord ++ tailWord_1127177).sum := by decide
  have hdescent : baseEnd_1127177 < baseStart_1127177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127201 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1127201 : Nat := 118140960795 + 1127201 * 2 ^ 59
def prefixEnd_1127201 : Nat := 4983230072969 + 3 ^ 40 * 1127201 * 2
def baseEnd_1127201 : Nat := 578795907228749554603603

theorem tailTrace_1127201 : CollatzResearch.WordTrace tailWord_1127201 prefixEnd_1127201 578795907228749554603603 := by
  unfold tailWord_1127201
  simp only [CollatzResearch.WordTrace]
  refine ⟨41112397989350762449357457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27408265326233841632904971 41112397989350762449357457)
  ·
    refine ⟨30834298492013071837018093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41112397989350762449357457 30834298492013071837018093)
    ·
      refine ⟨11562861934504901938881785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30834298492013071837018093 11562861934504901938881785)
      ·
        refine ⟨8672146450878676454161339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11562861934504901938881785 8672146450878676454161339)
        ·
          refine ⟨13008219676318014681242009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672146450878676454161339 13008219676318014681242009)
          ·
            refine ⟨9756164757238511010931507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13008219676318014681242009 9756164757238511010931507)
            ·
              refine ⟨14634247135857766516397261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756164757238511010931507 14634247135857766516397261)
              ·
                refine ⟨5487842675946662443648973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14634247135857766516397261 5487842675946662443648973)
                ·
                  refine ⟨2057941003479998416368365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5487842675946662443648973 2057941003479998416368365)
                  ·
                    refine ⟨771727876304999406138137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057941003479998416368365 771727876304999406138137)
                    ·
                      refine ⟨578795907228749554603603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771727876304999406138137 578795907228749554603603)
                      ·
                        rfl

theorem cell23_1127201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1127201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127201 prefixEnd_1127201 := by exact prefixLift 1127201
  have htrace : WordTrace (prefixWord ++ tailWord_1127201) baseStart_1127201 baseEnd_1127201 := by
    simpa [prefixWord, tailWord_1127201, baseEnd_1127201] using wordTrace_append hprefix tailTrace_1127201
  have hstable : (prefixWord ++ tailWord_1127201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127201).length < 2 ^ (prefixWord ++ tailWord_1127201).sum := by decide
  have hdescent : baseEnd_1127201 < baseStart_1127201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127218 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_1127218 : Nat := 118140960795 + 1127218 * 2 ^ 59
def prefixEnd_1127218 : Nat := 4983230072969 + 3 ^ 40 * 1127218 * 2
def baseEnd_1127218 : Nat := 578804636399875988091025

theorem tailTrace_1127218 : CollatzResearch.WordTrace tailWord_1127218 prefixEnd_1127218 578804636399875988091025 := by
  unfold tailWord_1127218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10278254507572293588181577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27408678686859449568484205 10278254507572293588181577)
  ·
    refine ⟨7708690880679220191136183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10278254507572293588181577 7708690880679220191136183)
    ·
      refine ⟨11563036321018830286704275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7708690880679220191136183 11563036321018830286704275)
      ·
        refine ⟨17344554481528245430056413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11563036321018830286704275 17344554481528245430056413)
        ·
          refine ⟨6504207930573092036271155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17344554481528245430056413 6504207930573092036271155)
          ·
            refine ⟨9756311895859638054406733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6504207930573092036271155 9756311895859638054406733)
            ·
              refine ⟨3658616960947364270402525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9756311895859638054406733 3658616960947364270402525)
              ·
                refine ⟨1371981360355261601400947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3658616960947364270402525 1371981360355261601400947)
                ·
                  refine ⟨2057972040532892402101421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371981360355261601400947 2057972040532892402101421)
                  ·
                    refine ⟨771739515199834650788033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2057972040532892402101421 771739515199834650788033)
                    ·
                      refine ⟨578804636399875988091025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771739515199834650788033 578804636399875988091025)
                      ·
                        rfl

theorem cell23_1127218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_1127218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127218 prefixEnd_1127218 := by exact prefixLift 1127218
  have htrace : WordTrace (prefixWord ++ tailWord_1127218) baseStart_1127218 baseEnd_1127218 := by
    simpa [prefixWord, tailWord_1127218, baseEnd_1127218] using wordTrace_append hprefix tailTrace_1127218
  have hstable : (prefixWord ++ tailWord_1127218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127218).length < 2 ^ (prefixWord ++ tailWord_1127218).sum := by decide
  have hdescent : baseEnd_1127218 < baseStart_1127218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127247 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_1127247 : Nat := 118140960795 + 1127247 * 2 ^ 59
def prefixEnd_1127247 : Nat := 4983230072969 + 3 ^ 40 * 1127247 * 2
def baseEnd_1127247 : Nat := 578819527338856374628391

theorem tailTrace_1127247 : CollatzResearch.WordTrace tailWord_1127247 prefixEnd_1127247 578819527338856374628391 := by
  unfold tailWord_1127247
  simp only [CollatzResearch.WordTrace]
  refine ⟨41114075747184112305531995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27409383831456074870354663 41114075747184112305531995)
  ·
    refine ⟨61671113620776168458297993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41114075747184112305531995 61671113620776168458297993)
    ·
      refine ⟨46253335215582126343723495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61671113620776168458297993 46253335215582126343723495)
      ·
        refine ⟨69380002823373189515585243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46253335215582126343723495 69380002823373189515585243)
        ·
          refine ⟨104070004235059784273377865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69380002823373189515585243 104070004235059784273377865)
          ·
            refine ⟨78052503176294838205033399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104070004235059784273377865 78052503176294838205033399)
            ·
              refine ⟨117078754764442257307550099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78052503176294838205033399 117078754764442257307550099)
              ·
                refine ⟨175618132146663385961325149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117078754764442257307550099 175618132146663385961325149)
                ·
                  refine ⟨65856799554998769735496931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175618132146663385961325149 65856799554998769735496931)
                  ·
                    refine ⟨98785199332498154603245397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65856799554998769735496931 98785199332498154603245397)
                    ·
                      refine ⟨578819527338856374628391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 98785199332498154603245397 578819527338856374628391)
                      ·
                        rfl

theorem cell23_1127247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_1127247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127247 prefixEnd_1127247 := by exact prefixLift 1127247
  have htrace : WordTrace (prefixWord ++ tailWord_1127247) baseStart_1127247 baseEnd_1127247 := by
    simpa [prefixWord, tailWord_1127247, baseEnd_1127247] using wordTrace_append hprefix tailTrace_1127247
  have hstable : (prefixWord ++ tailWord_1127247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127247).length < 2 ^ (prefixWord ++ tailWord_1127247).sum := by decide
  have hdescent : baseEnd_1127247 < baseStart_1127247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127248 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2]
def baseStart_1127248 : Nat := 118140960795 + 1127248 * 2 ^ 59
def prefixEnd_1127248 : Nat := 4983230072969 + 3 ^ 40 * 1127248 * 2
def baseEnd_1127248 : Nat := 578820040819510870715887

theorem tailTrace_1127248 : CollatzResearch.WordTrace tailWord_1127248 prefixEnd_1127248 578820040819510870715887 := by
  unfold tailWord_1127248
  simp only [CollatzResearch.WordTrace]
  refine ⟨20557056110090244738159199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27409408146786992984212265 20557056110090244738159199)
  ·
    refine ⟨30835584165135367107238799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20557056110090244738159199 30835584165135367107238799)
    ·
      refine ⟨46253376247703050660858199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30835584165135367107238799 46253376247703050660858199)
      ·
        refine ⟨69380064371554575991287299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46253376247703050660858199 69380064371554575991287299)
        ·
          refine ⟨104070096557331863986930949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69380064371554575991287299 104070096557331863986930949)
          ·
            refine ⟨19513143104499724497549553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104070096557331863986930949 19513143104499724497549553)
            ·
              refine ⟨14634857328374793373162165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19513143104499724497549553 14634857328374793373162165)
              ·
                refine ⟨1372017874535136878733953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14634857328374793373162165 1372017874535136878733953)
                ·
                  refine ⟨1029013405901352659050465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372017874535136878733953 1029013405901352659050465)
                  ·
                    refine ⟨771760054426014494287849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1029013405901352659050465 771760054426014494287849)
                    ·
                      refine ⟨578820040819510870715887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771760054426014494287849 578820040819510870715887)
                      ·
                        rfl

theorem cell23_1127248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 2, 2].length) (baseStart_1127248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127248 prefixEnd_1127248 := by exact prefixLift 1127248
  have htrace : WordTrace (prefixWord ++ tailWord_1127248) baseStart_1127248 baseEnd_1127248 := by
    simpa [prefixWord, tailWord_1127248, baseEnd_1127248] using wordTrace_append hprefix tailTrace_1127248
  have hstable : (prefixWord ++ tailWord_1127248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127248).length < 2 ^ (prefixWord ++ tailWord_1127248).sum := by decide
  have hdescent : baseEnd_1127248 < baseStart_1127248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127321 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 4, 4, 2]
def baseStart_1127321 : Nat := 118140960795 + 1127321 * 2 ^ 59
def prefixEnd_1127321 : Nat := 4983230072969 + 3 ^ 40 * 1127321 * 2
def baseEnd_1127321 : Nat := 578857524907289085103051

theorem tailTrace_1127321 : CollatzResearch.WordTrace tailWord_1127321 prefixEnd_1127321 578857524907289085103051 := by
  unfold tailWord_1127321
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116774748916022943725817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27411183165944015295817211 41116774748916022943725817)
  ·
    refine ⟨30837581061687017207794363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41116774748916022943725817 30837581061687017207794363)
    ·
      refine ⟨46256371592530525811691545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30837581061687017207794363 46256371592530525811691545)
      ·
        refine ⟨34692278694397894358768659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46256371592530525811691545 34692278694397894358768659)
        ·
          refine ⟨52038418041596841538152989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34692278694397894358768659 52038418041596841538152989)
          ·
            refine ⟨19514406765598815576807371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52038418041596841538152989 19514406765598815576807371)
            ·
              refine ⟨29271610148398223365211057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19514406765598815576807371 29271610148398223365211057)
              ·
                refine ⟨21953707611298667523908293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29271610148398223365211057 21953707611298667523908293)
                ·
                  refine ⟨4116320177118500160732805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21953707611298667523908293 4116320177118500160732805)
                  ·
                    refine ⟨771810033209718780137401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116320177118500160732805 771810033209718780137401)
                    ·
                      refine ⟨578857524907289085103051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771810033209718780137401 578857524907289085103051)
                      ·
                        rfl

theorem cell23_1127321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_1127321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127321 prefixEnd_1127321 := by exact prefixLift 1127321
  have htrace : WordTrace (prefixWord ++ tailWord_1127321) baseStart_1127321 baseEnd_1127321 := by
    simpa [prefixWord, tailWord_1127321, baseEnd_1127321] using wordTrace_append hprefix tailTrace_1127321
  have hstable : (prefixWord ++ tailWord_1127321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127321).length < 2 ^ (prefixWord ++ tailWord_1127321).sum := by decide
  have hdescent : baseEnd_1127321 < baseStart_1127321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127382 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1127382 : Nat := 118140960795 + 1127382 * 2 ^ 59
def prefixEnd_1127382 : Nat := 4983230072969 + 3 ^ 40 * 1127382 * 2
def baseEnd_1127382 : Nat := 192962949075737782146757

theorem tailTrace_1127382 : CollatzResearch.WordTrace tailWord_1127382 prefixEnd_1127382 192962949075737782146757 := by
  unfold tailWord_1127382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569937475105939397606025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27412666401130020241130933 2569937475105939397606025)
  ·
    refine ⟨1927453106329454548204519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2569937475105939397606025 1927453106329454548204519)
    ·
      refine ⟨2891179659494181822306779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927453106329454548204519 2891179659494181822306779)
      ·
        refine ⟨4336769489241272733460169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891179659494181822306779 4336769489241272733460169)
        ·
          refine ⟨3252577116930954550095127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336769489241272733460169 3252577116930954550095127)
          ·
            refine ⟨4878865675396431825142691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252577116930954550095127 4878865675396431825142691)
            ·
              refine ⟨7318298513094647737714037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878865675396431825142691 7318298513094647737714037)
              ·
                refine ⟨686090485602623225410691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7318298513094647737714037 686090485602623225410691)
                ·
                  refine ⟨1029135728403934838116037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686090485602623225410691 1029135728403934838116037)
                  ·
                    refine ⟨192962949075737782146757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029135728403934838116037 192962949075737782146757)
                    ·
                      rfl

theorem cell23_1127382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1127382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127382 prefixEnd_1127382 := by exact prefixLift 1127382
  have htrace : WordTrace (prefixWord ++ tailWord_1127382) baseStart_1127382 baseEnd_1127382 := by
    simpa [prefixWord, tailWord_1127382, baseEnd_1127382] using wordTrace_append hprefix tailTrace_1127382
  have hstable : (prefixWord ++ tailWord_1127382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127382).length < 2 ^ (prefixWord ++ tailWord_1127382).sum := by decide
  have hdescent : baseEnd_1127382 < baseStart_1127382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127404 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_1127404 : Nat := 118140960795 + 1127404 * 2 ^ 59
def prefixEnd_1127404 : Nat := 4983230072969 + 3 ^ 40 * 1127404 * 2
def baseEnd_1127404 : Nat := 192966714600537420121723

theorem tailTrace_1127404 : CollatzResearch.WordTrace tailWord_1127404 prefixEnd_1127404 192966714600537420121723 := by
  unfold tailWord_1127404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20559901003807664059498633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27413201338410218745998177 20559901003807664059498633)
  ·
    refine ⟨15419925752855748044623975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20559901003807664059498633 15419925752855748044623975)
    ·
      refine ⟨23129888629283622066935963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15419925752855748044623975 23129888629283622066935963)
      ·
        refine ⟨34694832943925433100403945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23129888629283622066935963 34694832943925433100403945)
        ·
          refine ⟨26021124707944074825302959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34694832943925433100403945 26021124707944074825302959)
          ·
            refine ⟨39031687061916112237954439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26021124707944074825302959 39031687061916112237954439)
            ·
              refine ⟨58547530592874168356931659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39031687061916112237954439 58547530592874168356931659)
              ·
                refine ⟨87821295889311252535397489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58547530592874168356931659 87821295889311252535397489)
                ·
                  refine ⟨65865971916983439401548117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87821295889311252535397489 65865971916983439401548117)
                  ·
                    refine ⟨192966714600537420121723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 65865971916983439401548117 192966714600537420121723)
                    ·
                      rfl

theorem cell23_1127404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_1127404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127404 prefixEnd_1127404 := by exact prefixLift 1127404
  have htrace : WordTrace (prefixWord ++ tailWord_1127404) baseStart_1127404 baseEnd_1127404 := by
    simpa [prefixWord, tailWord_1127404, baseEnd_1127404] using wordTrace_append hprefix tailTrace_1127404
  have hstable : (prefixWord ++ tailWord_1127404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127404).length < 2 ^ (prefixWord ++ tailWord_1127404).sum := by decide
  have hdescent : baseEnd_1127404 < baseStart_1127404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127431 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1127431 : Nat := 118140960795 + 1127431 * 2 ^ 59
def prefixEnd_1127431 : Nat := 4983230072969 + 3 ^ 40 * 1127431 * 2
def baseEnd_1127431 : Nat := 578914007779283654727545

theorem tailTrace_1127431 : CollatzResearch.WordTrace tailWord_1127431 prefixEnd_1127431 578914007779283654727545 := by
  unfold tailWord_1127431
  simp only [CollatzResearch.WordTrace]
  refine ⟨41120786778517511730230147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27413857852345007820153431 41120786778517511730230147)
  ·
    refine ⟨61681180167776267595345221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41120786778517511730230147 61681180167776267595345221)
    ·
      refine ⟨11565221281458050174127229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61681180167776267595345221 11565221281458050174127229)
      ·
        refine ⟨4336957980546768815297711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11565221281458050174127229 4336957980546768815297711)
        ·
          refine ⟨6505436970820153222946567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4336957980546768815297711 6505436970820153222946567)
          ·
            refine ⟨9758155456230229834419851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6505436970820153222946567 9758155456230229834419851)
            ·
              refine ⟨14637233184345344751629777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9758155456230229834419851 14637233184345344751629777)
              ·
                refine ⟨10977924888259008563722333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14637233184345344751629777 10977924888259008563722333)
                ·
                  refine ⟨4116721833097128211395875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10977924888259008563722333 4116721833097128211395875)
                  ·
                    refine ⟨6175082749645692317093813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116721833097128211395875 6175082749645692317093813)
                    ·
                      refine ⟨578914007779283654727545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6175082749645692317093813 578914007779283654727545)
                      ·
                        rfl

theorem cell23_1127431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1127431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127431 prefixEnd_1127431 := by exact prefixLift 1127431
  have htrace : WordTrace (prefixWord ++ tailWord_1127431) baseStart_1127431 baseEnd_1127431 := by
    simpa [prefixWord, tailWord_1127431, baseEnd_1127431] using wordTrace_append hprefix tailTrace_1127431
  have hstable : (prefixWord ++ tailWord_1127431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127431).length < 2 ^ (prefixWord ++ tailWord_1127431).sum := by decide
  have hdescent : baseEnd_1127431 < baseStart_1127431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127438 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1127438 : Nat := 118140960795 + 1127438 * 2 ^ 59
def prefixEnd_1127438 : Nat := 4983230072969 + 3 ^ 40 * 1127438 * 2
def baseEnd_1127438 : Nat := 192972534047955042446671

theorem tailTrace_1127438 : CollatzResearch.WordTrace tailWord_1127438 prefixEnd_1127438 192972534047955042446671 := by
  unfold tailWord_1127438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140130261186518990716871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27414028059661434617156645 5140130261186518990716871)
  ·
    refine ⟨7710195391779778486075307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5140130261186518990716871 7710195391779778486075307)
    ·
      refine ⟨11565293087669667729112961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7710195391779778486075307 11565293087669667729112961)
      ·
        refine ⟨8673969815752250796834721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11565293087669667729112961 8673969815752250796834721)
        ·
          refine ⟨6505477361814188097626041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8673969815752250796834721 6505477361814188097626041)
          ·
            refine ⟨4879108021360641073219531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6505477361814188097626041 4879108021360641073219531)
            ·
              refine ⟨7318662032040961609829297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879108021360641073219531 7318662032040961609829297)
              ·
                refine ⟨5488996524030721207371973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7318662032040961609829297 5488996524030721207371973)
                ·
                  refine ⟨1029186848255760226382245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5488996524030721207371973 1029186848255760226382245)
                  ·
                    refine ⟨192972534047955042446671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029186848255760226382245 192972534047955042446671)
                    ·
                      rfl

theorem cell23_1127438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1127438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127438 prefixEnd_1127438 := by exact prefixLift 1127438
  have htrace : WordTrace (prefixWord ++ tailWord_1127438) baseStart_1127438 baseEnd_1127438 := by
    simpa [prefixWord, tailWord_1127438, baseEnd_1127438] using wordTrace_append hprefix tailTrace_1127438
  have hstable : (prefixWord ++ tailWord_1127438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127438).length < 2 ^ (prefixWord ++ tailWord_1127438).sum := by decide
  have hdescent : baseEnd_1127438 < baseStart_1127438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127441 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_1127441 : Nat := 118140960795 + 1127441 * 2 ^ 59
def prefixEnd_1127441 : Nat := 4983230072969 + 3 ^ 40 * 1127441 * 2
def baseEnd_1127441 : Nat := 578919142585828615602499

theorem tailTrace_1127441 : CollatzResearch.WordTrace tailWord_1127441 prefixEnd_1127441 578919142585828615602499 := by
  unfold tailWord_1127441
  simp only [CollatzResearch.WordTrace]
  refine ⟨41121151508481283438094177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27414101005654188958729451 41121151508481283438094177)
  ·
    refine ⟨30840863631360962578570633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41121151508481283438094177 30840863631360962578570633)
    ·
      refine ⟨23130647723520721933927975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30840863631360962578570633 23130647723520721933927975)
      ·
        refine ⟨34695971585281082900891963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23130647723520721933927975 34695971585281082900891963)
        ·
          refine ⟨52043957377921624351337945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34695971585281082900891963 52043957377921624351337945)
          ·
            refine ⟨39032968033441218263503459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52043957377921624351337945 39032968033441218263503459)
            ·
              refine ⟨58549452050161827395255189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39032968033441218263503459 58549452050161827395255189)
              ·
                refine ⟨2744505564851335659152587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58549452050161827395255189 2744505564851335659152587)
                ·
                  refine ⟨4116758347277003488728881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744505564851335659152587 4116758347277003488728881)
                  ·
                    refine ⟨3087568760457752616546661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4116758347277003488728881 3087568760457752616546661)
                    ·
                      refine ⟨578919142585828615602499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3087568760457752616546661 578919142585828615602499)
                      ·
                        rfl

theorem cell23_1127441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_1127441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127441 prefixEnd_1127441 := by exact prefixLift 1127441
  have htrace : WordTrace (prefixWord ++ tailWord_1127441) baseStart_1127441 baseEnd_1127441 := by
    simpa [prefixWord, tailWord_1127441, baseEnd_1127441] using wordTrace_append hprefix tailTrace_1127441
  have hstable : (prefixWord ++ tailWord_1127441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127441).length < 2 ^ (prefixWord ++ tailWord_1127441).sum := by decide
  have hdescent : baseEnd_1127441 < baseStart_1127441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127448 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1127448 : Nat := 118140960795 + 1127448 * 2 ^ 59
def prefixEnd_1127448 : Nat := 4983230072969 + 3 ^ 40 * 1127448 * 2
def baseEnd_1127448 : Nat := 578922736950410088214967

theorem tailTrace_1127448 : CollatzResearch.WordTrace tailWord_1127448 prefixEnd_1127448 578922736950410088214967 := by
  unfold tailWord_1127448
  simp only [CollatzResearch.WordTrace]
  refine ⟨20560703409727961816799499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27414271212970615755732665 20560703409727961816799499)
  ·
    refine ⟨30841055114591942725199249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20560703409727961816799499 30841055114591942725199249)
    ·
      refine ⟨23130791335943957043899437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30841055114591942725199249 23130791335943957043899437)
      ·
        refine ⟨8674046750978983891462289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23130791335943957043899437 8674046750978983891462289)
        ·
          refine ⟨6505535063234237918596717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8674046750978983891462289 6505535063234237918596717)
          ·
            refine ⟨2439575648712839219473769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6505535063234237918596717 2439575648712839219473769)
            ·
              refine ⟨1829681736534629414605327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439575648712839219473769 1829681736534629414605327)
              ·
                refine ⟨2744522604801944121907991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829681736534629414605327 2744522604801944121907991)
                ·
                  refine ⟨4116783907202916182861987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744522604801944121907991 4116783907202916182861987)
                  ·
                    refine ⟨6175175860804374274292981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116783907202916182861987 6175175860804374274292981)
                    ·
                      refine ⟨578922736950410088214967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6175175860804374274292981 578922736950410088214967)
                      ·
                        rfl

theorem cell23_1127448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1127448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127448 prefixEnd_1127448 := by exact prefixLift 1127448
  have htrace : WordTrace (prefixWord ++ tailWord_1127448) baseStart_1127448 baseEnd_1127448 := by
    simpa [prefixWord, tailWord_1127448, baseEnd_1127448] using wordTrace_append hprefix tailTrace_1127448
  have hstable : (prefixWord ++ tailWord_1127448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127448).length < 2 ^ (prefixWord ++ tailWord_1127448).sum := by decide
  have hdescent : baseEnd_1127448 < baseStart_1127448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127456 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1127456 : Nat := 118140960795 + 1127456 * 2 ^ 59
def prefixEnd_1127456 : Nat := 4983230072969 + 3 ^ 40 * 1127456 * 2
def baseEnd_1127456 : Nat := 578926844795646056914931

theorem tailTrace_1127456 : CollatzResearch.WordTrace tailWord_1127456 prefixEnd_1127456 578926844795646056914931 := by
  unfold tailWord_1127456
  simp only [CollatzResearch.WordTrace]
  refine ⟨20560849301713470499945111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27414465735617960666593481 20560849301713470499945111)
  ·
    refine ⟨30841273952570205749917667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20560849301713470499945111 30841273952570205749917667)
    ·
      refine ⟨46261910928855308624876501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30841273952570205749917667 46261910928855308624876501)
      ·
        refine ⟨1084263537395046295895543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46261910928855308624876501 1084263537395046295895543)
        ·
          refine ⟨1626395306092569443843315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084263537395046295895543 1626395306092569443843315)
          ·
            refine ⟨2439592959138854165764973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626395306092569443843315 2439592959138854165764973)
            ·
              refine ⟨914847359677070312161865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2439592959138854165764973 914847359677070312161865)
              ·
                refine ⟨686135519757802734121399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914847359677070312161865 686135519757802734121399)
                ·
                  refine ⟨1029203279636704101182099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686135519757802734121399 1029203279636704101182099)
                  ·
                    refine ⟨1543804919455056151773149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1029203279636704101182099 1543804919455056151773149)
                    ·
                      refine ⟨578926844795646056914931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1543804919455056151773149 578926844795646056914931)
                      ·
                        rfl

theorem cell23_1127456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1127456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127456 prefixEnd_1127456 := by exact prefixLift 1127456
  have htrace : WordTrace (prefixWord ++ tailWord_1127456) baseStart_1127456 baseEnd_1127456 := by
    simpa [prefixWord, tailWord_1127456, baseEnd_1127456] using wordTrace_append hprefix tailTrace_1127456
  have hstable : (prefixWord ++ tailWord_1127456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127456).length < 2 ^ (prefixWord ++ tailWord_1127456).sum := by decide
  have hdescent : baseEnd_1127456 < baseStart_1127456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127505 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_1127505 : Nat := 118140960795 + 1127505 * 2 ^ 59
def prefixEnd_1127505 : Nat := 4983230072969 + 3 ^ 40 * 1127505 * 2
def baseEnd_1127505 : Nat := 578952005347716365202205

theorem tailTrace_1127505 : CollatzResearch.WordTrace tailWord_1127505 prefixEnd_1127505 578952005347716365202205 := by
  unfold tailWord_1127505
  simp only [CollatzResearch.WordTrace]
  refine ⟨41123485780249422368423969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27415657186832948245615979 41123485780249422368423969)
  ·
    refine ⟨30842614335187066776317977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41123485780249422368423969 30842614335187066776317977)
    ·
      refine ⟨23131960751390300082238483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30842614335187066776317977 23131960751390300082238483)
      ·
        refine ⟨34697941127085450123357725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23131960751390300082238483 34697941127085450123357725)
        ·
          refine ⟨13011727922657043796259147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34697941127085450123357725 13011727922657043796259147)
          ·
            refine ⟨19517591883985565694388721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13011727922657043796259147 19517591883985565694388721)
            ·
              refine ⟨14638193912989174270791541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19517591883985565694388721 14638193912989174270791541)
              ·
                refine ⟨1372330679342735087886707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14638193912989174270791541 1372330679342735087886707)
                ·
                  refine ⟨2058496019014102631830061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372330679342735087886707 2058496019014102631830061)
                  ·
                    refine ⟨771936007130288486936273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058496019014102631830061 771936007130288486936273)
                    ·
                      refine ⟨578952005347716365202205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771936007130288486936273 578952005347716365202205)
                      ·
                        rfl

theorem cell23_1127505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_1127505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127505 prefixEnd_1127505 := by exact prefixLift 1127505
  have htrace : WordTrace (prefixWord ++ tailWord_1127505) baseStart_1127505 baseEnd_1127505 := by
    simpa [prefixWord, tailWord_1127505, baseEnd_1127505] using wordTrace_append hprefix tailTrace_1127505
  have hstable : (prefixWord ++ tailWord_1127505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127505).length < 2 ^ (prefixWord ++ tailWord_1127505).sum := by decide
  have hdescent : baseEnd_1127505 < baseStart_1127505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127511 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 2, 6]
def baseStart_1127511 : Nat := 118140960795 + 1127511 * 2 ^ 59
def prefixEnd_1127511 : Nat := 4983230072969 + 3 ^ 40 * 1127511 * 2
def baseEnd_1127511 : Nat := 192985028743881113909059

theorem tailTrace_1127511 : CollatzResearch.WordTrace tailWord_1127511 prefixEnd_1127511 192985028743881113909059 := by
  unfold tailWord_1127511
  simp only [CollatzResearch.WordTrace]
  refine ⟨41123704618227685393142387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27415803078818456928761591 41123704618227685393142387)
  ·
    refine ⟨61685556927341528089713581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41123704618227685393142387 61685556927341528089713581)
    ·
      refine ⟨23132083847753073033642593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61685556927341528089713581 23132083847753073033642593)
      ·
        refine ⟨17349062885814804775231945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23132083847753073033642593 17349062885814804775231945)
        ·
          refine ⟨13011797164361103581423959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17349062885814804775231945 13011797164361103581423959)
          ·
            refine ⟨19517695746541655372135939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13011797164361103581423959 19517695746541655372135939)
            ·
              refine ⟨29276543619812483058203909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19517695746541655372135939 29276543619812483058203909)
              ·
                refine ⟨5489351928714840573413233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29276543619812483058203909 5489351928714840573413233)
                ·
                  refine ⟨4117013946536130430059925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5489351928714840573413233 4117013946536130430059925)
                  ·
                    refine ⟨192985028743881113909059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4117013946536130430059925 192985028743881113909059)
                    ·
                      rfl

theorem cell23_1127511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_1127511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127511 prefixEnd_1127511 := by exact prefixLift 1127511
  have htrace : WordTrace (prefixWord ++ tailWord_1127511) baseStart_1127511 baseEnd_1127511 := by
    simpa [prefixWord, tailWord_1127511, baseEnd_1127511] using wordTrace_append hprefix tailTrace_1127511
  have hstable : (prefixWord ++ tailWord_1127511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127511).length < 2 ^ (prefixWord ++ tailWord_1127511).sum := by decide
  have hdescent : baseEnd_1127511 < baseStart_1127511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127521 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1127521 : Nat := 118140960795 + 1127521 * 2 ^ 59
def prefixEnd_1127521 : Nat := 4983230072969 + 3 ^ 40 * 1127521 * 2
def baseEnd_1127521 : Nat := 578960221038188302602131

theorem tailTrace_1127521 : CollatzResearch.WordTrace tailWord_1127521 prefixEnd_1127521 578960221038188302602131 := by
  unfold tailWord_1127521
  simp only [CollatzResearch.WordTrace]
  refine ⟨41124069348191457101006417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27416046232127638067337611 41124069348191457101006417)
  ·
    refine ⟨30843052011143592825754813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41124069348191457101006417 30843052011143592825754813)
    ·
      refine ⟨11566144504178847309658055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30843052011143592825754813 11566144504178847309658055)
      ·
        refine ⟨17349216756268270964487083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11566144504178847309658055 17349216756268270964487083)
        ·
          refine ⟨26023825134402406446730625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17349216756268270964487083 26023825134402406446730625)
          ·
            refine ⟨19517868850801804835047969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26023825134402406446730625 19517868850801804835047969)
            ·
              refine ⟨14638401638101353626285977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19517868850801804835047969 14638401638101353626285977)
              ·
                refine ⟨10978801228576015219714483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14638401638101353626285977 10978801228576015219714483)
                ·
                  refine ⟨16468201842864022829571725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10978801228576015219714483 16468201842864022829571725)
                  ·
                    refine ⟨6175575691074008561089397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16468201842864022829571725 6175575691074008561089397)
                    ·
                      refine ⟨578960221038188302602131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6175575691074008561089397 578960221038188302602131)
                      ·
                        rfl

theorem cell23_1127521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1127521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127521 prefixEnd_1127521 := by exact prefixLift 1127521
  have htrace : WordTrace (prefixWord ++ tailWord_1127521) baseStart_1127521 baseEnd_1127521 := by
    simpa [prefixWord, tailWord_1127521, baseEnd_1127521] using wordTrace_append hprefix tailTrace_1127521
  have hstable : (prefixWord ++ tailWord_1127521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127521).length < 2 ^ (prefixWord ++ tailWord_1127521).sum := by decide
  have hdescent : baseEnd_1127521 < baseStart_1127521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127522 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1127522 : Nat := 118140960795 + 1127522 * 2 ^ 59
def prefixEnd_1127522 : Nat := 4983230072969 + 3 ^ 40 * 1127522 * 2
def baseEnd_1127522 : Nat := 578960734518842798689627

theorem tailTrace_1127522 : CollatzResearch.WordTrace tailWord_1127522 prefixEnd_1127522 578960734518842798689627 := by
  unfold tailWord_1127522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281026455296958567948205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27416070547458556181195213 10281026455296958567948205)
  ·
    refine ⟨3855384920736359462980577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10281026455296958567948205 3855384920736359462980577)
    ·
      refine ⟨2891538690552269597235433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3855384920736359462980577 2891538690552269597235433)
      ·
        refine ⟨2168654017914202197926575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2891538690552269597235433 2168654017914202197926575)
        ·
          refine ⟨3252981026871303296889863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168654017914202197926575 3252981026871303296889863)
          ·
            refine ⟨4879471540306954945334795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252981026871303296889863 4879471540306954945334795)
            ·
              refine ⟨7319207310460432418002193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879471540306954945334795 7319207310460432418002193)
              ·
                refine ⟨5489405482845324313501645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319207310460432418002193 5489405482845324313501645)
                ·
                  refine ⟨2058527056066996617563117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5489405482845324313501645 2058527056066996617563117)
                  ·
                    refine ⟨771947646025123731586169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2058527056066996617563117 771947646025123731586169)
                    ·
                      refine ⟨578960734518842798689627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771947646025123731586169 578960734518842798689627)
                      ·
                        rfl

theorem cell23_1127522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1127522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127522 prefixEnd_1127522 := by exact prefixLift 1127522
  have htrace : WordTrace (prefixWord ++ tailWord_1127522) baseStart_1127522 baseEnd_1127522 := by
    simpa [prefixWord, tailWord_1127522, baseEnd_1127522] using wordTrace_append hprefix tailTrace_1127522
  have hstable : (prefixWord ++ tailWord_1127522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127522).length < 2 ^ (prefixWord ++ tailWord_1127522).sum := by decide
  have hdescent : baseEnd_1127522 < baseStart_1127522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127535 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 1, 4, 2]
def baseStart_1127535 : Nat := 118140960795 + 1127535 * 2 ^ 59
def prefixEnd_1127535 : Nat := 4983230072969 + 3 ^ 40 * 1127535 * 2
def baseEnd_1127535 : Nat := 578967409767351247827067

theorem tailTrace_1127535 : CollatzResearch.WordTrace tailWord_1127535 prefixEnd_1127535 578967409767351247827067 := by
  unfold tailWord_1127535
  simp only [CollatzResearch.WordTrace]
  refine ⟨41124579970140737492016059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27416386646760491661344039 41124579970140737492016059)
  ·
    refine ⟨61686869955211106238024089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41124579970140737492016059 61686869955211106238024089)
    ·
      refine ⟨46265152466408329678518067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61686869955211106238024089 46265152466408329678518067)
      ·
        refine ⟨69397728699612494517777101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46265152466408329678518067 69397728699612494517777101)
        ·
          refine ⟨26024148262354685444166413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69397728699612494517777101 26024148262354685444166413)
          ·
            refine ⟨9759055598383007041562405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26024148262354685444166413 9759055598383007041562405)
            ·
              refine ⟨1829822924696813820292951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9759055598383007041562405 1829822924696813820292951)
              ·
                refine ⟨2744734387045220730439427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829822924696813820292951 2744734387045220730439427)
                ·
                  refine ⟨4117101580567831095659141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744734387045220730439427 4117101580567831095659141)
                  ·
                    refine ⟨771956546356468330436089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117101580567831095659141 771956546356468330436089)
                    ·
                      refine ⟨578967409767351247827067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771956546356468330436089 578967409767351247827067)
                      ·
                        rfl

theorem cell23_1127535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4, 2].length) (baseStart_1127535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127535 prefixEnd_1127535 := by exact prefixLift 1127535
  have htrace : WordTrace (prefixWord ++ tailWord_1127535) baseStart_1127535 baseEnd_1127535 := by
    simpa [prefixWord, tailWord_1127535, baseEnd_1127535] using wordTrace_append hprefix tailTrace_1127535
  have hstable : (prefixWord ++ tailWord_1127535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127535).length < 2 ^ (prefixWord ++ tailWord_1127535).sum := by decide
  have hdescent : baseEnd_1127535 < baseStart_1127535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127538 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1127538 : Nat := 118140960795 + 1127538 * 2 ^ 59
def prefixEnd_1127538 : Nat := 4983230072969 + 3 ^ 40 * 1127538 * 2
def baseEnd_1127538 : Nat := 578968950209314736089553

theorem tailTrace_1127538 : CollatzResearch.WordTrace tailWord_1127538 prefixEnd_1127538 578968950209314736089553 := by
  unfold tailWord_1127538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281172347282467251093817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27416459592753246002916845 10281172347282467251093817)
  ·
    refine ⟨7710879260461850438320363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10281172347282467251093817 7710879260461850438320363)
    ·
      refine ⟨11566318890692775657480545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7710879260461850438320363 11566318890692775657480545)
      ·
        refine ⟨8674739168019581743110409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11566318890692775657480545 8674739168019581743110409)
        ·
          refine ⟨6506054376014686307332807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8674739168019581743110409 6506054376014686307332807)
          ·
            refine ⟨9759081564022029460999211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6506054376014686307332807 9759081564022029460999211)
            ·
              refine ⟨14638622346033044191498817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9759081564022029460999211 14638622346033044191498817)
              ·
                refine ⟨10978966759524783143624113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14638622346033044191498817 10978966759524783143624113)
                ·
                  refine ⟨8234225069643587357718085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10978966759524783143624113 8234225069643587357718085)
                  ·
                    refine ⟨1543917200558172629572141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8234225069643587357718085 1543917200558172629572141)
                    ·
                      refine ⟨578968950209314736089553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1543917200558172629572141 578968950209314736089553)
                      ·
                        rfl

theorem cell23_1127538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1127538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127538 prefixEnd_1127538 := by exact prefixLift 1127538
  have htrace : WordTrace (prefixWord ++ tailWord_1127538) baseStart_1127538 baseEnd_1127538 := by
    simpa [prefixWord, tailWord_1127538, baseEnd_1127538] using wordTrace_append hprefix tailTrace_1127538
  have hstable : (prefixWord ++ tailWord_1127538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127538).length < 2 ^ (prefixWord ++ tailWord_1127538).sum := by decide
  have hdescent : baseEnd_1127538 < baseStart_1127538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127550 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1127550 : Nat := 118140960795 + 1127550 * 2 ^ 59
def prefixEnd_1127550 : Nat := 4983230072969 + 3 ^ 40 * 1127550 * 2
def baseEnd_1127550 : Nat := 578975111977168689139499

theorem tailTrace_1127550 : CollatzResearch.WordTrace tailWord_1127550 prefixEnd_1127550 578975111977168689139499 := by
  unfold tailWord_1127550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140640883135799381726513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27416751376724263369208069 5140640883135799381726513)
  ·
    refine ⟨3855480662351849536294885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5140640883135799381726513 3855480662351849536294885)
    ·
      refine ⟨722902624190971788055291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3855480662351849536294885 722902624190971788055291)
      ·
        refine ⟨1084353936286457682082937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722902624190971788055291 1084353936286457682082937)
        ·
          refine ⟨813265452214843261562203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1084353936286457682082937 813265452214843261562203)
          ·
            refine ⟨1219898178322264892343305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813265452214843261562203 1219898178322264892343305)
            ·
              refine ⟨914923633741698669257479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219898178322264892343305 914923633741698669257479)
              ·
                refine ⟨1372385450612548003886219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914923633741698669257479 1372385450612548003886219)
                ·
                  refine ⟨2058578175918822005829329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372385450612548003886219 2058578175918822005829329)
                  ·
                    refine ⟨1543933631939116504371997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2058578175918822005829329 1543933631939116504371997)
                    ·
                      refine ⟨578975111977168689139499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1543933631939116504371997 578975111977168689139499)
                      ·
                        rfl

theorem cell23_1127550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1127550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127550 prefixEnd_1127550 := by exact prefixLift 1127550
  have htrace : WordTrace (prefixWord ++ tailWord_1127550) baseStart_1127550 baseEnd_1127550 := by
    simpa [prefixWord, tailWord_1127550, baseEnd_1127550] using wordTrace_append hprefix tailTrace_1127550
  have hstable : (prefixWord ++ tailWord_1127550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127550).length < 2 ^ (prefixWord ++ tailWord_1127550).sum := by decide
  have hdescent : baseEnd_1127550 < baseStart_1127550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127575 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 5]
def baseStart_1127575 : Nat := 118140960795 + 1127575 * 2 ^ 59
def prefixEnd_1127575 : Nat := 4983230072969 + 3 ^ 40 * 1127575 * 2
def baseEnd_1127575 : Nat := 64331994332614565702987

theorem tailTrace_1127575 : CollatzResearch.WordTrace tailWord_1127575 prefixEnd_1127575 64331994332614565702987 := by
  unfold tailWord_1127575
  simp only [CollatzResearch.WordTrace]
  refine ⟨41126038889995824323472179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27417359259997216215648119 41126038889995824323472179)
  ·
    refine ⟨61689058334993736485208269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41126038889995824323472179 61689058334993736485208269)
    ·
      refine ⟨23133396875622651181953101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61689058334993736485208269 23133396875622651181953101)
      ·
        refine ⟨8675023828358494193232413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23133396875622651181953101 8675023828358494193232413)
        ·
          refine ⟨3253133935634435322462155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8675023828358494193232413 3253133935634435322462155)
          ·
            refine ⟨4879700903451652983693233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253133935634435322462155 4879700903451652983693233)
            ·
              refine ⟨3659775677588739737769925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879700903451652983693233 3659775677588739737769925)
              ·
                refine ⟨686207939547888700831861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3659775677588739737769925 686207939547888700831861)
                ·
                  refine ⟨64331994332614565702987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 686207939547888700831861 64331994332614565702987)
                  ·
                    rfl

theorem cell23_1127575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 5].length) (baseStart_1127575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127575 prefixEnd_1127575 := by exact prefixLift 1127575
  have htrace : WordTrace (prefixWord ++ tailWord_1127575) baseStart_1127575 baseEnd_1127575 := by
    simpa [prefixWord, tailWord_1127575, baseEnd_1127575] using wordTrace_append hprefix tailTrace_1127575
  have hstable : (prefixWord ++ tailWord_1127575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127575).length < 2 ^ (prefixWord ++ tailWord_1127575).sum := by decide
  have hdescent : baseEnd_1127575 < baseStart_1127575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127586 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1127586 : Nat := 118140960795 + 1127586 * 2 ^ 59
def prefixEnd_1127586 : Nat := 4983230072969 + 3 ^ 40 * 1127586 * 2
def baseEnd_1127586 : Nat := 578993597280730548289333

theorem tailTrace_1127586 : CollatzResearch.WordTrace tailWord_1127586 prefixEnd_1127586 578993597280730548289333 := by
  unfold tailWord_1127586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281610023238993300530653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27417626728637315468081741 10281610023238993300530653)
  ·
    refine ⟨3855603758714622487698995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10281610023238993300530653 3855603758714622487698995)
    ·
      refine ⟨5783405638071933731548493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855603758714622487698995 5783405638071933731548493)
      ·
        refine ⟨2168777114276975149330685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5783405638071933731548493 2168777114276975149330685)
        ·
          refine ⟨813291417853865680999007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2168777114276975149330685 813291417853865680999007)
          ·
            refine ⟨1219937126780798521498511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813291417853865680999007 1219937126780798521498511)
            ·
              refine ⟨1829905690171197782247767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219937126780798521498511 1829905690171197782247767)
              ·
                refine ⟨2744858535256796673371651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829905690171197782247767 2744858535256796673371651)
                ·
                  refine ⟨4117287802885195010057477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744858535256796673371651 4117287802885195010057477)
                  ·
                    refine ⟨771991463040974064385777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117287802885195010057477 771991463040974064385777)
                    ·
                      refine ⟨578993597280730548289333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 771991463040974064385777 578993597280730548289333)
                      ·
                        rfl

theorem cell23_1127586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1127586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127586 prefixEnd_1127586 := by exact prefixLift 1127586
  have htrace : WordTrace (prefixWord ++ tailWord_1127586) baseStart_1127586 baseEnd_1127586 := by
    simpa [prefixWord, tailWord_1127586, baseEnd_1127586] using wordTrace_append hprefix tailTrace_1127586
  have hstable : (prefixWord ++ tailWord_1127586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127586).length < 2 ^ (prefixWord ++ tailWord_1127586).sum := by decide
  have hdescent : baseEnd_1127586 < baseStart_1127586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127588 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_1127588 : Nat := 118140960795 + 1127588 * 2 ^ 59
def prefixEnd_1127588 : Nat := 4983230072969 + 3 ^ 40 * 1127588 * 2
def baseEnd_1127588 : Nat := 192998208080679846821441

theorem tailTrace_1127588 : CollatzResearch.WordTrace tailWord_1127588 prefixEnd_1127588 192998208080679846821441 := by
  unfold tailWord_1127588
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563256519474363771847709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27417675359299151695796945 20563256519474363771847709)
  ·
    refine ⟨7711221194802886414442891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20563256519474363771847709 7711221194802886414442891)
    ·
      refine ⟨11566831792204329621664337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711221194802886414442891 11566831792204329621664337)
      ·
        refine ⟨8675123844153247216248253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11566831792204329621664337 8675123844153247216248253)
        ·
          refine ⟨3253171441557467706093095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8675123844153247216248253 3253171441557467706093095)
          ·
            refine ⟨4879757162336201559139643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253171441557467706093095 4879757162336201559139643)
            ·
              refine ⟨7319635743504302338709465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879757162336201559139643 7319635743504302338709465)
              ·
                refine ⟨5489726807628226754032099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319635743504302338709465 5489726807628226754032099)
                ·
                  refine ⟨8234590211442340131048149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489726807628226754032099 8234590211442340131048149)
                  ·
                    refine ⟨192998208080679846821441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8234590211442340131048149 192998208080679846821441)
                    ·
                      rfl

theorem cell23_1127588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_1127588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127588 prefixEnd_1127588 := by exact prefixLift 1127588
  have htrace : WordTrace (prefixWord ++ tailWord_1127588) baseStart_1127588 baseEnd_1127588 := by
    simpa [prefixWord, tailWord_1127588, baseEnd_1127588] using wordTrace_append hprefix tailTrace_1127588
  have hstable : (prefixWord ++ tailWord_1127588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127588).length < 2 ^ (prefixWord ++ tailWord_1127588).sum := by decide
  have hdescent : baseEnd_1127588 < baseStart_1127588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127709 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1127709 : Nat := 118140960795 + 1127709 * 2 ^ 59
def prefixEnd_1127709 : Nat := 4983230072969 + 3 ^ 40 * 1127709 * 2
def baseEnd_1127709 : Nat := 579056755401233567051267

theorem tailTrace_1127709 : CollatzResearch.WordTrace tailWord_1127709 prefixEnd_1127709 579056755401233567051267 := by
  unfold tailWord_1127709
  simp only [CollatzResearch.WordTrace]
  refine ⟨41130926271510365208850181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27420617514340243472566787 41130926271510365208850181)
  ·
    refine ⟨7712048675908193476659409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41130926271510365208850181 7712048675908193476659409)
    ·
      refine ⟨5784036506931145107494557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7712048675908193476659409 5784036506931145107494557)
      ·
        refine ⟨2169013690099179415310459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5784036506931145107494557 2169013690099179415310459)
        ·
          refine ⟨3253520535148769122965689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169013690099179415310459 3253520535148769122965689)
          ·
            refine ⟨2440140401361576842224267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3253520535148769122965689 2440140401361576842224267)
            ·
              refine ⟨3660210602042365263336401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440140401361576842224267 3660210602042365263336401)
              ·
                refine ⟨2745157951531773947502301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660210602042365263336401 2745157951531773947502301)
                ·
                  refine ⟨1029434231824415230313363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2745157951531773947502301 1029434231824415230313363)
                  ·
                    refine ⟨1544151347736622845470045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1029434231824415230313363 1544151347736622845470045)
                    ·
                      refine ⟨579056755401233567051267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544151347736622845470045 579056755401233567051267)
                      ·
                        rfl

theorem cell23_1127709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1127709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127709 prefixEnd_1127709 := by exact prefixLift 1127709
  have htrace : WordTrace (prefixWord ++ tailWord_1127709) baseStart_1127709 baseEnd_1127709 := by
    simpa [prefixWord, tailWord_1127709, baseEnd_1127709] using wordTrace_append hprefix tailTrace_1127709
  have hstable : (prefixWord ++ tailWord_1127709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127709).length < 2 ^ (prefixWord ++ tailWord_1127709).sum := by decide
  have hdescent : baseEnd_1127709 < baseStart_1127709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127715 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1127715 : Nat := 118140960795 + 1127715 * 2 ^ 59
def prefixEnd_1127715 : Nat := 4983230072969 + 3 ^ 40 * 1127715 * 2
def baseEnd_1127715 : Nat := 579059836285160543576239

theorem tailTrace_1127715 : CollatzResearch.WordTrace tailWord_1127715 prefixEnd_1127715 579059836285160543576239 := by
  unfold tailWord_1127715
  simp only [CollatzResearch.WordTrace]
  refine ⟨41131145109488628233568599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27420763406325752155712399 41131145109488628233568599)
  ·
    refine ⟨61696717664232942350352899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41131145109488628233568599 61696717664232942350352899)
    ·
      refine ⟨92545076496349413525529349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61696717664232942350352899 92545076496349413525529349)
      ·
        refine ⟨17352201843065515036036753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92545076496349413525529349 17352201843065515036036753)
        ·
          refine ⟨13014151382299136277027565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17352201843065515036036753 13014151382299136277027565)
          ·
            refine ⟨4880306768362176103885337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13014151382299136277027565 4880306768362176103885337)
            ·
              refine ⟨3660230076271632077914003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880306768362176103885337 3660230076271632077914003)
              ·
                refine ⟨5490345114407448116871005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660230076271632077914003 5490345114407448116871005)
                ·
                  refine ⟨2058879417902793043826627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5490345114407448116871005 2058879417902793043826627)
                  ·
                    refine ⟨3088319126854189565739941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2058879417902793043826627 3088319126854189565739941)
                    ·
                      refine ⟨579059836285160543576239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3088319126854189565739941 579059836285160543576239)
                      ·
                        rfl

theorem cell23_1127715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1127715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127715 prefixEnd_1127715 := by exact prefixLift 1127715
  have htrace : WordTrace (prefixWord ++ tailWord_1127715) baseStart_1127715 baseEnd_1127715 := by
    simpa [prefixWord, tailWord_1127715, baseEnd_1127715] using wordTrace_append hprefix tailTrace_1127715
  have hstable : (prefixWord ++ tailWord_1127715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127715).length < 2 ^ (prefixWord ++ tailWord_1127715).sum := by decide
  have hdescent : baseEnd_1127715 < baseStart_1127715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127729 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 1, 5]
def baseStart_1127729 : Nat := 118140960795 + 1127729 * 2 ^ 59
def prefixEnd_1127729 : Nat := 4983230072969 + 3 ^ 40 * 1127729 * 2
def baseEnd_1127729 : Nat := 193022341671441162933725

theorem tailTrace_1127729 : CollatzResearch.WordTrace tailWord_1127729 prefixEnd_1127729 193022341671441162933725 := by
  unfold tailWord_1127729
  simp only [CollatzResearch.WordTrace]
  refine ⟨41131655731437908624578241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27421103820958605749718827 41131655731437908624578241)
  ·
    refine ⟨30848741798578431468433681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41131655731437908624578241 30848741798578431468433681)
    ·
      refine ⟨23136556348933823601325261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30848741798578431468433681 23136556348933823601325261)
      ·
        refine ⟨8676208630850183850496973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23136556348933823601325261 8676208630850183850496973)
        ·
          refine ⟨3253578236568818943936365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8676208630850183850496973 3253578236568818943936365)
          ·
            refine ⟨1220091838713307103976137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3253578236568818943936365 1220091838713307103976137)
            ·
              refine ⟨915068879034980327982103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220091838713307103976137 915068879034980327982103)
              ·
                refine ⟨1372603318552470491973155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915068879034980327982103 1372603318552470491973155)
                ·
                  refine ⟨2058904977828705737959733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372603318552470491973155 2058904977828705737959733)
                  ·
                    refine ⟨193022341671441162933725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2058904977828705737959733 193022341671441162933725)
                    ·
                      rfl

theorem cell23_1127729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_1127729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127729 prefixEnd_1127729 := by exact prefixLift 1127729
  have htrace : WordTrace (prefixWord ++ tailWord_1127729) baseStart_1127729 baseEnd_1127729 := by
    simpa [prefixWord, tailWord_1127729, baseEnd_1127729] using wordTrace_append hprefix tailTrace_1127729
  have hstable : (prefixWord ++ tailWord_1127729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127729).length < 2 ^ (prefixWord ++ tailWord_1127729).sum := by decide
  have hdescent : baseEnd_1127729 < baseStart_1127729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127738 : List Nat := [3, 1, 1, 1, 4, 1, 12]
def baseStart_1127738 : Nat := 118140960795 + 1127738 * 2 ^ 59
def prefixEnd_1127738 : Nat := 4983230072969 + 3 ^ 40 * 1127738 * 2
def baseEnd_1127738 : Nat := 7149032670866838933193

theorem tailTrace_1127738 : CollatzResearch.WordTrace tailWord_1127738 prefixEnd_1127738 7149032670866838933193 := by
  unfold tailWord_1127738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282995997101325790413967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27421322658936868774437245 10282995997101325790413967)
  ·
    refine ⟨15424493995651988685620951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10282995997101325790413967 15424493995651988685620951)
    ·
      refine ⟨23136740993477983028431427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15424493995651988685620951 23136740993477983028431427)
      ·
        refine ⟨34705111490216974542647141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23136740993477983028431427 34705111490216974542647141)
        ·
          refine ⟨6507208404415682726746339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34705111490216974542647141 6507208404415682726746339)
          ·
            refine ⟨9760812606623524090119509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6507208404415682726746339 9760812606623524090119509)
            ·
              refine ⟨7149032670866838933193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9760812606623524090119509 7149032670866838933193)
              ·
                rfl

theorem cell23_1127738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 12].length) (baseStart_1127738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127738 prefixEnd_1127738 := by exact prefixLift 1127738
  have htrace : WordTrace (prefixWord ++ tailWord_1127738) baseStart_1127738 baseEnd_1127738 := by
    simpa [prefixWord, tailWord_1127738, baseEnd_1127738] using wordTrace_append hprefix tailTrace_1127738
  have hstable : (prefixWord ++ tailWord_1127738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127738).length < 2 ^ (prefixWord ++ tailWord_1127738).sum := by decide
  have hdescent : baseEnd_1127738 < baseStart_1127738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127742 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1127742 : Nat := 118140960795 + 1127742 * 2 ^ 59
def prefixEnd_1127742 : Nat := 4983230072969 + 3 ^ 40 * 1127742 * 2
def baseEnd_1127742 : Nat := 193024566754277312646205

theorem tailTrace_1127742 : CollatzResearch.WordTrace tailWord_1127742 prefixEnd_1127742 193024566754277312646205 := by
  unfold tailWord_1127742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141516235048851480600185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27421419920260541229867653 5141516235048851480600185)
  ·
    refine ⟨3856137176286638610450139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5141516235048851480600185 3856137176286638610450139)
    ·
      refine ⟨5784205764429957915675209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856137176286638610450139 5784205764429957915675209)
      ·
        refine ⟨4338154323322468436756407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784205764429957915675209 4338154323322468436756407)
        ·
          refine ⟨6507231484983702655134611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338154323322468436756407 6507231484983702655134611)
          ·
            refine ⟨9760847227475553982701917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6507231484983702655134611 9760847227475553982701917)
            ·
              refine ⟨3660317710303332743513219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9760847227475553982701917 3660317710303332743513219)
              ·
                refine ⟨5490476565454999115269829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660317710303332743513219 5490476565454999115269829)
                ·
                  refine ⟨1029464356022812334113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5490476565454999115269829 1029464356022812334113093)
                  ·
                    refine ⟨193024566754277312646205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1029464356022812334113093 193024566754277312646205)
                    ·
                      rfl

theorem cell23_1127742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1127742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127742 prefixEnd_1127742 := by exact prefixLift 1127742
  have htrace : WordTrace (prefixWord ++ tailWord_1127742) baseStart_1127742 baseEnd_1127742 := by
    simpa [prefixWord, tailWord_1127742, baseEnd_1127742] using wordTrace_append hprefix tailTrace_1127742
  have hstable : (prefixWord ++ tailWord_1127742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127742).length < 2 ^ (prefixWord ++ tailWord_1127742).sum := by decide
  have hdescent : baseEnd_1127742 < baseStart_1127742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127805 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1127805 : Nat := 118140960795 + 1127805 * 2 ^ 59
def prefixEnd_1127805 : Nat := 4983230072969 + 3 ^ 40 * 1127805 * 2
def baseEnd_1127805 : Nat := 579106049544065191450825

theorem tailTrace_1127805 : CollatzResearch.WordTrace tailWord_1127805 prefixEnd_1127805 579106049544065191450825 := by
  unfold tailWord_1127805
  simp only [CollatzResearch.WordTrace]
  refine ⟨41134427679162573604344869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27422951786108382402896579 41134427679162573604344869)
  ·
    refine ⟨7712705189842982550814663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41134427679162573604344869 7712705189842982550814663)
    ·
      refine ⟨11569057784764473826221995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7712705189842982550814663 11569057784764473826221995)
      ·
        refine ⟨17353586677146710739332993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11569057784764473826221995 17353586677146710739332993)
        ·
          refine ⟨13015190007860033054499745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17353586677146710739332993 13015190007860033054499745)
          ·
            refine ⟨9761392505895024790874809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13015190007860033054499745 9761392505895024790874809)
            ·
              refine ⟨7321044379421268593156107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9761392505895024790874809 7321044379421268593156107)
              ·
                refine ⟨10981566569131902889734161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321044379421268593156107 10981566569131902889734161)
                ·
                  refine ⟨8236174926848927167300621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10981566569131902889734161 8236174926848927167300621)
                  ·
                    refine ⟨3088565597568347687737733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8236174926848927167300621 3088565597568347687737733)
                    ·
                      refine ⟨579106049544065191450825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3088565597568347687737733 579106049544065191450825)
                      ·
                        rfl

theorem cell23_1127805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1127805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127805 prefixEnd_1127805 := by exact prefixLift 1127805
  have htrace : WordTrace (prefixWord ++ tailWord_1127805) baseStart_1127805 baseEnd_1127805 := by
    simpa [prefixWord, tailWord_1127805, baseEnd_1127805] using wordTrace_append hprefix tailTrace_1127805
  have hstable : (prefixWord ++ tailWord_1127805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127805).length < 2 ^ (prefixWord ++ tailWord_1127805).sum := by decide
  have hdescent : baseEnd_1127805 < baseStart_1127805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127816 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_1127816 : Nat := 118140960795 + 1127816 * 2 ^ 59
def prefixEnd_1127816 : Nat := 4983230072969 + 3 ^ 40 * 1127816 * 2
def baseEnd_1127816 : Nat := 579111697831264648413275

theorem tailTrace_1127816 : CollatzResearch.WordTrace tailWord_1127816 prefixEnd_1127816 579111697831264648413275 := by
  unfold tailWord_1127816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20567414441061361241497651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27423219254748481655330201 20567414441061361241497651)
  ·
    refine ⟨30851121661592041862246477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20567414441061361241497651 30851121661592041862246477)
    ·
      refine ⟨11569170623097015698342429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30851121661592041862246477 11569170623097015698342429)
      ·
        refine ⟨4338438983661380886878411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11569170623097015698342429 4338438983661380886878411)
        ·
          refine ⟨6507658475492071330317617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338438983661380886878411 6507658475492071330317617)
          ·
            refine ⟨4880743856619053497738213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6507658475492071330317617 4880743856619053497738213)
            ·
              refine ⟨915139473116072530825915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4880743856619053497738213 915139473116072530825915)
              ·
                refine ⟨1372709209674108796238873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915139473116072530825915 1372709209674108796238873)
                ·
                  refine ⟨1029531907255581597179155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372709209674108796238873 1029531907255581597179155)
                  ·
                    refine ⟨1544297860883372395768733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1029531907255581597179155 1544297860883372395768733)
                    ·
                      refine ⟨579111697831264648413275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544297860883372395768733 579111697831264648413275)
                      ·
                        rfl

theorem cell23_1127816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_1127816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127816 prefixEnd_1127816 := by exact prefixLift 1127816
  have htrace : WordTrace (prefixWord ++ tailWord_1127816) baseStart_1127816 baseEnd_1127816 := by
    simpa [prefixWord, tailWord_1127816, baseEnd_1127816] using wordTrace_append hprefix tailTrace_1127816
  have hstable : (prefixWord ++ tailWord_1127816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127816).length < 2 ^ (prefixWord ++ tailWord_1127816).sum := by decide
  have hdescent : baseEnd_1127816 < baseStart_1127816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127825 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_1127825 : Nat := 118140960795 + 1127825 * 2 ^ 59
def prefixEnd_1127825 : Nat := 4983230072969 + 3 ^ 40 * 1127825 * 2
def baseEnd_1127825 : Nat := 579116319157155113200733

theorem tailTrace_1127825 : CollatzResearch.WordTrace tailWord_1127825 prefixEnd_1127825 579116319157155113200733 := by
  unfold tailWord_1127825
  simp only [CollatzResearch.WordTrace]
  refine ⟨41135157139090117020072929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27423438092726744680048619 41135157139090117020072929)
  ·
    refine ⟨30851367854317587765054697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41135157139090117020072929 30851367854317587765054697)
    ·
      refine ⟨23138525890738190823791023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30851367854317587765054697 23138525890738190823791023)
      ·
        refine ⟨34707788836107286235686535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23138525890738190823791023 34707788836107286235686535)
        ·
          refine ⟨52061683254160929353529803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34707788836107286235686535 52061683254160929353529803)
          ·
            refine ⟨78092524881241394030294705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52061683254160929353529803 78092524881241394030294705)
            ·
              refine ⟨58569393660931045522721029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78092524881241394030294705 58569393660931045522721029)
              ·
                refine ⟨10981761311424571035510193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58569393660931045522721029 10981761311424571035510193)
                ·
                  refine ⟨8236320983568428276632645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10981761311424571035510193 8236320983568428276632645)
                  ·
                    refine ⟨1544310184419080301868621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8236320983568428276632645 1544310184419080301868621)
                    ·
                      refine ⟨579116319157155113200733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544310184419080301868621 579116319157155113200733)
                      ·
                        rfl

theorem cell23_1127825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_1127825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127825 prefixEnd_1127825 := by exact prefixLift 1127825
  have htrace : WordTrace (prefixWord ++ tailWord_1127825) baseStart_1127825 baseEnd_1127825 := by
    simpa [prefixWord, tailWord_1127825, baseEnd_1127825] using wordTrace_append hprefix tailTrace_1127825
  have hstable : (prefixWord ++ tailWord_1127825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127825).length < 2 ^ (prefixWord ++ tailWord_1127825).sum := by decide
  have hdescent : baseEnd_1127825 < baseStart_1127825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127839 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1127839 : Nat := 118140960795 + 1127839 * 2 ^ 59
def prefixEnd_1127839 : Nat := 4983230072969 + 3 ^ 40 * 1127839 * 2
def baseEnd_1127839 : Nat := 579123507886318058425669

theorem tailTrace_1127839 : CollatzResearch.WordTrace tailWord_1127839 prefixEnd_1127839 579123507886318058425669 := by
  unfold tailWord_1127839
  simp only [CollatzResearch.WordTrace]
  refine ⟨41135667761039397411082571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27423778507359598274055047 41135667761039397411082571)
  ·
    refine ⟨61703501641559096116623857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41135667761039397411082571 61703501641559096116623857)
    ·
      refine ⟨46277626231169322087467893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61703501641559096116623857 46277626231169322087467893)
      ·
        refine ⟨4338527459172123945700115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46277626231169322087467893 4338527459172123945700115)
        ·
          refine ⟨6507791188758185918550173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338527459172123945700115 6507791188758185918550173)
          ·
            refine ⟨2440421695784319719456315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6507791188758185918550173 2440421695784319719456315)
            ·
              refine ⟨3660632543676479579184473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440421695784319719456315 3660632543676479579184473)
              ·
                refine ⟨2745474407757359684388355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660632543676479579184473 2745474407757359684388355)
                ·
                  refine ⟨4118211611636039526582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745474407757359684388355 4118211611636039526582533)
                  ·
                    refine ⟨772164677181757411234225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118211611636039526582533 772164677181757411234225)
                    ·
                      refine ⟨579123507886318058425669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772164677181757411234225 579123507886318058425669)
                      ·
                        rfl

theorem cell23_1127839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1127839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127839 prefixEnd_1127839 := by exact prefixLift 1127839
  have htrace : WordTrace (prefixWord ++ tailWord_1127839) baseStart_1127839 baseEnd_1127839 := by
    simpa [prefixWord, tailWord_1127839, baseEnd_1127839] using wordTrace_append hprefix tailTrace_1127839
  have hstable : (prefixWord ++ tailWord_1127839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127839).length < 2 ^ (prefixWord ++ tailWord_1127839).sum := by decide
  have hdescent : baseEnd_1127839 < baseStart_1127839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127842 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1127842 : Nat := 118140960795 + 1127842 * 2 ^ 59
def prefixEnd_1127842 : Nat := 4983230072969 + 3 ^ 40 * 1127842 * 2
def baseEnd_1127842 : Nat := 579125048328281546688155

theorem tailTrace_1127842 : CollatzResearch.WordTrace tailWord_1127842 prefixEnd_1127842 579125048328281546688155 := by
  unfold tailWord_1127842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283944295007132230860445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27423851453352352615627853 10283944295007132230860445)
  ·
    refine ⟨3856479110627674586572667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10283944295007132230860445 3856479110627674586572667)
    ·
      refine ⟨5784718665941511879859001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856479110627674586572667 5784718665941511879859001)
      ·
        refine ⟨4338538999456133909894251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784718665941511879859001 4338538999456133909894251)
        ·
          refine ⟨6507808499184200864841377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338538999456133909894251 6507808499184200864841377)
          ·
            refine ⟨4880856374388150648631033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6507808499184200864841377 4880856374388150648631033)
            ·
              refine ⟨3660642280791112986473275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880856374388150648631033 3660642280791112986473275)
              ·
                refine ⟨5490963421186669479709913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660642280791112986473275 5490963421186669479709913)
                ·
                  refine ⟨4118222565890002109782435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5490963421186669479709913 4118222565890002109782435)
                  ·
                    refine ⟨6177333848835003164673653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118222565890002109782435 6177333848835003164673653)
                    ·
                      refine ⟨579125048328281546688155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6177333848835003164673653 579125048328281546688155)
                      ·
                        rfl

theorem cell23_1127842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1127842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127842 prefixEnd_1127842 := by exact prefixLift 1127842
  have htrace : WordTrace (prefixWord ++ tailWord_1127842) baseStart_1127842 baseEnd_1127842 := by
    simpa [prefixWord, tailWord_1127842, baseEnd_1127842] using wordTrace_append hprefix tailTrace_1127842
  have hstable : (prefixWord ++ tailWord_1127842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127842).length < 2 ^ (prefixWord ++ tailWord_1127842).sum := by decide
  have hdescent : baseEnd_1127842 < baseStart_1127842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127855 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_1127855 : Nat := 118140960795 + 1127855 * 2 ^ 59
def prefixEnd_1127855 : Nat := 4983230072969 + 3 ^ 40 * 1127855 * 2
def baseEnd_1127855 : Nat := 579131723576789995825595

theorem tailTrace_1127855 : CollatzResearch.WordTrace tailWord_1127855 prefixEnd_1127855 579131723576789995825595 := by
  unfold tailWord_1127855
  simp only [CollatzResearch.WordTrace]
  refine ⟨41136251328981432143665019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27424167552654288095776679 41136251328981432143665019)
  ·
    refine ⟨61704376993472148215497529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41136251328981432143665019 61704376993472148215497529)
    ·
      refine ⟨46278282745104111161623147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61704376993472148215497529 46278282745104111161623147)
      ·
        refine ⟨69417424117656166742434721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46278282745104111161623147 69417424117656166742434721)
        ·
          refine ⟨52063068088242125056826041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69417424117656166742434721 52063068088242125056826041)
          ·
            refine ⟨39047301066181593792619531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52063068088242125056826041 39047301066181593792619531)
            ·
              refine ⟨58570951599272390688929297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39047301066181593792619531 58570951599272390688929297)
              ·
                refine ⟨43928213699454293016696973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58570951599272390688929297 43928213699454293016696973)
                ·
                  refine ⟨16473080137295359881261365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43928213699454293016696973 16473080137295359881261365)
                  ·
                    refine ⟨1544351262871439988868253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16473080137295359881261365 1544351262871439988868253)
                    ·
                      refine ⟨579131723576789995825595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544351262871439988868253 579131723576789995825595)
                      ·
                        rfl

theorem cell23_1127855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_1127855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127855 prefixEnd_1127855 := by exact prefixLift 1127855
  have htrace : WordTrace (prefixWord ++ tailWord_1127855) baseStart_1127855 baseEnd_1127855 := by
    simpa [prefixWord, tailWord_1127855, baseEnd_1127855] using wordTrace_append hprefix tailTrace_1127855
  have hstable : (prefixWord ++ tailWord_1127855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127855).length < 2 ^ (prefixWord ++ tailWord_1127855).sum := by decide
  have hdescent : baseEnd_1127855 < baseStart_1127855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127875 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 4, 5]
def baseStart_1127875 : Nat := 118140960795 + 1127875 * 2 ^ 59
def prefixEnd_1127875 : Nat := 4983230072969 + 3 ^ 40 * 1127875 * 2
def baseEnd_1127875 : Nat := 193047331063293305858501

theorem tailTrace_1127875 : CollatzResearch.WordTrace tailWord_1127875 prefixEnd_1127875 193047331063293305858501 := by
  unfold tailWord_1127875
  simp only [CollatzResearch.WordTrace]
  refine ⟨41136980788908975559393079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27424653859272650372928719 41136980788908975559393079)
  ·
    refine ⟨61705471183363463339089619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41136980788908975559393079 61705471183363463339089619)
    ·
      refine ⟨92558206775045195008634429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61705471183363463339089619 92558206775045195008634429)
      ·
        refine ⟨34709327540641948128237911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92558206775045195008634429 34709327540641948128237911)
        ·
          refine ⟨52063991310962922192356867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34709327540641948128237911 52063991310962922192356867)
          ·
            refine ⟨78095986966444383288535301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52063991310962922192356867 78095986966444383288535301)
            ·
              refine ⟨14642997556208321866600369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78095986966444383288535301 14642997556208321866600369)
              ·
                refine ⟨10982248167156241399950277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14642997556208321866600369 10982248167156241399950277)
                ·
                  refine ⟨2059171531341795262490677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10982248167156241399950277 2059171531341795262490677)
                  ·
                    refine ⟨193047331063293305858501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2059171531341795262490677 193047331063293305858501)
                    ·
                      rfl

theorem cell23_1127875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 5].length) (baseStart_1127875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127875 prefixEnd_1127875 := by exact prefixLift 1127875
  have htrace : WordTrace (prefixWord ++ tailWord_1127875) baseStart_1127875 baseEnd_1127875 := by
    simpa [prefixWord, tailWord_1127875, baseEnd_1127875] using wordTrace_append hprefix tailTrace_1127875
  have hstable : (prefixWord ++ tailWord_1127875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127875).length < 2 ^ (prefixWord ++ tailWord_1127875).sum := by decide
  have hdescent : baseEnd_1127875 < baseStart_1127875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127912 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1127912 : Nat := 118140960795 + 1127912 * 2 ^ 59
def prefixEnd_1127912 : Nat := 4983230072969 + 3 ^ 40 * 1127912 * 2
def baseEnd_1127912 : Nat := 579160991974096272812833

theorem tailTrace_1127912 : CollatzResearch.WordTrace tailWord_1127912 prefixEnd_1127912 579160991974096272812833 := by
  unfold tailWord_1127912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20569165144887465439244995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27425553526516620585659993 20569165144887465439244995)
  ·
    refine ⟨30853747717331198158867493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20569165144887465439244995 30853747717331198158867493)
    ·
      refine ⟨5785077696999599654787655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30853747717331198158867493 5785077696999599654787655)
      ·
        refine ⟨8677616545499399482181483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785077696999599654787655 8677616545499399482181483)
        ·
          refine ⟨13016424818249099223272225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8677616545499399482181483 13016424818249099223272225)
          ·
            refine ⟨9762318613686824417454169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13016424818249099223272225 9762318613686824417454169)
            ·
              refine ⟨7321738960265118313090627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9762318613686824417454169 7321738960265118313090627)
              ·
                refine ⟨10982608440397677469635941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321738960265118313090627 10982608440397677469635941)
                ·
                  refine ⟨2059239082574564525556739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10982608440397677469635941 2059239082574564525556739)
                  ·
                    refine ⟨3088858623861846788335109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059239082574564525556739 3088858623861846788335109)
                    ·
                      refine ⟨579160991974096272812833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3088858623861846788335109 579160991974096272812833)
                      ·
                        rfl

theorem cell23_1127912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1127912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127912 prefixEnd_1127912 := by exact prefixLift 1127912
  have htrace : WordTrace (prefixWord ++ tailWord_1127912) baseStart_1127912 baseEnd_1127912 := by
    simpa [prefixWord, tailWord_1127912, baseEnd_1127912] using wordTrace_append hprefix tailTrace_1127912
  have hstable : (prefixWord ++ tailWord_1127912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127912).length < 2 ^ (prefixWord ++ tailWord_1127912).sum := by decide
  have hdescent : baseEnd_1127912 < baseStart_1127912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127932 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_1127932 : Nat := 118140960795 + 1127932 * 2 ^ 59
def prefixEnd_1127932 : Nat := 4983230072969 + 3 ^ 40 * 1127932 * 2
def baseEnd_1127932 : Nat := 579171261587186194562741

theorem tailTrace_1127932 : CollatzResearch.WordTrace tailWord_1127932 prefixEnd_1127932 579171261587186194562741 := by
  unfold tailWord_1127932
  simp only [CollatzResearch.WordTrace]
  refine ⟨20569529874851237147109025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27426039833134982862812033 20569529874851237147109025)
  ·
    refine ⟨15427147406138427860331769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20569529874851237147109025 15427147406138427860331769)
    ·
      refine ⟨11570360554603820895248827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15427147406138427860331769 11570360554603820895248827)
      ·
        refine ⟨17355540831905731342873241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11570360554603820895248827 17355540831905731342873241)
        ·
          refine ⟨13016655623929298507154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17355540831905731342873241 13016655623929298507154931)
          ·
            refine ⟨19524983435893947760732397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13016655623929298507154931 19524983435893947760732397)
            ·
              refine ⟨7321868788460230410274649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19524983435893947760732397 7321868788460230410274649)
              ·
                refine ⟨5491401591345172807705987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7321868788460230410274649 5491401591345172807705987)
                ·
                  refine ⟨8237102387017759211558981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491401591345172807705987 8237102387017759211558981)
                  ·
                    refine ⟨1544456697565829852167309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8237102387017759211558981 1544456697565829852167309)
                    ·
                      refine ⟨579171261587186194562741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544456697565829852167309 579171261587186194562741)
                      ·
                        rfl

theorem cell23_1127932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_1127932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127932 prefixEnd_1127932 := by exact prefixLift 1127932
  have htrace : WordTrace (prefixWord ++ tailWord_1127932) baseStart_1127932 baseEnd_1127932 := by
    simpa [prefixWord, tailWord_1127932, baseEnd_1127932] using wordTrace_append hprefix tailTrace_1127932
  have hstable : (prefixWord ++ tailWord_1127932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127932).length < 2 ^ (prefixWord ++ tailWord_1127932).sum := by decide
  have hdescent : baseEnd_1127932 < baseStart_1127932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127995 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 12]
def baseStart_1127995 : Nat := 118140960795 + 1127995 * 2 ^ 59
def prefixEnd_1127995 : Nat := 4983230072969 + 3 ^ 40 * 1127995 * 2
def baseEnd_1127995 : Nat := 193067870289473149358317

theorem tailTrace_1127995 : CollatzResearch.WordTrace tailWord_1127995 prefixEnd_1127995 193067870289473149358317 := by
  unfold tailWord_1127995
  simp only [CollatzResearch.WordTrace]
  refine ⟨41141357548474236053761439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27427571698982824035840959 41141357548474236053761439)
  ·
    refine ⟨61712036322711354080642159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41141357548474236053761439 61712036322711354080642159)
    ·
      refine ⟨92568054484067031120963239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61712036322711354080642159 92568054484067031120963239)
      ·
        refine ⟨138852081726100546681444859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92568054484067031120963239 138852081726100546681444859)
        ·
          refine ⟨208278122589150820022167289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138852081726100546681444859 208278122589150820022167289)
          ·
            refine ⟨156208591941863115016625467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208278122589150820022167289 156208591941863115016625467)
            ·
              refine ⟨234312887912794672524938201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156208591941863115016625467 234312887912794672524938201)
              ·
                refine ⟨175734665934596004393703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234312887912794672524938201 175734665934596004393703651)
                ·
                  refine ⟨263601998901894006590555477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175734665934596004393703651 263601998901894006590555477)
                  ·
                    refine ⟨193067870289473149358317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 263601998901894006590555477 193067870289473149358317)
                    ·
                      rfl

theorem cell23_1127995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_1127995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127995 prefixEnd_1127995 := by exact prefixLift 1127995
  have htrace : WordTrace (prefixWord ++ tailWord_1127995) baseStart_1127995 baseEnd_1127995 := by
    simpa [prefixWord, tailWord_1127995, baseEnd_1127995] using wordTrace_append hprefix tailTrace_1127995
  have hstable : (prefixWord ++ tailWord_1127995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127995).length < 2 ^ (prefixWord ++ tailWord_1127995).sum := by decide
  have hdescent : baseEnd_1127995 < baseStart_1127995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127999 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 1, 5]
def baseStart_1127999 : Nat := 118140960795 + 1127999 * 2 ^ 59
def prefixEnd_1127999 : Nat := 4983230072969 + 3 ^ 40 * 1127999 * 2
def baseEnd_1127999 : Nat := 193068554930345810808311

theorem tailTrace_1127999 : CollatzResearch.WordTrace tailWord_1127999 prefixEnd_1127999 193068554930345810808311 := by
  unfold tailWord_1127999
  simp only [CollatzResearch.WordTrace]
  refine ⟨41141503440459744736907051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27427668960306496491271367 41141503440459744736907051)
  ·
    refine ⟨61712255160689617105360577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41141503440459744736907051 61712255160689617105360577)
    ·
      refine ⟨46284191370517212829020433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61712255160689617105360577 46284191370517212829020433)
      ·
        refine ⟨34713143527887909621765325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46284191370517212829020433 34713143527887909621765325)
        ·
          refine ⟨13017428822957966108161997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34713143527887909621765325 13017428822957966108161997)
          ·
            refine ⟨4881535808609237290560749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13017428822957966108161997 4881535808609237290560749)
            ·
              refine ⟨1830575928228463983960281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4881535808609237290560749 1830575928228463983960281)
              ·
                refine ⟨1372931946171347987970211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830575928228463983960281 1372931946171347987970211)
                ·
                  refine ⟨2059397919257021981955317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372931946171347987970211 2059397919257021981955317)
                  ·
                    refine ⟨193068554930345810808311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2059397919257021981955317 193068554930345810808311)
                    ·
                      rfl

theorem cell23_1127999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_1127999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1127999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1127999 prefixEnd_1127999 := by exact prefixLift 1127999
  have htrace : WordTrace (prefixWord ++ tailWord_1127999) baseStart_1127999 baseEnd_1127999 := by
    simpa [prefixWord, tailWord_1127999, baseEnd_1127999] using wordTrace_append hprefix tailTrace_1127999
  have hstable : (prefixWord ++ tailWord_1127999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127999).length < 2 ^ (prefixWord ++ tailWord_1127999).sum := by decide
  have hdescent : baseEnd_1127999 < baseStart_1127999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128012 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_1128012 : Nat := 118140960795 + 1128012 * 2 ^ 59
def prefixEnd_1128012 : Nat := 4983230072969 + 3 ^ 40 * 1128012 * 2
def baseEnd_1128012 : Nat := 193070780013181960520791

theorem tailTrace_1128012 : CollatzResearch.WordTrace tailWord_1128012 prefixEnd_1128012 193070780013181960520791 := by
  unfold tailWord_1128012
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570988794706323978565145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27427985059608431971420193 20570988794706323978565145)
  ·
    refine ⟨15428241596029742983923859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20570988794706323978565145 15428241596029742983923859)
    ·
      refine ⟨23142362394044614475885789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15428241596029742983923859 23142362394044614475885789)
      ·
        refine ⟨8678385897766730428457171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23142362394044614475885789 8678385897766730428457171)
        ·
          refine ⟨13017578846650095642685757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8678385897766730428457171 13017578846650095642685757)
          ·
            refine ⟨4881592067493785866007159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13017578846650095642685757 4881592067493785866007159)
            ·
              refine ⟨7322388101240678799010739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881592067493785866007159 7322388101240678799010739)
              ·
                refine ⟨10983582151861018198516109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322388101240678799010739 10983582151861018198516109)
                ·
                  refine ⟨4118843306947881824443541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10983582151861018198516109 4118843306947881824443541)
                  ·
                    refine ⟨193070780013181960520791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4118843306947881824443541 193070780013181960520791)
                    ·
                      rfl

theorem cell23_1128012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_1128012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128012 prefixEnd_1128012 := by exact prefixLift 1128012
  have htrace : WordTrace (prefixWord ++ tailWord_1128012) baseStart_1128012 baseEnd_1128012 := by
    simpa [prefixWord, tailWord_1128012, baseEnd_1128012] using wordTrace_append hprefix tailTrace_1128012
  have hstable : (prefixWord ++ tailWord_1128012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128012).length < 2 ^ (prefixWord ++ tailWord_1128012).sum := by decide
  have hdescent : baseEnd_1128012 < baseStart_1128012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128032 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1128032 : Nat := 118140960795 + 1128032 * 2 ^ 59
def prefixEnd_1128032 : Nat := 4983230072969 + 3 ^ 40 * 1128032 * 2
def baseEnd_1128032 : Nat := 579222609652635803312281

theorem tailTrace_1128032 : CollatzResearch.WordTrace tailWord_1128032 prefixEnd_1128032 579222609652635803312281 := by
  unfold tailWord_1128032
  simp only [CollatzResearch.WordTrace]
  refine ⟨20571353524670095686429175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27428471366226794248572233 20571353524670095686429175)
  ·
    refine ⟨30857030287005143529643763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20571353524670095686429175 30857030287005143529643763)
    ·
      refine ⟨46285545430507715294465645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30857030287005143529643763 46285545430507715294465645)
      ·
        refine ⟨17357079536440393235424617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46285545430507715294465645 17357079536440393235424617)
        ·
          refine ⟨13017809652330294926568463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17357079536440393235424617 13017809652330294926568463)
          ·
            refine ⟨19526714478495442389852695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017809652330294926568463 19526714478495442389852695)
            ·
              refine ⟨29290071717743163584779043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19526714478495442389852695 29290071717743163584779043)
              ·
                refine ⟨43935107576614745377168565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29290071717743163584779043 43935107576614745377168565)
                ·
                  refine ⟨4118916335307632379109553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43935107576614745377168565 4118916335307632379109553)
                  ·
                    refine ⟨3089187251480724284332165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118916335307632379109553 3089187251480724284332165)
                    ·
                      refine ⟨579222609652635803312281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3089187251480724284332165 579222609652635803312281)
                      ·
                        rfl

theorem cell23_1128032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1128032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128032 prefixEnd_1128032 := by exact prefixLift 1128032
  have htrace : WordTrace (prefixWord ++ tailWord_1128032) baseStart_1128032 baseEnd_1128032 := by
    simpa [prefixWord, tailWord_1128032, baseEnd_1128032] using wordTrace_append hprefix tailTrace_1128032
  have hstable : (prefixWord ++ tailWord_1128032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128032).length < 2 ^ (prefixWord ++ tailWord_1128032).sum := by decide
  have hdescent : baseEnd_1128032 < baseStart_1128032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128039 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1128039 : Nat := 118140960795 + 1128039 * 2 ^ 59
def prefixEnd_1128039 : Nat := 4983230072969 + 3 ^ 40 * 1128039 * 2
def baseEnd_1128039 : Nat := 579226204017217275924749

theorem tailTrace_1128039 : CollatzResearch.WordTrace tailWord_1128039 prefixEnd_1128039 579226204017217275924749 := by
  unfold tailWord_1128039
  simp only [CollatzResearch.WordTrace]
  refine ⟨41142962360314831568363171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27428641573543221045575447 41142962360314831568363171)
  ·
    refine ⟨61714443540472247352544757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41142962360314831568363171 61714443540472247352544757)
    ·
      refine ⟨5785729081919273189301071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61714443540472247352544757 5785729081919273189301071)
      ·
        refine ⟨8678593622878909783951607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785729081919273189301071 8678593622878909783951607)
        ·
          refine ⟨13017890434318364675927411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8678593622878909783951607 13017890434318364675927411)
          ·
            refine ⟨19526835651477547013891117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017890434318364675927411 19526835651477547013891117)
            ·
              refine ⟨7322563369304080130209169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19526835651477547013891117 7322563369304080130209169)
              ·
                refine ⟨5491922526978060097656877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322563369304080130209169 5491922526978060097656877)
                ·
                  refine ⟨2059470947616772536621329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5491922526978060097656877 2059470947616772536621329)
                  ·
                    refine ⟨1544603210712579402465997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2059470947616772536621329 1544603210712579402465997)
                    ·
                      refine ⟨579226204017217275924749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544603210712579402465997 579226204017217275924749)
                      ·
                        rfl

theorem cell23_1128039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1128039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128039 prefixEnd_1128039 := by exact prefixLift 1128039
  have htrace : WordTrace (prefixWord ++ tailWord_1128039) baseStart_1128039 baseEnd_1128039 := by
    simpa [prefixWord, tailWord_1128039, baseEnd_1128039] using wordTrace_append hprefix tailTrace_1128039
  have hstable : (prefixWord ++ tailWord_1128039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128039).length < 2 ^ (prefixWord ++ tailWord_1128039).sum := by decide
  have hdescent : baseEnd_1128039 < baseStart_1128039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128046 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1128046 : Nat := 118140960795 + 1128046 * 2 ^ 59
def prefixEnd_1128046 : Nat := 4983230072969 + 3 ^ 40 * 1128046 * 2
def baseEnd_1128046 : Nat := 193076599460599582845739

theorem tailTrace_1128046 : CollatzResearch.WordTrace tailWord_1128046 prefixEnd_1128046 193076599460599582845739 := by
  unfold tailWord_1128046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142902208911183970483499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27428811780859647842578661 5142902208911183970483499)
  ·
    refine ⟨7714353313366775955725249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5142902208911183970483499 7714353313366775955725249)
    ·
      refine ⟨5785764985025081966793937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7714353313366775955725249 5785764985025081966793937)
      ·
        refine ⟨4339323738768811475095453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5785764985025081966793937 4339323738768811475095453)
        ·
          refine ⟨1627246402038304303160795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4339323738768811475095453 1627246402038304303160795)
          ·
            refine ⟨2440869603057456454741193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627246402038304303160795 2440869603057456454741193)
            ·
              refine ⟨1830652202293092341055895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2440869603057456454741193 1830652202293092341055895)
              ·
                refine ⟨2745978303439638511583843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830652202293092341055895 2745978303439638511583843)
                ·
                  refine ⟨4118967455159457767375765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745978303439638511583843 4118967455159457767375765)
                  ·
                    refine ⟨193076599460599582845739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4118967455159457767375765 193076599460599582845739)
                    ·
                      rfl

theorem cell23_1128046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1128046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128046 prefixEnd_1128046 := by exact prefixLift 1128046
  have htrace : WordTrace (prefixWord ++ tailWord_1128046) baseStart_1128046 baseEnd_1128046 := by
    simpa [prefixWord, tailWord_1128046, baseEnd_1128046] using wordTrace_append hprefix tailTrace_1128046
  have hstable : (prefixWord ++ tailWord_1128046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128046).length < 2 ^ (prefixWord ++ tailWord_1128046).sum := by decide
  have hdescent : baseEnd_1128046 < baseStart_1128046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128053 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1128053 : Nat := 118140960795 + 1128053 * 2 ^ 59
def prefixEnd_1128053 : Nat := 4983230072969 + 3 ^ 40 * 1128053 * 2
def baseEnd_1128053 : Nat := 579233392746380221149685

theorem tailTrace_1128053 : CollatzResearch.WordTrace tailWord_1128053 prefixEnd_1128053 579233392746380221149685 := by
  unfold tailWord_1128053
  simp only [CollatzResearch.WordTrace]
  refine ⟨41143472982264111959372813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27428981988176074639581875 41143472982264111959372813)
  ·
    refine ⟨15428802368349041984764805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41143472982264111959372813 15428802368349041984764805)
    ·
      refine ⟨2892900444065445372143401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15428802368349041984764805 2892900444065445372143401)
      ·
        refine ⟨2169675333049084029107551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2892900444065445372143401 2169675333049084029107551)
        ·
          refine ⟨3254512999573626043661327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169675333049084029107551 3254512999573626043661327)
          ·
            refine ⟨4881769499360439065491991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254512999573626043661327 4881769499360439065491991)
            ·
              refine ⟨7322654249040658598237987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881769499360439065491991 7322654249040658598237987)
              ·
                refine ⟨10983981373560987897356981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322654249040658598237987 10983981373560987897356981)
                ·
                  refine ⟨1029748253771342615377217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10983981373560987897356981 1029748253771342615377217)
                  ·
                    refine ⟨772311190328506961532913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1029748253771342615377217 772311190328506961532913)
                    ·
                      refine ⟨579233392746380221149685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772311190328506961532913 579233392746380221149685)
                      ·
                        rfl

theorem cell23_1128053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1128053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128053 prefixEnd_1128053 := by exact prefixLift 1128053
  have htrace : WordTrace (prefixWord ++ tailWord_1128053) baseStart_1128053 baseEnd_1128053 := by
    simpa [prefixWord, tailWord_1128053, baseEnd_1128053] using wordTrace_append hprefix tailTrace_1128053
  have hstable : (prefixWord ++ tailWord_1128053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128053).length < 2 ^ (prefixWord ++ tailWord_1128053).sum := by decide
  have hdescent : baseEnd_1128053 < baseStart_1128053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128069 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_1128069 : Nat := 118140960795 + 1128069 * 2 ^ 59
def prefixEnd_1128069 : Nat := 4983230072969 + 3 ^ 40 * 1128069 * 2
def baseEnd_1128069 : Nat := 579241608436852158549611

theorem tailTrace_1128069 : CollatzResearch.WordTrace tailWord_1128069 prefixEnd_1128069 579241608436852158549611 := by
  unfold tailWord_1128069
  simp only [CollatzResearch.WordTrace]
  refine ⟨41144056550206146691955261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27429371033470764461303507 41144056550206146691955261)
  ·
    refine ⟨15429021206327305009483223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41144056550206146691955261 15429021206327305009483223)
    ·
      refine ⟨23143531809490957514224835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15429021206327305009483223 23143531809490957514224835)
      ·
        refine ⟨34715297714236436271337253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23143531809490957514224835 34715297714236436271337253)
        ·
          refine ⟨6509118321419331800875735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34715297714236436271337253 6509118321419331800875735)
          ·
            refine ⟨9763677482128997701313603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509118321419331800875735 9763677482128997701313603)
            ·
              refine ⟨14645516223193496551970405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9763677482128997701313603 14645516223193496551970405)
              ·
                refine ⟨2746034291848780603494451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14645516223193496551970405 2746034291848780603494451)
                ·
                  refine ⟨4119051437773170905241677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746034291848780603494451 4119051437773170905241677)
                  ·
                    refine ⟨1544644289164939089465629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4119051437773170905241677 1544644289164939089465629)
                    ·
                      refine ⟨579241608436852158549611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544644289164939089465629 579241608436852158549611)
                      ·
                        rfl

theorem cell23_1128069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_1128069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128069 prefixEnd_1128069 := by exact prefixLift 1128069
  have htrace : WordTrace (prefixWord ++ tailWord_1128069) baseStart_1128069 baseEnd_1128069 := by
    simpa [prefixWord, tailWord_1128069, baseEnd_1128069] using wordTrace_append hprefix tailTrace_1128069
  have hstable : (prefixWord ++ tailWord_1128069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128069).length < 2 ^ (prefixWord ++ tailWord_1128069).sum := by decide
  have hdescent : baseEnd_1128069 < baseStart_1128069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128110 : List Nat := [4, 1, 4, 1, 3, 1, 2, 7]
def baseStart_1128110 : Nat := 118140960795 + 1128110 * 2 ^ 59
def prefixEnd_1128110 : Nat := 4983230072969 + 3 ^ 40 * 1128110 * 2
def baseEnd_1128110 : Nat := 21454172634951351782849

theorem tailTrace_1128110 : CollatzResearch.WordTrace tailWord_1128110 prefixEnd_1128110 21454172634951351782849 := by
  unfold tailWord_1128110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143193992882201336774723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27430367962038407129465189 5143193992882201336774723)
  ·
    refine ⟨7714790989323302005162085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5143193992882201336774723 7714790989323302005162085)
    ·
      refine ⟨1446523310498119125967891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7714790989323302005162085 1446523310498119125967891)
      ·
        refine ⟨2169784965747178688951837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446523310498119125967891 2169784965747178688951837)
        ·
          refine ⟨813669362155192008356939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2169784965747178688951837 813669362155192008356939)
          ·
            refine ⟨1220504043232788012535409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813669362155192008356939 1220504043232788012535409)
            ·
              refine ⟨915378032424591009401557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220504043232788012535409 915378032424591009401557)
              ·
                refine ⟨21454172634951351782849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 915378032424591009401557 21454172634951351782849)
                ·
                  rfl

theorem cell23_1128110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_1128110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128110 prefixEnd_1128110 := by exact prefixLift 1128110
  have htrace : WordTrace (prefixWord ++ tailWord_1128110) baseStart_1128110 baseEnd_1128110 := by
    simpa [prefixWord, tailWord_1128110, baseEnd_1128110] using wordTrace_append hprefix tailTrace_1128110
  have hstable : (prefixWord ++ tailWord_1128110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128110).length < 2 ^ (prefixWord ++ tailWord_1128110).sum := by decide
  have hdescent : baseEnd_1128110 < baseStart_1128110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128159 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1128159 : Nat := 118140960795 + 1128159 * 2 ^ 59
def prefixEnd_1128159 : Nat := 4983230072969 + 3 ^ 40 * 1128159 * 2
def baseEnd_1128159 : Nat := 579287821695756806424197

theorem tailTrace_1128159 : CollatzResearch.WordTrace tailWord_1128159 prefixEnd_1128159 579287821695756806424197 := by
  unfold tailWord_1128159
  simp only [CollatzResearch.WordTrace]
  refine ⟨41147339119880092062731531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27431559413253394708487687 41147339119880092062731531)
  ·
    refine ⟨61721008679820138094097297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41147339119880092062731531 61721008679820138094097297)
    ·
      refine ⟨46290756509865103570572973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61721008679820138094097297 46290756509865103570572973)
      ·
        refine ⟨17359033691199413838964865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46290756509865103570572973 17359033691199413838964865)
        ·
          refine ⟨13019275268399560379223649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17359033691199413838964865 13019275268399560379223649)
          ·
            refine ⟨9764456451299670284417737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13019275268399560379223649 9764456451299670284417737)
            ·
              refine ⟨7323342338474752713313303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764456451299670284417737 7323342338474752713313303)
              ·
                refine ⟨10985013507712129069969955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323342338474752713313303 10985013507712129069969955)
                ·
                  refine ⟨16477520261568193604954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985013507712129069969955 16477520261568193604954933)
                  ·
                    refine ⟨1544767524522018150464525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16477520261568193604954933 1544767524522018150464525)
                    ·
                      refine ⟨579287821695756806424197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544767524522018150464525 579287821695756806424197)
                      ·
                        rfl

theorem cell23_1128159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1128159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128159 prefixEnd_1128159 := by exact prefixLift 1128159
  have htrace : WordTrace (prefixWord ++ tailWord_1128159) baseStart_1128159 baseEnd_1128159 := by
    simpa [prefixWord, tailWord_1128159, baseEnd_1128159] using wordTrace_append hprefix tailTrace_1128159
  have hstable : (prefixWord ++ tailWord_1128159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128159).length < 2 ^ (prefixWord ++ tailWord_1128159).sum := by decide
  have hdescent : baseEnd_1128159 < baseStart_1128159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128160 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2]
def baseStart_1128160 : Nat := 118140960795 + 1128160 * 2 ^ 59
def prefixEnd_1128160 : Nat := 4983230072969 + 3 ^ 40 * 1128160 * 2
def baseEnd_1128160 : Nat := 579288335176411302511693

theorem tailTrace_1128160 : CollatzResearch.WordTrace tailWord_1128160 prefixEnd_1128160 579288335176411302511693 := by
  unfold tailWord_1128160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20573687796438234616758967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27431583728584312822345289 20573687796438234616758967)
  ·
    refine ⟨30860531694657351925138451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20573687796438234616758967 30860531694657351925138451)
    ·
      refine ⟨46290797541986027887707677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30860531694657351925138451 46290797541986027887707677)
      ·
        refine ⟨17359049078244760457890379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46290797541986027887707677 17359049078244760457890379)
        ·
          refine ⟨26038573617367140686835569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17359049078244760457890379 26038573617367140686835569)
          ·
            refine ⟨19528930213025355515126677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26038573617367140686835569 19528930213025355515126677)
            ·
              refine ⟨915418603735563539771563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19528930213025355515126677 915418603735563539771563)
              ·
                refine ⟨1373127905603345309657345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915418603735563539771563 1373127905603345309657345)
                ·
                  refine ⟨1029845929202508982243009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1373127905603345309657345 1029845929202508982243009)
                  ·
                    refine ⟨772384446901881736682257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1029845929202508982243009 772384446901881736682257)
                    ·
                      refine ⟨579288335176411302511693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772384446901881736682257 579288335176411302511693)
                      ·
                        rfl

theorem cell23_1128160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_1128160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128160 prefixEnd_1128160 := by exact prefixLift 1128160
  have htrace : WordTrace (prefixWord ++ tailWord_1128160) baseStart_1128160 baseEnd_1128160 := by
    simpa [prefixWord, tailWord_1128160, baseEnd_1128160] using wordTrace_append hprefix tailTrace_1128160
  have hstable : (prefixWord ++ tailWord_1128160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128160).length < 2 ^ (prefixWord ++ tailWord_1128160).sum := by decide
  have hdescent : baseEnd_1128160 < baseStart_1128160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128179 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 2, 5]
def baseStart_1128179 : Nat := 118140960795 + 1128179 * 2 ^ 59
def prefixEnd_1128179 : Nat := 4983230072969 + 3 ^ 40 * 1128179 * 2
def baseEnd_1128179 : Nat := 193099363769615576058035

theorem tailTrace_1128179 : CollatzResearch.WordTrace tailWord_1128179 prefixEnd_1128179 193099363769615576058035 := by
  unfold tailWord_1128179
  simp only [CollatzResearch.WordTrace]
  refine ⟨41148068579807635478459591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27432045719871756985639727 41148068579807635478459591)
  ·
    refine ⟨61722102869711453217689387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41148068579807635478459591 61722102869711453217689387)
    ·
      refine ⟨92583154304567179826534081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61722102869711453217689387 92583154304567179826534081)
      ·
        refine ⟨69437365728425384869900561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92583154304567179826534081 69437365728425384869900561)
        ·
          refine ⟨52078024296319038652425421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69437365728425384869900561 52078024296319038652425421)
          ·
            refine ⟨19529259111119639494659533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52078024296319038652425421 19529259111119639494659533)
            ·
              refine ⟨7323472166669864810497325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19529259111119639494659533 7323472166669864810497325)
              ·
                refine ⟨2746302062501199303936497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7323472166669864810497325 2746302062501199303936497)
                ·
                  refine ⟨2059726546875899477952373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746302062501199303936497 2059726546875899477952373)
                  ·
                    refine ⟨193099363769615576058035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2059726546875899477952373 193099363769615576058035)
                    ·
                      rfl

theorem cell23_1128179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 5].length) (baseStart_1128179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128179 prefixEnd_1128179 := by exact prefixLift 1128179
  have htrace : WordTrace (prefixWord ++ tailWord_1128179) baseStart_1128179 baseEnd_1128179 := by
    simpa [prefixWord, tailWord_1128179, baseEnd_1128179] using wordTrace_append hprefix tailTrace_1128179
  have hstable : (prefixWord ++ tailWord_1128179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128179).length < 2 ^ (prefixWord ++ tailWord_1128179).sum := by decide
  have hdescent : baseEnd_1128179 < baseStart_1128179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128196 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1128196 : Nat := 118140960795 + 1128196 * 2 ^ 59
def prefixEnd_1128196 : Nat := 4983230072969 + 3 ^ 40 * 1128196 * 2
def baseEnd_1128196 : Nat := 193102273493324387220509

theorem tailTrace_1128196 : CollatzResearch.WordTrace tailWord_1128196 prefixEnd_1128196 193102273493324387220509 := by
  unfold tailWord_1128196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20574344310373023690914221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27432459080497364921218961 20574344310373023690914221)
  ·
    refine ⟨7715379116389883884092833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20574344310373023690914221 7715379116389883884092833)
    ·
      refine ⟨5786534337292412913069625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7715379116389883884092833 5786534337292412913069625)
      ·
        refine ⟨4339900752969309684802219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5786534337292412913069625 4339900752969309684802219)
        ·
          refine ⟨6509851129453964527203329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339900752969309684802219 6509851129453964527203329)
          ·
            refine ⟨4882388347090473395402497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509851129453964527203329 4882388347090473395402497)
            ·
              refine ⟨3661791260317855046551873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4882388347090473395402497 3661791260317855046551873)
              ·
                refine ⟨2746343445238391284913905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661791260317855046551873 2746343445238391284913905)
                ·
                  refine ⟨2059757583928793463685429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746343445238391284913905 2059757583928793463685429)
                  ·
                    refine ⟨193102273493324387220509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2059757583928793463685429 193102273493324387220509)
                    ·
                      rfl

theorem cell23_1128196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1128196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128196 prefixEnd_1128196 := by exact prefixLift 1128196
  have htrace : WordTrace (prefixWord ++ tailWord_1128196) baseStart_1128196 baseEnd_1128196 := by
    simpa [prefixWord, tailWord_1128196, baseEnd_1128196] using wordTrace_append hprefix tailTrace_1128196
  have hstable : (prefixWord ++ tailWord_1128196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128196).length < 2 ^ (prefixWord ++ tailWord_1128196).sum := by decide
  have hdescent : baseEnd_1128196 < baseStart_1128196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128216 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1128216 : Nat := 118140960795 + 1128216 * 2 ^ 59
def prefixEnd_1128216 : Nat := 4983230072969 + 3 ^ 40 * 1128216 * 2
def baseEnd_1128216 : Nat := 579317090093063083411435

theorem tailTrace_1128216 : CollatzResearch.WordTrace tailWord_1128216 prefixEnd_1128216 579317090093063083411435 := by
  unfold tailWord_1128216
  simp only [CollatzResearch.WordTrace]
  refine ⟨20574709040336795398778251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27432945387115727198371001 20574709040336795398778251)
  ·
    refine ⟨30862063560505193098167377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20574709040336795398778251 30862063560505193098167377)
    ·
      refine ⟨23146547670378894823625533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30862063560505193098167377 23146547670378894823625533)
      ·
        refine ⟨8679955376392085558859575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23146547670378894823625533 8679955376392085558859575)
        ·
          refine ⟨13019933064588128338289363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8679955376392085558859575 13019933064588128338289363)
          ·
            refine ⟨19529899596882192507434045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13019933064588128338289363 19529899596882192507434045)
            ·
              refine ⟨7323712348830822190287767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19529899596882192507434045 7323712348830822190287767)
              ·
                refine ⟨10985568523246233285431651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323712348830822190287767 10985568523246233285431651)
                ·
                  refine ⟨16478352784869349928147477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985568523246233285431651 16478352784869349928147477)
                  ·
                    refine ⟨772422786790750777881913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16478352784869349928147477 772422786790750777881913)
                    ·
                      refine ⟨579317090093063083411435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772422786790750777881913 579317090093063083411435)
                      ·
                        rfl

theorem cell23_1128216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1128216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128216 prefixEnd_1128216 := by exact prefixLift 1128216
  have htrace : WordTrace (prefixWord ++ tailWord_1128216) baseStart_1128216 baseEnd_1128216 := by
    simpa [prefixWord, tailWord_1128216, baseEnd_1128216] using wordTrace_append hprefix tailTrace_1128216
  have hstable : (prefixWord ++ tailWord_1128216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128216).length < 2 ^ (prefixWord ++ tailWord_1128216).sum := by decide
  have hdescent : baseEnd_1128216 < baseStart_1128216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3]
def baseStart_1128219 : Nat := 118140960795 + 1128219 * 2 ^ 59
def prefixEnd_1128219 : Nat := 4983230072969 + 3 ^ 40 * 1128219 * 2
def baseEnd_1128219 : Nat := 579318630535026571673921

theorem tailTrace_1128219 : CollatzResearch.WordTrace tailWord_1128219 prefixEnd_1128219 579318630535026571673921 := by
  unfold tailWord_1128219
  simp only [CollatzResearch.WordTrace]
  refine ⟨41149527499662722309915711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27433018333108481539943807 41149527499662722309915711)
  ·
    refine ⟨61724291249494083464873567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41149527499662722309915711 61724291249494083464873567)
    ·
      refine ⟨92586436874241125197310351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61724291249494083464873567 92586436874241125197310351)
      ·
        refine ⟨138879655311361687795965527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92586436874241125197310351 138879655311361687795965527)
        ·
          refine ⟨208319482967042531693948291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138879655311361687795965527 208319482967042531693948291)
          ·
            refine ⟨312479224450563797540922437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208319482967042531693948291 312479224450563797540922437)
            ·
              refine ⟨58589854584480712038922957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312479224450563797540922437 58589854584480712038922957)
              ·
                refine ⟨21971195469180267014596109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58589854584480712038922957 21971195469180267014596109)
                ·
                  refine ⟨8239198300942600130473541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21971195469180267014596109 8239198300942600130473541)
                  ·
                    refine ⟨1544849681426737524463789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8239198300942600130473541 1544849681426737524463789)
                    ·
                      refine ⟨579318630535026571673921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544849681426737524463789 579318630535026571673921)
                      ·
                        rfl

theorem cell23_1128219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 3].length) (baseStart_1128219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128219 prefixEnd_1128219 := by exact prefixLift 1128219
  have htrace : WordTrace (prefixWord ++ tailWord_1128219) baseStart_1128219 baseEnd_1128219 := by
    simpa [prefixWord, tailWord_1128219, baseEnd_1128219] using wordTrace_append hprefix tailTrace_1128219
  have hstable : (prefixWord ++ tailWord_1128219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128219).length < 2 ^ (prefixWord ++ tailWord_1128219).sum := by decide
  have hdescent : baseEnd_1128219 < baseStart_1128219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128236 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_1128236 : Nat := 118140960795 + 1128236 * 2 ^ 59
def prefixEnd_1128236 : Nat := 4983230072969 + 3 ^ 40 * 1128236 * 2
def baseEnd_1128236 : Nat := 579327359706153005161343

theorem tailTrace_1128236 : CollatzResearch.WordTrace tailWord_1128236 prefixEnd_1128236 579327359706153005161343 := by
  unfold tailWord_1128236
  simp only [CollatzResearch.WordTrace]
  refine ⟨20575073770300567106642281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27433431693734089475523041 20575073770300567106642281)
  ·
    refine ⟨15431305327725425329981711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20575073770300567106642281 15431305327725425329981711)
    ·
      refine ⟨23146957991588137994972567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15431305327725425329981711 23146957991588137994972567)
      ·
        refine ⟨34720436987382206992458851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23146957991588137994972567 34720436987382206992458851)
        ·
          refine ⟨52080655481073310488688277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34720436987382206992458851 52080655481073310488688277)
          ·
            refine ⟨2441280725675311429157263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52080655481073310488688277 2441280725675311429157263)
            ·
              refine ⟨3661921088512967143735895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441280725675311429157263 3661921088512967143735895)
              ·
                refine ⟨5492881632769450715603843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3661921088512967143735895 5492881632769450715603843)
                ·
                  refine ⟨8239322449154176073405765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5492881632769450715603843 8239322449154176073405765)
                  ·
                    refine ⟨1544872959216408013763581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8239322449154176073405765 1544872959216408013763581)
                    ·
                      refine ⟨579327359706153005161343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1544872959216408013763581 579327359706153005161343)
                      ·
                        rfl

theorem cell23_1128236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_1128236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128236 prefixEnd_1128236 := by exact prefixLift 1128236
  have htrace : WordTrace (prefixWord ++ tailWord_1128236) baseStart_1128236 baseEnd_1128236 := by
    simpa [prefixWord, tailWord_1128236, baseEnd_1128236] using wordTrace_append hprefix tailTrace_1128236
  have hstable : (prefixWord ++ tailWord_1128236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128236).length < 2 ^ (prefixWord ++ tailWord_1128236).sum := by decide
  have hdescent : baseEnd_1128236 < baseStart_1128236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128259 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1128259 : Nat := 118140960795 + 1128259 * 2 ^ 59
def prefixEnd_1128259 : Nat := 4983230072969 + 3 ^ 40 * 1128259 * 2
def baseEnd_1128259 : Nat := 579339169761206415173737

theorem tailTrace_1128259 : CollatzResearch.WordTrace tailWord_1128259 prefixEnd_1128259 579339169761206415173737 := by
  unfold tailWord_1128259
  simp only [CollatzResearch.WordTrace]
  refine ⟨41150986419517809141371831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27433990946345206094247887 41150986419517809141371831)
  ·
    refine ⟨61726479629276713712057747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41150986419517809141371831 61726479629276713712057747)
    ·
      refine ⟨92589719443915070568086621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61726479629276713712057747 92589719443915070568086621)
      ·
        refine ⟨34721144791468151463032483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92589719443915070568086621 34721144791468151463032483)
        ·
          refine ⟨52081717187202227194548725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34721144791468151463032483 52081717187202227194548725)
          ·
            refine ⟨4882660986300208799488943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52081717187202227194548725 4882660986300208799488943)
            ·
              refine ⟨7323991479450313199233415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882660986300208799488943 7323991479450313199233415)
              ·
                refine ⟨10985987219175469798850123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323991479450313199233415 10985987219175469798850123)
                ·
                  refine ⟨16478980828763204698275185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10985987219175469798850123 16478980828763204698275185)
                  ·
                    refine ⟨12359235621572403523706389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16478980828763204698275185 12359235621572403523706389)
                    ·
                      refine ⟨579339169761206415173737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12359235621572403523706389 579339169761206415173737)
                      ·
                        rfl

theorem cell23_1128259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1128259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128259 prefixEnd_1128259 := by exact prefixLift 1128259
  have htrace : WordTrace (prefixWord ++ tailWord_1128259) baseStart_1128259 baseEnd_1128259 := by
    simpa [prefixWord, tailWord_1128259, baseEnd_1128259] using wordTrace_append hprefix tailTrace_1128259
  have hstable : (prefixWord ++ tailWord_1128259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128259).length < 2 ^ (prefixWord ++ tailWord_1128259).sum := by decide
  have hdescent : baseEnd_1128259 < baseStart_1128259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128273 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 6]
def baseStart_1128273 : Nat := 118140960795 + 1128273 * 2 ^ 59
def prefixEnd_1128273 : Nat := 4983230072969 + 3 ^ 40 * 1128273 * 2
def baseEnd_1128273 : Nat := 64371817610041040044297

theorem tailTrace_1128273 : CollatzResearch.WordTrace tailWord_1128273 prefixEnd_1128273 64371817610041040044297 := by
  unfold tailWord_1128273
  simp only [CollatzResearch.WordTrace]
  refine ⟨41151497041467089532381473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27434331360978059688254315 41151497041467089532381473)
  ·
    refine ⟨30863622781100317149286105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41151497041467089532381473 30863622781100317149286105)
    ·
      refine ⟨23147717085825237861964579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30863622781100317149286105 23147717085825237861964579)
      ·
        refine ⟨34721575628737856792946869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23147717085825237861964579 34721575628737856792946869)
        ·
          refine ⟨3255147715194174074338769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34721575628737856792946869 3255147715194174074338769)
          ·
            refine ⟨2441360786395630555754077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255147715194174074338769 2441360786395630555754077)
            ·
              refine ⟨915510294898361458407779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2441360786395630555754077 915510294898361458407779)
              ·
                refine ⟨1373265442347542187611669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915510294898361458407779 1373265442347542187611669)
                ·
                  refine ⟨64371817610041040044297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1373265442347542187611669 64371817610041040044297)
                  ·
                    rfl

theorem cell23_1128273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 6].length) (baseStart_1128273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128273 prefixEnd_1128273 := by exact prefixLift 1128273
  have htrace : WordTrace (prefixWord ++ tailWord_1128273) baseStart_1128273 baseEnd_1128273 := by
    simpa [prefixWord, tailWord_1128273, baseEnd_1128273] using wordTrace_append hprefix tailTrace_1128273
  have hstable : (prefixWord ++ tailWord_1128273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128273).length < 2 ^ (prefixWord ++ tailWord_1128273).sum := by decide
  have hdescent : baseEnd_1128273 < baseStart_1128273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128293 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_1128293 : Nat := 118140960795 + 1128293 * 2 ^ 59
def prefixEnd_1128293 : Nat := 4983230072969 + 3 ^ 40 * 1128293 * 2
def baseEnd_1128293 : Nat := 579356628103459282148581

theorem tailTrace_1128293 : CollatzResearch.WordTrace tailWord_1128293 prefixEnd_1128293 579356628103459282148581 := by
  unfold tailWord_1128293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41152226501394632948109533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27434817667596421965406355 41152226501394632948109533)
  ·
    refine ⟨15432084938022987355541075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41152226501394632948109533 15432084938022987355541075)
    ·
      refine ⟨23148127407034481033311613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15432084938022987355541075 23148127407034481033311613)
      ·
        refine ⟨8680547777637930387491855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23148127407034481033311613 8680547777637930387491855)
        ·
          refine ⟨13020821666456895581237783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8680547777637930387491855 13020821666456895581237783)
          ·
            refine ⟨19531232499685343371856675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13020821666456895581237783 19531232499685343371856675)
            ·
              refine ⟨29296848749528015057785013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19531232499685343371856675 29296848749528015057785013)
              ·
                refine ⟨2746579570268251411667345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29296848749528015057785013 2746579570268251411667345)
                ·
                  refine ⟨2059934677701188558750509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746579570268251411667345 2059934677701188558750509)
                  ·
                    refine ⟨772475504137945709531441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059934677701188558750509 772475504137945709531441)
                    ·
                      refine ⟨579356628103459282148581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772475504137945709531441 579356628103459282148581)
                      ·
                        rfl

theorem cell23_1128293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_1128293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128293 prefixEnd_1128293 := by exact prefixLift 1128293
  have htrace : WordTrace (prefixWord ++ tailWord_1128293) baseStart_1128293 baseEnd_1128293 := by
    simpa [prefixWord, tailWord_1128293, baseEnd_1128293] using wordTrace_append hprefix tailTrace_1128293
  have hstable : (prefixWord ++ tailWord_1128293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128293).length < 2 ^ (prefixWord ++ tailWord_1128293).sum := by decide
  have hdescent : baseEnd_1128293 < baseStart_1128293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128299 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 6]
def baseStart_1128299 : Nat := 118140960795 + 1128299 * 2 ^ 59
def prefixEnd_1128299 : Nat := 4983230072969 + 3 ^ 40 * 1128299 * 2
def baseEnd_1128299 : Nat := 193119902995795419557851

theorem tailTrace_1128299 : CollatzResearch.WordTrace tailWord_1128299 prefixEnd_1128299 193119902995795419557851 := by
  unfold tailWord_1128299
  simp only [CollatzResearch.WordTrace]
  refine ⟨41152445339372895972827951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27434963559581930648551967 41152445339372895972827951)
  ·
    refine ⟨61728668009059343959241927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41152445339372895972827951 61728668009059343959241927)
    ·
      refine ⟨92593002013589015938862891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61728668009059343959241927 92593002013589015938862891)
      ·
        refine ⟨138889503020383523908294337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92593002013589015938862891 138889503020383523908294337)
        ·
          refine ⟨104167127265287642931220753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138889503020383523908294337 104167127265287642931220753)
          ·
            refine ⟨78125345448965732198415565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104167127265287642931220753 78125345448965732198415565)
            ·
              refine ⟨29297004543362149574405837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78125345448965732198415565 29297004543362149574405837)
              ·
                refine ⟨10986376703760806090402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29297004543362149574405837 10986376703760806090402189)
                ·
                  refine ⟨4119891263910302283900821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10986376703760806090402189 4119891263910302283900821)
                  ·
                    refine ⟨193119902995795419557851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4119891263910302283900821 193119902995795419557851)
                    ·
                      rfl

theorem cell23_1128299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_1128299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128299 prefixEnd_1128299 := by exact prefixLift 1128299
  have htrace : WordTrace (prefixWord ++ tailWord_1128299) baseStart_1128299 baseEnd_1128299 := by
    simpa [prefixWord, tailWord_1128299, baseEnd_1128299] using wordTrace_append hprefix tailTrace_1128299
  have hstable : (prefixWord ++ tailWord_1128299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128299).length < 2 ^ (prefixWord ++ tailWord_1128299).sum := by decide
  have hdescent : baseEnd_1128299 < baseStart_1128299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128306 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1128306 : Nat := 118140960795 + 1128306 * 2 ^ 59
def prefixEnd_1128306 : Nat := 4983230072969 + 3 ^ 40 * 1128306 * 2
def baseEnd_1128306 : Nat := 579363303351967731286021

theorem tailTrace_1128306 : CollatzResearch.WordTrace tailWord_1128306 prefixEnd_1128306 579363303351967731286021 := by
  unfold tailWord_1128306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10288175162586884042083193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27435133766898357445555181 10288175162586884042083193)
  ·
    refine ⟨7716131371940163031562395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10288175162586884042083193 7716131371940163031562395)
    ·
      refine ⟨11574197057910244547343593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7716131371940163031562395 11574197057910244547343593)
      ·
        refine ⟨8680647793432683410507695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11574197057910244547343593 8680647793432683410507695)
        ·
          refine ⟨13020971690149025115761543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8680647793432683410507695 13020971690149025115761543)
          ·
            refine ⟨19531457535223537673642315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13020971690149025115761543 19531457535223537673642315)
            ·
              refine ⟨29297186302835306510463473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19531457535223537673642315 29297186302835306510463473)
              ·
                refine ⟨21972889727126479882847605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29297186302835306510463473 21972889727126479882847605)
                ·
                  refine ⟨2059958411918107489016963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21972889727126479882847605 2059958411918107489016963)
                  ·
                    refine ⟨3089937617877161233525445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2059958411918107489016963 3089937617877161233525445)
                    ·
                      refine ⟨579363303351967731286021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3089937617877161233525445 579363303351967731286021)
                      ·
                        rfl

theorem cell23_1128306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1128306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128306 prefixEnd_1128306 := by exact prefixLift 1128306
  have htrace : WordTrace (prefixWord ++ tailWord_1128306) baseStart_1128306 baseEnd_1128306 := by
    simpa [prefixWord, tailWord_1128306, baseEnd_1128306] using wordTrace_append hprefix tailTrace_1128306
  have hstable : (prefixWord ++ tailWord_1128306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128306).length < 2 ^ (prefixWord ++ tailWord_1128306).sum := by decide
  have hdescent : baseEnd_1128306 < baseStart_1128306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128340 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1128340 : Nat := 118140960795 + 1128340 * 2 ^ 59
def prefixEnd_1128340 : Nat := 4983230072969 + 3 ^ 40 * 1128340 * 2
def baseEnd_1128340 : Nat := 579380761694220598260865

theorem tailTrace_1128340 : CollatzResearch.WordTrace tailWord_1128340 prefixEnd_1128340 579380761694220598260865 := by
  unfold tailWord_1128340
  simp only [CollatzResearch.WordTrace]
  refine ⟨20576970366112179987535237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27435960488149573316713649 20576970366112179987535237)
  ·
    refine ⟨3858181943646033747662857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20576970366112179987535237 3858181943646033747662857)
    ·
      refine ⟨2893636457734525310747143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3858181943646033747662857 2893636457734525310747143)
      ·
        refine ⟨4340454686601787966120715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893636457734525310747143 4340454686601787966120715)
        ·
          refine ⟨6510682029902681949181073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4340454686601787966120715 6510682029902681949181073)
          ·
            refine ⟨4883011522427011461885805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6510682029902681949181073 4883011522427011461885805)
            ·
              refine ⟨1831129320910129298207177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4883011522427011461885805 1831129320910129298207177)
              ·
                refine ⟨1373346990682596973655383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1831129320910129298207177 1373346990682596973655383)
                ·
                  refine ⟨2060020486023895460483075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373346990682596973655383 2060020486023895460483075)
                  ·
                    refine ⟨3090030729035843190724613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2060020486023895460483075 3090030729035843190724613)
                    ·
                      refine ⟨579380761694220598260865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3090030729035843190724613 579380761694220598260865)
                      ·
                        rfl

theorem cell23_1128340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1128340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128340 prefixEnd_1128340 := by exact prefixLift 1128340
  have htrace : WordTrace (prefixWord ++ tailWord_1128340) baseStart_1128340 baseEnd_1128340 := by
    simpa [prefixWord, tailWord_1128340, baseEnd_1128340] using wordTrace_append hprefix tailTrace_1128340
  have hstable : (prefixWord ++ tailWord_1128340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128340).length < 2 ^ (prefixWord ++ tailWord_1128340).sum := by decide
  have hdescent : baseEnd_1128340 < baseStart_1128340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128343 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1128343 : Nat := 118140960795 + 1128343 * 2 ^ 59
def prefixEnd_1128343 : Nat := 4983230072969 + 3 ^ 40 * 1128343 * 2
def baseEnd_1128343 : Nat := 579382302136184086523351

theorem tailTrace_1128343 : CollatzResearch.WordTrace tailWord_1128343 prefixEnd_1128343 579382302136184086523351 := by
  unfold tailWord_1128343
  simp only [CollatzResearch.WordTrace]
  refine ⟨41154050151213491487429683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27436033434142327658286455 41154050151213491487429683)
  ·
    refine ⟨61731075226820237231144525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41154050151213491487429683 61731075226820237231144525)
    ·
      refine ⟨23149153210057588961679197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61731075226820237231144525 23149153210057588961679197)
      ·
        refine ⟨8680932453771595860629699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23149153210057588961679197 8680932453771595860629699)
        ·
          refine ⟨13021398680657393790944549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8680932453771595860629699 13021398680657393790944549)
          ·
            refine ⟨2441512252623261335802103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13021398680657393790944549 2441512252623261335802103)
            ·
              refine ⟨3662268378934892003703155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441512252623261335802103 3662268378934892003703155)
              ·
                refine ⟨5493402568402338005554733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662268378934892003703155 5493402568402338005554733)
                ·
                  refine ⟨2060025963150876752083025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5493402568402338005554733 2060025963150876752083025)
                  ·
                    refine ⟨1545019472363157564062269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060025963150876752083025 1545019472363157564062269)
                    ·
                      refine ⟨579382302136184086523351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1545019472363157564062269 579382302136184086523351)
                      ·
                        rfl

theorem cell23_1128343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1128343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128343 prefixEnd_1128343 := by exact prefixLift 1128343
  have htrace : WordTrace (prefixWord ++ tailWord_1128343) baseStart_1128343 baseEnd_1128343 := by
    simpa [prefixWord, tailWord_1128343, baseEnd_1128343] using wordTrace_append hprefix tailTrace_1128343
  have hstable : (prefixWord ++ tailWord_1128343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128343).length < 2 ^ (prefixWord ++ tailWord_1128343).sum := by decide
  have hdescent : baseEnd_1128343 < baseStart_1128343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128346 : List Nat := [3, 1, 1, 4, 2, 1, 2, 9]
def baseStart_1128346 : Nat := 118140960795 + 1128346 * 2 ^ 59
def prefixEnd_1128346 : Nat := 4983230072969 + 3 ^ 40 * 1128346 * 2
def baseEnd_1128346 : Nat := 21458660836227687955031

theorem tailTrace_1128346 : CollatzResearch.WordTrace tailWord_1128346 prefixEnd_1128346 21458660836227687955031 := by
  unfold tailWord_1128346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10288539892550655749947223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27436106380135081999859261 10288539892550655749947223)
  ·
    refine ⟨15432809838825983624920835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10288539892550655749947223 15432809838825983624920835)
    ·
      refine ⟨23149214758238975437381253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15432809838825983624920835 23149214758238975437381253)
      ·
        refine ⟨4340477767169807894508985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23149214758238975437381253 4340477767169807894508985)
        ·
          refine ⟨3255358325377355920881739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4340477767169807894508985 3255358325377355920881739)
          ·
            refine ⟨4883037488066033881322609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3255358325377355920881739 4883037488066033881322609)
            ·
              refine ⟨3662278116049525410991957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4883037488066033881322609 3662278116049525410991957)
              ·
                refine ⟨21458660836227687955031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3662278116049525410991957 21458660836227687955031)
                ·
                  rfl

theorem cell23_1128346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_1128346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128346 prefixEnd_1128346 := by exact prefixLift 1128346
  have htrace : WordTrace (prefixWord ++ tailWord_1128346) baseStart_1128346 baseEnd_1128346 := by
    simpa [prefixWord, tailWord_1128346, baseEnd_1128346] using wordTrace_append hprefix tailTrace_1128346
  have hstable : (prefixWord ++ tailWord_1128346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128346).length < 2 ^ (prefixWord ++ tailWord_1128346).sum := by decide
  have hdescent : baseEnd_1128346 < baseStart_1128346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128380 : List Nat := [2, 2, 2, 5, 1, 2, 1, 8]
def baseStart_1128380 : Nat := 118140960795 + 1128380 * 2 ^ 59
def prefixEnd_1128380 : Nat := 4983230072969 + 3 ^ 40 * 1128380 * 2
def baseEnd_1128380 : Nat := 21459307441496312657803

theorem tailTrace_1128380 : CollatzResearch.WordTrace tailWord_1128380 prefixEnd_1128380 21459307441496312657803 := by
  unfold tailWord_1128380
  simp only [CollatzResearch.WordTrace]
  refine ⟨20577699826039723403263297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27436933101386297871017729 20577699826039723403263297)
  ·
    refine ⟨15433274869529792552447473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20577699826039723403263297 15433274869529792552447473)
    ·
      refine ⟨11574956152147344414335605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15433274869529792552447473 11574956152147344414335605)
      ·
        refine ⟨1085152139263813538843963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11574956152147344414335605 1085152139263813538843963)
        ·
          refine ⟨1627728208895720308265945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085152139263813538843963 1627728208895720308265945)
          ·
            refine ⟨1220796156671790231199459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627728208895720308265945 1220796156671790231199459)
            ·
              refine ⟨1831194235007685346799189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220796156671790231199459 1831194235007685346799189)
              ·
                refine ⟨21459307441496312657803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1831194235007685346799189 21459307441496312657803)
                ·
                  rfl

theorem cell23_1128380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 8].length) (baseStart_1128380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128380 prefixEnd_1128380 := by exact prefixLift 1128380
  have htrace : WordTrace (prefixWord ++ tailWord_1128380) baseStart_1128380 baseEnd_1128380 := by
    simpa [prefixWord, tailWord_1128380, baseEnd_1128380] using wordTrace_append hprefix tailTrace_1128380
  have hstable : (prefixWord ++ tailWord_1128380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128380).length < 2 ^ (prefixWord ++ tailWord_1128380).sum := by decide
  have hdescent : baseEnd_1128380 < baseStart_1128380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128383 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 5, 3, 2]
def baseStart_1128383 : Nat := 118140960795 + 1128383 * 2 ^ 59
def prefixEnd_1128383 : Nat := 4983230072969 + 3 ^ 40 * 1128383 * 2
def baseEnd_1128383 : Nat := 579402841362363930023167

theorem tailTrace_1128383 : CollatzResearch.WordTrace tailWord_1128383 prefixEnd_1128383 579402841362363930023167 := by
  unfold tailWord_1128383
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155509071068578318885803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27437006047379052212590535 41155509071068578318885803)
  ·
    refine ⟨61733263606602867478328705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41155509071068578318885803 61733263606602867478328705)
    ·
      refine ⟨46299947704952150608746529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61733263606602867478328705 46299947704952150608746529)
      ·
        refine ⟨34724960778714112956559897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46299947704952150608746529 34724960778714112956559897)
        ·
          refine ⟨26043720584035584717419923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34724960778714112956559897 26043720584035584717419923)
          ·
            refine ⟨39065580876053377076129885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26043720584035584717419923 39065580876053377076129885)
            ·
              refine ⟨14649592828520016403548707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39065580876053377076129885 14649592828520016403548707)
              ·
                refine ⟨21974389242780024605323061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14649592828520016403548707 21974389242780024605323061)
                ·
                  refine ⟨2060098991510627306749037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21974389242780024605323061 2060098991510627306749037)
                  ·
                    refine ⟨772537121816485240030889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060098991510627306749037 772537121816485240030889)
                    ·
                      refine ⟨579402841362363930023167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772537121816485240030889 579402841362363930023167)
                      ·
                        rfl

theorem cell23_1128383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_1128383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128383 prefixEnd_1128383 := by exact prefixLift 1128383
  have htrace : WordTrace (prefixWord ++ tailWord_1128383) baseStart_1128383 baseEnd_1128383 := by
    simpa [prefixWord, tailWord_1128383, baseEnd_1128383] using wordTrace_append hprefix tailTrace_1128383
  have hstable : (prefixWord ++ tailWord_1128383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128383).length < 2 ^ (prefixWord ++ tailWord_1128383).sum := by decide
  have hdescent : baseEnd_1128383 < baseStart_1128383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128416 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1128416 : Nat := 118140960795 + 1128416 * 2 ^ 59
def prefixEnd_1128416 : Nat := 4983230072969 + 3 ^ 40 * 1128416 * 2
def baseEnd_1128416 : Nat := 579419786223962300910515

theorem tailTrace_1128416 : CollatzResearch.WordTrace tailWord_1128416 prefixEnd_1128416 579419786223962300910515 := by
  unfold tailWord_1128416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20578356339974512477418551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27437808453299349969891401 20578356339974512477418551)
  ·
    refine ⟨30867534509961768716127827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20578356339974512477418551 30867534509961768716127827)
    ·
      refine ⟨46301301764942653074191741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30867534509961768716127827 46301301764942653074191741)
      ·
        refine ⟨17362988161853494902821903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46301301764942653074191741 17362988161853494902821903)
        ·
          refine ⟨26044482242780242354232855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17362988161853494902821903 26044482242780242354232855)
          ·
            refine ⟨39066723364170363531349283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26044482242780242354232855 39066723364170363531349283)
            ·
              refine ⟨58600085046255545297023925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39066723364170363531349283 58600085046255545297023925)
              ·
                refine ⟨5493757973086457371595993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58600085046255545297023925 5493757973086457371595993)
                ·
                  refine ⟨4120318479814843028696995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5493757973086457371595993 4120318479814843028696995)
                  ·
                    refine ⟨6180477719722264543045493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4120318479814843028696995 6180477719722264543045493)
                    ·
                      refine ⟨579419786223962300910515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6180477719722264543045493 579419786223962300910515)
                      ·
                        rfl

theorem cell23_1128416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1128416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128416 prefixEnd_1128416 := by exact prefixLift 1128416
  have htrace : WordTrace (prefixWord ++ tailWord_1128416) baseStart_1128416 baseEnd_1128416 := by
    simpa [prefixWord, tailWord_1128416, baseEnd_1128416] using wordTrace_append hprefix tailTrace_1128416
  have hstable : (prefixWord ++ tailWord_1128416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128416).length < 2 ^ (prefixWord ++ tailWord_1128416).sum := by decide
  have hdescent : baseEnd_1128416 < baseStart_1128416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128417 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_1128417 : Nat := 118140960795 + 1128417 * 2 ^ 59
def prefixEnd_1128417 : Nat := 4983230072969 + 3 ^ 40 * 1128417 * 2
def baseEnd_1128417 : Nat := 579420299704616796998011

theorem tailTrace_1128417 : CollatzResearch.WordTrace tailWord_1128417 prefixEnd_1128417 579420299704616796998011 := by
  unfold tailWord_1128417
  simp only [CollatzResearch.WordTrace]
  refine ⟨41156749152945402125623505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27437832768630268083749003 41156749152945402125623505)
  ·
    refine ⟨30867561864709051594217629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41156749152945402125623505 30867561864709051594217629)
    ·
      refine ⟨11575335699265894347831611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30867561864709051594217629 11575335699265894347831611)
      ·
        refine ⟨17363003548898841521747417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11575335699265894347831611 17363003548898841521747417)
        ·
          refine ⟨13022252661674131141310563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17363003548898841521747417 13022252661674131141310563)
          ·
            refine ⟨19533378992511196711965845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13022252661674131141310563 19533378992511196711965845)
            ·
              refine ⟨915627140273962345873399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19533378992511196711965845 915627140273962345873399)
              ·
                refine ⟨1373440710410943518810099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915627140273962345873399 1373440710410943518810099)
                ·
                  refine ⟨2060161065616415278215149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373440710410943518810099 2060161065616415278215149)
                  ·
                    refine ⟨772560399606155729330681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060161065616415278215149 772560399606155729330681)
                    ·
                      refine ⟨579420299704616796998011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772560399606155729330681 579420299704616796998011)
                      ·
                        rfl

theorem cell23_1128417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_1128417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128417 prefixEnd_1128417 := by exact prefixLift 1128417
  have htrace : WordTrace (prefixWord ++ tailWord_1128417) baseStart_1128417 baseEnd_1128417 := by
    simpa [prefixWord, tailWord_1128417, baseEnd_1128417] using wordTrace_append hprefix tailTrace_1128417
  have hstable : (prefixWord ++ tailWord_1128417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128417).length < 2 ^ (prefixWord ++ tailWord_1128417).sum := by decide
  have hdescent : baseEnd_1128417 < baseStart_1128417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128473 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 7, 2]
def baseStart_1128473 : Nat := 118140960795 + 1128473 * 2 ^ 59
def prefixEnd_1128473 : Nat := 4983230072969 + 3 ^ 40 * 1128473 * 2
def baseEnd_1128473 : Nat := 579449054621268577897753

theorem tailTrace_1128473 : CollatzResearch.WordTrace tailWord_1128473 prefixEnd_1128473 579449054621268577897753 := by
  unfold tailWord_1128473
  simp only [CollatzResearch.WordTrace]
  refine ⟨41158791640742523689662073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27439194427161682459774715 41158791640742523689662073)
  ·
    refine ⟨30869093730556892767246555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41158791640742523689662073 30869093730556892767246555)
    ·
      refine ⟨46303640595835339150869833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30869093730556892767246555 46303640595835339150869833)
      ·
        refine ⟨34727730446876504363152375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46303640595835339150869833 34727730446876504363152375)
        ·
          refine ⟨52091595670314756544728563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34727730446876504363152375 52091595670314756544728563)
          ·
            refine ⟨78137393505472134817092845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52091595670314756544728563 78137393505472134817092845)
            ·
              refine ⟨29301522564552050556409817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78137393505472134817092845 29301522564552050556409817)
              ·
                refine ⟨21976141923414037917307363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29301522564552050556409817 21976141923414037917307363)
                ·
                  refine ⟨32964212885121056875961045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21976141923414037917307363 32964212885121056875961045)
                  ·
                    refine ⟨772598739495024770530337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32964212885121056875961045 772598739495024770530337)
                    ·
                      refine ⟨579449054621268577897753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772598739495024770530337 579449054621268577897753)
                      ·
                        rfl

theorem cell23_1128473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_1128473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128473 prefixEnd_1128473 := by exact prefixLift 1128473
  have htrace : WordTrace (prefixWord ++ tailWord_1128473) baseStart_1128473 baseEnd_1128473 := by
    simpa [prefixWord, tailWord_1128473, baseEnd_1128473] using wordTrace_append hprefix tailTrace_1128473
  have hstable : (prefixWord ++ tailWord_1128473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128473).length < 2 ^ (prefixWord ++ tailWord_1128473).sum := by decide
  have hdescent : baseEnd_1128473 < baseStart_1128473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128483 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 2, 5]
def baseStart_1128483 : Nat := 118140960795 + 1128483 * 2 ^ 59
def prefixEnd_1128483 : Nat := 4983230072969 + 3 ^ 40 * 1128483 * 2
def baseEnd_1128483 : Nat := 193151396475937846257569

theorem tailTrace_1128483 : CollatzResearch.WordTrace tailWord_1128483 prefixEnd_1128483 193151396475937846257569 := by
  unfold tailWord_1128483
  simp only [CollatzResearch.WordTrace]
  refine ⟨41159156370706295397526103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27439437580470863598350735 41159156370706295397526103)
  ·
    refine ⟨61738734556059443096289155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41159156370706295397526103 61738734556059443096289155)
    ·
      refine ⟨92608101834089164644433733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61738734556059443096289155 92608101834089164644433733)
      ·
        refine ⟨17364019093891718370831325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92608101834089164644433733 17364019093891718370831325)
        ·
          refine ⟨6511507160209394389061747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17364019093891718370831325 6511507160209394389061747)
          ·
            refine ⟨9767260740314091583592621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6511507160209394389061747 9767260740314091583592621)
            ·
              refine ⟨3662722777617784343847233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9767260740314091583592621 3662722777617784343847233)
              ·
                refine ⟨2747042083213338257885425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3662722777617784343847233 2747042083213338257885425)
                ·
                  refine ⟨2060281562410003693414069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747042083213338257885425 2060281562410003693414069)
                  ·
                    refine ⟨193151396475937846257569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2060281562410003693414069 193151396475937846257569)
                    ·
                      rfl

theorem cell23_1128483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 5].length) (baseStart_1128483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128483 prefixEnd_1128483 := by exact prefixLift 1128483
  have htrace : WordTrace (prefixWord ++ tailWord_1128483) baseStart_1128483 baseEnd_1128483 := by
    simpa [prefixWord, tailWord_1128483, baseEnd_1128483] using wordTrace_append hprefix tailTrace_1128483
  have hstable : (prefixWord ++ tailWord_1128483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128483).length < 2 ^ (prefixWord ++ tailWord_1128483).sum := by decide
  have hdescent : baseEnd_1128483 < baseStart_1128483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128487 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 7]
def baseStart_1128487 : Nat := 118140960795 + 1128487 * 2 ^ 59
def prefixEnd_1128487 : Nat := 4983230072969 + 3 ^ 40 * 1128487 * 2
def baseEnd_1128487 : Nat := 64384027038936835902521

theorem tailTrace_1128487 : CollatzResearch.WordTrace tailWord_1128487 prefixEnd_1128487 64384027038936835902521 := by
  unfold tailWord_1128487
  simp only [CollatzResearch.WordTrace]
  refine ⟨41159302262691804080671715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27439534841794536053781143 41159302262691804080671715)
  ·
    refine ⟨61738953394037706121007573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41159302262691804080671715 61738953394037706121007573)
    ·
      refine ⟨1447006720172758737211115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 61738953394037706121007573 1447006720172758737211115)
      ·
        refine ⟨2170510080259138105816673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447006720172758737211115 2170510080259138105816673)
        ·
          refine ⟨1627882560194353579362505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170510080259138105816673 1627882560194353579362505)
          ·
            refine ⟨1220911920145765184521879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627882560194353579362505 1220911920145765184521879)
            ·
              refine ⟨1831367880218647776782819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220911920145765184521879 1831367880218647776782819)
              ·
                refine ⟨2747051820327971665174229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831367880218647776782819 2747051820327971665174229)
                ·
                  refine ⟨64384027038936835902521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2747051820327971665174229 64384027038936835902521)
                  ·
                    rfl

theorem cell23_1128487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 7].length) (baseStart_1128487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128487 prefixEnd_1128487 := by exact prefixLift 1128487
  have htrace : WordTrace (prefixWord ++ tailWord_1128487) baseStart_1128487 baseEnd_1128487 := by
    simpa [prefixWord, tailWord_1128487, baseEnd_1128487] using wordTrace_append hprefix tailTrace_1128487
  have hstable : (prefixWord ++ tailWord_1128487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128487).length < 2 ^ (prefixWord ++ tailWord_1128487).sum := by decide
  have hdescent : baseEnd_1128487 < baseStart_1128487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128523 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3]
def baseStart_1128523 : Nat := 118140960795 + 1128523 * 2 ^ 59
def prefixEnd_1128523 : Nat := 4983230072969 + 3 ^ 40 * 1128523 * 2
def baseEnd_1128523 : Nat := 579474728653993382272523

theorem tailTrace_1128523 : CollatzResearch.WordTrace tailWord_1128523 prefixEnd_1128523 579474728653993382272523 := by
  unfold tailWord_1128523
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160615290561382228982223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27440410193707588152654815 41160615290561382228982223)
  ·
    refine ⟨61740922935842073343473335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41160615290561382228982223 61740922935842073343473335)
    ·
      refine ⟨92611384403763110015210003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61740922935842073343473335 92611384403763110015210003)
      ·
        refine ⟨138917076605644665022815005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92611384403763110015210003 138917076605644665022815005)
        ·
          refine ⟨52093903727116749383555627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138917076605644665022815005 52093903727116749383555627)
          ·
            refine ⟨78140855590675124075333441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52093903727116749383555627 78140855590675124075333441)
            ·
              refine ⟨58605641693006343056500081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78140855590675124075333441 58605641693006343056500081)
              ·
                refine ⟨43954231269754757292375061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58605641693006343056500081 43954231269754757292375061)
                ·
                  refine ⟨2060354590769754248080081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43954231269754757292375061 2060354590769754248080081)
                  ·
                    refine ⟨1545265943077315686060061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060354590769754248080081 1545265943077315686060061)
                    ·
                      refine ⟨579474728653993382272523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1545265943077315686060061 579474728653993382272523)
                      ·
                        rfl

theorem cell23_1128523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 3].length) (baseStart_1128523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128523 prefixEnd_1128523 := by exact prefixLift 1128523
  have htrace : WordTrace (prefixWord ++ tailWord_1128523) baseStart_1128523 baseEnd_1128523 := by
    simpa [prefixWord, tailWord_1128523, baseEnd_1128523] using wordTrace_append hprefix tailTrace_1128523
  have hstable : (prefixWord ++ tailWord_1128523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128523).length < 2 ^ (prefixWord ++ tailWord_1128523).sum := by decide
  have hdescent : baseEnd_1128523 < baseStart_1128523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128604 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1128604 : Nat := 118140960795 + 1128604 * 2 ^ 59
def prefixEnd_1128604 : Nat := 4983230072969 + 3 ^ 40 * 1128604 * 2
def baseEnd_1128604 : Nat := 579516320587007565359651

theorem tailTrace_1128604 : CollatzResearch.WordTrace tailWord_1128604 prefixEnd_1128604 579516320587007565359651 := by
  unfold tailWord_1128604
  simp only [CollatzResearch.WordTrace]
  refine ⟨20581784801633966531340433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27442379735511955375120577 20581784801633966531340433)
  ·
    refine ⟨15436338601225474898505325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20581784801633966531340433 15436338601225474898505325)
    ·
      refine ⟨5788626975459553086939497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15436338601225474898505325 5788626975459553086939497)
      ·
        refine ⟨4341470231594664815204623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5788626975459553086939497 4341470231594664815204623)
        ·
          refine ⟨6512205347391997222806935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341470231594664815204623 6512205347391997222806935)
          ·
            refine ⟨9768308021087995834210403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512205347391997222806935 9768308021087995834210403)
            ·
              refine ⟨14652462031631993751315605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9768308021087995834210403 14652462031631993751315605)
              ·
                refine ⟨686834157732749707092919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14652462031631993751315605 686834157732749707092919)
                ·
                  refine ⟨1030251236599124560639379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686834157732749707092919 1030251236599124560639379)
                  ·
                    refine ⟨1545376854898686840959069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1030251236599124560639379 1545376854898686840959069)
                    ·
                      refine ⟨579516320587007565359651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1545376854898686840959069 579516320587007565359651)
                      ·
                        rfl

theorem cell23_1128604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1128604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128604 prefixEnd_1128604 := by exact prefixLift 1128604
  have htrace : WordTrace (prefixWord ++ tailWord_1128604) baseStart_1128604 baseEnd_1128604 := by
    simpa [prefixWord, tailWord_1128604, baseEnd_1128604] using wordTrace_append hprefix tailTrace_1128604
  have hstable : (prefixWord ++ tailWord_1128604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128604).length < 2 ^ (prefixWord ++ tailWord_1128604).sum := by decide
  have hdescent : baseEnd_1128604 < baseStart_1128604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128633 : List Nat := [1, 2, 1, 4, 1, 2, 3, 9]
def baseStart_1128633 : Nat := 118140960795 + 1128633 * 2 ^ 59
def prefixEnd_1128633 : Nat := 4983230072969 + 3 ^ 40 * 1128633 * 2
def baseEnd_1128633 : Nat := 21464118945406961181371

theorem tailTrace_1128633 : CollatzResearch.WordTrace tailWord_1128633 prefixEnd_1128633 21464118945406961181371 := by
  unfold tailWord_1128633
  simp only [CollatzResearch.WordTrace]
  refine ⟨41164627320162871015486553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27443084880108580676991035 41164627320162871015486553)
  ·
    refine ⟨30873470490122153261614915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41164627320162871015486553 30873470490122153261614915)
    ·
      refine ⟨46310205735183229892422373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30873470490122153261614915 46310205735183229892422373)
      ·
        refine ⟨8683163575346855604829195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46310205735183229892422373 8683163575346855604829195)
        ·
          refine ⟨13024745363020283407243793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8683163575346855604829195 13024745363020283407243793)
          ·
            refine ⟨9768559022265212555432845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13024745363020283407243793 9768559022265212555432845)
            ·
              refine ⟨3663209633349454708287317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9768559022265212555432845 3663209633349454708287317)
              ·
                refine ⟨21464118945406961181371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3663209633349454708287317 21464118945406961181371)
                ·
                  rfl

theorem cell23_1128633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 9].length) (baseStart_1128633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128633 prefixEnd_1128633 := by exact prefixLift 1128633
  have htrace : WordTrace (prefixWord ++ tailWord_1128633) baseStart_1128633 baseEnd_1128633 := by
    simpa [prefixWord, tailWord_1128633, baseEnd_1128633] using wordTrace_append hprefix tailTrace_1128633
  have hstable : (prefixWord ++ tailWord_1128633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128633).length < 2 ^ (prefixWord ++ tailWord_1128633).sum := by decide
  have hdescent : baseEnd_1128633 < baseStart_1128633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128638 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_1128638 : Nat := 118140960795 + 1128638 * 2 ^ 59
def prefixEnd_1128638 : Nat := 4983230072969 + 3 ^ 40 * 1128638 * 2
def baseEnd_1128638 : Nat := 579533778929260432334495

theorem tailTrace_1128638 : CollatzResearch.WordTrace tailWord_1128638 prefixEnd_1128638 579533778929260432334495 := by
  unfold tailWord_1128638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145601210643094608677321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27443206456763171246279045 5145601210643094608677321)
  ·
    refine ⟨3859200907982320956507991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5145601210643094608677321 3859200907982320956507991)
    ·
      refine ⟨5788801361973481434761987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859200907982320956507991 5788801361973481434761987)
      ·
        refine ⟨8683202042960222152142981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5788801361973481434761987 8683202042960222152142981)
        ·
          refine ⟨1628100383055041653526809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8683202042960222152142981 1628100383055041653526809)
          ·
            refine ⟨1221075287291281240145107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628100383055041653526809 1221075287291281240145107)
            ·
              refine ⟨1831612930936921860217661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221075287291281240145107 1831612930936921860217661)
              ·
                refine ⟨686854849101345697581623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1831612930936921860217661 686854849101345697581623)
                ·
                  refine ⟨1030282273652018546372435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686854849101345697581623 1030282273652018546372435)
                  ·
                    refine ⟨1545423410478027819558653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1030282273652018546372435 1545423410478027819558653)
                    ·
                      refine ⟨579533778929260432334495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1545423410478027819558653 579533778929260432334495)
                      ·
                        rfl

theorem cell23_1128638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_1128638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128638 prefixEnd_1128638 := by exact prefixLift 1128638
  have htrace : WordTrace (prefixWord ++ tailWord_1128638) baseStart_1128638 baseEnd_1128638 := by
    simpa [prefixWord, tailWord_1128638, baseEnd_1128638] using wordTrace_append hprefix tailTrace_1128638
  have hstable : (prefixWord ++ tailWord_1128638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128638).length < 2 ^ (prefixWord ++ tailWord_1128638).sum := by decide
  have hdescent : baseEnd_1128638 < baseStart_1128638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128663 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 7]
def baseStart_1128663 : Nat := 118140960795 + 1128663 * 2 ^ 59
def prefixEnd_1128663 : Nat := 4983230072969 + 3 ^ 40 * 1128663 * 2
def baseEnd_1128663 : Nat := 193182205315207611507293

theorem tailTrace_1128663 : CollatzResearch.WordTrace tailWord_1128663 prefixEnd_1128663 193182205315207611507293 := by
  unfold tailWord_1128663
  simp only [CollatzResearch.WordTrace]
  refine ⟨41165721510054186139078643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27443814340036124092719095 41165721510054186139078643)
  ·
    refine ⟨61748582265081279208617965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41165721510054186139078643 61748582265081279208617965)
    ·
      refine ⟨23155718349405479703231737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61748582265081279208617965 23155718349405479703231737)
      ·
        refine ⟨17366788762054109777423803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23155718349405479703231737 17366788762054109777423803)
        ·
          refine ⟨26050183143081164666135705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17366788762054109777423803 26050183143081164666135705)
          ·
            refine ⟨19537637357310873499601779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26050183143081164666135705 19537637357310873499601779)
            ·
              refine ⟨29306456035966310249402669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19537637357310873499601779 29306456035966310249402669)
              ·
                refine ⟨10989921013487366343526001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29306456035966310249402669 10989921013487366343526001)
                ·
                  refine ⟨8242440760115524757644501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989921013487366343526001 8242440760115524757644501)
                  ·
                    refine ⟨193182205315207611507293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8242440760115524757644501 193182205315207611507293)
                    ·
                      rfl

theorem cell23_1128663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_1128663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128663 prefixEnd_1128663 := by exact prefixLift 1128663
  have htrace : WordTrace (prefixWord ++ tailWord_1128663) baseStart_1128663 baseEnd_1128663 := by
    simpa [prefixWord, tailWord_1128663, baseEnd_1128663] using wordTrace_append hprefix tailTrace_1128663
  have hstable : (prefixWord ++ tailWord_1128663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128663).length < 2 ^ (prefixWord ++ tailWord_1128663).sum := by decide
  have hdescent : baseEnd_1128663 < baseStart_1128663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128723 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 11]
def baseStart_1128723 : Nat := 118140960795 + 1128723 * 2 ^ 59
def prefixEnd_1128723 : Nat := 4983230072969 + 3 ^ 40 * 1128723 * 2
def baseEnd_1128723 : Nat := 64397491642765844419067

theorem tailTrace_1128723 : CollatzResearch.WordTrace tailWord_1128723 prefixEnd_1128723 64397491642765844419067 := by
  unfold tailWord_1128723
  simp only [CollatzResearch.WordTrace]
  refine ⟨41167909889836816386262823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27445273259891210924175215 41167909889836816386262823)
  ·
    refine ⟨61751864834755224579394235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41167909889836816386262823 61751864834755224579394235)
    ·
      refine ⟨92627797252132836869091353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61751864834755224579394235 92627797252132836869091353)
      ·
        refine ⟨69470847939099627651818515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92627797252132836869091353 69470847939099627651818515)
        ·
          refine ⟨104206271908649441477727773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69470847939099627651818515 104206271908649441477727773)
          ·
            refine ⟨39077351965743540554147915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104206271908649441477727773 39077351965743540554147915)
            ·
              refine ⟨58616027948615310831221873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39077351965743540554147915 58616027948615310831221873)
              ·
                refine ⟨43962020961461483123416405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58616027948615310831221873 43962020961461483123416405)
                ·
                  refine ⟨64397491642765844419067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 43962020961461483123416405 64397491642765844419067)
                  ·
                    rfl

theorem cell23_1128723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 11].length) (baseStart_1128723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128723 prefixEnd_1128723 := by exact prefixLift 1128723
  have htrace : WordTrace (prefixWord ++ tailWord_1128723) baseStart_1128723 baseEnd_1128723 := by
    simpa [prefixWord, tailWord_1128723, baseEnd_1128723] using wordTrace_append hprefix tailTrace_1128723
  have hstable : (prefixWord ++ tailWord_1128723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128723).length < 2 ^ (prefixWord ++ tailWord_1128723).sum := by decide
  have hdescent : baseEnd_1128723 < baseStart_1128723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128740 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1128740 : Nat := 118140960795 + 1128740 * 2 ^ 59
def prefixEnd_1128740 : Nat := 4983230072969 + 3 ^ 40 * 1128740 * 2
def baseEnd_1128740 : Nat := 64398461550668781473225

theorem tailTrace_1128740 : CollatzResearch.WordTrace tailWord_1128740 prefixEnd_1128740 64398461550668781473225 := by
  unfold tailWord_1128740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20584264965387614144815837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27445686620516818859754449 20584264965387614144815837)
  ·
    refine ⟨7719099362020355304305939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20584264965387614144815837 7719099362020355304305939)
    ·
      refine ⟨11578649043030532956458909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7719099362020355304305939 11578649043030532956458909)
      ·
        refine ⟨4341993391136449858672091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11578649043030532956458909 4341993391136449858672091)
        ·
          refine ⟨6512990086704674788008137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341993391136449858672091 6512990086704674788008137)
          ·
            refine ⟨4884742565028506091006103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6512990086704674788008137 4884742565028506091006103)
            ·
              refine ⟨7327113847542759136509155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884742565028506091006103 7327113847542759136509155)
              ·
                refine ⟨10990670771314138704763733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327113847542759136509155 10990670771314138704763733)
                ·
                  refine ⟨64398461550668781473225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10990670771314138704763733 64398461550668781473225)
                  ·
                    rfl

theorem cell23_1128740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1128740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128740 prefixEnd_1128740 := by exact prefixLift 1128740
  have htrace : WordTrace (prefixWord ++ tailWord_1128740) baseStart_1128740 baseEnd_1128740 := by
    simpa [prefixWord, tailWord_1128740, baseEnd_1128740] using wordTrace_append hprefix tailTrace_1128740
  have hstable : (prefixWord ++ tailWord_1128740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128740).length < 2 ^ (prefixWord ++ tailWord_1128740).sum := by decide
  have hdescent : baseEnd_1128740 < baseStart_1128740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128780 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1128780 : Nat := 118140960795 + 1128780 * 2 ^ 59
def prefixEnd_1128780 : Nat := 4983230072969 + 3 ^ 40 * 1128780 * 2
def baseEnd_1128780 : Nat := 579606693182198876758841

theorem tailTrace_1128780 : CollatzResearch.WordTrace tailWord_1128780 prefixEnd_1128780 579606693182198876758841 := by
  unfold tailWord_1128780
  simp only [CollatzResearch.WordTrace]
  refine ⟨20584994425315157560543897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27446659233753543414058529 20584994425315157560543897)
  ·
    refine ⟨15438745818986368170407923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20584994425315157560543897 15438745818986368170407923)
    ·
      refine ⟨23158118728479552255611885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15438745818986368170407923 23158118728479552255611885)
      ·
        refine ⟨8684294523179832095854457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23158118728479552255611885 8684294523179832095854457)
        ·
          refine ⟨6513220892384874071890843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8684294523179832095854457 6513220892384874071890843)
          ·
            refine ⟨9769831338577311107836265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6513220892384874071890843 9769831338577311107836265)
            ·
              refine ⟨7327373503932983330877199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9769831338577311107836265 7327373503932983330877199)
              ·
                refine ⟨10991060255899474996315799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327373503932983330877199 10991060255899474996315799)
                ·
                  refine ⟨16486590383849212494473699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10991060255899474996315799 16486590383849212494473699)
                  ·
                    refine ⟨24729885575773818741710549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16486590383849212494473699 24729885575773818741710549)
                    ·
                      refine ⟨579606693182198876758841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24729885575773818741710549 579606693182198876758841)
                      ·
                        rfl

theorem cell23_1128780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1128780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128780 prefixEnd_1128780 := by exact prefixLift 1128780
  have htrace : WordTrace (prefixWord ++ tailWord_1128780) baseStart_1128780 baseEnd_1128780 := by
    simpa [prefixWord, tailWord_1128780, baseEnd_1128780] using wordTrace_append hprefix tailTrace_1128780
  have hstable : (prefixWord ++ tailWord_1128780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128780).length < 2 ^ (prefixWord ++ tailWord_1128780).sum := by decide
  have hdescent : baseEnd_1128780 < baseStart_1128780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128807 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1128807 : Nat := 118140960795 + 1128807 * 2 ^ 59
def prefixEnd_1128807 : Nat := 4983230072969 + 3 ^ 40 * 1128807 * 2
def baseEnd_1128807 : Nat := 579620557159870271121217

theorem tailTrace_1128807 : CollatzResearch.WordTrace tailWord_1128807 prefixEnd_1128807 579620557159870271121217 := by
  unfold tailWord_1128807
  simp only [CollatzResearch.WordTrace]
  refine ⟨41170973621532498732320675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27447315747688332488213783 41170973621532498732320675)
  ·
    refine ⟨61756460432298748098481013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41170973621532498732320675 61756460432298748098481013)
    ·
      refine ⟨5789668165528007634232595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61756460432298748098481013 5789668165528007634232595)
      ·
        refine ⟨8684502248292011451348893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789668165528007634232595 8684502248292011451348893)
        ·
          refine ⟨3256688343109504294255835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8684502248292011451348893 3256688343109504294255835)
          ·
            refine ⟨4885032514664256441383753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256688343109504294255835 4885032514664256441383753)
            ·
              refine ⟨3663774385998192331037815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4885032514664256441383753 3663774385998192331037815)
              ·
                refine ⟨5495661578997288496556723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663774385998192331037815 5495661578997288496556723)
                ·
                  refine ⟨8243492368495932744835085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5495661578997288496556723 8243492368495932744835085)
                  ·
                    refine ⟨3091309638185974779313157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8243492368495932744835085 3091309638185974779313157)
                    ·
                      refine ⟨579620557159870271121217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3091309638185974779313157 579620557159870271121217)
                      ·
                        rfl

theorem cell23_1128807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1128807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128807 prefixEnd_1128807 := by exact prefixLift 1128807
  have htrace : WordTrace (prefixWord ++ tailWord_1128807) baseStart_1128807 baseEnd_1128807 := by
    simpa [prefixWord, tailWord_1128807, baseEnd_1128807] using wordTrace_append hprefix tailTrace_1128807
  have hstable : (prefixWord ++ tailWord_1128807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128807).length < 2 ^ (prefixWord ++ tailWord_1128807).sum := by decide
  have hdescent : baseEnd_1128807 < baseStart_1128807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128827 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3]
def baseStart_1128827 : Nat := 118140960795 + 1128827 * 2 ^ 59
def prefixEnd_1128827 : Nat := 4983230072969 + 3 ^ 40 * 1128827 * 2
def baseEnd_1128827 : Nat := 579630826772960192871125

theorem tailTrace_1128827 : CollatzResearch.WordTrace tailWord_1128827 prefixEnd_1128827 579630826772960192871125 := by
  unfold tailWord_1128827
  simp only [CollatzResearch.WordTrace]
  refine ⟨41171703081460042148048735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27447802054306694765365823 41171703081460042148048735)
  ·
    refine ⟨61757554622190063222073103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41171703081460042148048735 61757554622190063222073103)
    ·
      refine ⟨92636331933285094833109655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61757554622190063222073103 92636331933285094833109655)
      ·
        refine ⟨138954497899927642249664483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92636331933285094833109655 138954497899927642249664483)
        ·
          refine ⟨208431746849891463374496725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138954497899927642249664483 208431746849891463374496725)
          ·
            refine ⟨4885119066794331172839767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 208431746849891463374496725 4885119066794331172839767)
            ·
              refine ⟨7327678600191496759259651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4885119066794331172839767 7327678600191496759259651)
              ·
                refine ⟨10991517900287245138889477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327678600191496759259651 10991517900287245138889477)
                ·
                  refine ⟨2060909606303858463541777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10991517900287245138889477 2060909606303858463541777)
                  ·
                    refine ⟨1545682204727893847656333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060909606303858463541777 1545682204727893847656333)
                    ·
                      refine ⟨579630826772960192871125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1545682204727893847656333 579630826772960192871125)
                      ·
                        rfl

theorem cell23_1128827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 3].length) (baseStart_1128827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128827 prefixEnd_1128827 := by exact prefixLift 1128827
  have htrace : WordTrace (prefixWord ++ tailWord_1128827) baseStart_1128827 baseEnd_1128827 := by
    simpa [prefixWord, tailWord_1128827, baseEnd_1128827] using wordTrace_append hprefix tailTrace_1128827
  have hstable : (prefixWord ++ tailWord_1128827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128827).length < 2 ^ (prefixWord ++ tailWord_1128827).sum := by decide
  have hdescent : baseEnd_1128827 < baseStart_1128827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128861 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1128861 : Nat := 118140960795 + 1128861 * 2 ^ 59
def prefixEnd_1128861 : Nat := 4983230072969 + 3 ^ 40 * 1128861 * 2
def baseEnd_1128861 : Nat := 579648285115213059845969

theorem tailTrace_1128861 : CollatzResearch.WordTrace tailWord_1128861 prefixEnd_1128861 579648285115213059845969 := by
  unfold tailWord_1128861
  simp only [CollatzResearch.WordTrace]
  refine ⟨41172943163336865954786437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27448628775557910636524291 41172943163336865954786437)
  ·
    refine ⟨7719926843125662366522457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41172943163336865954786437 7719926843125662366522457)
    ·
      refine ⟨5789945132344246774891843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7719926843125662366522457 5789945132344246774891843)
      ·
        refine ⟨8684917698516370162337765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789945132344246774891843 8684917698516370162337765)
        ·
          refine ⟨1628422068471819405438331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8684917698516370162337765 1628422068471819405438331)
          ·
            refine ⟨2442633102707729108157497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628422068471819405438331 2442633102707729108157497)
            ·
              refine ⟨1831974827030796831118123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442633102707729108157497 1831974827030796831118123)
              ·
                refine ⟨2747962240546195246677185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831974827030796831118123 2747962240546195246677185)
                ·
                  refine ⟨2060971680409646435007889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747962240546195246677185 2060971680409646435007889)
                  ·
                    refine ⟨1545728760307234826255917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060971680409646435007889 1545728760307234826255917)
                    ·
                      refine ⟨579648285115213059845969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1545728760307234826255917 579648285115213059845969)
                      ·
                        rfl

theorem cell23_1128861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1128861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128861 prefixEnd_1128861 := by exact prefixLift 1128861
  have htrace : WordTrace (prefixWord ++ tailWord_1128861) baseStart_1128861 baseEnd_1128861 := by
    simpa [prefixWord, tailWord_1128861, baseEnd_1128861] using wordTrace_append hprefix tailTrace_1128861
  have hstable : (prefixWord ++ tailWord_1128861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128861).length < 2 ^ (prefixWord ++ tailWord_1128861).sum := by decide
  have hdescent : baseEnd_1128861 < baseStart_1128861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128885 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1128885 : Nat := 118140960795 + 1128885 * 2 ^ 59
def prefixEnd_1128885 : Nat := 4983230072969 + 3 ^ 40 * 1128885 * 2
def baseEnd_1128885 : Nat := 193220202883640321981953

theorem tailTrace_1128885 : CollatzResearch.WordTrace tailWord_1128885 prefixEnd_1128885 193220202883640321981953 := by
  unfold tailWord_1128885
  simp only [CollatzResearch.WordTrace]
  refine ⟨41173818515249918053660109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27449212343499945369106739 41173818515249918053660109)
  ·
    refine ⟨15440181943218719270122541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41173818515249918053660109 15440181943218719270122541)
    ·
      refine ⟨5790068228707019726295953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15440181943218719270122541 5790068228707019726295953)
      ·
        refine ⟨4342551171530264794721965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5790068228707019726295953 4342551171530264794721965)
        ·
          refine ⟨1628456689323849298020737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4342551171530264794721965 1628456689323849298020737)
          ·
            refine ⟨1221342516992886973515553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628456689323849298020737 1221342516992886973515553)
            ·
              refine ⟨916006887744665230136665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221342516992886973515553 916006887744665230136665)
              ·
                refine ⟨687005165808498922602499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916006887744665230136665 687005165808498922602499)
                ·
                  refine ⟨1030507748712748383903749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687005165808498922602499 1030507748712748383903749)
                  ·
                    refine ⟨193220202883640321981953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030507748712748383903749 193220202883640321981953)
                    ·
                      rfl

theorem cell23_1128885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1128885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128885 prefixEnd_1128885 := by exact prefixLift 1128885
  have htrace : WordTrace (prefixWord ++ tailWord_1128885) baseStart_1128885 baseEnd_1128885 := by
    simpa [prefixWord, tailWord_1128885, baseEnd_1128885] using wordTrace_append hprefix tailTrace_1128885
  have hstable : (prefixWord ++ tailWord_1128885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128885).length < 2 ^ (prefixWord ++ tailWord_1128885).sum := by decide
  have hdescent : baseEnd_1128885 < baseStart_1128885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128907 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 6, 4]
def baseStart_1128907 : Nat := 118140960795 + 1128907 * 2 ^ 59
def prefixEnd_1128907 : Nat := 4983230072969 + 3 ^ 40 * 1128907 * 2
def baseEnd_1128907 : Nat := 193223968408439959956919

theorem tailTrace_1128907 : CollatzResearch.WordTrace tailWord_1128907 prefixEnd_1128907 193223968408439959956919 := by
  unfold tailWord_1128907
  simp only [CollatzResearch.WordTrace]
  refine ⟨41174620921170215810960975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27449747280780143873973983 41174620921170215810960975)
  ·
    refine ⟨61761931381755323716441463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41174620921170215810960975 61761931381755323716441463)
    ·
      refine ⟨92642897072632985574662195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61761931381755323716441463 92642897072632985574662195)
      ·
        refine ⟨138964345608949478361993293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92642897072632985574662195 138964345608949478361993293)
        ·
          refine ⟨52111629603356054385747485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138964345608949478361993293 52111629603356054385747485)
          ·
            refine ⟨19541861101258520394655307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52111629603356054385747485 19541861101258520394655307)
            ·
              refine ⟨29312791651887780591982961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19541861101258520394655307 29312791651887780591982961)
              ·
                refine ⟨21984593738915835443987221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29312791651887780591982961 21984593738915835443987221)
                ·
                  refine ⟨1030527831511679786436901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21984593738915835443987221 1030527831511679786436901)
                  ·
                    refine ⟨193223968408439959956919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030527831511679786436901 193223968408439959956919)
                    ·
                      rfl

theorem cell23_1128907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 4].length) (baseStart_1128907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128907 prefixEnd_1128907 := by exact prefixLift 1128907
  have htrace : WordTrace (prefixWord ++ tailWord_1128907) baseStart_1128907 baseEnd_1128907 := by
    simpa [prefixWord, tailWord_1128907, baseEnd_1128907] using wordTrace_append hprefix tailTrace_1128907
  have hstable : (prefixWord ++ tailWord_1128907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128907).length < 2 ^ (prefixWord ++ tailWord_1128907).sum := by decide
  have hdescent : baseEnd_1128907 < baseStart_1128907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128931 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1128931 : Nat := 118140960795 + 1128931 * 2 ^ 59
def prefixEnd_1128931 : Nat := 4983230072969 + 3 ^ 40 * 1128931 * 2
def baseEnd_1128931 : Nat := 579684228761027785970647

theorem tailTrace_1128931 : CollatzResearch.WordTrace tailWord_1128931 prefixEnd_1128931 579684228761027785970647 := by
  unfold tailWord_1128931
  simp only [CollatzResearch.WordTrace]
  refine ⟨41175496273083267909834647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27450330848722178606556431 41175496273083267909834647)
  ·
    refine ⟨61763244409624901864751971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41175496273083267909834647 61763244409624901864751971)
    ·
      refine ⟨92644866614437352797127957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61763244409624901864751971 92644866614437352797127957)
      ·
        refine ⟨4342728122551750912365373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92644866614437352797127957 4342728122551750912365373)
        ·
          refine ⟨1628523045956906592137015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4342728122551750912365373 1628523045956906592137015)
          ·
            refine ⟨2442784568935359888205523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628523045956906592137015 2442784568935359888205523)
            ·
              refine ⟨3664176853403039832308285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442784568935359888205523 3664176853403039832308285)
              ·
                refine ⟨1374066320026139937115607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3664176853403039832308285 1374066320026139937115607)
                ·
                  refine ⟨2061099480039209905673411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374066320026139937115607 2061099480039209905673411)
                  ·
                    refine ⟨3091649220058814858510117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2061099480039209905673411 3091649220058814858510117)
                    ·
                      refine ⟨579684228761027785970647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3091649220058814858510117 579684228761027785970647)
                      ·
                        rfl

theorem cell23_1128931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1128931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128931 prefixEnd_1128931 := by exact prefixLift 1128931
  have htrace : WordTrace (prefixWord ++ tailWord_1128931) baseStart_1128931 baseEnd_1128931 := by
    simpa [prefixWord, tailWord_1128931, baseEnd_1128931] using wordTrace_append hprefix tailTrace_1128931
  have hstable : (prefixWord ++ tailWord_1128931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128931).length < 2 ^ (prefixWord ++ tailWord_1128931).sum := by decide
  have hdescent : baseEnd_1128931 < baseStart_1128931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128941 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1128941 : Nat := 118140960795 + 1128941 * 2 ^ 59
def prefixEnd_1128941 : Nat := 4983230072969 + 3 ^ 40 * 1128941 * 2
def baseEnd_1128941 : Nat := 193229787855857582281867

theorem tailTrace_1128941 : CollatzResearch.WordTrace tailWord_1128941 prefixEnd_1128941 193229787855857582281867 := by
  unfold tailWord_1128941
  simp only [CollatzResearch.WordTrace]
  refine ⟨41175861003047039617698677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27450574002031359745132451 41175861003047039617698677)
  ·
    refine ⟨3860236969035659964159251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41175861003047039617698677 3860236969035659964159251)
    ·
      refine ⟨5790355453553489946238877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860236969035659964159251 5790355453553489946238877)
      ·
        refine ⟨2171383295082558729839579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5790355453553489946238877 2171383295082558729839579)
        ·
          refine ⟨3257074942623838094759369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171383295082558729839579 3257074942623838094759369)
          ·
            refine ⟨2442806206967878571069527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3257074942623838094759369 2442806206967878571069527)
            ·
              refine ⟨3664209310451817856604291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442806206967878571069527 3664209310451817856604291)
              ·
                refine ⟨5496313965677726784906437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664209310451817856604291 5496313965677726784906437)
                ·
                  refine ⟨1030558868564573772169957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5496313965677726784906437 1030558868564573772169957)
                  ·
                    refine ⟨193229787855857582281867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030558868564573772169957 193229787855857582281867)
                    ·
                      rfl

theorem cell23_1128941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1128941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128941 prefixEnd_1128941 := by exact prefixLift 1128941
  have htrace : WordTrace (prefixWord ++ tailWord_1128941) baseStart_1128941 baseEnd_1128941 := by
    simpa [prefixWord, tailWord_1128941, baseEnd_1128941] using wordTrace_append hprefix tailTrace_1128941
  have hstable : (prefixWord ++ tailWord_1128941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128941).length < 2 ^ (prefixWord ++ tailWord_1128941).sum := by decide
  have hdescent : baseEnd_1128941 < baseStart_1128941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128961 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1128961 : Nat := 118140960795 + 1128961 * 2 ^ 59
def prefixEnd_1128961 : Nat := 4983230072969 + 3 ^ 40 * 1128961 * 2
def baseEnd_1128961 : Nat := 579699633180662668595509

theorem tailTrace_1128961 : CollatzResearch.WordTrace tailWord_1128961 prefixEnd_1128961 579699633180662668595509 := by
  unfold tailWord_1128961
  simp only [CollatzResearch.WordTrace]
  refine ⟨41176590462974583033426737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27451060308649722022284491 41176590462974583033426737)
  ·
    refine ⟨30882442847230937275070053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41176590462974583033426737 30882442847230937275070053)
    ·
      refine ⟨5790458033855800739075635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30882442847230937275070053 5790458033855800739075635)
      ·
        refine ⟨8685687050783701108613453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5790458033855800739075635 8685687050783701108613453)
        ·
          refine ⟨3257132644043887915730045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8685687050783701108613453 3257132644043887915730045)
          ·
            refine ⟨1221424741516457968398767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3257132644043887915730045 1221424741516457968398767)
            ·
              refine ⟨1832137112274686952598151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221424741516457968398767 1832137112274686952598151)
              ·
                refine ⟨2748205668412030428897227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832137112274686952598151 2748205668412030428897227)
                ·
                  refine ⟨4122308502618045643345841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748205668412030428897227 4122308502618045643345841)
                  ·
                    refine ⟨3091731376963534232509381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4122308502618045643345841 3091731376963534232509381)
                    ·
                      refine ⟨579699633180662668595509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3091731376963534232509381 579699633180662668595509)
                      ·
                        rfl

theorem cell23_1128961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1128961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128961 prefixEnd_1128961 := by exact prefixLift 1128961
  have htrace : WordTrace (prefixWord ++ tailWord_1128961) baseStart_1128961 baseEnd_1128961 := by
    simpa [prefixWord, tailWord_1128961, baseEnd_1128961] using wordTrace_append hprefix tailTrace_1128961
  have hstable : (prefixWord ++ tailWord_1128961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128961).length < 2 ^ (prefixWord ++ tailWord_1128961).sum := by decide
  have hdescent : baseEnd_1128961 < baseStart_1128961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128997 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_1128997 : Nat := 118140960795 + 1128997 * 2 ^ 59
def prefixEnd_1128997 : Nat := 4983230072969 + 3 ^ 40 * 1128997 * 2
def baseEnd_1128997 : Nat := 193239372828074842581781

theorem tailTrace_1128997 : CollatzResearch.WordTrace tailWord_1128997 prefixEnd_1128997 193239372828074842581781 := by
  unfold tailWord_1128997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41177903490844161181737245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27451935660562774121158163 41177903490844161181737245)
  ·
    refine ⟨15441713809066560443151467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41177903490844161181737245 15441713809066560443151467)
    ·
      refine ⟨23162570713599840664727201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15441713809066560443151467 23162570713599840664727201)
      ·
        refine ⟨17371928035199880498545401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23162570713599840664727201 17371928035199880498545401)
        ·
          refine ⟨13028946026399910373909051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17371928035199880498545401 13028946026399910373909051)
          ·
            refine ⟨19543419039599865560863577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13028946026399910373909051 19543419039599865560863577)
            ·
              refine ⟨14657564279699899170647683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19543419039599865560863577 14657564279699899170647683)
              ·
                refine ⟨21986346419549848755971525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14657564279699899170647683 21986346419549848755971525)
                ·
                  refine ⟨4122439953665596641744661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21986346419549848755971525 4122439953665596641744661)
                  ·
                    refine ⟨193239372828074842581781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4122439953665596641744661 193239372828074842581781)
                    ·
                      rfl

theorem cell23_1128997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_1128997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128997 prefixEnd_1128997 := by exact prefixLift 1128997
  have htrace : WordTrace (prefixWord ++ tailWord_1128997) baseStart_1128997 baseEnd_1128997 := by
    simpa [prefixWord, tailWord_1128997, baseEnd_1128997] using wordTrace_append hprefix tailTrace_1128997
  have hstable : (prefixWord ++ tailWord_1128997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128997).length < 2 ^ (prefixWord ++ tailWord_1128997).sum := by decide
  have hdescent : baseEnd_1128997 < baseStart_1128997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128999 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1128999 : Nat := 118140960795 + 1128999 * 2 ^ 59
def prefixEnd_1128999 : Nat := 4983230072969 + 3 ^ 40 * 1128999 * 2
def baseEnd_1128999 : Nat := 579719145445533519920335

theorem tailTrace_1128999 : CollatzResearch.WordTrace tailWord_1128999 prefixEnd_1128999 579719145445533519920335 := by
  unfold tailWord_1128999
  simp only [CollatzResearch.WordTrace]
  refine ⟨41177976436836915523310051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27451984291224610348873367 41177976436836915523310051)
  ·
    refine ⟨61766964655255373284965077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41177976436836915523310051 61766964655255373284965077)
    ·
      refine ⟨1447663234107547811366369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 61766964655255373284965077 1447663234107547811366369)
      ·
        refine ⟨1085747425580660858524777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447663234107547811366369 1085747425580660858524777)
        ·
          refine ⟨814310569185495643893583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085747425580660858524777 814310569185495643893583)
          ·
            refine ⟨1221465853778243465840375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814310569185495643893583 1221465853778243465840375)
            ·
              refine ⟨1832198780667365198760563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221465853778243465840375 1832198780667365198760563)
              ·
                refine ⟨2748298171001047798140845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832198780667365198760563 2748298171001047798140845)
                ·
                  refine ⟨1030611814125392924302817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2748298171001047798140845 1030611814125392924302817)
                  ·
                    refine ⟨772958860594044693227113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1030611814125392924302817 772958860594044693227113)
                    ·
                      refine ⟨579719145445533519920335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772958860594044693227113 579719145445533519920335)
                      ·
                        rfl

theorem cell23_1128999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1128999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1128999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1128999 prefixEnd_1128999 := by exact prefixLift 1128999
  have htrace : WordTrace (prefixWord ++ tailWord_1128999) baseStart_1128999 baseEnd_1128999 := by
    simpa [prefixWord, tailWord_1128999, baseEnd_1128999] using wordTrace_append hprefix tailTrace_1128999
  have hstable : (prefixWord ++ tailWord_1128999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128999).length < 2 ^ (prefixWord ++ tailWord_1128999).sum := by decide
  have hdescent : baseEnd_1128999 < baseStart_1128999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129025 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1129025 : Nat := 118140960795 + 1129025 * 2 ^ 59
def prefixEnd_1129025 : Nat := 4983230072969 + 3 ^ 40 * 1129025 * 2
def baseEnd_1129025 : Nat := 579732495942550418195215

theorem tailTrace_1129025 : CollatzResearch.WordTrace tailWord_1129025 prefixEnd_1129025 579732495942550418195215 := by
  unfold tailWord_1129025
  simp only [CollatzResearch.WordTrace]
  refine ⟨41178924734742721963756529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27452616489828481309171019 41178924734742721963756529)
  ·
    refine ⟨30884193551057041472817397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41178924734742721963756529 30884193551057041472817397)
    ·
      refine ⟨2895393145411597638076631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30884193551057041472817397 2895393145411597638076631)
      ·
        refine ⟨4343089718117396457114947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2895393145411597638076631 4343089718117396457114947)
        ·
          refine ⟨6514634577176094685672421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343089718117396457114947 6514634577176094685672421)
          ·
            refine ⟨1221493983220517753563579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6514634577176094685672421 1221493983220517753563579)
            ·
              refine ⟨1832240974830776630345369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221493983220517753563579 1832240974830776630345369)
              ·
                refine ⟨1374180731123082472759027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832240974830776630345369 1374180731123082472759027)
                ·
                  refine ⟨2061271096684623709138541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374180731123082472759027 2061271096684623709138541)
                  ·
                    refine ⟨772976661256733890926953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061271096684623709138541 772976661256733890926953)
                    ·
                      refine ⟨579732495942550418195215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 772976661256733890926953 579732495942550418195215)
                      ·
                        rfl

theorem cell23_1129025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1129025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129025 prefixEnd_1129025 := by exact prefixLift 1129025
  have htrace : WordTrace (prefixWord ++ tailWord_1129025) baseStart_1129025 baseEnd_1129025 := by
    simpa [prefixWord, tailWord_1129025, baseEnd_1129025] using wordTrace_append hprefix tailTrace_1129025
  have hstable : (prefixWord ++ tailWord_1129025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129025).length < 2 ^ (prefixWord ++ tailWord_1129025).sum := by decide
  have hdescent : baseEnd_1129025 < baseStart_1129025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129027 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 7]
def baseStart_1129027 : Nat := 118140960795 + 1129027 * 2 ^ 59
def prefixEnd_1129027 : Nat := 4983230072969 + 3 ^ 40 * 1129027 * 2
def baseEnd_1129027 : Nat := 64414835878206601152245

theorem tailTrace_1129027 : CollatzResearch.WordTrace tailWord_1129027 prefixEnd_1129027 64414835878206601152245 := by
  unfold tailWord_1129027
  simp only [CollatzResearch.WordTrace]
  refine ⟨41178997680735476305329335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27452665120490317536886223 41178997680735476305329335)
  ·
    refine ⟨61768496521103214457994003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41178997680735476305329335 61768496521103214457994003)
    ·
      refine ⟨92652744781654821686991005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61768496521103214457994003 92652744781654821686991005)
      ·
        refine ⟨34744779293120558132621627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92652744781654821686991005 34744779293120558132621627)
        ·
          refine ⟨52117168939680837198932441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34744779293120558132621627 52117168939680837198932441)
          ·
            refine ⟨39087876704760627899199331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52117168939680837198932441 39087876704760627899199331)
            ·
              refine ⟨58631815057140941848798997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39087876704760627899199331 58631815057140941848798997)
              ·
                refine ⟨2748366330803481649162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58631815057140941848798997 2748366330803481649162453)
                ·
                  refine ⟨64414835878206601152245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2748366330803481649162453 64414835878206601152245)
                  ·
                    rfl

theorem cell23_1129027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 7].length) (baseStart_1129027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129027 prefixEnd_1129027 := by exact prefixLift 1129027
  have htrace : WordTrace (prefixWord ++ tailWord_1129027) baseStart_1129027 baseEnd_1129027 := by
    simpa [prefixWord, tailWord_1129027, baseEnd_1129027] using wordTrace_append hprefix tailTrace_1129027
  have hstable : (prefixWord ++ tailWord_1129027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129027).length < 2 ^ (prefixWord ++ tailWord_1129027).sum := by decide
  have hdescent : baseEnd_1129027 < baseStart_1129027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129067 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_1129067 : Nat := 118140960795 + 1129067 * 2 ^ 59
def prefixEnd_1129067 : Nat := 4983230072969 + 3 ^ 40 * 1129067 * 2
def baseEnd_1129067 : Nat := 579754062130039253870021

theorem tailTrace_1129067 : CollatzResearch.WordTrace tailWord_1129067 prefixEnd_1129067 579754062130039253870021 := by
  unfold tailWord_1129067
  simp only [CollatzResearch.WordTrace]
  refine ⟨41180456600590563136785455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27453637733727042091190303 41180456600590563136785455)
  ·
    refine ⟨61770684900885844705178183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41180456600590563136785455 61770684900885844705178183)
    ·
      refine ⟨92656027351328767057767275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61770684900885844705178183 92656027351328767057767275)
      ·
        refine ⟨138984041026993150586650913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92656027351328767057767275 138984041026993150586650913)
        ·
          refine ⟨104238030770244862939988185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138984041026993150586650913 104238030770244862939988185)
          ·
            refine ⟨78178523077683647204991139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104238030770244862939988185 78178523077683647204991139)
            ·
              refine ⟨117267784616525470807486709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78178523077683647204991139 117267784616525470807486709)
              ·
                refine ⟨10993854807799262888201879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117267784616525470807486709 10993854807799262888201879)
                ·
                  refine ⟨16490782211698894332302819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10993854807799262888201879 16490782211698894332302819)
                  ·
                    refine ⟨24736173317548341498454229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16490782211698894332302819 24736173317548341498454229)
                    ·
                      refine ⟨579754062130039253870021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24736173317548341498454229 579754062130039253870021)
                      ·
                        rfl

theorem cell23_1129067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_1129067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129067 prefixEnd_1129067 := by exact prefixLift 1129067
  have htrace : WordTrace (prefixWord ++ tailWord_1129067) baseStart_1129067 baseEnd_1129067 := by
    simpa [prefixWord, tailWord_1129067, baseEnd_1129067] using wordTrace_append hprefix tailTrace_1129067
  have hstable : (prefixWord ++ tailWord_1129067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129067).length < 2 ^ (prefixWord ++ tailWord_1129067).sum := by decide
  have hdescent : baseEnd_1129067 < baseStart_1129067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129087 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 10]
def baseStart_1129087 : Nat := 118140960795 + 1129087 * 2 ^ 59
def prefixEnd_1129087 : Nat := 4983230072969 + 3 ^ 40 * 1129087 * 2
def baseEnd_1129087 : Nat := 193254777247709725206643

theorem tailTrace_1129087 : CollatzResearch.WordTrace tailWord_1129087 prefixEnd_1129087 193254777247709725206643 := by
  unfold tailWord_1129087
  simp only [CollatzResearch.WordTrace]
  refine ⟨41181186060518106552513515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27454124040345404368342343 41181186060518106552513515)
  ·
    refine ⟨61771779090777159828770273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41181186060518106552513515 61771779090777159828770273)
    ·
      refine ⟨46328834318082869871577705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61771779090777159828770273 46328834318082869871577705)
      ·
        refine ⟨34746625738562152403683279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46328834318082869871577705 34746625738562152403683279)
        ·
          refine ⟨52119938607843228605524919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34746625738562152403683279 52119938607843228605524919)
          ·
            refine ⟨78179907911764842908287379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52119938607843228605524919 78179907911764842908287379)
            ·
              refine ⟨117269861867647264362431069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78179907911764842908287379 117269861867647264362431069)
              ·
                refine ⟨43976198200367724135911651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117269861867647264362431069 43976198200367724135911651)
                ·
                  refine ⟨65964297300551586203867477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43976198200367724135911651 65964297300551586203867477)
                  ·
                    refine ⟨193254777247709725206643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 65964297300551586203867477 193254777247709725206643)
                    ·
                      rfl

theorem cell23_1129087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_1129087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129087 prefixEnd_1129087 := by exact prefixLift 1129087
  have htrace : WordTrace (prefixWord ++ tailWord_1129087) baseStart_1129087 baseEnd_1129087 := by
    simpa [prefixWord, tailWord_1129087, baseEnd_1129087] using wordTrace_append hprefix tailTrace_1129087
  have hstable : (prefixWord ++ tailWord_1129087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129087).length < 2 ^ (prefixWord ++ tailWord_1129087).sum := by decide
  have hdescent : baseEnd_1129087 < baseStart_1129087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129111 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_1129111 : Nat := 118140960795 + 1129111 * 2 ^ 59
def prefixEnd_1129111 : Nat := 4983230072969 + 3 ^ 40 * 1129111 * 2
def baseEnd_1129111 : Nat := 579776655278837081719819

theorem tailTrace_1129111 : CollatzResearch.WordTrace tailWord_1129111 prefixEnd_1129111 579776655278837081719819 := by
  unfold tailWord_1129111
  simp only [CollatzResearch.WordTrace]
  refine ⟨41182061412431158651387187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27454707608287439100924791 41182061412431158651387187)
  ·
    refine ⟨61773092118646737977080781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41182061412431158651387187 61773092118646737977080781)
    ·
      refine ⟨23164909544492526741405293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61773092118646737977080781 23164909544492526741405293)
      ·
        refine ⟨8686841079184697528026985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23164909544492526741405293 8686841079184697528026985)
        ·
          refine ⟨6515130809388523146020239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8686841079184697528026985 6515130809388523146020239)
          ·
            refine ⟨9772696214082784719030359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515130809388523146020239 9772696214082784719030359)
            ·
              refine ⟨14659044321124177078545539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9772696214082784719030359 14659044321124177078545539)
              ·
                refine ⟨21988566481686265617818309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14659044321124177078545539 21988566481686265617818309)
                ·
                  refine ⟨4122856215316174803340933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21988566481686265617818309 4122856215316174803340933)
                  ·
                    refine ⟨773035540371782775626425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122856215316174803340933 773035540371782775626425)
                    ·
                      refine ⟨579776655278837081719819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773035540371782775626425 579776655278837081719819)
                      ·
                        rfl

theorem cell23_1129111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_1129111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129111 prefixEnd_1129111 := by exact prefixLift 1129111
  have htrace : WordTrace (prefixWord ++ tailWord_1129111) baseStart_1129111 baseEnd_1129111 := by
    simpa [prefixWord, tailWord_1129111, baseEnd_1129111] using wordTrace_append hprefix tailTrace_1129111
  have hstable : (prefixWord ++ tailWord_1129111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129111).length < 2 ^ (prefixWord ++ tailWord_1129111).sum := by decide
  have hdescent : baseEnd_1129111 < baseStart_1129111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129124 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1129124 : Nat := 118140960795 + 1129124 * 2 ^ 59
def prefixEnd_1129124 : Nat := 4983230072969 + 3 ^ 40 * 1129124 * 2
def baseEnd_1129124 : Nat := 579783330527345530857259

theorem tailTrace_1129124 : CollatzResearch.WordTrace tailWord_1129124 prefixEnd_1129124 579783330527345530857259 := by
  unfold tailWord_1129124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591267780692030935805213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27455023707589374581073617 20591267780692030935805213)
  ·
    refine ⟨7721725417759511600926955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20591267780692030935805213 7721725417759511600926955)
    ·
      refine ⟨11582588126639267401390433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7721725417759511600926955 11582588126639267401390433)
      ·
        refine ⟨8686941094979450551042825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11582588126639267401390433 8686941094979450551042825)
        ·
          refine ⟨6515205821234587913282119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8686941094979450551042825 6515205821234587913282119)
          ·
            refine ⟨9772808731851881869923179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515205821234587913282119 9772808731851881869923179)
            ·
              refine ⟨14659213097777822804884769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9772808731851881869923179 14659213097777822804884769)
              ·
                refine ⟨10994409823333367103663577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14659213097777822804884769 10994409823333367103663577)
                ·
                  refine ⟨8245807367500025327747683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10994409823333367103663577 8245807367500025327747683)
                  ·
                    refine ⟨12368711051250037991621525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8245807367500025327747683 12368711051250037991621525)
                    ·
                      refine ⟨579783330527345530857259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12368711051250037991621525 579783330527345530857259)
                      ·
                        rfl

theorem cell23_1129124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1129124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129124 prefixEnd_1129124 := by exact prefixLift 1129124
  have htrace : WordTrace (prefixWord ++ tailWord_1129124) baseStart_1129124 baseEnd_1129124 := by
    simpa [prefixWord, tailWord_1129124, baseEnd_1129124] using wordTrace_append hprefix tailTrace_1129124
  have hstable : (prefixWord ++ tailWord_1129124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129124).length < 2 ^ (prefixWord ++ tailWord_1129124).sum := by decide
  have hdescent : baseEnd_1129124 < baseStart_1129124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129172 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1129172 : Nat := 118140960795 + 1129172 * 2 ^ 59
def prefixEnd_1129172 : Nat := 4983230072969 + 3 ^ 40 * 1129172 * 2
def baseEnd_1129172 : Nat := 193269325866253781019013

theorem tailTrace_1129172 : CollatzResearch.WordTrace tailWord_1129172 prefixEnd_1129172 193269325866253781019013 := by
  unfold tailWord_1129172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20592143132605083034678885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27456190843473444046238513 20592143132605083034678885)
  ·
    refine ⟨3861026837363453069002291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20592143132605083034678885 3861026837363453069002291)
    ·
      refine ⟨5791540256045179603503437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861026837363453069002291 5791540256045179603503437)
      ·
        refine ⟨2171827596016942351313789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5791540256045179603503437 2171827596016942351313789)
        ·
          refine ⟨814435348506353381742671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2171827596016942351313789 814435348506353381742671)
          ·
            refine ⟨1221653022759530072614007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814435348506353381742671 1221653022759530072614007)
            ·
              refine ⟨1832479534139295108921011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221653022759530072614007 1832479534139295108921011)
              ·
                refine ⟨2748719301208942663381517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832479534139295108921011 2748719301208942663381517)
                ·
                  refine ⟨1030769737953353498768069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2748719301208942663381517 1030769737953353498768069)
                  ·
                    refine ⟨193269325866253781019013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1030769737953353498768069 193269325866253781019013)
                    ·
                      rfl

theorem cell23_1129172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1129172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129172 prefixEnd_1129172 := by exact prefixLift 1129172
  have htrace : WordTrace (prefixWord ++ tailWord_1129172) baseStart_1129172 baseEnd_1129172 := by
    simpa [prefixWord, tailWord_1129172, baseEnd_1129172] using wordTrace_append hprefix tailTrace_1129172
  have hstable : (prefixWord ++ tailWord_1129172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129172).length < 2 ^ (prefixWord ++ tailWord_1129172).sum := by decide
  have hdescent : baseEnd_1129172 < baseStart_1129172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129184 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1129184 : Nat := 118140960795 + 1129184 * 2 ^ 59
def prefixEnd_1129184 : Nat := 4983230072969 + 3 ^ 40 * 1129184 * 2
def baseEnd_1129184 : Nat := 579814139366615296106983

theorem tailTrace_1129184 : CollatzResearch.WordTrace tailWord_1129184 prefixEnd_1129184 579814139366615296106983 := by
  unfold tailWord_1129184
  simp only [CollatzResearch.WordTrace]
  refine ⟨20592361970583346059397303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27456482627444461412529737 20592361970583346059397303)
  ·
    refine ⟨30888542955875019089095955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20592361970583346059397303 30888542955875019089095955)
    ·
      refine ⟨46332814433812528633643933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30888542955875019089095955 46332814433812528633643933)
      ·
        refine ⟨17374805412679698237616475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46332814433812528633643933 17374805412679698237616475)
        ·
          refine ⟨26062208119019547356424713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17374805412679698237616475 26062208119019547356424713)
          ·
            refine ⟨19546656089264660517318535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26062208119019547356424713 19546656089264660517318535)
            ·
              refine ⟨29319984133896990775977803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19546656089264660517318535 29319984133896990775977803)
              ·
                refine ⟨43979976200845486163966705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29319984133896990775977803 43979976200845486163966705)
                ·
                  refine ⟨32984982150634114622975029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43979976200845486163966705 32984982150634114622975029)
                  ·
                    refine ⟨3092342076621948245903909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32984982150634114622975029 3092342076621948245903909)
                    ·
                      refine ⟨579814139366615296106983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3092342076621948245903909 579814139366615296106983)
                      ·
                        rfl

theorem cell23_1129184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1129184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129184 prefixEnd_1129184 := by exact prefixLift 1129184
  have htrace : WordTrace (prefixWord ++ tailWord_1129184) baseStart_1129184 baseEnd_1129184 := by
    simpa [prefixWord, tailWord_1129184, baseEnd_1129184] using wordTrace_append hprefix tailTrace_1129184
  have hstable : (prefixWord ++ tailWord_1129184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129184).length < 2 ^ (prefixWord ++ tailWord_1129184).sum := by decide
  have hdescent : baseEnd_1129184 < baseStart_1129184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129198 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1129198 : Nat := 118140960795 + 1129198 * 2 ^ 59
def prefixEnd_1129198 : Nat := 4983230072969 + 3 ^ 40 * 1129198 * 2
def baseEnd_1129198 : Nat := 193273776031926080443973

theorem tailTrace_1129198 : CollatzResearch.WordTrace tailWord_1129198 prefixEnd_1129198 193273776031926080443973 := by
  unfold tailWord_1129198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5148154320389496563725531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27456823042077315006536165 5148154320389496563725531)
  ·
    refine ⟨7722231480584244845588297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5148154320389496563725531 7722231480584244845588297)
    ·
      refine ⟨5791673610438183634191223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7722231480584244845588297 5791673610438183634191223)
      ·
        refine ⟨8687510415657275451286835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791673610438183634191223 8687510415657275451286835)
        ·
          refine ⟨13031265623485913176930253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8687510415657275451286835 13031265623485913176930253)
          ·
            refine ⟨4886724608807217441348845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13031265623485913176930253 4886724608807217441348845)
            ·
              refine ⟨1832521728302706540505817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4886724608807217441348845 1832521728302706540505817)
              ·
                refine ⟨1374391296227029905379363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832521728302706540505817 1374391296227029905379363)
                ·
                  refine ⟨2061586944340544858069045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374391296227029905379363 2061586944340544858069045)
                  ·
                    refine ⟨193273776031926080443973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2061586944340544858069045 193273776031926080443973)
                    ·
                      rfl

theorem cell23_1129198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1129198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129198 prefixEnd_1129198 := by exact prefixLift 1129198
  have htrace : WordTrace (prefixWord ++ tailWord_1129198) baseStart_1129198 baseEnd_1129198 := by
    simpa [prefixWord, tailWord_1129198, baseEnd_1129198] using wordTrace_append hprefix tailTrace_1129198
  have hstable : (prefixWord ++ tailWord_1129198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129198).length < 2 ^ (prefixWord ++ tailWord_1129198).sum := by decide
  have hdescent : baseEnd_1129198 < baseStart_1129198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129201 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_1129201 : Nat := 118140960795 + 1129201 * 2 ^ 59
def prefixEnd_1129201 : Nat := 4983230072969 + 3 ^ 40 * 1129201 * 2
def baseEnd_1129201 : Nat := 579822868537741729594405

theorem tailTrace_1129201 : CollatzResearch.WordTrace tailWord_1129201 prefixEnd_1129201 579822868537741729594405 := by
  unfold tailWord_1129201
  simp only [CollatzResearch.WordTrace]
  refine ⟨41185343982105104022163457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27456895988070069348108971 41185343982105104022163457)
  ·
    refine ⟨30889007986578828016622593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41185343982105104022163457 30889007986578828016622593)
    ·
      refine ⟨23166755989934121012466945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30889007986578828016622593 23166755989934121012466945)
      ·
        refine ⟨17375066992450590759350209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23166755989934121012466945 17375066992450590759350209)
        ·
          refine ⟨13031300244337943069512657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17375066992450590759350209 13031300244337943069512657)
          ·
            refine ⟨9773475183253457302134493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13031300244337943069512657 9773475183253457302134493)
            ·
              refine ⟨3665053193720046488300435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9773475183253457302134493 3665053193720046488300435)
              ·
                refine ⟨5497579790580069732450653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665053193720046488300435 5497579790580069732450653)
                ·
                  refine ⟨2061592421467526149668995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5497579790580069732450653 2061592421467526149668995)
                  ·
                    refine ⟨3092388632201289224503493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2061592421467526149668995 3092388632201289224503493)
                    ·
                      refine ⟨579822868537741729594405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3092388632201289224503493 579822868537741729594405)
                      ·
                        rfl

theorem cell23_1129201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_1129201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129201 prefixEnd_1129201 := by exact prefixLift 1129201
  have htrace : WordTrace (prefixWord ++ tailWord_1129201) baseStart_1129201 baseEnd_1129201 := by
    simpa [prefixWord, tailWord_1129201, baseEnd_1129201] using wordTrace_append hprefix tailTrace_1129201
  have hstable : (prefixWord ++ tailWord_1129201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129201).length < 2 ^ (prefixWord ++ tailWord_1129201).sum := by decide
  have hdescent : baseEnd_1129201 < baseStart_1129201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129224 : List Nat := [2, 1, 3, 2, 2, 13]
def baseStart_1129224 : Nat := 118140960795 + 1129224 * 2 ^ 59
def prefixEnd_1129224 : Nat := 4983230072969 + 3 ^ 40 * 1129224 * 2
def baseEnd_1129224 : Nat := 2386150940711091109493

theorem tailTrace_1129224 : CollatzResearch.WordTrace tailWord_1129224 prefixEnd_1129224 2386150940711091109493 := by
  unfold tailWord_1129224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20593091430510889475125363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27457455240681185966833817 20593091430510889475125363)
  ·
    refine ⟨30889637145766334212688045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20593091430510889475125363 30889637145766334212688045)
    ·
      refine ⟨11583613929662375329758017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30889637145766334212688045 11583613929662375329758017)
      ·
        refine ⟨8687710447246781497318513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11583613929662375329758017 8687710447246781497318513)
        ·
          refine ⟨6515782835435086122988885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8687710447246781497318513 6515782835435086122988885)
          ·
            refine ⟨2386150940711091109493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6515782835435086122988885 2386150940711091109493)
            ·
              rfl

theorem cell23_1129224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 13].length) (baseStart_1129224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129224 prefixEnd_1129224 := by exact prefixLift 1129224
  have htrace : WordTrace (prefixWord ++ tailWord_1129224) baseStart_1129224 baseEnd_1129224 := by
    simpa [prefixWord, tailWord_1129224, baseEnd_1129224] using wordTrace_append hprefix tailTrace_1129224
  have hstable : (prefixWord ++ tailWord_1129224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129224).length < 2 ^ (prefixWord ++ tailWord_1129224).sum := by decide
  have hdescent : baseEnd_1129224 < baseStart_1129224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129245 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1129245 : Nat := 118140960795 + 1129245 * 2 ^ 59
def prefixEnd_1129245 : Nat := 4983230072969 + 3 ^ 40 * 1129245 * 2
def baseEnd_1129245 : Nat := 193281820562179852481401

theorem tailTrace_1129245 : CollatzResearch.WordTrace tailWord_1129245 prefixEnd_1129245 193281820562179852481401 := by
  unfold tailWord_1129245
  simp only [CollatzResearch.WordTrace]
  refine ⟨41186948793945699536765189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27457965862630466357843459 41186948793945699536765189)
  ·
    refine ⟨7722552898864818663143473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41186948793945699536765189 7722552898864818663143473)
    ·
      refine ⟨5791914674148613997357605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7722552898864818663143473 5791914674148613997357605)
      ·
        refine ⟨1085984001402865124504551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5791914674148613997357605 1085984001402865124504551)
        ·
          refine ⟨1628976002104297686756827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085984001402865124504551 1628976002104297686756827)
          ·
            refine ⟨2443464003156446530135241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628976002104297686756827 2443464003156446530135241)
            ·
              refine ⟨1832598002367334897601431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443464003156446530135241 1832598002367334897601431)
              ·
                refine ⟨2748897003551002346402147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832598002367334897601431 2748897003551002346402147)
                ·
                  refine ⟨4123345505326503519603221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748897003551002346402147 4123345505326503519603221)
                  ·
                    refine ⟨193281820562179852481401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4123345505326503519603221 193281820562179852481401)
                    ·
                      rfl

theorem cell23_1129245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1129245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129245 prefixEnd_1129245 := by exact prefixLift 1129245
  have htrace : WordTrace (prefixWord ++ tailWord_1129245) baseStart_1129245 baseEnd_1129245 := by
    simpa [prefixWord, tailWord_1129245, baseEnd_1129245] using wordTrace_append hprefix tailTrace_1129245
  have hstable : (prefixWord ++ tailWord_1129245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129245).length < 2 ^ (prefixWord ++ tailWord_1129245).sum := by decide
  have hdescent : baseEnd_1129245 < baseStart_1129245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129248 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1129248 : Nat := 118140960795 + 1129248 * 2 ^ 59
def prefixEnd_1129248 : Nat := 4983230072969 + 3 ^ 40 * 1129248 * 2
def baseEnd_1129248 : Nat := 579847002128503045706689

theorem tailTrace_1129248 : CollatzResearch.WordTrace tailWord_1129248 prefixEnd_1129248 579847002128503045706689 := by
  unfold tailWord_1129248
  simp only [CollatzResearch.WordTrace]
  refine ⟨20593529106467415524562199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27458038808623220699416265 20593529106467415524562199)
  ·
    refine ⟨30890293659701123286843299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20593529106467415524562199 30890293659701123286843299)
    ·
      refine ⟨46335440489551684930264949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30890293659701123286843299 46335440489551684930264949)
      ·
        refine ⟨4343947545895470462212339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46335440489551684930264949 4343947545895470462212339)
        ·
          refine ⟨6515921318843205693318509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343947545895470462212339 6515921318843205693318509)
          ·
            refine ⟨2443470494566202134994441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6515921318843205693318509 2443470494566202134994441)
            ·
              refine ⟨1832602870924651601245831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443470494566202134994441 1832602870924651601245831)
              ·
                refine ⟨2748904306386977401868747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832602870924651601245831 2748904306386977401868747)
                ·
                  refine ⟨4123356459580466102803121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748904306386977401868747 4123356459580466102803121)
                  ·
                    refine ⟨3092517344685349577102341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4123356459580466102803121 3092517344685349577102341)
                    ·
                      refine ⟨579847002128503045706689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3092517344685349577102341 579847002128503045706689)
                      ·
                        rfl

theorem cell23_1129248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1129248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129248 prefixEnd_1129248 := by exact prefixLift 1129248
  have htrace : WordTrace (prefixWord ++ tailWord_1129248) baseStart_1129248 baseEnd_1129248 := by
    simpa [prefixWord, tailWord_1129248, baseEnd_1129248] using wordTrace_append hprefix tailTrace_1129248
  have hstable : (prefixWord ++ tailWord_1129248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129248).length < 2 ^ (prefixWord ++ tailWord_1129248).sum := by decide
  have hdescent : baseEnd_1129248 < baseStart_1129248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129252 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_1129252 : Nat := 118140960795 + 1129252 * 2 ^ 59
def prefixEnd_1129252 : Nat := 4983230072969 + 3 ^ 40 * 1129252 * 2
def baseEnd_1129252 : Nat := 579849056051121030056671

theorem tailTrace_1129252 : CollatzResearch.WordTrace tailWord_1129252 prefixEnd_1129252 579849056051121030056671 := by
  unfold tailWord_1129252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20593602052460169866135005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27458136069946893154846673 20593602052460169866135005)
  ·
    refine ⟨7722600769672563699800627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20593602052460169866135005 7722600769672563699800627)
    ·
      refine ⟨11583901154508845549700941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7722600769672563699800627 11583901154508845549700941)
      ·
        refine ⟨4343962932940817081137853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11583901154508845549700941 4343962932940817081137853)
        ·
          refine ⟨1628986099852806405426695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4343962932940817081137853 1628986099852806405426695)
          ·
            refine ⟨2443479149779209608140043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628986099852806405426695 2443479149779209608140043)
            ·
              refine ⟨3665218724668814412210065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443479149779209608140043 3665218724668814412210065)
              ·
                refine ⟨2748914043501610809157549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665218724668814412210065 2748914043501610809157549)
                ·
                  refine ⟨1030842766313104053434081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2748914043501610809157549 1030842766313104053434081)
                  ·
                    refine ⟨773132074734828040075561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1030842766313104053434081 773132074734828040075561)
                    ·
                      refine ⟨579849056051121030056671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773132074734828040075561 579849056051121030056671)
                      ·
                        rfl

theorem cell23_1129252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_1129252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129252 prefixEnd_1129252 := by exact prefixLift 1129252
  have htrace : WordTrace (prefixWord ++ tailWord_1129252) baseStart_1129252 baseEnd_1129252 := by
    simpa [prefixWord, tailWord_1129252, baseEnd_1129252] using wordTrace_append hprefix tailTrace_1129252
  have hstable : (prefixWord ++ tailWord_1129252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129252).length < 2 ^ (prefixWord ++ tailWord_1129252).sum := by decide
  have hdescent : baseEnd_1129252 < baseStart_1129252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129269 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_1129269 : Nat := 118140960795 + 1129269 * 2 ^ 59
def prefixEnd_1129269 : Nat := 4983230072969 + 3 ^ 40 * 1129269 * 2
def baseEnd_1129269 : Nat := 579857785222247463544093

theorem tailTrace_1129269 : CollatzResearch.WordTrace tailWord_1129269 prefixEnd_1129269 579857785222247463544093 := by
  unfold tailWord_1129269
  simp only [CollatzResearch.WordTrace]
  refine ⟨41187824145858751635638861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27458549430572501090425907 41187824145858751635638861)
  ·
    refine ⟨15445434054697031863364573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41187824145858751635638861 15445434054697031863364573)
    ·
      refine ⟨5792037770511386948761715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15445434054697031863364573 5792037770511386948761715)
      ·
        refine ⟨8688056655767080423142573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792037770511386948761715 8688056655767080423142573)
        ·
          refine ⟨3258021245912655158678465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8688056655767080423142573 3258021245912655158678465)
          ·
            refine ⟨2443515934434491369008849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3258021245912655158678465 2443515934434491369008849)
            ·
              refine ⟨1832636950825868526756637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443515934434491369008849 1832636950825868526756637)
              ·
                refine ⟨687238856559700697533739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1832636950825868526756637 687238856559700697533739)
                ·
                  refine ⟨1030858284839551046300609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687238856559700697533739 1030858284839551046300609)
                  ·
                    refine ⟨773143713629663284725457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1030858284839551046300609 773143713629663284725457)
                    ·
                      refine ⟨579857785222247463544093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773143713629663284725457 579857785222247463544093)
                      ·
                        rfl

theorem cell23_1129269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_1129269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129269 prefixEnd_1129269 := by exact prefixLift 1129269
  have htrace : WordTrace (prefixWord ++ tailWord_1129269) baseStart_1129269 baseEnd_1129269 := by
    simpa [prefixWord, tailWord_1129269, baseEnd_1129269] using wordTrace_append hprefix tailTrace_1129269
  have hstable : (prefixWord ++ tailWord_1129269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129269).length < 2 ^ (prefixWord ++ tailWord_1129269).sum := by decide
  have hdescent : baseEnd_1129269 < baseStart_1129269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129286 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1129286 : Nat := 118140960795 + 1129286 * 2 ^ 59
def prefixEnd_1129286 : Nat := 4983230072969 + 3 ^ 40 * 1129286 * 2
def baseEnd_1129286 : Nat := 579866514393373897031515

theorem tailTrace_1129286 : CollatzResearch.WordTrace tailWord_1129286 prefixEnd_1129286 579866514393373897031515 := by
  unfold tailWord_1129286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1287138880837411360593991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27458962791198109026005141 1287138880837411360593991)
  ·
    refine ⟨1930708321256117040890987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1287138880837411360593991 1930708321256117040890987)
    ·
      refine ⟨2896062481884175561336481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1930708321256117040890987 2896062481884175561336481)
      ·
        refine ⟨2172046861413131671002361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2896062481884175561336481 2172046861413131671002361)
        ·
          refine ⟨1629035146059848753251771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172046861413131671002361 1629035146059848753251771)
          ·
            refine ⟨2443552719089773129877657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629035146059848753251771 2443552719089773129877657)
            ·
              refine ⟨1832664539317329847408243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443552719089773129877657 1832664539317329847408243)
              ·
                refine ⟨2748996808975994771112365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832664539317329847408243 2748996808975994771112365)
                ·
                  refine ⟨1030873803365998039167137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2748996808975994771112365 1030873803365998039167137)
                  ·
                    refine ⟨773155352524498529375353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1030873803365998039167137 773155352524498529375353)
                    ·
                      refine ⟨579866514393373897031515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773155352524498529375353 579866514393373897031515)
                      ·
                        rfl

theorem cell23_1129286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1129286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129286 prefixEnd_1129286 := by exact prefixLift 1129286
  have htrace : WordTrace (prefixWord ++ tailWord_1129286) baseStart_1129286 baseEnd_1129286 := by
    simpa [prefixWord, tailWord_1129286, baseEnd_1129286] using wordTrace_append hprefix tailTrace_1129286
  have hstable : (prefixWord ++ tailWord_1129286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129286).length < 2 ^ (prefixWord ++ tailWord_1129286).sum := by decide
  have hdescent : baseEnd_1129286 < baseStart_1129286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129301 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1129301 : Nat := 118140960795 + 1129301 * 2 ^ 59
def prefixEnd_1129301 : Nat := 4983230072969 + 3 ^ 40 * 1129301 * 2
def baseEnd_1129301 : Nat := 193291405534397112781315

theorem tailTrace_1129301 : CollatzResearch.WordTrace tailWord_1129301 prefixEnd_1129301 193291405534397112781315 := by
  unfold tailWord_1129301
  simp only [CollatzResearch.WordTrace]
  refine ⟨41188991281742821100803757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27459327521161880733869171 41188991281742821100803757)
  ·
    refine ⟨15445871730653557912801409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41188991281742821100803757 15445871730653557912801409)
    ·
      refine ⟨11584403797990168434601057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15445871730653557912801409 11584403797990168434601057)
      ·
        refine ⟨8688302848492626325950793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11584403797990168434601057 8688302848492626325950793)
        ·
          refine ⟨6516227136369469744463095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8688302848492626325950793 6516227136369469744463095)
          ·
            refine ⟨9774340704554204616694643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516227136369469744463095 9774340704554204616694643)
            ·
              refine ⟨14661511056831306925041965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774340704554204616694643 14661511056831306925041965)
              ·
                refine ⟨5498066646311740096890737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14661511056831306925041965 5498066646311740096890737)
                ·
                  refine ⟨4123549984733805072668053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498066646311740096890737 4123549984733805072668053)
                  ·
                    refine ⟨193291405534397112781315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4123549984733805072668053 193291405534397112781315)
                    ·
                      rfl

theorem cell23_1129301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1129301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129301 prefixEnd_1129301 := by exact prefixLift 1129301
  have htrace : WordTrace (prefixWord ++ tailWord_1129301) baseStart_1129301 baseEnd_1129301 := by
    simpa [prefixWord, tailWord_1129301, baseEnd_1129301] using wordTrace_append hprefix tailTrace_1129301
  have hstable : (prefixWord ++ tailWord_1129301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129301).length < 2 ^ (prefixWord ++ tailWord_1129301).sum := by decide
  have hdescent : baseEnd_1129301 < baseStart_1129301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129311 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1129311 : Nat := 118140960795 + 1129311 * 2 ^ 59
def prefixEnd_1129311 : Nat := 4983230072969 + 3 ^ 40 * 1129311 * 2
def baseEnd_1129311 : Nat := 579879351409736299218899

theorem tailTrace_1129311 : CollatzResearch.WordTrace tailWord_1129311 prefixEnd_1129311 579879351409736299218899 := by
  unfold tailWord_1129311
  simp only [CollatzResearch.WordTrace]
  refine ⟨41189356011706592808667787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27459570674471061872445191 41189356011706592808667787)
  ·
    refine ⟨61784034017559889213001681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41189356011706592808667787 61784034017559889213001681)
    ·
      refine ⟨46338025513169916909751261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61784034017559889213001681 46338025513169916909751261)
      ·
        refine ⟨17376759567438718841156723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46338025513169916909751261 17376759567438718841156723)
        ·
          refine ⟨26065139351158078261735085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17376759567438718841156723 26065139351158078261735085)
          ·
            refine ⟨9774427256684279348150657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26065139351158078261735085 9774427256684279348150657)
            ·
              refine ⟨7330820442513209511112993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9774427256684279348150657 7330820442513209511112993)
              ·
                refine ⟨5498115331884907133334745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7330820442513209511112993 5498115331884907133334745)
                ·
                  refine ⟨4123586498913680350001059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5498115331884907133334745 4123586498913680350001059)
                  ·
                    refine ⟨6185379748370520525001589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4123586498913680350001059 6185379748370520525001589)
                    ·
                      refine ⟨579879351409736299218899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6185379748370520525001589 579879351409736299218899)
                      ·
                        rfl

theorem cell23_1129311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1129311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129311 prefixEnd_1129311 := by exact prefixLift 1129311
  have htrace : WordTrace (prefixWord ++ tailWord_1129311) baseStart_1129311 baseEnd_1129311 := by
    simpa [prefixWord, tailWord_1129311, baseEnd_1129311] using wordTrace_append hprefix tailTrace_1129311
  have hstable : (prefixWord ++ tailWord_1129311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129311).length < 2 ^ (prefixWord ++ tailWord_1129311).sum := by decide
  have hdescent : baseEnd_1129311 < baseStart_1129311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129361 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_1129361 : Nat := 118140960795 + 1129361 * 2 ^ 59
def prefixEnd_1129361 : Nat := 4983230072969 + 3 ^ 40 * 1129361 * 2
def baseEnd_1129361 : Nat := 193301675147487034531223

theorem tailTrace_1129361 : CollatzResearch.WordTrace tailWord_1129361 prefixEnd_1129361 193301675147487034531223 := by
  unfold tailWord_1129361
  simp only [CollatzResearch.WordTrace]
  refine ⟨41191179661525451347987937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27460786441016967565325291 41191179661525451347987937)
  ·
    refine ⟨30893384746144088510990953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41191179661525451347987937 30893384746144088510990953)
    ·
      refine ⟨23170038559608066383243215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30893384746144088510990953 23170038559608066383243215)
      ·
        refine ⟨34755057839412099574864823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23170038559608066383243215 34755057839412099574864823)
        ·
          refine ⟨52132586759118149362297235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34755057839412099574864823 52132586759118149362297235)
          ·
            refine ⟨78198880138677224043445853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52132586759118149362297235 78198880138677224043445853)
            ·
              refine ⟨29324580052003959016292195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78198880138677224043445853 29324580052003959016292195)
              ·
                refine ⟨43986870078005938524438293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29324580052003959016292195 43986870078005938524438293)
                ·
                  refine ⟨2061884534906528368333045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43986870078005938524438293 2061884534906528368333045)
                  ·
                    refine ⟨193301675147487034531223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2061884534906528368333045 193301675147487034531223)
                    ·
                      rfl

theorem cell23_1129361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_1129361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129361 prefixEnd_1129361 := by exact prefixLift 1129361
  have htrace : WordTrace (prefixWord ++ tailWord_1129361) baseStart_1129361 baseEnd_1129361 := by
    simpa [prefixWord, tailWord_1129361, baseEnd_1129361] using wordTrace_append hprefix tailTrace_1129361
  have hstable : (prefixWord ++ tailWord_1129361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129361).length < 2 ^ (prefixWord ++ tailWord_1129361).sum := by decide
  have hdescent : baseEnd_1129361 < baseStart_1129361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129411 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1129411 : Nat := 118140960795 + 1129411 * 2 ^ 59
def prefixEnd_1129411 : Nat := 4983230072969 + 3 ^ 40 * 1129411 * 2
def baseEnd_1129411 : Nat := 579930699475185907968439

theorem tailTrace_1129411 : CollatzResearch.WordTrace tailWord_1129411 prefixEnd_1129411 579930699475185907968439 := by
  unfold tailWord_1129411
  simp only [CollatzResearch.WordTrace]
  refine ⟨41193003311344309887308087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27462002207562873258205391 41193003311344309887308087)
  ·
    refine ⟨61789504967016464830962131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41193003311344309887308087 61789504967016464830962131)
    ·
      refine ⟨92684257450524697246443197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61789504967016464830962131 92684257450524697246443197)
      ·
        refine ⟨34756596543946761467416199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92684257450524697246443197 34756596543946761467416199)
        ·
          refine ⟨52134894815920142201124299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34756596543946761467416199 52134894815920142201124299)
          ·
            refine ⟨78202342223880213301686449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52134894815920142201124299 78202342223880213301686449)
            ·
              refine ⟨58651756667910159976264837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78202342223880213301686449 58651756667910159976264837)
              ·
                refine ⟨10997204375233154995549657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58651756667910159976264837 10997204375233154995549657)
                ·
                  refine ⟨8247903281424866246662243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10997204375233154995549657 8247903281424866246662243)
                  ·
                    refine ⟨12371854922137299369993365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8247903281424866246662243 12371854922137299369993365)
                    ·
                      refine ⟨579930699475185907968439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12371854922137299369993365 579930699475185907968439)
                      ·
                        rfl

theorem cell23_1129411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1129411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129411 prefixEnd_1129411 := by exact prefixLift 1129411
  have htrace : WordTrace (prefixWord ++ tailWord_1129411) baseStart_1129411 baseEnd_1129411 := by
    simpa [prefixWord, tailWord_1129411, baseEnd_1129411] using wordTrace_append hprefix tailTrace_1129411
  have hstable : (prefixWord ++ tailWord_1129411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129411).length < 2 ^ (prefixWord ++ tailWord_1129411).sum := by decide
  have hdescent : baseEnd_1129411 < baseStart_1129411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129418 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1129418 : Nat := 118140960795 + 1129418 * 2 ^ 59
def prefixEnd_1129418 : Nat := 4983230072969 + 3 ^ 40 * 1129418 * 2
def baseEnd_1129418 : Nat := 579934293839767380580907

theorem tailTrace_1129418 : CollatzResearch.WordTrace tailWord_1129418 prefixEnd_1129418 579934293839767380580907 := by
  unfold tailWord_1129418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298314655579737520703227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27462172414879300055208605 10298314655579737520703227)
  ·
    refine ⟨15447471983369606281054841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10298314655579737520703227 15447471983369606281054841)
    ·
      refine ⟨11585603987527204710791131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15447471983369606281054841 11585603987527204710791131)
      ·
        refine ⟨17378405981290807066186697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11585603987527204710791131 17378405981290807066186697)
        ·
          refine ⟨13033804485968105299640023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17378405981290807066186697 13033804485968105299640023)
          ·
            refine ⟨19550706728952157949460035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13033804485968105299640023 19550706728952157949460035)
            ·
              refine ⟨29326060093428236924190053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19550706728952157949460035 29326060093428236924190053)
              ·
                refine ⟨5498636267517794423285635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29326060093428236924190053 5498636267517794423285635)
                ·
                  refine ⟨8247954401276691634928453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5498636267517794423285635 8247954401276691634928453)
                  ·
                    refine ⟨1546491450239379681549085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8247954401276691634928453 1546491450239379681549085)
                    ·
                      refine ⟨579934293839767380580907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1546491450239379681549085 579934293839767380580907)
                      ·
                        rfl

theorem cell23_1129418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1129418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129418 prefixEnd_1129418 := by exact prefixLift 1129418
  have htrace : WordTrace (prefixWord ++ tailWord_1129418) baseStart_1129418 baseEnd_1129418 := by
    simpa [prefixWord, tailWord_1129418, baseEnd_1129418] using wordTrace_append hprefix tailTrace_1129418
  have hstable : (prefixWord ++ tailWord_1129418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129418).length < 2 ^ (prefixWord ++ tailWord_1129418).sum := by decide
  have hdescent : baseEnd_1129418 < baseStart_1129418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129455 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 6]
def baseStart_1129455 : Nat := 118140960795 + 1129455 * 2 ^ 59
def prefixEnd_1129455 : Nat := 4983230072969 + 3 ^ 40 * 1129455 * 2
def baseEnd_1129455 : Nat := 64439254735998192868693

theorem tailTrace_1129455 : CollatzResearch.WordTrace tailWord_1129455 prefixEnd_1129455 64439254735998192868693 := by
  unfold tailWord_1129455
  simp only [CollatzResearch.WordTrace]
  refine ⟨41194608123184905401909819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27463072082123270267939879 41194608123184905401909819)
  ·
    refine ⟨61791912184777358102864729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41194608123184905401909819 61791912184777358102864729)
    ·
      refine ⟨46343934138583018577148547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61791912184777358102864729 46343934138583018577148547)
      ·
        refine ⟨69515901207874527865722821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46343934138583018577148547 69515901207874527865722821)
        ·
          refine ⟨13034231476476473974823029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69515901207874527865722821 13034231476476473974823029)
          ·
            refine ⟨1221959200919669435139659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13034231476476473974823029 1221959200919669435139659)
            ·
              refine ⟨1832938801379504152709489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221959200919669435139659 1832938801379504152709489)
              ·
                refine ⟨1374704101034628114532117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832938801379504152709489 1374704101034628114532117)
                ·
                  refine ⟨64439254735998192868693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1374704101034628114532117 64439254735998192868693)
                  ·
                    rfl

theorem cell23_1129455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 6].length) (baseStart_1129455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129455 prefixEnd_1129455 := by exact prefixLift 1129455
  have htrace : WordTrace (prefixWord ++ tailWord_1129455) baseStart_1129455 baseEnd_1129455 := by
    simpa [prefixWord, tailWord_1129455, baseEnd_1129455] using wordTrace_append hprefix tailTrace_1129455
  have hstable : (prefixWord ++ tailWord_1129455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129455).length < 2 ^ (prefixWord ++ tailWord_1129455).sum := by decide
  have hdescent : baseEnd_1129455 < baseStart_1129455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129482 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1129482 : Nat := 118140960795 + 1129482 * 2 ^ 59
def prefixEnd_1129482 : Nat := 4983230072969 + 3 ^ 40 * 1129482 * 2
def baseEnd_1129482 : Nat := 579967156601655130180613

theorem tailTrace_1129482 : CollatzResearch.WordTrace tailWord_1129482 prefixEnd_1129482 579967156601655130180613 := by
  unfold tailWord_1129482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298898223521772253285675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27463728596058059342095133 10298898223521772253285675)
  ·
    refine ⟨15448347335282658379928513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10298898223521772253285675 15448347335282658379928513)
    ·
      refine ⟨11586260501461993784946385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15448347335282658379928513 11586260501461993784946385)
      ·
        refine ⟨8689695376096495338709789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11586260501461993784946385 8689695376096495338709789)
        ·
          refine ⟨3258635766036185752016171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8689695376096495338709789 3258635766036185752016171)
          ·
            refine ⟨4887953649054278628024257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258635766036185752016171 4887953649054278628024257)
            ·
              refine ⟨3665965236790708971018193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4887953649054278628024257 3665965236790708971018193)
              ·
                refine ⟨2749473927593031728263645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3665965236790708971018193 2749473927593031728263645)
                ·
                  refine ⟨1031052722847386898098867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2749473927593031728263645 1031052722847386898098867)
                  ·
                    refine ⟨1546579084271080347148301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1031052722847386898098867 1546579084271080347148301)
                    ·
                      refine ⟨579967156601655130180613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1546579084271080347148301 579967156601655130180613)
                      ·
                        rfl

theorem cell23_1129482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1129482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129482 prefixEnd_1129482 := by exact prefixLift 1129482
  have htrace : WordTrace (prefixWord ++ tailWord_1129482) baseStart_1129482 baseEnd_1129482 := by
    simpa [prefixWord, tailWord_1129482, baseEnd_1129482] using wordTrace_append hprefix tailTrace_1129482
  have hstable : (prefixWord ++ tailWord_1129482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129482).length < 2 ^ (prefixWord ++ tailWord_1129482).sum := by decide
  have hdescent : baseEnd_1129482 < baseStart_1129482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129498 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_1129498 : Nat := 118140960795 + 1129498 * 2 ^ 59
def prefixEnd_1129498 : Nat := 4983230072969 + 3 ^ 40 * 1129498 * 2
def baseEnd_1129498 : Nat := 193325124097375689193513

theorem tailTrace_1129498 : CollatzResearch.WordTrace tailWord_1129498 prefixEnd_1129498 193325124097375689193513 := by
  unfold tailWord_1129498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10299044115507280936431287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27464117641352749163816765 10299044115507280936431287)
  ·
    refine ⟨15448566173260921404646931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10299044115507280936431287 15448566173260921404646931)
    ·
      refine ⟨23172849259891382106970397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15448566173260921404646931 23172849259891382106970397)
      ·
        refine ⟨8689818472459268290113899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23172849259891382106970397 8689818472459268290113899)
        ·
          refine ⟨13034727708688902435170849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8689818472459268290113899 13034727708688902435170849)
          ·
            refine ⟨9776045781516676826378137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13034727708688902435170849 9776045781516676826378137)
            ·
              refine ⟨7332034336137507619783603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9776045781516676826378137 7332034336137507619783603)
              ·
                refine ⟨10998051504206261429675405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332034336137507619783603 10998051504206261429675405)
                ·
                  refine ⟨4124269314077348036128277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10998051504206261429675405 4124269314077348036128277)
                  ·
                    refine ⟨193325124097375689193513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4124269314077348036128277 193325124097375689193513)
                    ·
                      rfl

theorem cell23_1129498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_1129498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129498 prefixEnd_1129498 := by exact prefixLift 1129498
  have htrace : WordTrace (prefixWord ++ tailWord_1129498) baseStart_1129498 baseEnd_1129498 := by
    simpa [prefixWord, tailWord_1129498, baseEnd_1129498] using wordTrace_append hprefix tailTrace_1129498
  have hstable : (prefixWord ++ tailWord_1129498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129498).length < 2 ^ (prefixWord ++ tailWord_1129498).sum := by decide
  have hdescent : baseEnd_1129498 < baseStart_1129498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129515 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 2, 4]
def baseStart_1129515 : Nat := 118140960795 + 1129515 * 2 ^ 59
def prefixEnd_1129515 : Nat := 4983230072969 + 3 ^ 40 * 1129515 * 2
def baseEnd_1129515 : Nat := 193328033821084500355987

theorem tailTrace_1129515 : CollatzResearch.WordTrace tailWord_1129515 prefixEnd_1129515 193328033821084500355987 := by
  unfold tailWord_1129515
  simp only [CollatzResearch.WordTrace]
  refine ⟨41196796502967535649093999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27464531001978357099395999 41196796502967535649093999)
  ·
    refine ⟨61795194754451303473640999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41196796502967535649093999 61795194754451303473640999)
    ·
      refine ⟨92692792131676955210461499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61795194754451303473640999 92692792131676955210461499)
      ·
        refine ⟨139039188197515432815692249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92692792131676955210461499 139039188197515432815692249)
        ·
          refine ⟨104279391148136574611769187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139039188197515432815692249 104279391148136574611769187)
          ·
            refine ⟨156419086722204861917653781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104279391148136574611769187 156419086722204861917653781)
            ·
              refine ⟨7332144690103352902390021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156419086722204861917653781 7332144690103352902390021)
              ·
                refine ⟨1374777129394378669198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7332144690103352902390021 1374777129394378669198129)
                ·
                  refine ⟨1031082847045784001898597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374777129394378669198129 1031082847045784001898597)
                  ·
                    refine ⟨193328033821084500355987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031082847045784001898597 193328033821084500355987)
                    ·
                      rfl

theorem cell23_1129515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 4].length) (baseStart_1129515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129515 prefixEnd_1129515 := by exact prefixLift 1129515
  have htrace : WordTrace (prefixWord ++ tailWord_1129515) baseStart_1129515 baseEnd_1129515 := by
    simpa [prefixWord, tailWord_1129515, baseEnd_1129515] using wordTrace_append hprefix tailTrace_1129515
  have hstable : (prefixWord ++ tailWord_1129515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129515).length < 2 ^ (prefixWord ++ tailWord_1129515).sum := by decide
  have hdescent : baseEnd_1129515 < baseStart_1129515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129525 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1129525 : Nat := 118140960795 + 1129525 * 2 ^ 59
def prefixEnd_1129525 : Nat := 4983230072969 + 3 ^ 40 * 1129525 * 2
def baseEnd_1129525 : Nat := 579989236269798461942915

theorem tailTrace_1129525 : CollatzResearch.WordTrace tailWord_1129525 prefixEnd_1129525 579989236269798461942915 := by
  unfold tailWord_1129525
  simp only [CollatzResearch.WordTrace]
  refine ⟨41197161232931307356958029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27464774155287538237972019 41197161232931307356958029)
  ·
    refine ⟨15448935462349240258859261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41197161232931307356958029 15448935462349240258859261)
    ·
      refine ⟨5793350798380965097072223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15448935462349240258859261 5793350798380965097072223)
      ·
        refine ⟨8690026197571447645608335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793350798380965097072223 8690026197571447645608335)
        ·
          refine ⟨13035039296357171468412503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8690026197571447645608335 13035039296357171468412503)
          ·
            refine ⟨19552558944535757202618755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13035039296357171468412503 19552558944535757202618755)
            ·
              refine ⟨29328838416803635803928133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19552558944535757202618755 29328838416803635803928133)
              ·
                refine ⟨5499157203150681713236525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29328838416803635803928133 5499157203150681713236525)
                ·
                  refine ⟨2062183951181505642463697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5499157203150681713236525 2062183951181505642463697)
                  ·
                    refine ⟨1546637963386129231847773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2062183951181505642463697 1546637963386129231847773)
                    ·
                      refine ⟨579989236269798461942915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1546637963386129231847773 579989236269798461942915)
                      ·
                        rfl

theorem cell23_1129525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1129525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129525 prefixEnd_1129525 := by exact prefixLift 1129525
  have htrace : WordTrace (prefixWord ++ tailWord_1129525) baseStart_1129525 baseEnd_1129525 := by
    simpa [prefixWord, tailWord_1129525, baseEnd_1129525] using wordTrace_append hprefix tailTrace_1129525
  have hstable : (prefixWord ++ tailWord_1129525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129525).length < 2 ^ (prefixWord ++ tailWord_1129525).sum := by decide
  have hdescent : baseEnd_1129525 < baseStart_1129525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129528 : List Nat := [2, 1, 2, 1, 5, 1, 1, 10]
def baseStart_1129528 : Nat := 118140960795 + 1129528 * 2 ^ 59
def prefixEnd_1129528 : Nat := 4983230072969 + 3 ^ 40 * 1129528 * 2
def baseEnd_1129528 : Nat := 21481139878213405563163

theorem tailTrace_1129528 : CollatzResearch.WordTrace tailWord_1129528 prefixEnd_1129528 21481139878213405563163 := by
  unfold tailWord_1129528
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598635325960219434658619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27464847101280292579544825 20598635325960219434658619)
  ·
    refine ⟨30897952988940329151987929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20598635325960219434658619 30897952988940329151987929)
    ·
      refine ⟨23173464741705246863990947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30897952988940329151987929 23173464741705246863990947)
      ·
        refine ⟨34760197112557870295986421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23173464741705246863990947 34760197112557870295986421)
        ·
          refine ⟨3258768479302300340248727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34760197112557870295986421 3258768479302300340248727)
          ·
            refine ⟨4888152718953450510373091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258768479302300340248727 4888152718953450510373091)
            ·
              refine ⟨7332229078430175765559637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888152718953450510373091 7332229078430175765559637)
              ·
                refine ⟨21481139878213405563163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7332229078430175765559637 21481139878213405563163)
                ·
                  rfl

theorem cell23_1129528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 10].length) (baseStart_1129528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129528 prefixEnd_1129528 := by exact prefixLift 1129528
  have htrace : WordTrace (prefixWord ++ tailWord_1129528) baseStart_1129528 baseEnd_1129528 := by
    simpa [prefixWord, tailWord_1129528, baseEnd_1129528] using wordTrace_append hprefix tailTrace_1129528
  have hstable : (prefixWord ++ tailWord_1129528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129528).length < 2 ^ (prefixWord ++ tailWord_1129528).sum := by decide
  have hdescent : baseEnd_1129528 < baseStart_1129528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129532 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1129532 : Nat := 118140960795 + 1129532 * 2 ^ 59
def prefixEnd_1129532 : Nat := 4983230072969 + 3 ^ 40 * 1129532 * 2
def baseEnd_1129532 : Nat := 193330943544793311518461

theorem tailTrace_1129532 : CollatzResearch.WordTrace tailWord_1129532 prefixEnd_1129532 193330943544793311518461 := by
  unfold tailWord_1129532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598708271952973776231425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27464944362603965034975233 20598708271952973776231425)
  ·
    refine ⟨15449031203964730332173569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20598708271952973776231425 15449031203964730332173569)
    ·
      refine ⟨11586773402973547749130177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15449031203964730332173569 11586773402973547749130177)
      ·
        refine ⟨8690080052230160811847633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11586773402973547749130177 8690080052230160811847633)
        ·
          refine ⟨6517560039172620608885725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8690080052230160811847633 6517560039172620608885725)
          ·
            refine ⟨2444085014689732728332147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6517560039172620608885725 2444085014689732728332147)
            ·
              refine ⟨3666127522034599092498221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444085014689732728332147 3666127522034599092498221)
              ·
                refine ⟨1374797820762974659686833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3666127522034599092498221 1374797820762974659686833)
                ·
                  refine ⟨1031098365572230994765125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374797820762974659686833 1031098365572230994765125)
                  ·
                    refine ⟨193330943544793311518461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031098365572230994765125 193330943544793311518461)
                    ·
                      rfl

theorem cell23_1129532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1129532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129532 prefixEnd_1129532 := by exact prefixLift 1129532
  have htrace : WordTrace (prefixWord ++ tailWord_1129532) baseStart_1129532 baseEnd_1129532 := by
    simpa [prefixWord, tailWord_1129532, baseEnd_1129532] using wordTrace_append hprefix tailTrace_1129532
  have hstable : (prefixWord ++ tailWord_1129532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129532).length < 2 ^ (prefixWord ++ tailWord_1129532).sum := by decide
  have hdescent : baseEnd_1129532 < baseStart_1129532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129566 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1129566 : Nat := 118140960795 + 1129566 * 2 ^ 59
def prefixEnd_1129566 : Nat := 4983230072969 + 3 ^ 40 * 1129566 * 2
def baseEnd_1129566 : Nat := 193336762992210933843409

theorem tailTrace_1129566 : CollatzResearch.WordTrace tailWord_1129566 prefixEnd_1129566 193336762992210933843409 := by
  unfold tailWord_1129566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149832078222846419900069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27465771083855180906133701 5149832078222846419900069)
  ·
    refine ⟨965593514666783703731263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5149832078222846419900069 965593514666783703731263)
    ·
      refine ⟨1448390272000175555596895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965593514666783703731263 1448390272000175555596895)
      ·
        refine ⟨2172585408000263333395343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448390272000175555596895 2172585408000263333395343)
        ·
          refine ⟨3258878112000395000093015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172585408000263333395343 3258878112000395000093015)
          ·
            refine ⟨4888317168000592500139523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258878112000395000093015 4888317168000592500139523)
            ·
              refine ⟨7332475752000888750209285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888317168000592500139523 7332475752000888750209285)
              ·
                refine ⟨1374839203500166640664241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7332475752000888750209285 1374839203500166640664241)
                ·
                  refine ⟨1031129402625124980498181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1374839203500166640664241 1031129402625124980498181)
                  ·
                    refine ⟨193336762992210933843409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031129402625124980498181 193336762992210933843409)
                    ·
                      rfl

theorem cell23_1129566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1129566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129566 prefixEnd_1129566 := by exact prefixLift 1129566
  have htrace : WordTrace (prefixWord ++ tailWord_1129566) baseStart_1129566 baseEnd_1129566 := by
    simpa [prefixWord, tailWord_1129566, baseEnd_1129566] using wordTrace_append hprefix tailTrace_1129566
  have hstable : (prefixWord ++ tailWord_1129566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129566).length < 2 ^ (prefixWord ++ tailWord_1129566).sum := by decide
  have hdescent : baseEnd_1129566 < baseStart_1129566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129629 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_1129629 : Nat := 118140960795 + 1129629 * 2 ^ 59
def prefixEnd_1129629 : Nat := 4983230072969 + 3 ^ 40 * 1129629 * 2
def baseEnd_1129629 : Nat := 580042638257866055042437

theorem tailTrace_1129629 : CollatzResearch.WordTrace tailWord_1129629 prefixEnd_1129629 580042638257866055042437 := by
  unfold tailWord_1129629
  simp only [CollatzResearch.WordTrace]
  refine ⟨41200954424554533118743941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27467302949703022079162627 41200954424554533118743941)
  ·
    refine ⟨7725178954603974959764489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41200954424554533118743941 7725178954603974959764489)
    ·
      refine ⟨5793884215952981219823367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7725178954603974959764489 5793884215952981219823367)
      ·
        refine ⟨8690826323929471829735051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793884215952981219823367 8690826323929471829735051)
        ·
          refine ⟨13036239485894207744602577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8690826323929471829735051 13036239485894207744602577)
          ·
            refine ⟨9777179614420655808451933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13036239485894207744602577 9777179614420655808451933)
            ·
              refine ⟨3666442355407745928169475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9777179614420655808451933 3666442355407745928169475)
              ·
                refine ⟨5499663533111618892254213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666442355407745928169475 5499663533111618892254213)
                ·
                  refine ⟨1031186912458428542297665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5499663533111618892254213 1031186912458428542297665)
                  ·
                    refine ⟨773390184343821406723249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1031186912458428542297665 773390184343821406723249)
                    ·
                      refine ⟨580042638257866055042437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773390184343821406723249 580042638257866055042437)
                      ·
                        rfl

theorem cell23_1129629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_1129629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129629 prefixEnd_1129629 := by exact prefixLift 1129629
  have htrace : WordTrace (prefixWord ++ tailWord_1129629) baseStart_1129629 baseEnd_1129629 := by
    simpa [prefixWord, tailWord_1129629, baseEnd_1129629] using wordTrace_append hprefix tailTrace_1129629
  have hstable : (prefixWord ++ tailWord_1129629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129629).length < 2 ^ (prefixWord ++ tailWord_1129629).sum := by decide
  have hdescent : baseEnd_1129629 < baseStart_1129629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129666 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1129666 : Nat := 118140960795 + 1129666 * 2 ^ 59
def prefixEnd_1129666 : Nat := 4983230072969 + 3 ^ 40 * 1129666 * 2
def baseEnd_1129666 : Nat := 580061637042082410279767

theorem tailTrace_1129666 : CollatzResearch.WordTrace tailWord_1129666 prefixEnd_1129666 580061637042082410279767 := by
  unfold tailWord_1129666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10300575981355122109460213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27468202616946992291893901 10300575981355122109460213)
  ·
    refine ⟨965678998252042697761895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10300575981355122109460213 965678998252042697761895)
    ·
      refine ⟨1448518497378064046642843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965678998252042697761895 1448518497378064046642843)
      ·
        refine ⟨2172777746067096069964265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448518497378064046642843 2172777746067096069964265)
        ·
          refine ⟨1629583309550322052473199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172777746067096069964265 1629583309550322052473199)
          ·
            refine ⟨2444374964325483078709799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629583309550322052473199 2444374964325483078709799)
            ·
              refine ⟨3666562446488224618064699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444374964325483078709799 3666562446488224618064699)
              ·
                refine ⟨5499843669732336927097049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666562446488224618064699 5499843669732336927097049)
                ·
                  refine ⟨4124882752299252695322787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5499843669732336927097049 4124882752299252695322787)
                  ·
                    refine ⟨6187324128448879042984181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4124882752299252695322787 6187324128448879042984181)
                    ·
                      refine ⟨580061637042082410279767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6187324128448879042984181 580061637042082410279767)
                      ·
                        rfl

theorem cell23_1129666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1129666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129666 prefixEnd_1129666 := by exact prefixLift 1129666
  have htrace : WordTrace (prefixWord ++ tailWord_1129666) baseStart_1129666 baseEnd_1129666 := by
    simpa [prefixWord, tailWord_1129666, baseEnd_1129666] using wordTrace_append hprefix tailTrace_1129666
  have hstable : (prefixWord ++ tailWord_1129666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129666).length < 2 ^ (prefixWord ++ tailWord_1129666).sum := by decide
  have hdescent : baseEnd_1129666 < baseStart_1129666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129682 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1129682 : Nat := 118140960795 + 1129682 * 2 ^ 59
def prefixEnd_1129682 : Nat := 4983230072969 + 3 ^ 40 * 1129682 * 2
def baseEnd_1129682 : Nat := 193356617577518115893231

theorem tailTrace_1129682 : CollatzResearch.WordTrace tailWord_1129682 prefixEnd_1129682 193356617577518115893231 := by
  unfold tailWord_1129682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10300721873340630792605825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27468591662241682113615533 10300721873340630792605825)
  ·
    refine ⟨7725541405005473094454369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10300721873340630792605825 7725541405005473094454369)
    ·
      refine ⟨5794156053754104820840777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7725541405005473094454369 5794156053754104820840777)
      ·
        refine ⟨4345617040315578615630583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5794156053754104820840777 4345617040315578615630583)
        ·
          refine ⟨6518425560473367923445875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345617040315578615630583 6518425560473367923445875)
          ·
            refine ⟨9777638340710051885168813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518425560473367923445875 9777638340710051885168813)
            ·
              refine ⟨3666614377766269456938305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9777638340710051885168813 3666614377766269456938305)
              ·
                refine ⟨2749960783324702092703729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3666614377766269456938305 2749960783324702092703729)
                ·
                  refine ⟨2062470587493526569527797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2749960783324702092703729 2062470587493526569527797)
                  ·
                    refine ⟨193356617577518115893231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2062470587493526569527797 193356617577518115893231)
                    ·
                      rfl

theorem cell23_1129682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1129682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129682 prefixEnd_1129682 := by exact prefixLift 1129682
  have htrace : WordTrace (prefixWord ++ tailWord_1129682) baseStart_1129682 baseEnd_1129682 := by
    simpa [prefixWord, tailWord_1129682, baseEnd_1129682] using wordTrace_append hprefix tailTrace_1129682
  have hstable : (prefixWord ++ tailWord_1129682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129682).length < 2 ^ (prefixWord ++ tailWord_1129682).sum := by decide
  have hdescent : baseEnd_1129682 < baseStart_1129682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129686 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1129686 : Nat := 118140960795 + 1129686 * 2 ^ 59
def prefixEnd_1129686 : Nat := 4983230072969 + 3 ^ 40 * 1129686 * 2
def baseEnd_1129686 : Nat := 64452434072796925781075

theorem tailTrace_1129686 : CollatzResearch.WordTrace tailWord_1129686 prefixEnd_1129686 64452434072796925781075 := by
  unfold tailWord_1129686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575189586584251990848057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27468688923565354569045941 2575189586584251990848057)
  ·
    refine ⟨1931392189938188993136043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2575189586584251990848057 1931392189938188993136043)
    ·
      refine ⟨2897088284907283489704065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931392189938188993136043 2897088284907283489704065)
      ·
        refine ⟨2172816213680462617278049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2897088284907283489704065 2172816213680462617278049)
        ·
          refine ⟨1629612160260346962958537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172816213680462617278049 1629612160260346962958537)
          ·
            refine ⟨1222209120195260222218903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1629612160260346962958537 1222209120195260222218903)
            ·
              refine ⟨1833313680292890333328355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222209120195260222218903 1833313680292890333328355)
              ·
                refine ⟨2749970520439335499992533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833313680292890333328355 2749970520439335499992533)
                ·
                  refine ⟨64452434072796925781075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2749970520439335499992533 64452434072796925781075)
                  ·
                    rfl

theorem cell23_1129686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1129686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129686 prefixEnd_1129686 := by exact prefixLift 1129686
  have htrace : WordTrace (prefixWord ++ tailWord_1129686) baseStart_1129686 baseEnd_1129686 := by
    simpa [prefixWord, tailWord_1129686, baseEnd_1129686] using wordTrace_append hprefix tailTrace_1129686
  have hstable : (prefixWord ++ tailWord_1129686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129686).length < 2 ^ (prefixWord ++ tailWord_1129686).sum := by decide
  have hdescent : baseEnd_1129686 < baseStart_1129686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129742 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_1129742 : Nat := 118140960795 + 1129742 * 2 ^ 59
def prefixEnd_1129742 : Nat := 4983230072969 + 3 ^ 40 * 1129742 * 2
def baseEnd_1129742 : Nat := 64455629063536012547713

theorem tailTrace_1129742 : CollatzResearch.WordTrace tailWord_1129742 prefixEnd_1129742 64455629063536012547713 := by
  unfold tailWord_1129742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150634484143144177200935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27470050582096768945071653 5150634484143144177200935)
  ·
    refine ⟨7725951726214716265801403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5150634484143144177200935 7725951726214716265801403)
    ·
      refine ⟨11588927589322074398702105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7725951726214716265801403 11588927589322074398702105)
      ·
        refine ⟨8691695691991555799026579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11588927589322074398702105 8691695691991555799026579)
        ·
          refine ⟨13037543537987333698539869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691695691991555799026579 13037543537987333698539869)
          ·
            refine ⟨4889078826745250136952451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13037543537987333698539869 4889078826745250136952451)
            ·
              refine ⟨7333618240117875205428677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889078826745250136952451 7333618240117875205428677)
              ·
                refine ⟨1375053420022101601017877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7333618240117875205428677 1375053420022101601017877)
                ·
                  refine ⟨64455629063536012547713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1375053420022101601017877 64455629063536012547713)
                  ·
                    rfl

theorem cell23_1129742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_1129742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129742 prefixEnd_1129742 := by exact prefixLift 1129742
  have htrace : WordTrace (prefixWord ++ tailWord_1129742) baseStart_1129742 baseEnd_1129742 := by
    simpa [prefixWord, tailWord_1129742, baseEnd_1129742] using wordTrace_append hprefix tailTrace_1129742
  have hstable : (prefixWord ++ tailWord_1129742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129742).length < 2 ^ (prefixWord ++ tailWord_1129742).sum := by decide
  have hdescent : baseEnd_1129742 < baseStart_1129742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129745 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1129745 : Nat := 118140960795 + 1129745 * 2 ^ 59
def prefixEnd_1129745 : Nat := 4983230072969 + 3 ^ 40 * 1129745 * 2
def baseEnd_1129745 : Nat := 580102202013787601191903

theorem tailTrace_1129745 : CollatzResearch.WordTrace tailWord_1129745 prefixEnd_1129745 580102202013787601191903 := by
  unfold tailWord_1129745
  simp only [CollatzResearch.WordTrace]
  refine ⟨41205185292134284929966689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27470123528089523286644459 41205185292134284929966689)
  ·
    refine ⟨30903888969100713697475017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41205185292134284929966689 30903888969100713697475017)
    ·
      refine ⟨23177916726825535273106263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30903888969100713697475017 23177916726825535273106263)
      ·
        refine ⟨34766875090238302909659395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23177916726825535273106263 34766875090238302909659395)
        ·
          refine ⟨52150312635357454364489093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34766875090238302909659395 52150312635357454364489093)
          ·
            refine ⟨9778183619129522693341705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52150312635357454364489093 9778183619129522693341705)
            ·
              refine ⟨7333637714347142020006279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778183619129522693341705 7333637714347142020006279)
              ·
                refine ⟨11000456571520713030009419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333637714347142020006279 11000456571520713030009419)
                ·
                  refine ⟨16500684857281069545014129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11000456571520713030009419 16500684857281069545014129)
                  ·
                    refine ⟨12375513642960802158760597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16500684857281069545014129 12375513642960802158760597)
                    ·
                      refine ⟨580102202013787601191903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12375513642960802158760597 580102202013787601191903)
                      ·
                        rfl

theorem cell23_1129745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1129745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129745 prefixEnd_1129745 := by exact prefixLift 1129745
  have htrace : WordTrace (prefixWord ++ tailWord_1129745) baseStart_1129745 baseEnd_1129745 := by
    simpa [prefixWord, tailWord_1129745, baseEnd_1129745] using wordTrace_append hprefix tailTrace_1129745
  have hstable : (prefixWord ++ tailWord_1129745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129745).length < 2 ^ (prefixWord ++ tailWord_1129745).sum := by decide
  have hdescent : baseEnd_1129745 < baseStart_1129745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129772 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_1129772 : Nat := 118140960795 + 1129772 * 2 ^ 59
def prefixEnd_1129772 : Nat := 4983230072969 + 3 ^ 40 * 1129772 * 2
def baseEnd_1129772 : Nat := 193372021997152998518093

theorem tailTrace_1129772 : CollatzResearch.WordTrace tailWord_1129772 prefixEnd_1129772 193372021997152998518093 := by
  unfold tailWord_1129772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20603085031518234270599785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27470780042024312360799713 20603085031518234270599785)
  ·
    refine ⟨15452313773638675702949839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20603085031518234270599785 15452313773638675702949839)
    ·
      refine ⟨23178470660458013554424759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15452313773638675702949839 23178470660458013554424759)
      ·
        refine ⟨34767705990687020331637139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23178470660458013554424759 34767705990687020331637139)
        ·
          refine ⟨52151558986030530497455709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34767705990687020331637139 52151558986030530497455709)
          ·
            refine ⟨19556834619761448936545891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52151558986030530497455709 19556834619761448936545891)
            ·
              refine ⟨29335251929642173404818837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19556834619761448936545891 29335251929642173404818837)
              ·
                refine ⟨1375089934201976878350883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29335251929642173404818837 1375089934201976878350883)
                ·
                  refine ⟨2062634901302965317526325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375089934201976878350883 2062634901302965317526325)
                  ·
                    refine ⟨193372021997152998518093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2062634901302965317526325 193372021997152998518093)
                    ·
                      rfl

theorem cell23_1129772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_1129772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129772 prefixEnd_1129772 := by exact prefixLift 1129772
  have htrace : WordTrace (prefixWord ++ tailWord_1129772) baseStart_1129772 baseEnd_1129772 := by
    simpa [prefixWord, tailWord_1129772, baseEnd_1129772] using wordTrace_append hprefix tailTrace_1129772
  have hstable : (prefixWord ++ tailWord_1129772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129772).length < 2 ^ (prefixWord ++ tailWord_1129772).sum := by decide
  have hdescent : baseEnd_1129772 < baseStart_1129772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129773 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1129773 : Nat := 118140960795 + 1129773 * 2 ^ 59
def prefixEnd_1129773 : Nat := 4983230072969 + 3 ^ 40 * 1129773 * 2
def baseEnd_1129773 : Nat := 580116579472113491641775

theorem tailTrace_1129773 : CollatzResearch.WordTrace tailWord_1129773 prefixEnd_1129773 580116579472113491641775 := by
  unfold tailWord_1129773
  simp only [CollatzResearch.WordTrace]
  refine ⟨41206206536032845711985973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27470804357355230474657315 41206206536032845711985973)
  ·
    refine ⟨3863081862753079285498685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41206206536032845711985973 3863081862753079285498685)
    ·
      refine ⟨1448655698532404732062007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3863081862753079285498685 1448655698532404732062007)
      ·
        refine ⟨2172983547798607098093011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448655698532404732062007 2172983547798607098093011)
        ·
          refine ⟨3259475321697910647139517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172983547798607098093011 3259475321697910647139517)
          ·
            refine ⟨1222303245636716492677319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3259475321697910647139517 1222303245636716492677319)
            ·
              refine ⟨1833454868455074739015979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222303245636716492677319 1833454868455074739015979)
              ·
                refine ⟨2750182302682612108523969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833454868455074739015979 2750182302682612108523969)
                ·
                  refine ⟨2062636727011959081392977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2750182302682612108523969 2062636727011959081392977)
                  ·
                    refine ⟨1546977545258969311044733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2062636727011959081392977 1546977545258969311044733)
                    ·
                      refine ⟨580116579472113491641775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1546977545258969311044733 580116579472113491641775)
                      ·
                        rfl

theorem cell23_1129773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1129773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129773 prefixEnd_1129773 := by exact prefixLift 1129773
  have htrace : WordTrace (prefixWord ++ tailWord_1129773) baseStart_1129773 baseEnd_1129773 := by
    simpa [prefixWord, tailWord_1129773, baseEnd_1129773] using wordTrace_append hprefix tailTrace_1129773
  have hstable : (prefixWord ++ tailWord_1129773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129773).length < 2 ^ (prefixWord ++ tailWord_1129773).sum := by decide
  have hdescent : baseEnd_1129773 < baseStart_1129773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129779 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 5, 2]
def baseStart_1129779 : Nat := 118140960795 + 1129779 * 2 ^ 59
def prefixEnd_1129779 : Nat := 4983230072969 + 3 ^ 40 * 1129779 * 2
def baseEnd_1129779 : Nat := 580119660356040468166747

theorem tailTrace_1129779 : CollatzResearch.WordTrace tailWord_1129779 prefixEnd_1129779 580119660356040468166747 := by
  unfold tailWord_1129779
  simp only [CollatzResearch.WordTrace]
  refine ⟨41206425374011108736704391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27470950249340739157802927 41206425374011108736704391)
  ·
    refine ⟨61809638061016663105056587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41206425374011108736704391 61809638061016663105056587)
    ·
      refine ⟨92714457091524994657584881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61809638061016663105056587 92714457091524994657584881)
      ·
        refine ⟨69535842818643745993188661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92714457091524994657584881 69535842818643745993188661)
        ·
          refine ⟨6518985264247851186861437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69535842818643745993188661 6518985264247851186861437)
          ·
            refine ⟨2444619474092944195073039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6518985264247851186861437 2444619474092944195073039)
            ·
              refine ⟨3666929211139416292609559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444619474092944195073039 3666929211139416292609559)
              ·
                refine ⟨5500393816709124438914339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666929211139416292609559 5500393816709124438914339)
                ·
                  refine ⟨8250590725063686658371509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5500393816709124438914339 8250590725063686658371509)
                  ·
                    refine ⟨773492880474720624222329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8250590725063686658371509 773492880474720624222329)
                    ·
                      refine ⟨580119660356040468166747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773492880474720624222329 580119660356040468166747)
                      ·
                        rfl

theorem cell23_1129779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5, 2].length) (baseStart_1129779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129779 prefixEnd_1129779 := by exact prefixLift 1129779
  have htrace : WordTrace (prefixWord ++ tailWord_1129779) baseStart_1129779 baseEnd_1129779 := by
    simpa [prefixWord, tailWord_1129779, baseEnd_1129779] using wordTrace_append hprefix tailTrace_1129779
  have hstable : (prefixWord ++ tailWord_1129779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129779).length < 2 ^ (prefixWord ++ tailWord_1129779).sum := by decide
  have hdescent : baseEnd_1129779 < baseStart_1129779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129826 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1129826 : Nat := 118140960795 + 1129826 * 2 ^ 59
def prefixEnd_1129826 : Nat := 4983230072969 + 3 ^ 40 * 1129826 * 2
def baseEnd_1129826 : Nat := 580143793946801784279031

theorem tailTrace_1129826 : CollatzResearch.WordTrace tailWord_1129826 prefixEnd_1129826 580143793946801784279031 := by
  unfold tailWord_1129826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10302034901210208940916333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27472093069893890509110221 10302034901210208940916333)
  ·
    refine ⟨3863263087953828352843625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10302034901210208940916333 3863263087953828352843625)
    ·
      refine ⟨2897447315965371264632719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3863263087953828352843625 2897447315965371264632719)
      ·
        refine ⟨4346170973948056896949079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897447315965371264632719 4346170973948056896949079)
        ·
          refine ⟨6519256460922085345423619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346170973948056896949079 6519256460922085345423619)
          ·
            refine ⟨9778884691383128018135429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6519256460922085345423619 9778884691383128018135429)
            ·
              refine ⟨1833540879634336503400393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9778884691383128018135429 1833540879634336503400393)
              ·
                refine ⟨1375155659725752377550295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833540879634336503400393 1375155659725752377550295)
                ·
                  refine ⟨2062733489588628566325443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375155659725752377550295 2062733489588628566325443)
                  ·
                    refine ⟨3094100234382942849488165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2062733489588628566325443 3094100234382942849488165)
                    ·
                      refine ⟨580143793946801784279031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3094100234382942849488165 580143793946801784279031)
                      ·
                        rfl

theorem cell23_1129826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1129826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129826 prefixEnd_1129826 := by exact prefixLift 1129826
  have htrace : WordTrace (prefixWord ++ tailWord_1129826) baseStart_1129826 baseEnd_1129826 := by
    simpa [prefixWord, tailWord_1129826, baseEnd_1129826] using wordTrace_append hprefix tailTrace_1129826
  have hstable : (prefixWord ++ tailWord_1129826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129826).length < 2 ^ (prefixWord ++ tailWord_1129826).sum := by decide
  have hdescent : baseEnd_1129826 < baseStart_1129826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129854 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1129854 : Nat := 118140960795 + 1129854 * 2 ^ 59
def prefixEnd_1129854 : Nat := 4983230072969 + 3 ^ 40 * 1129854 * 2
def baseEnd_1129854 : Nat := 580158171405127674728903

theorem tailTrace_1129854 : CollatzResearch.WordTrace tailWord_1129854 prefixEnd_1129854 580158171405127674728903 := by
  unfold tailWord_1129854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151145106092424568210577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27472773899159597697123077 5151145106092424568210577)
  ·
    refine ⟨3863358829569318426157933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5151145106092424568210577 3863358829569318426157933)
    ·
      refine ⟨1448759561088494409809225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3863358829569318426157933 1448759561088494409809225)
      ·
        refine ⟨1086569670816370807356919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1448759561088494409809225 1086569670816370807356919)
        ·
          refine ⟨1629854506224556211035379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086569670816370807356919 1629854506224556211035379)
          ·
            refine ⟨2444781759336834316553069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629854506224556211035379 2444781759336834316553069)
            ·
              refine ⟨916793159751312868707401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444781759336834316553069 916793159751312868707401)
              ·
                refine ⟨687594869813484651530551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916793159751312868707401 687594869813484651530551)
                ·
                  refine ⟨1031392304720226977295827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687594869813484651530551 1031392304720226977295827)
                  ·
                    refine ⟨1547088457080340465943741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1031392304720226977295827 1547088457080340465943741)
                    ·
                      refine ⟨580158171405127674728903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1547088457080340465943741 580158171405127674728903)
                      ·
                        rfl

theorem cell23_1129854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1129854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129854 prefixEnd_1129854 := by exact prefixLift 1129854
  have htrace : WordTrace (prefixWord ++ tailWord_1129854) baseStart_1129854 baseEnd_1129854 := by
    simpa [prefixWord, tailWord_1129854, baseEnd_1129854] using wordTrace_append hprefix tailTrace_1129854
  have hstable : (prefixWord ++ tailWord_1129854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129854).length < 2 ^ (prefixWord ++ tailWord_1129854).sum := by decide
  have hdescent : baseEnd_1129854 < baseStart_1129854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129870 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1129870 : Nat := 118140960795 + 1129870 * 2 ^ 59
def prefixEnd_1129870 : Nat := 4983230072969 + 3 ^ 40 * 1129870 * 2
def baseEnd_1129870 : Nat := 193388795698533204042943

theorem tailTrace_1129870 : CollatzResearch.WordTrace tailWord_1129870 prefixEnd_1129870 193388795698533204042943 := by
  unfold tailWord_1129870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151218052085178909783383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27473162944454287518844709 5151218052085178909783383)
  ·
    refine ⟨7726827078127768364675075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5151218052085178909783383 7726827078127768364675075)
    ·
      refine ⟨11590240617191652547012613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7726827078127768364675075 11590240617191652547012613)
      ·
        refine ⟨2173170115723434852564865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11590240617191652547012613 2173170115723434852564865)
        ·
          refine ⟨1629877586792576139423649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2173170115723434852564865 1629877586792576139423649)
          ·
            refine ⟨1222408190094432104567737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1629877586792576139423649 1222408190094432104567737)
            ·
              refine ⟨916806142570824078425803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1222408190094432104567737 916806142570824078425803)
              ·
                refine ⟨1375209213856236117638705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916806142570824078425803 1375209213856236117638705)
                ·
                  refine ⟨1031406910392177088229029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375209213856236117638705 1031406910392177088229029)
                  ·
                    refine ⟨193388795698533204042943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1031406910392177088229029 193388795698533204042943)
                    ·
                      rfl

theorem cell23_1129870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1129870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129870 prefixEnd_1129870 := by exact prefixLift 1129870
  have htrace : WordTrace (prefixWord ++ tailWord_1129870) baseStart_1129870 baseEnd_1129870 := by
    simpa [prefixWord, tailWord_1129870, baseEnd_1129870] using wordTrace_append hprefix tailTrace_1129870
  have hstable : (prefixWord ++ tailWord_1129870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129870).length < 2 ^ (prefixWord ++ tailWord_1129870).sum := by decide
  have hdescent : baseEnd_1129870 < baseStart_1129870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129880 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1129880 : Nat := 118140960795 + 1129880 * 2 ^ 59
def prefixEnd_1129880 : Nat := 4983230072969 + 3 ^ 40 * 1129880 * 2
def baseEnd_1129880 : Nat := 580171521902144573003783

theorem tailTrace_1129880 : CollatzResearch.WordTrace tailWord_1129880 prefixEnd_1129880 580171521902144573003783 := by
  unfold tailWord_1129880
  simp only [CollatzResearch.WordTrace]
  refine ⟨20605054573322601493065547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27473406097763468657420729 20605054573322601493065547)
  ·
    refine ⟨30907581859983902239598321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20605054573322601493065547 30907581859983902239598321)
    ·
      refine ⟨23180686394987926679698741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30907581859983902239598321 23180686394987926679698741)
      ·
        refine ⟨2173189349530118126221757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23180686394987926679698741 2173189349530118126221757)
        ·
          refine ⟨814946006073794297333159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2173189349530118126221757 814946006073794297333159)
          ·
            refine ⟨1222419009110691445999739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814946006073794297333159 1222419009110691445999739)
            ·
              refine ⟨1833628513666037168999609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222419009110691445999739 1833628513666037168999609)
              ·
                refine ⟨1375221385249527876749707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833628513666037168999609 1375221385249527876749707)
                ·
                  refine ⟨2062832077874291815124561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375221385249527876749707 2062832077874291815124561)
                  ·
                    refine ⟨1547124058405718861343421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2062832077874291815124561 1547124058405718861343421)
                    ·
                      refine ⟨580171521902144573003783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1547124058405718861343421 580171521902144573003783)
                      ·
                        rfl

theorem cell23_1129880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1129880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129880 prefixEnd_1129880 := by exact prefixLift 1129880
  have htrace : WordTrace (prefixWord ++ tailWord_1129880) baseStart_1129880 baseEnd_1129880 := by
    simpa [prefixWord, tailWord_1129880, baseEnd_1129880] using wordTrace_append hprefix tailTrace_1129880
  have hstable : (prefixWord ++ tailWord_1129880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129880).length < 2 ^ (prefixWord ++ tailWord_1129880).sum := by decide
  have hdescent : baseEnd_1129880 < baseStart_1129880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129892 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_1129892 : Nat := 118140960795 + 1129892 * 2 ^ 59
def prefixEnd_1129892 : Nat := 4983230072969 + 3 ^ 40 * 1129892 * 2
def baseEnd_1129892 : Nat := 193392561223332842017909

theorem tailTrace_1129892 : CollatzResearch.WordTrace tailWord_1129892 prefixEnd_1129892 193392561223332842017909 := by
  unfold tailWord_1129892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20605273411300864517783965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27473697881734486023711953 20605273411300864517783965)
  ·
    refine ⟨7726977529237824194168987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20605273411300864517783965 7726977529237824194168987)
    ·
      refine ⟨11590466293856736291253481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7726977529237824194168987 11590466293856736291253481)
      ·
        refine ⟨8692849720392552218440111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11590466293856736291253481 8692849720392552218440111)
        ·
          refine ⟨13039274580588828327660167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8692849720392552218440111 13039274580588828327660167)
          ·
            refine ⟨19558911870883242491490251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13039274580588828327660167 19558911870883242491490251)
            ·
              refine ⟨29338367806324863737235377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19558911870883242491490251 29338367806324863737235377)
              ·
                refine ⟨22003775854743647802926533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29338367806324863737235377 22003775854743647802926533)
                ·
                  refine ⟨4125707972764433963048725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22003775854743647802926533 4125707972764433963048725)
                  ·
                    refine ⟨193392561223332842017909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4125707972764433963048725 193392561223332842017909)
                    ·
                      rfl

theorem cell23_1129892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_1129892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129892 prefixEnd_1129892 := by exact prefixLift 1129892
  have htrace : WordTrace (prefixWord ++ tailWord_1129892) baseStart_1129892 baseEnd_1129892 := by
    simpa [prefixWord, tailWord_1129892, baseEnd_1129892] using wordTrace_append hprefix tailTrace_1129892
  have hstable : (prefixWord ++ tailWord_1129892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129892).length < 2 ^ (prefixWord ++ tailWord_1129892).sum := by decide
  have hdescent : baseEnd_1129892 < baseStart_1129892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129973 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 5]
def baseStart_1129973 : Nat := 118140960795 + 1129973 * 2 ^ 59
def prefixEnd_1129973 : Nat := 4983230072969 + 3 ^ 40 * 1129973 * 2
def baseEnd_1129973 : Nat := 64468808400334745460095

theorem tailTrace_1129973 : CollatzResearch.WordTrace tailWord_1129973 prefixEnd_1129973 64468808400334745460095 := by
  unfold tailWord_1129973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41213501135308279869266573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27475667423538853246177715 41213501135308279869266573)
  ·
    refine ⟨15455062925740604950974965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41213501135308279869266573 15455062925740604950974965)
    ·
      refine ⟨1448912149288181714153903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15455062925740604950974965 1448912149288181714153903)
      ·
        refine ⟨2173368223932272571230855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448912149288181714153903 2173368223932272571230855)
        ·
          refine ⟨3260052335898408856846283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173368223932272571230855 3260052335898408856846283)
          ·
            refine ⟨4890078503847613285269425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260052335898408856846283 4890078503847613285269425)
            ·
              refine ⟨3667558877885709963952069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890078503847613285269425 3667558877885709963952069)
              ·
                refine ⟨687667289603570618241013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3667558877885709963952069 687667289603570618241013)
                ·
                  refine ⟨64468808400334745460095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 687667289603570618241013 64468808400334745460095)
                  ·
                    rfl

theorem cell23_1129973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_1129973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129973 prefixEnd_1129973 := by exact prefixLift 1129973
  have htrace : WordTrace (prefixWord ++ tailWord_1129973) baseStart_1129973 baseEnd_1129973 := by
    simpa [prefixWord, tailWord_1129973, baseEnd_1129973] using wordTrace_append hprefix tailTrace_1129973
  have hstable : (prefixWord ++ tailWord_1129973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129973).length < 2 ^ (prefixWord ++ tailWord_1129973).sum := by decide
  have hdescent : baseEnd_1129973 < baseStart_1129973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129986 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1129986 : Nat := 118140960795 + 1129986 * 2 ^ 59
def prefixEnd_1129986 : Nat := 4983230072969 + 3 ^ 40 * 1129986 * 2
def baseEnd_1129986 : Nat := 193408650283840386092765

theorem tailTrace_1129986 : CollatzResearch.WordTrace tailWord_1129986 prefixEnd_1129986 193408650283840386092765 := by
  unfold tailWord_1129986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303493821065295772372453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27475983522840788726326541 10303493821065295772372453)
  ·
    refine ⟨1931905091449742957319835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10303493821065295772372453 1931905091449742957319835)
    ·
      refine ⟨2897857637174614435979753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931905091449742957319835 2897857637174614435979753)
      ·
        refine ⟨2173393227880960826984815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2897857637174614435979753 2173393227880960826984815)
        ·
          refine ⟨3260089841821441240477223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173393227880960826984815 3260089841821441240477223)
          ·
            refine ⟨4890134762732161860715835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260089841821441240477223 4890134762732161860715835)
            ·
              refine ⟨7335202144098242791073753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890134762732161860715835 7335202144098242791073753)
              ·
                refine ⟨5501401608073682093305315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335202144098242791073753 5501401608073682093305315)
                ·
                  refine ⟨8252102412110523139957973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5501401608073682093305315 8252102412110523139957973)
                  ·
                    refine ⟨193408650283840386092765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8252102412110523139957973 193408650283840386092765)
                    ·
                      rfl

theorem cell23_1129986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1129986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1129986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1129986 prefixEnd_1129986 := by exact prefixLift 1129986
  have htrace : WordTrace (prefixWord ++ tailWord_1129986) baseStart_1129986 baseEnd_1129986 := by
    simpa [prefixWord, tailWord_1129986, baseEnd_1129986] using wordTrace_append hprefix tailTrace_1129986
  have hstable : (prefixWord ++ tailWord_1129986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129986).length < 2 ^ (prefixWord ++ tailWord_1129986).sum := by decide
  have hdescent : baseEnd_1129986 < baseStart_1129986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130083 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 2, 3, 2]
def baseStart_1130083 : Nat := 118140960795 + 1130083 * 2 ^ 59
def prefixEnd_1130083 : Nat := 4983230072969 + 3 ^ 40 * 1130083 * 2
def baseEnd_1130083 : Nat := 580275758475007278765349

theorem tailTrace_1130083 : CollatzResearch.WordTrace tailWord_1130083 prefixEnd_1130083 580275758475007278765349 := by
  unfold tailWord_1130083
  simp only [CollatzResearch.WordTrace]
  refine ⟨41217513164909768655770903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27478342109939845770513935 41217513164909768655770903)
  ·
    refine ⟨61826269747364652983656355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41217513164909768655770903 61826269747364652983656355)
    ·
      refine ⟨92739404621046979475484533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61826269747364652983656355 92739404621046979475484533)
      ·
        refine ⟨8694319183223154325826675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92739404621046979475484533 8694319183223154325826675)
        ·
          refine ⟨13041478774834731488740013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694319183223154325826675 13041478774834731488740013)
          ·
            refine ⟨4890554540563024308277505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13041478774834731488740013 4890554540563024308277505)
            ·
              refine ⟨3667915905422268231208129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890554540563024308277505 3667915905422268231208129)
              ·
                refine ⟨2750936929066701173406097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3667915905422268231208129 2750936929066701173406097)
                ·
                  refine ⟨2063202696800025880054573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2750936929066701173406097 2063202696800025880054573)
                  ·
                    refine ⟨773701011300009705020465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063202696800025880054573 773701011300009705020465)
                    ·
                      refine ⟨580275758475007278765349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773701011300009705020465 580275758475007278765349)
                      ·
                        rfl

theorem cell23_1130083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_1130083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130083 prefixEnd_1130083 := by exact prefixLift 1130083
  have htrace : WordTrace (prefixWord ++ tailWord_1130083) baseStart_1130083 baseEnd_1130083 := by
    simpa [prefixWord, tailWord_1130083, baseEnd_1130083] using wordTrace_append hprefix tailTrace_1130083
  have hstable : (prefixWord ++ tailWord_1130083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130083).length < 2 ^ (prefixWord ++ tailWord_1130083).sum := by decide
  have hdescent : baseEnd_1130083 < baseStart_1130083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130096 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_1130096 : Nat := 118140960795 + 1130096 * 2 ^ 59
def prefixEnd_1130096 : Nat := 4983230072969 + 3 ^ 40 * 1130096 * 2
def baseEnd_1130096 : Nat := 580282433723515727902789

theorem tailTrace_1130096 : CollatzResearch.WordTrace tailWord_1130096 prefixEnd_1130096 580282433723515727902789 := by
  unfold tailWord_1130096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608993656931335937997071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27478658209241781250662761 20608993656931335937997071)
  ·
    refine ⟨30913490485397003906995607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20608993656931335937997071 30913490485397003906995607)
    ·
      refine ⟨46370235728095505860493411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30913490485397003906995607 46370235728095505860493411)
      ·
        refine ⟨69555353592143258790740117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46370235728095505860493411 69555353592143258790740117)
        ·
          refine ⟨3260407199631715255815943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69555353592143258790740117 3260407199631715255815943)
          ·
            refine ⟨4890610799447572883723915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260407199631715255815943 4890610799447572883723915)
            ·
              refine ⟨7335916199171359325585873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890610799447572883723915 7335916199171359325585873)
              ·
                refine ⟨5501937149378519494189405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335916199171359325585873 5501937149378519494189405)
                ·
                  refine ⟨2063226431016944810321027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5501937149378519494189405 2063226431016944810321027)
                  ·
                    refine ⟨3094839646525417215481541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2063226431016944810321027 3094839646525417215481541)
                    ·
                      refine ⟨580282433723515727902789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3094839646525417215481541 580282433723515727902789)
                      ·
                        rfl

theorem cell23_1130096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_1130096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130096 prefixEnd_1130096 := by exact prefixLift 1130096
  have htrace : WordTrace (prefixWord ++ tailWord_1130096) baseStart_1130096 baseEnd_1130096 := by
    simpa [prefixWord, tailWord_1130096, baseEnd_1130096] using wordTrace_append hprefix tailTrace_1130096
  have hstable : (prefixWord ++ tailWord_1130096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130096).length < 2 ^ (prefixWord ++ tailWord_1130096).sum := by decide
  have hdescent : baseEnd_1130096 < baseStart_1130096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130130 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1130130 : Nat := 118140960795 + 1130130 * 2 ^ 59
def prefixEnd_1130130 : Nat := 4983230072969 + 3 ^ 40 * 1130130 * 2
def baseEnd_1130130 : Nat := 580299892065768594877633

theorem tailTrace_1130130 : CollatzResearch.WordTrace tailWord_1130130 prefixEnd_1130130 580299892065768594877633 := by
  unfold tailWord_1130130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10304806848934873920682961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27479484930492997121821229 10304806848934873920682961)
  ·
    refine ⟨7728605136701155440512221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10304806848934873920682961 7728605136701155440512221)
    ·
      refine ⟨2898226926262933290192083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7728605136701155440512221 2898226926262933290192083)
      ·
        refine ⟨4347340389394399935288125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898226926262933290192083 4347340389394399935288125)
        ·
          refine ⟨1630252646022899975733047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4347340389394399935288125 1630252646022899975733047)
          ·
            refine ⟨2445378969034349963599571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630252646022899975733047 2445378969034349963599571)
            ·
              refine ⟨3668068453551524945399357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445378969034349963599571 3668068453551524945399357)
              ·
                refine ⟨1375525670081821854524759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3668068453551524945399357 1375525670081821854524759)
                ·
                  refine ⟨2063288505122732781787139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375525670081821854524759 2063288505122732781787139)
                  ·
                    refine ⟨3094932757684099172680709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2063288505122732781787139 3094932757684099172680709)
                    ·
                      refine ⟨580299892065768594877633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3094932757684099172680709 580299892065768594877633)
                      ·
                        rfl

theorem cell23_1130130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1130130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130130 prefixEnd_1130130 := by exact prefixLift 1130130
  have htrace : WordTrace (prefixWord ++ tailWord_1130130) baseStart_1130130 baseEnd_1130130 := by
    simpa [prefixWord, tailWord_1130130, baseEnd_1130130] using wordTrace_append hprefix tailTrace_1130130
  have hstable : (prefixWord ++ tailWord_1130130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130130).length < 2 ^ (prefixWord ++ tailWord_1130130).sum := by decide
  have hdescent : baseEnd_1130130 < baseStart_1130130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130149 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_1130149 : Nat := 118140960795 + 1130149 * 2 ^ 59
def prefixEnd_1130149 : Nat := 4983230072969 + 3 ^ 40 * 1130149 * 2
def baseEnd_1130149 : Nat := 193436549399401340180015

theorem tailTrace_1130149 : CollatzResearch.WordTrace tailWord_1130149 prefixEnd_1130149 193436549399401340180015 := by
  unfold tailWord_1130149
  simp only [CollatzResearch.WordTrace]
  refine ⟨41219920382670661927673501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27479946921780441285115667 41219920382670661927673501)
  ·
    refine ⟨15457470143501498222877563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41219920382670661927673501 15457470143501498222877563)
    ·
      refine ⟨23186205215252247334316345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15457470143501498222877563 23186205215252247334316345)
      ·
        refine ⟨17389653911439185500737259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23186205215252247334316345 17389653911439185500737259)
        ·
          refine ⟨26084480867158778251105889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17389653911439185500737259 26084480867158778251105889)
          ·
            refine ⟨19563360650369083688329417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26084480867158778251105889 19563360650369083688329417)
            ·
              refine ⟨14672520487776812766247063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19563360650369083688329417 14672520487776812766247063)
              ·
                refine ⟨22008780731665219149370595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14672520487776812766247063 22008780731665219149370595)
                ·
                  refine ⟨33013171097497828724055893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22008780731665219149370595 33013171097497828724055893)
                  ·
                    refine ⟨193436549399401340180015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33013171097497828724055893 193436549399401340180015)
                    ·
                      rfl

theorem cell23_1130149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_1130149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130149 prefixEnd_1130149 := by exact prefixLift 1130149
  have htrace : WordTrace (prefixWord ++ tailWord_1130149) baseStart_1130149 baseEnd_1130149 := by
    simpa [prefixWord, tailWord_1130149, baseEnd_1130149] using wordTrace_append hprefix tailTrace_1130149
  have hstable : (prefixWord ++ tailWord_1130149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130149).length < 2 ^ (prefixWord ++ tailWord_1130149).sum := by decide
  have hdescent : baseEnd_1130149 < baseStart_1130149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130190 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_1130190 : Nat := 118140960795 + 1130190 * 2 ^ 59
def prefixEnd_1130190 : Nat := 4983230072969 + 3 ^ 40 * 1130190 * 2
def baseEnd_1130190 : Nat := 580330700905038360127357

theorem tailTrace_1130190 : CollatzResearch.WordTrace tailWord_1130190 prefixEnd_1130190 580330700905038360127357 := by
  unfold tailWord_1130190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152676971940265741239503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27480943850348083953277349 5152676971940265741239503)
  ·
    refine ⟨7729015457910398611859255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152676971940265741239503 7729015457910398611859255)
    ·
      refine ⟨11593523186865597917788883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729015457910398611859255 11593523186865597917788883)
      ·
        refine ⟨17390284780298396876683325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11593523186865597917788883 17390284780298396876683325)
        ·
          refine ⟨6521356792611898828756247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17390284780298396876683325 6521356792611898828756247)
          ·
            refine ⟨9782035188917848243134371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6521356792611898828756247 9782035188917848243134371)
            ·
              refine ⟨14673052783376772364701557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9782035188917848243134371 14673052783376772364701557)
              ·
                refine ⟨1375598698441572409190771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14673052783376772364701557 1375598698441572409190771)
                ·
                  refine ⟨2063398047662358613786157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375598698441572409190771 2063398047662358613786157)
                  ·
                    refine ⟨773774267873384480169809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063398047662358613786157 773774267873384480169809)
                    ·
                      refine ⟨580330700905038360127357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773774267873384480169809 580330700905038360127357)
                      ·
                        rfl

theorem cell23_1130190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_1130190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130190 prefixEnd_1130190 := by exact prefixLift 1130190
  have htrace : WordTrace (prefixWord ++ tailWord_1130190) baseStart_1130190 baseEnd_1130190 := by
    simpa [prefixWord, tailWord_1130190, baseEnd_1130190] using wordTrace_append hprefix tailTrace_1130190
  have hstable : (prefixWord ++ tailWord_1130190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130190).length < 2 ^ (prefixWord ++ tailWord_1130190).sum := by decide
  have hdescent : baseEnd_1130190 < baseStart_1130190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130198 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1130198 : Nat := 118140960795 + 1130198 * 2 ^ 59
def prefixEnd_1130198 : Nat := 4983230072969 + 3 ^ 40 * 1130198 * 2
def baseEnd_1130198 : Nat := 580334808750274328827321

theorem tailTrace_1130198 : CollatzResearch.WordTrace tailWord_1130198 prefixEnd_1130198 580334808750274328827321 := by
  unfold tailWord_1130198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576356722468321456012953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27481138372995428864138165 2576356722468321456012953)
  ·
    refine ⟨1932267541851241092009715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2576356722468321456012953 1932267541851241092009715)
    ·
      refine ⟨2898401312776861638014573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932267541851241092009715 2898401312776861638014573)
      ·
        refine ⟨1086900492291323114255465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2898401312776861638014573 1086900492291323114255465)
        ·
          refine ⟨815175369218492335691599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086900492291323114255465 815175369218492335691599)
          ·
            refine ⟨1222763053827738503537399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815175369218492335691599 1222763053827738503537399)
            ·
              refine ⟨1834144580741607755306099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222763053827738503537399 1834144580741607755306099)
              ·
                refine ⟨2751216871112411632959149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834144580741607755306099 2751216871112411632959149)
                ·
                  refine ⟨1031706326667154362359681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2751216871112411632959149 1031706326667154362359681)
                  ·
                    refine ⟨773779745000365771769761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1031706326667154362359681 773779745000365771769761)
                    ·
                      refine ⟨580334808750274328827321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773779745000365771769761 580334808750274328827321)
                      ·
                        rfl

theorem cell23_1130198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1130198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130198 prefixEnd_1130198 := by exact prefixLift 1130198
  have htrace : WordTrace (prefixWord ++ tailWord_1130198) baseStart_1130198 baseEnd_1130198 := by
    simpa [prefixWord, tailWord_1130198, baseEnd_1130198] using wordTrace_append hprefix tailTrace_1130198
  have hstable : (prefixWord ++ tailWord_1130198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130198).length < 2 ^ (prefixWord ++ tailWord_1130198).sum := by decide
  have hdescent : baseEnd_1130198 < baseStart_1130198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130226 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_1130226 : Nat := 118140960795 + 1130226 * 2 ^ 59
def prefixEnd_1130226 : Nat := 4983230072969 + 3 ^ 40 * 1130226 * 2
def baseEnd_1130226 : Nat := 64483242912066691030799

theorem tailTrace_1130226 : CollatzResearch.WordTrace tailWord_1130226 prefixEnd_1130226 64483242912066691030799 := by
  unfold tailWord_1130226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10305682200847926019556633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27481819202261136052151021 10305682200847926019556633)
  ·
    refine ⟨7729261650635944514667475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10305682200847926019556633 7729261650635944514667475)
    ·
      refine ⟨11593892475953916772001213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729261650635944514667475 11593892475953916772001213)
      ·
        refine ⟨4347709678482718789500455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11593892475953916772001213 4347709678482718789500455)
        ·
          refine ⟨6521564517724078184250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347709678482718789500455 6521564517724078184250683)
          ·
            refine ⟨9782346776586117276376025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6521564517724078184250683 9782346776586117276376025)
            ·
              refine ⟨7336760082439587957282019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9782346776586117276376025 7336760082439587957282019)
              ·
                refine ⟨11005140123659381935923029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7336760082439587957282019 11005140123659381935923029)
                ·
                  refine ⟨64483242912066691030799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11005140123659381935923029 64483242912066691030799)
                  ·
                    rfl

theorem cell23_1130226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_1130226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130226 prefixEnd_1130226 := by exact prefixLift 1130226
  have htrace : WordTrace (prefixWord ++ tailWord_1130226) baseStart_1130226 baseEnd_1130226 := by
    simpa [prefixWord, tailWord_1130226, baseEnd_1130226] using wordTrace_append hprefix tailTrace_1130226
  have hstable : (prefixWord ++ tailWord_1130226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130226).length < 2 ^ (prefixWord ++ tailWord_1130226).sum := by decide
  have hdescent : baseEnd_1130226 < baseStart_1130226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130290 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_1130290 : Nat := 118140960795 + 1130290 * 2 ^ 59
def prefixEnd_1130290 : Nat := 4983230072969 + 3 ^ 40 * 1130290 * 2
def baseEnd_1130290 : Nat := 193460682990162656292299

theorem tailTrace_1130290 : CollatzResearch.WordTrace tailWord_1130290 prefixEnd_1130290 193460682990162656292299 := by
  unfold tailWord_1130290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10306265768789960752139081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27483375383439895339037549 10306265768789960752139081)
  ·
    refine ⟨7729699326592470564104311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10306265768789960752139081 7729699326592470564104311)
    ·
      refine ⟨11594548989888705846156467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729699326592470564104311 11594548989888705846156467)
      ·
        refine ⟨17391823484833058769234701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594548989888705846156467 17391823484833058769234701)
        ·
          refine ⟨6521933806812397038463013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17391823484833058769234701 6521933806812397038463013)
          ·
            refine ⟨1222862588777324444711815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6521933806812397038463013 1222862588777324444711815)
            ·
              refine ⟨1834293883165986667067723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222862588777324444711815 1834293883165986667067723)
              ·
                refine ⟨2751440824748980000601585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834293883165986667067723 2751440824748980000601585)
                ·
                  refine ⟨2063580618561735000451189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2751440824748980000601585 2063580618561735000451189)
                  ·
                    refine ⟨193460682990162656292299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2063580618561735000451189 193460682990162656292299)
                    ·
                      rfl

theorem cell23_1130290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_1130290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130290 prefixEnd_1130290 := by exact prefixLift 1130290
  have htrace : WordTrace (prefixWord ++ tailWord_1130290) baseStart_1130290 baseEnd_1130290 := by
    simpa [prefixWord, tailWord_1130290, baseEnd_1130290] using wordTrace_append hprefix tailTrace_1130290
  have hstable : (prefixWord ++ tailWord_1130290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130290).length < 2 ^ (prefixWord ++ tailWord_1130290).sum := by decide
  have hdescent : baseEnd_1130290 < baseStart_1130290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130313 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_1130313 : Nat := 118140960795 + 1130313 * 2 ^ 59
def prefixEnd_1130313 : Nat := 4983230072969 + 3 ^ 40 * 1130313 * 2
def baseEnd_1130313 : Nat := 580393859025541378889291

theorem tailTrace_1130313 : CollatzResearch.WordTrace tailWord_1130313 prefixEnd_1130313 580393859025541378889291 := by
  unfold tailWord_1130313
  simp only [CollatzResearch.WordTrace]
  refine ⟨41225901954076517936643593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27483934636051011957762395 41225901954076517936643593)
  ·
    refine ⟨30919426465557388452482695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41225901954076517936643593 30919426465557388452482695)
    ·
      refine ⟨46379139698336082678724043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30919426465557388452482695 46379139698336082678724043)
      ·
        refine ⟨69568709547504124018086065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46379139698336082678724043 69568709547504124018086065)
        ·
          refine ⟨52176532160628093013564549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69568709547504124018086065 52176532160628093013564549)
          ·
            refine ⟨9783099780117767440043353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52176532160628093013564549 9783099780117767440043353)
            ·
              refine ⟨7337324835088325580032515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783099780117767440043353 7337324835088325580032515)
              ·
                refine ⟨11005987252632488370048773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7337324835088325580032515 11005987252632488370048773)
                ·
                  refine ⟨2063622609868591569384145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11005987252632488370048773 2063622609868591569384145)
                  ·
                    refine ⟨1547716957401443677038109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2063622609868591569384145 1547716957401443677038109)
                    ·
                      refine ⟨580393859025541378889291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1547716957401443677038109 580393859025541378889291)
                      ·
                        rfl

theorem cell23_1130313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_1130313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130313 prefixEnd_1130313 := by exact prefixLift 1130313
  have htrace : WordTrace (prefixWord ++ tailWord_1130313) baseStart_1130313 baseEnd_1130313 := by
    simpa [prefixWord, tailWord_1130313, baseEnd_1130313] using wordTrace_append hprefix tailTrace_1130313
  have hstable : (prefixWord ++ tailWord_1130313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130313).length < 2 ^ (prefixWord ++ tailWord_1130313).sum := by decide
  have hdescent : baseEnd_1130313 < baseStart_1130313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130343 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1130343 : Nat := 118140960795 + 1130343 * 2 ^ 59
def prefixEnd_1130343 : Nat := 4983230072969 + 3 ^ 40 * 1130343 * 2
def baseEnd_1130343 : Nat := 580409263445176261514153

theorem tailTrace_1130343 : CollatzResearch.WordTrace tailWord_1130343 prefixEnd_1130343 580409263445176261514153 := by
  unfold tailWord_1130343
  simp only [CollatzResearch.WordTrace]
  refine ⟨41226996143967833060235683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27484664095978555373490455 41226996143967833060235683)
  ·
    refine ⟨61840494215951749590353525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41226996143967833060235683 61840494215951749590353525)
    ·
      refine ⟨5797546332745476524095643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61840494215951749590353525 5797546332745476524095643)
      ·
        refine ⟨8696319499118214786143465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5797546332745476524095643 8696319499118214786143465)
        ·
          refine ⟨6522239624338661089607599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8696319499118214786143465 6522239624338661089607599)
          ·
            refine ⟨9783359436507991634411399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6522239624338661089607599 9783359436507991634411399)
            ·
              refine ⟨14675039154761987451617099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9783359436507991634411399 14675039154761987451617099)
              ·
                refine ⟨22012558732142981177425649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14675039154761987451617099 22012558732142981177425649)
                ·
                  refine ⟨16509419049107235883069237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22012558732142981177425649 16509419049107235883069237)
                  ·
                    refine ⟨1547758035853803364037741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16509419049107235883069237 1547758035853803364037741)
                    ·
                      refine ⟨580409263445176261514153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1547758035853803364037741 580409263445176261514153)
                      ·
                        rfl

theorem cell23_1130343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1130343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130343 prefixEnd_1130343 := by exact prefixLift 1130343
  have htrace : WordTrace (prefixWord ++ tailWord_1130343) baseStart_1130343 baseEnd_1130343 := by
    simpa [prefixWord, tailWord_1130343, baseEnd_1130343] using wordTrace_append hprefix tailTrace_1130343
  have hstable : (prefixWord ++ tailWord_1130343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130343).length < 2 ^ (prefixWord ++ tailWord_1130343).sum := by decide
  have hdescent : baseEnd_1130343 < baseStart_1130343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130397 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1130397 : Nat := 118140960795 + 1130397 * 2 ^ 59
def prefixEnd_1130397 : Nat := 4983230072969 + 3 ^ 40 * 1130397 * 2
def baseEnd_1130397 : Nat := 193478997133506350079635

theorem tailTrace_1130397 : CollatzResearch.WordTrace tailWord_1130397 prefixEnd_1130397 193478997133506350079635 := by
  unfold tailWord_1130397
  simp only [CollatzResearch.WordTrace]
  refine ⟨41228965685772200282701445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27485977123848133521800963 41228965685772200282701445)
  ·
    refine ⟨7730431066082287553006521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41228965685772200282701445 7730431066082287553006521)
    ·
      refine ⟨5797823299561715664754891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7730431066082287553006521 5797823299561715664754891)
      ·
        refine ⟨8696734949342573497132337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5797823299561715664754891 8696734949342573497132337)
        ·
          refine ⟨6522551212006930122849253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8696734949342573497132337 6522551212006930122849253)
          ·
            refine ⟨1222978352251299398034235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6522551212006930122849253 1222978352251299398034235)
            ·
              refine ⟨1834467528376949097051353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222978352251299398034235 1834467528376949097051353)
              ·
                refine ⟨1375850646282711822788515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834467528376949097051353 1375850646282711822788515)
                ·
                  refine ⟨2063775969424067734182773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375850646282711822788515 2063775969424067734182773)
                  ·
                    refine ⟨193478997133506350079635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2063775969424067734182773 193478997133506350079635)
                    ·
                      rfl

theorem cell23_1130397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1130397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130397 prefixEnd_1130397 := by exact prefixLift 1130397
  have htrace : WordTrace (prefixWord ++ tailWord_1130397) baseStart_1130397 baseEnd_1130397 := by
    simpa [prefixWord, tailWord_1130397, baseEnd_1130397] using wordTrace_append hprefix tailTrace_1130397
  have hstable : (prefixWord ++ tailWord_1130397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130397).length < 2 ^ (prefixWord ++ tailWord_1130397).sum := by decide
  have hdescent : baseEnd_1130397 < baseStart_1130397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130440 : List Nat := [2, 1, 3, 1, 4, 3, 1, 8]
def baseStart_1130440 : Nat := 118140960795 + 1130440 * 2 ^ 59
def prefixEnd_1130440 : Nat := 4983230072969 + 3 ^ 40 * 1130440 * 2
def baseEnd_1130440 : Nat := 21498484113654162296341

theorem tailTrace_1130440 : CollatzResearch.WordTrace tailWord_1130440 prefixEnd_1130440 21498484113654162296341 := by
  unfold tailWord_1130440
  simp only [CollatzResearch.WordTrace]
  refine ⟨20615267012308209313258387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27487022683077612417677849 20615267012308209313258387)
  ·
    refine ⟨30922900518462313969887581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20615267012308209313258387 30922900518462313969887581)
    ·
      refine ⟨11596087694423367738707843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30922900518462313969887581 11596087694423367738707843)
      ·
        refine ⟨17394131541635051608061765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11596087694423367738707843 17394131541635051608061765)
        ·
          refine ⟨3261399664056572176511581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17394131541635051608061765 3261399664056572176511581)
          ·
            refine ⟨1223024874021214566191843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3261399664056572176511581 1223024874021214566191843)
            ·
              refine ⟨1834537311031821849287765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223024874021214566191843 1834537311031821849287765)
              ·
                refine ⟨21498484113654162296341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1834537311031821849287765 21498484113654162296341)
                ·
                  rfl

theorem cell23_1130440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 8].length) (baseStart_1130440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130440 prefixEnd_1130440 := by exact prefixLift 1130440
  have htrace : WordTrace (prefixWord ++ tailWord_1130440) baseStart_1130440 baseEnd_1130440 := by
    simpa [prefixWord, tailWord_1130440, baseEnd_1130440] using wordTrace_append hprefix tailTrace_1130440
  have hstable : (prefixWord ++ tailWord_1130440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130440).length < 2 ^ (prefixWord ++ tailWord_1130440).sum := by decide
  have hdescent : baseEnd_1130440 < baseStart_1130440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130471 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1130471 : Nat := 118140960795 + 1130471 * 2 ^ 59
def prefixEnd_1130471 : Nat := 4983230072969 + 3 ^ 40 * 1130471 * 2
def baseEnd_1130471 : Nat := 580474988968951760713565

theorem tailTrace_1130471 : CollatzResearch.WordTrace tailWord_1130471 prefixEnd_1130471 580474988968951760713565 := by
  unfold tailWord_1130471
  simp only [CollatzResearch.WordTrace]
  refine ⟨41231664687504110920895267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27487776458336073947263511 41231664687504110920895267)
  ·
    refine ⟨61847497031256166381342901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41231664687504110920895267 61847497031256166381342901)
    ·
      refine ⟨5798202846680265598250897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61847497031256166381342901 5798202846680265598250897)
      ·
        refine ⟨4348652135010199198688173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5798202846680265598250897 4348652135010199198688173)
        ·
          refine ⟨1630744550628824699508065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4348652135010199198688173 1630744550628824699508065)
          ·
            refine ⟨1223058412971618524631049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630744550628824699508065 1223058412971618524631049)
            ·
              refine ⟨917293809728713893473287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223058412971618524631049 917293809728713893473287)
              ·
                refine ⟨1375940714593070840209931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917293809728713893473287 1375940714593070840209931)
                ·
                  refine ⟨2063911071889606260314897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375940714593070840209931 2063911071889606260314897)
                  ·
                    refine ⟨1547933303917204695236173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2063911071889606260314897 1547933303917204695236173)
                    ·
                      refine ⟨580474988968951760713565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1547933303917204695236173 580474988968951760713565)
                      ·
                        rfl

theorem cell23_1130471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1130471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130471 prefixEnd_1130471 := by exact prefixLift 1130471
  have htrace : WordTrace (prefixWord ++ tailWord_1130471) baseStart_1130471 baseEnd_1130471 := by
    simpa [prefixWord, tailWord_1130471, baseEnd_1130471] using wordTrace_append hprefix tailTrace_1130471
  have hstable : (prefixWord ++ tailWord_1130471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130471).length < 2 ^ (prefixWord ++ tailWord_1130471).sum := by decide
  have hdescent : baseEnd_1130471 < baseStart_1130471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130490 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_1130490 : Nat := 118140960795 + 1130490 * 2 ^ 59
def prefixEnd_1130490 : Nat := 4983230072969 + 3 ^ 40 * 1130490 * 2
def baseEnd_1130490 : Nat := 580484745101387186375977

theorem tailTrace_1130490 : CollatzResearch.WordTrace tailWord_1130490 prefixEnd_1130490 580484745101387186375977 := by
  unfold tailWord_1130490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308089418608819291459231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27488238449623518110557949 10308089418608819291459231)
  ·
    refine ⟨15462134127913228937188847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10308089418608819291459231 15462134127913228937188847)
    ·
      refine ⟨23193201191869843405783271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15462134127913228937188847 23193201191869843405783271)
      ·
        refine ⟨34789801787804765108674907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23193201191869843405783271 34789801787804765108674907)
        ·
          refine ⟨52184702681707147663012361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34789801787804765108674907 52184702681707147663012361)
          ·
            refine ⟨39138527011280360747259271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52184702681707147663012361 39138527011280360747259271)
            ·
              refine ⟨58707790516920541120888907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39138527011280360747259271 58707790516920541120888907)
              ·
                refine ⟨88061685775380811681333361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58707790516920541120888907 88061685775380811681333361)
                ·
                  refine ⟨66046264331535608761000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88061685775380811681333361 66046264331535608761000021)
                  ·
                    refine ⟨773979660135182915167969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66046264331535608761000021 773979660135182915167969)
                    ·
                      refine ⟨580484745101387186375977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 773979660135182915167969 580484745101387186375977)
                      ·
                        rfl

theorem cell23_1130490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_1130490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130490 prefixEnd_1130490 := by exact prefixLift 1130490
  have htrace : WordTrace (prefixWord ++ tailWord_1130490) baseStart_1130490 baseEnd_1130490 := by
    simpa [prefixWord, tailWord_1130490, baseEnd_1130490] using wordTrace_append hprefix tailTrace_1130490
  have hstable : (prefixWord ++ tailWord_1130490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130490).length < 2 ^ (prefixWord ++ tailWord_1130490).sum := by decide
  have hdescent : baseEnd_1130490 < baseStart_1130490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130510 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1130510 : Nat := 118140960795 + 1130510 * 2 ^ 59
def prefixEnd_1130510 : Nat := 4983230072969 + 3 ^ 40 * 1130510 * 2
def baseEnd_1130510 : Nat := 580495014714477108125885

theorem tailTrace_1130510 : CollatzResearch.WordTrace tailWord_1130510 prefixEnd_1130510 580495014714477108125885 := by
  unfold tailWord_1130510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154135891795352572695623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27488724756241880387709989 5154135891795352572695623)
  ·
    refine ⟨7731203837693028859043435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5154135891795352572695623 7731203837693028859043435)
    ·
      refine ⟨11596805756539543288565153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7731203837693028859043435 11596805756539543288565153)
      ·
        refine ⟨8697604317404657466423865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11596805756539543288565153 8697604317404657466423865)
        ·
          refine ⟨6523203238053493099817899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8697604317404657466423865 6523203238053493099817899)
          ·
            refine ⟨9784804857080239649726849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523203238053493099817899 9784804857080239649726849)
            ·
              refine ⟨7338603642810179737295137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9784804857080239649726849 7338603642810179737295137)
              ·
                refine ⟨5503952732107634802971353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7338603642810179737295137 5503952732107634802971353)
                ·
                  refine ⟨4127964549080726102228515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5503952732107634802971353 4127964549080726102228515)
                  ·
                    refine ⟨6191946823621089153342773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4127964549080726102228515 6191946823621089153342773)
                    ·
                      refine ⟨580495014714477108125885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6191946823621089153342773 580495014714477108125885)
                      ·
                        rfl

theorem cell23_1130510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1130510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130510 prefixEnd_1130510 := by exact prefixLift 1130510
  have htrace : WordTrace (prefixWord ++ tailWord_1130510) baseStart_1130510 baseEnd_1130510 := by
    simpa [prefixWord, tailWord_1130510, baseEnd_1130510] using wordTrace_append hprefix tailTrace_1130510
  have hstable : (prefixWord ++ tailWord_1130510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130510).length < 2 ^ (prefixWord ++ tailWord_1130510).sum := by decide
  have hdescent : baseEnd_1130510 < baseStart_1130510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130524 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_1130524 : Nat := 118140960795 + 1130524 * 2 ^ 59
def prefixEnd_1130524 : Nat := 4983230072969 + 3 ^ 40 * 1130524 * 2
def baseEnd_1130524 : Nat := 580502203443640053350821

theorem tailTrace_1130524 : CollatzResearch.WordTrace tailWord_1130524 prefixEnd_1130524 580502203443640053350821 := by
  unfold tailWord_1130524
  simp only [CollatzResearch.WordTrace]
  refine ⟨20616798878156050486287313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27489065170874733981716417 20616798878156050486287313)
  ·
    refine ⟨15462599158617037864715485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20616798878156050486287313 15462599158617037864715485)
    ·
      refine ⟨5798474684481389199268307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15462599158617037864715485 5798474684481389199268307)
      ·
        refine ⟨8697712026722083798902461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5798474684481389199268307 8697712026722083798902461)
        ·
          refine ⟨3261642010020781424588423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8697712026722083798902461 3261642010020781424588423)
          ·
            refine ⟨4892463015031172136882635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261642010020781424588423 4892463015031172136882635)
            ·
              refine ⟨7338694522546758205323953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892463015031172136882635 7338694522546758205323953)
              ·
                refine ⟨5504020891910068653992965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7338694522546758205323953 5504020891910068653992965)
                ·
                  refine ⟨1032003917233137872623681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5504020891910068653992965 1032003917233137872623681)
                  ·
                    refine ⟨774002937924853404467761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1032003917233137872623681 774002937924853404467761)
                    ·
                      refine ⟨580502203443640053350821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774002937924853404467761 580502203443640053350821)
                      ·
                        rfl

theorem cell23_1130524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_1130524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130524 prefixEnd_1130524 := by exact prefixLift 1130524
  have htrace : WordTrace (prefixWord ++ tailWord_1130524) baseStart_1130524 baseEnd_1130524 := by
    simpa [prefixWord, tailWord_1130524, baseEnd_1130524] using wordTrace_append hprefix tailTrace_1130524
  have hstable : (prefixWord ++ tailWord_1130524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130524).length < 2 ^ (prefixWord ++ tailWord_1130524).sum := by decide
  have hdescent : baseEnd_1130524 < baseStart_1130524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130540 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_1130540 : Nat := 118140960795 + 1130540 * 2 ^ 59
def prefixEnd_1130540 : Nat := 4983230072969 + 3 ^ 40 * 1130540 * 2
def baseEnd_1130540 : Nat := 580510419134111990750747

theorem tailTrace_1130540 : CollatzResearch.WordTrace tailWord_1130540 prefixEnd_1130540 580510419134111990750747 := by
  unfold tailWord_1130540
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617090662127067852578537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27489454216169423803438049 20617090662127067852578537)
  ·
    refine ⟨15462817996595300889433903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20617090662127067852578537 15462817996595300889433903)
    ·
      refine ⟨23194226994892951334150855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15462817996595300889433903 23194226994892951334150855)
      ·
        refine ⟨34791340492339427001226283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23194226994892951334150855 34791340492339427001226283)
        ·
          refine ⟨52187010738509140501839425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34791340492339427001226283 52187010738509140501839425)
          ·
            refine ⟨39140258053881855376379569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52187010738509140501839425 39140258053881855376379569)
            ·
              refine ⟨29355193540411391532284677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39140258053881855376379569 29355193540411391532284677)
              ·
                refine ⟨5504098788827135912303377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29355193540411391532284677 5504098788827135912303377)
                ·
                  refine ⟨4128074091620351934227533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5504098788827135912303377 4128074091620351934227533)
                  ·
                    refine ⟨1548027784357631975335325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4128074091620351934227533 1548027784357631975335325)
                    ·
                      refine ⟨580510419134111990750747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548027784357631975335325 580510419134111990750747)
                      ·
                        rfl

theorem cell23_1130540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_1130540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130540 prefixEnd_1130540 := by exact prefixLift 1130540
  have htrace : WordTrace (prefixWord ++ tailWord_1130540) baseStart_1130540 baseEnd_1130540 := by
    simpa [prefixWord, tailWord_1130540, baseEnd_1130540] using wordTrace_append hprefix tailTrace_1130540
  have hstable : (prefixWord ++ tailWord_1130540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130540).length < 2 ^ (prefixWord ++ tailWord_1130540).sum := by decide
  have hdescent : baseEnd_1130540 < baseStart_1130540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130543 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 7]
def baseStart_1130543 : Nat := 118140960795 + 1130543 * 2 ^ 59
def prefixEnd_1130543 : Nat := 4983230072969 + 3 ^ 40 * 1130543 * 2
def baseEnd_1130543 : Nat := 193503986525358493004411

theorem tailTrace_1130543 : CollatzResearch.WordTrace tailWord_1130543 prefixEnd_1130543 193503986525358493004411 := by
  unfold tailWord_1130543
  simp only [CollatzResearch.WordTrace]
  refine ⟨41234290743243267217516283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27489527162162178145010855 41234290743243267217516283)
  ·
    refine ⟨61851436114864900826274425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41234290743243267217516283 61851436114864900826274425)
    ·
      refine ⟨46388577086148675619705819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61851436114864900826274425 46388577086148675619705819)
      ·
        refine ⟨69582865629223013429558729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46388577086148675619705819 69582865629223013429558729)
        ·
          refine ⟨52187149221917260072169047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69582865629223013429558729 52187149221917260072169047)
          ·
            refine ⟨78280723832875890108253571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52187149221917260072169047 78280723832875890108253571)
            ·
              refine ⟨117421085749313835162380357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78280723832875890108253571 117421085749313835162380357)
              ·
                refine ⟨22016453577996344092946317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117421085749313835162380357 22016453577996344092946317)
                ·
                  refine ⟨8256170091748629034854869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22016453577996344092946317 8256170091748629034854869)
                  ·
                    refine ⟨193503986525358493004411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8256170091748629034854869 193503986525358493004411)
                    ·
                      rfl

theorem cell23_1130543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_1130543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130543 prefixEnd_1130543 := by exact prefixLift 1130543
  have htrace : WordTrace (prefixWord ++ tailWord_1130543) baseStart_1130543 baseEnd_1130543 := by
    simpa [prefixWord, tailWord_1130543, baseEnd_1130543] using wordTrace_append hprefix tailTrace_1130543
  have hstable : (prefixWord ++ tailWord_1130543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130543).length < 2 ^ (prefixWord ++ tailWord_1130543).sum := by decide
  have hdescent : baseEnd_1130543 < baseStart_1130543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130558 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1130558 : Nat := 118140960795 + 1130558 * 2 ^ 59
def prefixEnd_1130558 : Nat := 4983230072969 + 3 ^ 40 * 1130558 * 2
def baseEnd_1130558 : Nat := 580519661785892920325665

theorem tailTrace_1130558 : CollatzResearch.WordTrace tailWord_1130558 prefixEnd_1130558 580519661785892920325665 := by
  unfold tailWord_1130558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154354729773615597414041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27489891892125949852874885 5154354729773615597414041)
  ·
    refine ⟨3865766047330211698060531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5154354729773615597414041 3865766047330211698060531)
    ·
      refine ⟨5798649070995317547090797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865766047330211698060531 5798649070995317547090797)
      ·
        refine ⟨2174493401623244080159049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5798649070995317547090797 2174493401623244080159049)
        ·
          refine ⟨1630870051217433060119287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2174493401623244080159049 1630870051217433060119287)
          ·
            refine ⟨2446305076826149590178931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630870051217433060119287 2446305076826149590178931)
            ·
              refine ⟨3669457615239224385268397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446305076826149590178931 3669457615239224385268397)
              ·
                refine ⟨1376046605714709144475649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3669457615239224385268397 1376046605714709144475649)
                ·
                  refine ⟨1032034954286031858356737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376046605714709144475649 1032034954286031858356737)
                  ·
                    refine ⟨774026215714523893767553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1032034954286031858356737 774026215714523893767553)
                    ·
                      refine ⟨580519661785892920325665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774026215714523893767553 580519661785892920325665)
                      ·
                        rfl

theorem cell23_1130558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1130558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130558 prefixEnd_1130558 := by exact prefixLift 1130558
  have htrace : WordTrace (prefixWord ++ tailWord_1130558) baseStart_1130558 baseEnd_1130558 := by
    simpa [prefixWord, tailWord_1130558, baseEnd_1130558] using wordTrace_append hprefix tailTrace_1130558
  have hstable : (prefixWord ++ tailWord_1130558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130558).length < 2 ^ (prefixWord ++ tailWord_1130558).sum := by decide
  have hdescent : baseEnd_1130558 < baseStart_1130558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130597 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1130597 : Nat := 118140960795 + 1130597 * 2 ^ 59
def prefixEnd_1130597 : Nat := 4983230072969 + 3 ^ 40 * 1130597 * 2
def baseEnd_1130597 : Nat := 580539687531418267737985

theorem tailTrace_1130597 : CollatzResearch.WordTrace tailWord_1130597 prefixEnd_1130597 580539687531418267737985 := by
  unfold tailWord_1130597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41236260285047634439982045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27490840190031756293321363 41236260285047634439982045)
  ·
    refine ⟨15463597606892862914993267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41236260285047634439982045 15463597606892862914993267)
    ·
      refine ⟨23195396410339294372489901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15463597606892862914993267 23195396410339294372489901)
      ·
        refine ⟨8698273653877235389683713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23195396410339294372489901 8698273653877235389683713)
        ·
          refine ⟨6523705240407926542262785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8698273653877235389683713 6523705240407926542262785)
          ·
            refine ⟨4892778930305944906697089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6523705240407926542262785 4892778930305944906697089)
            ·
              refine ⟨3669584197729458680022817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892778930305944906697089 3669584197729458680022817)
              ·
                refine ⟨2752188148297094010017113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3669584197729458680022817 2752188148297094010017113)
                ·
                  refine ⟨2064141111222820507512835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2752188148297094010017113 2064141111222820507512835)
                  ·
                    refine ⟨3096211666834230761269253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2064141111222820507512835 3096211666834230761269253)
                    ·
                      refine ⟨580539687531418267737985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3096211666834230761269253 580539687531418267737985)
                      ·
                        rfl

theorem cell23_1130597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1130597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130597 prefixEnd_1130597 := by exact prefixLift 1130597
  have htrace : WordTrace (prefixWord ++ tailWord_1130597) baseStart_1130597 baseEnd_1130597 := by
    simpa [prefixWord, tailWord_1130597, baseEnd_1130597] using wordTrace_append hprefix tailTrace_1130597
  have hstable : (prefixWord ++ tailWord_1130597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130597).length < 2 ^ (prefixWord ++ tailWord_1130597).sum := by decide
  have hdescent : baseEnd_1130597 < baseStart_1130597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130614 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1130614 : Nat := 118140960795 + 1130614 * 2 ^ 59
def prefixEnd_1130614 : Nat := 4983230072969 + 3 ^ 40 * 1130614 * 2
def baseEnd_1130614 : Nat := 580548416702544701225407

theorem tailTrace_1130614 : CollatzResearch.WordTrace tailWord_1130614 prefixEnd_1130614 580548416702544701225407 := by
  unfold tailWord_1130614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577305020374127896459431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27491253550657364228900597 2577305020374127896459431)
  ·
    refine ⟨3865957530561191844689147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2577305020374127896459431 3865957530561191844689147)
    ·
      refine ⟨5798936295841787767033721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3865957530561191844689147 5798936295841787767033721)
      ·
        refine ⟨4349202221881340825275291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5798936295841787767033721 4349202221881340825275291)
        ·
          refine ⟨6523803332822011237912937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349202221881340825275291 6523803332822011237912937)
          ·
            refine ⟨4892852499616508428434703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6523803332822011237912937 4892852499616508428434703)
            ·
              refine ⟨7339278749424762642652055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892852499616508428434703 7339278749424762642652055)
              ·
                refine ⟨11008918124137143963978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7339278749424762642652055 11008918124137143963978083)
                ·
                  refine ⟨16513377186205715945967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11008918124137143963978083 16513377186205715945967125)
                  ·
                    refine ⟨774064555603392934967209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16513377186205715945967125 774064555603392934967209)
                    ·
                      refine ⟨580548416702544701225407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774064555603392934967209 580548416702544701225407)
                      ·
                        rfl

theorem cell23_1130614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1130614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130614 prefixEnd_1130614 := by exact prefixLift 1130614
  have htrace : WordTrace (prefixWord ++ tailWord_1130614) baseStart_1130614 baseEnd_1130614 := by
    simpa [prefixWord, tailWord_1130614, baseEnd_1130614] using wordTrace_append hprefix tailTrace_1130614
  have hstable : (prefixWord ++ tailWord_1130614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130614).length < 2 ^ (prefixWord ++ tailWord_1130614).sum := by decide
  have hdescent : baseEnd_1130614 < baseStart_1130614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130634 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1130634 : Nat := 118140960795 + 1130634 * 2 ^ 59
def prefixEnd_1130634 : Nat := 4983230072969 + 3 ^ 40 * 1130634 * 2
def baseEnd_1130634 : Nat := 580558686315634622975315

theorem tailTrace_1130634 : CollatzResearch.WordTrace tailWord_1130634 prefixEnd_1130634 580558686315634622975315 := by
  unfold tailWord_1130634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309402446478397439769739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27491739857275726506052637 10309402446478397439769739)
  ·
    refine ⟨15464103669717596159654609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10309402446478397439769739 15464103669717596159654609)
    ·
      refine ⟨11598077752288197119740957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15464103669717596159654609 11598077752288197119740957)
      ·
        refine ⟨4349279157108073919902859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11598077752288197119740957 4349279157108073919902859)
        ·
          refine ⟨6523918735662110879854289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349279157108073919902859 6523918735662110879854289)
          ·
            refine ⟨4892939051746583159890717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6523918735662110879854289 4892939051746583159890717)
            ·
              refine ⟨1834852144404968684959019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4892939051746583159890717 1834852144404968684959019)
              ·
                refine ⟨2752278216607453027438529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834852144404968684959019 2752278216607453027438529)
                ·
                  refine ⟨2064208662455589770578897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2752278216607453027438529 2064208662455589770578897)
                  ·
                    refine ⟨1548156496841692327934173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064208662455589770578897 1548156496841692327934173)
                    ·
                      refine ⟨580558686315634622975315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548156496841692327934173 580558686315634622975315)
                      ·
                        rfl

theorem cell23_1130634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1130634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130634 prefixEnd_1130634 := by exact prefixLift 1130634
  have htrace : WordTrace (prefixWord ++ tailWord_1130634) baseStart_1130634 baseEnd_1130634 := by
    simpa [prefixWord, tailWord_1130634, baseEnd_1130634] using wordTrace_append hprefix tailTrace_1130634
  have hstable : (prefixWord ++ tailWord_1130634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130634).length < 2 ^ (prefixWord ++ tailWord_1130634).sum := by decide
  have hdescent : baseEnd_1130634 < baseStart_1130634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130654 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1130654 : Nat := 118140960795 + 1130654 * 2 ^ 59
def prefixEnd_1130654 : Nat := 4983230072969 + 3 ^ 40 * 1130654 * 2
def baseEnd_1130654 : Nat := 64507661769858282747247

theorem tailTrace_1130654 : CollatzResearch.WordTrace tailWord_1130654 prefixEnd_1130654 64507661769858282747247 := by
  unfold tailWord_1130654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154792405730141646850877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27492226163894088783204677 5154792405730141646850877)
  ·
    refine ⟨1933047152148803117569079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5154792405730141646850877 1933047152148803117569079)
    ·
      refine ⟨2899570728223204676353619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933047152148803117569079 2899570728223204676353619)
      ·
        refine ⟨4349356092334807014530429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899570728223204676353619 4349356092334807014530429)
        ·
          refine ⟨1631008534625552630448911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4349356092334807014530429 1631008534625552630448911)
          ·
            refine ⟨2446512801938328945673367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631008534625552630448911 2446512801938328945673367)
            ·
              refine ⟨3669769202907493418510051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446512801938328945673367 3669769202907493418510051)
              ·
                refine ⟨5504653804361240127765077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669769202907493418510051 5504653804361240127765077)
                ·
                  refine ⟨64507661769858282747247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5504653804361240127765077 64507661769858282747247)
                  ·
                    rfl

theorem cell23_1130654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1130654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130654 prefixEnd_1130654 := by exact prefixLift 1130654
  have htrace : WordTrace (prefixWord ++ tailWord_1130654) baseStart_1130654 baseEnd_1130654 := by
    simpa [prefixWord, tailWord_1130654, baseEnd_1130654] using wordTrace_append hprefix tailTrace_1130654
  have hstable : (prefixWord ++ tailWord_1130654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130654).length < 2 ^ (prefixWord ++ tailWord_1130654).sum := by decide
  have hdescent : baseEnd_1130654 < baseStart_1130654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130687 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 8, 2]
def baseStart_1130687 : Nat := 118140960795 + 1130687 * 2 ^ 59
def prefixEnd_1130687 : Nat := 4983230072969 + 3 ^ 40 * 1130687 * 2
def baseEnd_1130687 : Nat := 580585900790322915612571

theorem tailTrace_1130687 : CollatzResearch.WordTrace tailWord_1130687 prefixEnd_1130687 580585900790322915612571 := by
  unfold tailWord_1130687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41239542854721579810758315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27493028569814386540505543 41239542854721579810758315)
  ·
    refine ⟨61859314282082369716137473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41239542854721579810758315 61859314282082369716137473)
    ·
      refine ⟨46394485711561777287103105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61859314282082369716137473 46394485711561777287103105)
      ·
        refine ⟨34795864283671332965327329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46394485711561777287103105 34795864283671332965327329)
        ·
          refine ⟨26096898212753499723995497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34795864283671332965327329 26096898212753499723995497)
          ·
            refine ⟨19572673659565124792996623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26096898212753499723995497 19572673659565124792996623)
            ·
              refine ⟨29359010489347687189494935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19572673659565124792996623 29359010489347687189494935)
              ·
                refine ⟨44038515734021530784242403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29359010489347687189494935 44038515734021530784242403)
                ·
                  refine ⟨66057773601032296176363605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44038515734021530784242403 66057773601032296176363605)
                  ·
                    refine ⟨774114534387097220816761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66057773601032296176363605 774114534387097220816761)
                    ·
                      refine ⟨580585900790322915612571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774114534387097220816761 580585900790322915612571)
                      ·
                        rfl

theorem cell23_1130687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_1130687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130687 prefixEnd_1130687 := by exact prefixLift 1130687
  have htrace : WordTrace (prefixWord ++ tailWord_1130687) baseStart_1130687 baseEnd_1130687 := by
    simpa [prefixWord, tailWord_1130687, baseEnd_1130687] using wordTrace_append hprefix tailTrace_1130687
  have hstable : (prefixWord ++ tailWord_1130687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130687).length < 2 ^ (prefixWord ++ tailWord_1130687).sum := by decide
  have hdescent : baseEnd_1130687 < baseStart_1130687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130722 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1130722 : Nat := 118140960795 + 1130722 * 2 ^ 59
def prefixEnd_1130722 : Nat := 4983230072969 + 3 ^ 40 * 1130722 * 2
def baseEnd_1130722 : Nat := 64511541401470030963879

theorem tailTrace_1130722 : CollatzResearch.WordTrace tailWord_1130722 prefixEnd_1130722 64511541401470030963879 := by
  unfold tailWord_1130722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10310204852398695197070605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27493879606396520525521613 10310204852398695197070605)
  ·
    refine ⟨3866326819649510698901477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10310204852398695197070605 3866326819649510698901477)
    ·
      refine ⟨724936278684283256044027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3866326819649510698901477 724936278684283256044027)
      ·
        refine ⟨1087404418026424884066041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724936278684283256044027 1087404418026424884066041)
        ·
          refine ⟨815553313519818663049531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087404418026424884066041 815553313519818663049531)
          ·
            refine ⟨1223329970279727994574297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815553313519818663049531 1223329970279727994574297)
            ·
              refine ⟨917497477709795995930723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223329970279727994574297 917497477709795995930723)
              ·
                refine ⟨1376246216564693993896085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917497477709795995930723 1376246216564693993896085)
                ·
                  refine ⟨64511541401470030963879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1376246216564693993896085 64511541401470030963879)
                  ·
                    rfl

theorem cell23_1130722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1130722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130722 prefixEnd_1130722 := by exact prefixLift 1130722
  have htrace : WordTrace (prefixWord ++ tailWord_1130722) baseStart_1130722 baseEnd_1130722 := by
    simpa [prefixWord, tailWord_1130722, baseEnd_1130722] using wordTrace_append hprefix tailTrace_1130722
  have hstable : (prefixWord ++ tailWord_1130722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130722).length < 2 ^ (prefixWord ++ tailWord_1130722).sum := by decide
  have hdescent : baseEnd_1130722 < baseStart_1130722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130727 : List Nat := [1, 1, 5, 3, 1, 1, 1, 10]
def baseStart_1130727 : Nat := 118140960795 + 1130727 * 2 ^ 59
def prefixEnd_1130727 : Nat := 4983230072969 + 3 ^ 40 * 1130727 * 2
def baseEnd_1130727 : Nat := 21503942222833435522681

theorem tailTrace_1130727 : CollatzResearch.WordTrace tailWord_1130727 prefixEnd_1130727 21503942222833435522681 := by
  unfold tailWord_1130727
  simp only [CollatzResearch.WordTrace]
  refine ⟨41241001774576666642214435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27494001183051111094809623 41241001774576666642214435)
  ·
    refine ⟨61861502661864999963321653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41241001774576666642214435 61861502661864999963321653)
    ·
      refine ⟨5799515874549843746561405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61861502661864999963321653 5799515874549843746561405)
      ·
        refine ⟨2174818452956191404960527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5799515874549843746561405 2174818452956191404960527)
        ·
          refine ⟨3262227679434287107440791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174818452956191404960527 3262227679434287107440791)
          ·
            refine ⟨4893341519151430661161187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262227679434287107440791 4893341519151430661161187)
            ·
              refine ⟨7340012278727145991741781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893341519151430661161187 7340012278727145991741781)
              ·
                refine ⟨21503942222833435522681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7340012278727145991741781 21503942222833435522681)
                ·
                  rfl

theorem cell23_1130727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 10].length) (baseStart_1130727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130727 prefixEnd_1130727 := by exact prefixLift 1130727
  have htrace : WordTrace (prefixWord ++ tailWord_1130727) baseStart_1130727 baseEnd_1130727 := by
    simpa [prefixWord, tailWord_1130727, baseEnd_1130727] using wordTrace_append hprefix tailTrace_1130727
  have hstable : (prefixWord ++ tailWord_1130727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130727).length < 2 ^ (prefixWord ++ tailWord_1130727).sum := by decide
  have hdescent : baseEnd_1130727 < baseStart_1130727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130787 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 2, 6]
def baseStart_1130787 : Nat := 118140960795 + 1130787 * 2 ^ 59
def prefixEnd_1130787 : Nat := 4983230072969 + 3 ^ 40 * 1130787 * 2
def baseEnd_1130787 : Nat := 193545749618590841454037

theorem tailTrace_1130787 : CollatzResearch.WordTrace tailWord_1130787 prefixEnd_1130787 193545749618590841454037 := by
  unfold tailWord_1130787
  simp only [CollatzResearch.WordTrace]
  refine ⟨41243190154359296889398615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27495460102906197926265743 41243190154359296889398615)
  ·
    refine ⟨61864785231538945334097923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41243190154359296889398615 61864785231538945334097923)
    ·
      refine ⟨92797177847308418001146885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61864785231538945334097923 92797177847308418001146885)
      ·
        refine ⟨17399470846370328375215041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92797177847308418001146885 17399470846370328375215041)
        ·
          refine ⟨13049603134777746281411281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17399470846370328375215041 13049603134777746281411281)
          ·
            refine ⟨9787202351083309711058461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13049603134777746281411281 9787202351083309711058461)
            ·
              refine ⟨3670200881656241141646923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9787202351083309711058461 3670200881656241141646923)
              ·
                refine ⟨5505301322484361712470385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670200881656241141646923 5505301322484361712470385)
                ·
                  refine ⟨4128975991863271284352789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505301322484361712470385 4128975991863271284352789)
                  ·
                    refine ⟨193545749618590841454037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4128975991863271284352789 193545749618590841454037)
                    ·
                      rfl

theorem cell23_1130787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_1130787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130787 prefixEnd_1130787 := by exact prefixLift 1130787
  have htrace : WordTrace (prefixWord ++ tailWord_1130787) baseStart_1130787 baseEnd_1130787 := by
    simpa [prefixWord, tailWord_1130787, baseEnd_1130787] using wordTrace_append hprefix tailTrace_1130787
  have hstable : (prefixWord ++ tailWord_1130787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130787).length < 2 ^ (prefixWord ++ tailWord_1130787).sum := by decide
  have hdescent : baseEnd_1130787 < baseStart_1130787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130847 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 7]
def baseStart_1130847 : Nat := 118140960795 + 1130847 * 2 ^ 59
def prefixEnd_1130847 : Nat := 4983230072969 + 3 ^ 40 * 1130847 * 2
def baseEnd_1130847 : Nat := 193556019231680763203945

theorem tailTrace_1130847 : CollatzResearch.WordTrace tailWord_1130847 prefixEnd_1130847 193556019231680763203945 := by
  unfold tailWord_1130847
  simp only [CollatzResearch.WordTrace]
  refine ⟨41245378534141927136582795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27496919022761284757721863 41245378534141927136582795)
  ·
    refine ⟨61868067801212890704874193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41245378534141927136582795 61868067801212890704874193)
    ·
      refine ⟨46401050850909668028655645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61868067801212890704874193 46401050850909668028655645)
      ·
        refine ⟨17400394069091125510745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46401050850909668028655645 17400394069091125510745867)
        ·
          refine ⟨26100591103636688266118801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17400394069091125510745867 26100591103636688266118801)
          ·
            refine ⟨19575443327727516199589101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26100591103636688266118801 19575443327727516199589101)
            ·
              refine ⟨7340791247897818574845913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19575443327727516199589101 7340791247897818574845913)
              ·
                refine ⟨5505593435923363931134435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7340791247897818574845913 5505593435923363931134435)
                ·
                  refine ⟨8258390153885045896701653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505593435923363931134435 8258390153885045896701653)
                  ·
                    refine ⟨193556019231680763203945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8258390153885045896701653 193556019231680763203945)
                    ·
                      rfl

theorem cell23_1130847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_1130847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130847 prefixEnd_1130847 := by exact prefixLift 1130847
  have htrace : WordTrace (prefixWord ++ tailWord_1130847) baseStart_1130847 baseEnd_1130847 := by
    simpa [prefixWord, tailWord_1130847, baseEnd_1130847] using wordTrace_append hprefix tailTrace_1130847
  have hstable : (prefixWord ++ tailWord_1130847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130847).length < 2 ^ (prefixWord ++ tailWord_1130847).sum := by decide
  have hdescent : baseEnd_1130847 < baseStart_1130847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130881 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1130881 : Nat := 118140960795 + 1130881 * 2 ^ 59
def prefixEnd_1130881 : Nat := 4983230072969 + 3 ^ 40 * 1130881 * 2
def baseEnd_1130881 : Nat := 193561838679098385528893

theorem tailTrace_1130881 : CollatzResearch.WordTrace tailWord_1130881 prefixEnd_1130881 193561838679098385528893 := by
  unfold tailWord_1130881
  simp only [CollatzResearch.WordTrace]
  refine ⟨41246618616018750943320497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27497745744012500628880331 41246618616018750943320497)
  ·
    refine ⟨30934963962014063207490373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41246618616018750943320497 30934963962014063207490373)
    ·
      refine ⟨5800305742877636851404445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30934963962014063207490373 5800305742877636851404445)
      ·
        refine ⟨2175114653579113819276667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5800305742877636851404445 2175114653579113819276667)
        ·
          refine ⟨3262671980368670728915001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175114653579113819276667 3262671980368670728915001)
          ·
            refine ⟨2447003985276503046686251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3262671980368670728915001 2447003985276503046686251)
            ·
              refine ⟨3670505977914754570029377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447003985276503046686251 3670505977914754570029377)
              ·
                refine ⟨2752879483436065927522033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3670505977914754570029377 2752879483436065927522033)
                ·
                  refine ⟨2064659612577049445641525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2752879483436065927522033 2064659612577049445641525)
                  ·
                    refine ⟨193561838679098385528893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2064659612577049445641525 193561838679098385528893)
                    ·
                      rfl

theorem cell23_1130881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1130881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130881 prefixEnd_1130881 := by exact prefixLift 1130881
  have htrace : WordTrace (prefixWord ++ tailWord_1130881) baseStart_1130881 baseEnd_1130881 := by
    simpa [prefixWord, tailWord_1130881, baseEnd_1130881] using wordTrace_append hprefix tailTrace_1130881
  have hstable : (prefixWord ++ tailWord_1130881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130881).length < 2 ^ (prefixWord ++ tailWord_1130881).sum := by decide
  have hdescent : baseEnd_1130881 < baseStart_1130881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130927 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1130927 : Nat := 118140960795 + 1130927 * 2 ^ 59
def prefixEnd_1130927 : Nat := 4983230072969 + 3 ^ 40 * 1130927 * 2
def baseEnd_1130927 : Nat := 580709136147401976611467

theorem tailTrace_1130927 : CollatzResearch.WordTrace tailWord_1130927 prefixEnd_1130927 580709136147401976611467 := by
  unfold tailWord_1130927
  simp only [CollatzResearch.WordTrace]
  refine ⟨41248296373852100799495035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27498864249234733866330023 41248296373852100799495035)
  ·
    refine ⟨61872444560778151199242553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41248296373852100799495035 61872444560778151199242553)
    ·
      refine ⟨46404333420583613399431915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61872444560778151199242553 46404333420583613399431915)
      ·
        refine ⟨69606500130875420099147873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46404333420583613399431915 69606500130875420099147873)
        ·
          refine ⟨52204875098156565074360905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69606500130875420099147873 52204875098156565074360905)
          ·
            refine ⟨39153656323617423805770679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52204875098156565074360905 39153656323617423805770679)
            ·
              refine ⟨58730484485426135708656019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39153656323617423805770679 58730484485426135708656019)
              ·
                refine ⟨88095726728139203562984029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58730484485426135708656019 88095726728139203562984029)
                ·
                  refine ⟨33035897523052201336119011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88095726728139203562984029 33035897523052201336119011)
                  ·
                    refine ⟨49553846284578302004178517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33035897523052201336119011 49553846284578302004178517)
                    ·
                      refine ⟨580709136147401976611467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 49553846284578302004178517 580709136147401976611467)
                      ·
                        rfl

theorem cell23_1130927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1130927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130927 prefixEnd_1130927 := by exact prefixLift 1130927
  have htrace : WordTrace (prefixWord ++ tailWord_1130927) baseStart_1130927 baseEnd_1130927 := by
    simpa [prefixWord, tailWord_1130927, baseEnd_1130927] using wordTrace_append hprefix tailTrace_1130927
  have hstable : (prefixWord ++ tailWord_1130927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130927).length < 2 ^ (prefixWord ++ tailWord_1130927).sum := by decide
  have hdescent : baseEnd_1130927 < baseStart_1130927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130941 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 6]
def baseStart_1130941 : Nat := 118140960795 + 1130941 * 2 ^ 59
def prefixEnd_1130941 : Nat := 4983230072969 + 3 ^ 40 * 1130941 * 2
def baseEnd_1130941 : Nat := 64524036097396102426267

theorem tailTrace_1130941 : CollatzResearch.WordTrace tailWord_1130941 prefixEnd_1130941 64524036097396102426267 := by
  unfold tailWord_1130941
  simp only [CollatzResearch.WordTrace]
  refine ⟨41248806995801381190504677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27499204663867587460336451 41248806995801381190504677)
  ·
    refine ⟨7734151311712758973219627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41248806995801381190504677 7734151311712758973219627)
    ·
      refine ⟨11601226967569138459829441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7734151311712758973219627 11601226967569138459829441)
      ·
        refine ⟨8700920225676853844872081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11601226967569138459829441 8700920225676853844872081)
        ·
          refine ⟨6525690169257640383654061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8700920225676853844872081 6525690169257640383654061)
          ·
            refine ⟨2447133813471615143870273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6525690169257640383654061 2447133813471615143870273)
            ·
              refine ⟨1835350360103711357902705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447133813471615143870273 1835350360103711357902705)
              ·
                refine ⟨1376512770077783518427029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835350360103711357902705 1376512770077783518427029)
                ·
                  refine ⟨64524036097396102426267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1376512770077783518427029 64524036097396102426267)
                  ·
                    rfl

theorem cell23_1130941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_1130941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130941 prefixEnd_1130941 := by exact prefixLift 1130941
  have htrace : WordTrace (prefixWord ++ tailWord_1130941) baseStart_1130941 baseEnd_1130941 := by
    simpa [prefixWord, tailWord_1130941, baseEnd_1130941] using wordTrace_append hprefix tailTrace_1130941
  have hstable : (prefixWord ++ tailWord_1130941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130941).length < 2 ^ (prefixWord ++ tailWord_1130941).sum := by decide
  have hdescent : baseEnd_1130941 < baseStart_1130941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130954 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1130954 : Nat := 118140960795 + 1130954 * 2 ^ 59
def prefixEnd_1130954 : Nat := 4983230072969 + 3 ^ 40 * 1130954 * 2
def baseEnd_1130954 : Nat := 193574333375024456991281

theorem tailTrace_1130954 : CollatzResearch.WordTrace tailWord_1130954 prefixEnd_1130954 193574333375024456991281 := by
  unfold tailWord_1130954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10312320286188571102681979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27499520763169522940485277 10312320286188571102681979)
  ·
    refine ⟨15468480429282856654022969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10312320286188571102681979 15468480429282856654022969)
    ·
      refine ⟨11601360321962142490517227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15468480429282856654022969 11601360321962142490517227)
      ·
        refine ⟨17402040482943213735775841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11601360321962142490517227 17402040482943213735775841)
        ·
          refine ⟨13051530362207410301831881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17402040482943213735775841 13051530362207410301831881)
          ·
            refine ⟨9788647771655557726373911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13051530362207410301831881 9788647771655557726373911)
            ·
              refine ⟨14682971657483336589560867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9788647771655557726373911 14682971657483336589560867)
              ·
                refine ⟨22024457486225004884341301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14682971657483336589560867 22024457486225004884341301)
                ·
                  refine ⟨2064792889333594207906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22024457486225004884341301 2064792889333594207906997)
                  ·
                    refine ⟨193574333375024456991281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2064792889333594207906997 193574333375024456991281)
                    ·
                      rfl

theorem cell23_1130954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1130954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130954 prefixEnd_1130954 := by exact prefixLift 1130954
  have htrace : WordTrace (prefixWord ++ tailWord_1130954) baseStart_1130954 baseEnd_1130954 := by
    simpa [prefixWord, tailWord_1130954, baseEnd_1130954] using wordTrace_append hprefix tailTrace_1130954
  have hstable : (prefixWord ++ tailWord_1130954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130954).length < 2 ^ (prefixWord ++ tailWord_1130954).sum := by decide
  have hdescent : baseEnd_1130954 < baseStart_1130954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130961 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_1130961 : Nat := 118140960795 + 1130961 * 2 ^ 59
def prefixEnd_1130961 : Nat := 4983230072969 + 3 ^ 40 * 1130961 * 2
def baseEnd_1130961 : Nat := 580726594489654843586311

theorem tailTrace_1130961 : CollatzResearch.WordTrace tailWord_1130961 prefixEnd_1130961 580726594489654843586311 := by
  unfold tailWord_1130961
  simp only [CollatzResearch.WordTrace]
  refine ⟨41249536455728924606232737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27499690970485949737488491 41249536455728924606232737)
  ·
    refine ⟨30937152341796693454674553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41249536455728924606232737 30937152341796693454674553)
    ·
      refine ⟨23202864256347520091005915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30937152341796693454674553 23202864256347520091005915)
      ·
        refine ⟨34804296384521280136508873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23202864256347520091005915 34804296384521280136508873)
        ·
          refine ⟨26103222288390960102381655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34804296384521280136508873 26103222288390960102381655)
          ·
            refine ⟨39154833432586440153572483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26103222288390960102381655 39154833432586440153572483)
            ·
              refine ⟨58732250148879660230358725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39154833432586440153572483 58732250148879660230358725)
              ·
                refine ⟨11012296902914936293192261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58732250148879660230358725 11012296902914936293192261)
                ·
                  refine ⟨2064805669296550554973549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11012296902914936293192261 2064805669296550554973549)
                  ·
                    refine ⟨774302125986206458115081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064805669296550554973549 774302125986206458115081)
                    ·
                      refine ⟨580726594489654843586311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 774302125986206458115081 580726594489654843586311)
                      ·
                        rfl

theorem cell23_1130961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_1130961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1130961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1130961 prefixEnd_1130961 := by exact prefixLift 1130961
  have htrace : WordTrace (prefixWord ++ tailWord_1130961) baseStart_1130961 baseEnd_1130961 := by
    simpa [prefixWord, tailWord_1130961, baseEnd_1130961] using wordTrace_append hprefix tailTrace_1130961
  have hstable : (prefixWord ++ tailWord_1130961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130961).length < 2 ^ (prefixWord ++ tailWord_1130961).sum := by decide
  have hdescent : baseEnd_1130961 < baseStart_1130961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131004 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_1131004 : Nat := 118140960795 + 1131004 * 2 ^ 59
def prefixEnd_1131004 : Nat := 4983230072969 + 3 ^ 40 * 1131004 * 2
def baseEnd_1131004 : Nat := 580748674157798175348613

theorem tailTrace_1131004 : CollatzResearch.WordTrace tailWord_1131004 prefixEnd_1131004 580748674157798175348613 := by
  unfold tailWord_1131004
  simp only [CollatzResearch.WordTrace]
  refine ⟨20625552397286571475024033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27500736529715428633365377 20625552397286571475024033)
  ·
    refine ⟨15469164297964928606268025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20625552397286571475024033 15469164297964928606268025)
    ·
      refine ⟨11601873223473696454701019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15469164297964928606268025 11601873223473696454701019)
      ·
        refine ⟨17402809835210544682051529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11601873223473696454701019 17402809835210544682051529)
        ·
          refine ⟨13052107376407908511538647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17402809835210544682051529 13052107376407908511538647)
          ·
            refine ⟨19578161064611862767307971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13052107376407908511538647 19578161064611862767307971)
            ·
              refine ⟨29367241596917794150961957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19578161064611862767307971 29367241596917794150961957)
              ·
                refine ⟨5506357799422086403305367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29367241596917794150961957 5506357799422086403305367)
                ·
                  refine ⟨8259536699133129604958051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5506357799422086403305367 8259536699133129604958051)
                  ·
                    refine ⟨12389305048699694407437077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8259536699133129604958051 12389305048699694407437077)
                    ·
                      refine ⟨580748674157798175348613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12389305048699694407437077 580748674157798175348613)
                      ·
                        rfl

theorem cell23_1131004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_1131004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131004 prefixEnd_1131004 := by exact prefixLift 1131004
  have htrace : WordTrace (prefixWord ++ tailWord_1131004) baseStart_1131004 baseEnd_1131004 := by
    simpa [prefixWord, tailWord_1131004, baseEnd_1131004] using wordTrace_append hprefix tailTrace_1131004
  have hstable : (prefixWord ++ tailWord_1131004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131004).length < 2 ^ (prefixWord ++ tailWord_1131004).sum := by decide
  have hdescent : baseEnd_1131004 < baseStart_1131004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131041 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1131041 : Nat := 118140960795 + 1131041 * 2 ^ 59
def prefixEnd_1131041 : Nat := 4983230072969 + 3 ^ 40 * 1131041 * 2
def baseEnd_1131041 : Nat := 580767672942014530585943

theorem tailTrace_1131041 : CollatzResearch.WordTrace tailWord_1131041 prefixEnd_1131041 580767672942014530585943 := by
  unfold tailWord_1131041
  simp only [CollatzResearch.WordTrace]
  refine ⟨41252454295439098269144977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27501636196959398846096651 41252454295439098269144977)
  ·
    refine ⟨30939340721579323701858733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41252454295439098269144977 30939340721579323701858733)
    ·
      refine ⟨11602252770592246388197025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30939340721579323701858733 11602252770592246388197025)
      ·
        refine ⟨8701689577944184791147769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11602252770592246388197025 8701689577944184791147769)
        ·
          refine ⟨6526267183458138593360827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8701689577944184791147769 6526267183458138593360827)
          ·
            refine ⟨9789400775187207890041241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526267183458138593360827 9789400775187207890041241)
            ·
              refine ⟨7342050581390405917530931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9789400775187207890041241 7342050581390405917530931)
              ·
                refine ⟨11013075872085608876296397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342050581390405917530931 11013075872085608876296397)
                ·
                  refine ⟨4129903452032103328611149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11013075872085608876296397 4129903452032103328611149)
                  ·
                    refine ⟨1548713794512038748229181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4129903452032103328611149 1548713794512038748229181)
                    ·
                      refine ⟨580767672942014530585943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548713794512038748229181 580767672942014530585943)
                      ·
                        rfl

theorem cell23_1131041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1131041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131041 prefixEnd_1131041 := by exact prefixLift 1131041
  have htrace : WordTrace (prefixWord ++ tailWord_1131041) baseStart_1131041 baseEnd_1131041 := by
    simpa [prefixWord, tailWord_1131041, baseEnd_1131041] using wordTrace_append hprefix tailTrace_1131041
  have hstable : (prefixWord ++ tailWord_1131041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131041).length < 2 ^ (prefixWord ++ tailWord_1131041).sum := by decide
  have hdescent : baseEnd_1131041 < baseStart_1131041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131053 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1131053 : Nat := 118140960795 + 1131053 * 2 ^ 59
def prefixEnd_1131053 : Nat := 4983230072969 + 3 ^ 40 * 1131053 * 2
def baseEnd_1131053 : Nat := 580773834709868483635889

theorem tailTrace_1131053 : CollatzResearch.WordTrace tailWord_1131053 prefixEnd_1131053 580773834709868483635889 := by
  unfold tailWord_1131053
  simp only [CollatzResearch.WordTrace]
  refine ⟨41252891971395624318581813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27501927980930416212387875 41252891971395624318581813)
  ·
    refine ⟨3867458622318339779867045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41252891971395624318581813 3867458622318339779867045)
    ·
      refine ⟨725148491684688708725071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3867458622318339779867045 725148491684688708725071)
      ·
        refine ⟨1087722737527033063087607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725148491684688708725071 1087722737527033063087607)
        ·
          refine ⟨1631584106290549594631411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087722737527033063087607 1631584106290549594631411)
          ·
            refine ⟨2447376159435824391947117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631584106290549594631411 2447376159435824391947117)
            ·
              refine ⟨917766059788434146980169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2447376159435824391947117 917766059788434146980169)
              ·
                refine ⟨688324544841325610235127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917766059788434146980169 688324544841325610235127)
                ·
                  refine ⟨1032486817261988415352691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688324544841325610235127 1032486817261988415352691)
                  ·
                    refine ⟨1548730225892982623029037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1032486817261988415352691 1548730225892982623029037)
                    ·
                      refine ⟨580773834709868483635889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548730225892982623029037 580773834709868483635889)
                      ·
                        rfl

theorem cell23_1131053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1131053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131053 prefixEnd_1131053 := by exact prefixLift 1131053
  have htrace : WordTrace (prefixWord ++ tailWord_1131053) baseStart_1131053 baseEnd_1131053 := by
    simpa [prefixWord, tailWord_1131053, baseEnd_1131053] using wordTrace_append hprefix tailTrace_1131053
  have hstable : (prefixWord ++ tailWord_1131053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131053).length < 2 ^ (prefixWord ++ tailWord_1131053).sum := by decide
  have hdescent : baseEnd_1131053 < baseStart_1131053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131058 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1131058 : Nat := 118140960795 + 1131058 * 2 ^ 59
def prefixEnd_1131058 : Nat := 4983230072969 + 3 ^ 40 * 1131058 * 2
def baseEnd_1131058 : Nat := 580776402113140964073365

theorem tailTrace_1131058 : CollatzResearch.WordTrace tailWord_1131058 prefixEnd_1131058 580776402113140964073365 := by
  unfold tailWord_1131058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10313268584094377543128457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27502049557585006781675885 10313268584094377543128457)
  ·
    refine ⟨7734951438070783157346343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10313268584094377543128457 7734951438070783157346343)
    ·
      refine ⟨11602427157106174736019515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7734951438070783157346343 11602427157106174736019515)
      ·
        refine ⟨17403640735659262104029273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11602427157106174736019515 17403640735659262104029273)
        ·
          refine ⟨13052730551744446578021955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17403640735659262104029273 13052730551744446578021955)
          ·
            refine ⟨19579095827616669867032933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13052730551744446578021955 19579095827616669867032933)
            ·
              refine ⟨3671080467678125600068675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19579095827616669867032933 3671080467678125600068675)
              ·
                refine ⟨5506620701517188400103013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671080467678125600068675 5506620701517188400103013)
                ·
                  refine ⟨1032491381534472825019315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5506620701517188400103013 1032491381534472825019315)
                  ·
                    refine ⟨1548737072301709237528973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1032491381534472825019315 1548737072301709237528973)
                    ·
                      refine ⟨580776402113140964073365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548737072301709237528973 580776402113140964073365)
                      ·
                        rfl

theorem cell23_1131058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1131058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131058 prefixEnd_1131058 := by exact prefixLift 1131058
  have htrace : WordTrace (prefixWord ++ tailWord_1131058) baseStart_1131058 baseEnd_1131058 := by
    simpa [prefixWord, tailWord_1131058, baseEnd_1131058] using wordTrace_append hprefix tailTrace_1131058
  have hstable : (prefixWord ++ tailWord_1131058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131058).length < 2 ^ (prefixWord ++ tailWord_1131058).sum := by decide
  have hdescent : baseEnd_1131058 < baseStart_1131058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131076 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1131076 : Nat := 118140960795 + 1131076 * 2 ^ 59
def prefixEnd_1131076 : Nat := 4983230072969 + 3 ^ 40 * 1131076 * 2
def baseEnd_1131076 : Nat := 580785644764921893648283

theorem tailTrace_1131076 : CollatzResearch.WordTrace tailWord_1131076 prefixEnd_1131076 580785644764921893648283 := by
  unfold tailWord_1131076
  simp only [CollatzResearch.WordTrace]
  refine ⟨20626865425156149623334541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27502487233541532831112721 20626865425156149623334541)
  ·
    refine ⟨7735074534433556108750453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20626865425156149623334541 7735074534433556108750453)
    ·
      refine ⟨725163237603145885195355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7735074534433556108750453 725163237603145885195355)
      ·
        refine ⟨1087744856404718827793033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725163237603145885195355 1087744856404718827793033)
        ·
          refine ⟨815808642303539120844775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087744856404718827793033 815808642303539120844775)
          ·
            refine ⟨1223712963455308681267163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815808642303539120844775 1223712963455308681267163)
            ·
              refine ⟨1835569445182963021900745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223712963455308681267163 1835569445182963021900745)
              ·
                refine ⟨1376677083887222266425559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835569445182963021900745 1376677083887222266425559)
                ·
                  refine ⟨2065015625830833399638339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376677083887222266425559 2065015625830833399638339)
                  ·
                    refine ⟨3097523438746250099457509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065015625830833399638339 3097523438746250099457509)
                    ·
                      refine ⟨580785644764921893648283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3097523438746250099457509 580785644764921893648283)
                      ·
                        rfl

theorem cell23_1131076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1131076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131076 prefixEnd_1131076 := by exact prefixLift 1131076
  have htrace : WordTrace (prefixWord ++ tailWord_1131076) baseStart_1131076 baseEnd_1131076 := by
    simpa [prefixWord, tailWord_1131076, baseEnd_1131076] using wordTrace_append hprefix tailTrace_1131076
  have hstable : (prefixWord ++ tailWord_1131076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131076).length < 2 ^ (prefixWord ++ tailWord_1131076).sum := by decide
  have hdescent : baseEnd_1131076 < baseStart_1131076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131111 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1131111 : Nat := 118140960795 + 1131111 * 2 ^ 59
def prefixEnd_1131111 : Nat := 4983230072969 + 3 ^ 40 * 1131111 * 2
def baseEnd_1131111 : Nat := 580803616587829256710621

theorem tailTrace_1131111 : CollatzResearch.WordTrace tailWord_1131111 prefixEnd_1131111 580803616587829256710621 := by
  unfold tailWord_1131111
  simp only [CollatzResearch.WordTrace]
  refine ⟨41255007405185500224193187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27503338270123666816128791 41255007405185500224193187)
  ·
    refine ⟨61882511107778250336289781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41255007405185500224193187 61882511107778250336289781)
    ·
      refine ⟨5801485416354210969027167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61882511107778250336289781 5801485416354210969027167)
      ·
        refine ⟨8702228124531316453540751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801485416354210969027167 8702228124531316453540751)
        ·
          refine ⟨13053342186796974680311127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702228124531316453540751 13053342186796974680311127)
          ·
            refine ⟨19580013280195462020466691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13053342186796974680311127 19580013280195462020466691)
            ·
              refine ⟨29370019920293193030700037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19580013280195462020466691 29370019920293193030700037)
              ·
                refine ⟨5506878735054973693256257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29370019920293193030700037 5506878735054973693256257)
                ·
                  refine ⟨4130159051291230269942193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506878735054973693256257 4130159051291230269942193)
                  ·
                    refine ⟨3097619288468422702456645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4130159051291230269942193 3097619288468422702456645)
                    ·
                      refine ⟨580803616587829256710621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3097619288468422702456645 580803616587829256710621)
                      ·
                        rfl

theorem cell23_1131111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1131111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131111 prefixEnd_1131111 := by exact prefixLift 1131111
  have htrace : WordTrace (prefixWord ++ tailWord_1131111) baseStart_1131111 baseEnd_1131111 := by
    simpa [prefixWord, tailWord_1131111, baseEnd_1131111] using wordTrace_append hprefix tailTrace_1131111
  have hstable : (prefixWord ++ tailWord_1131111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131111).length < 2 ^ (prefixWord ++ tailWord_1131111).sum := by decide
  have hdescent : baseEnd_1131111 < baseStart_1131111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131118 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1131118 : Nat := 118140960795 + 1131118 * 2 ^ 59
def prefixEnd_1131118 : Nat := 4983230072969 + 3 ^ 40 * 1131118 * 2
def baseEnd_1131118 : Nat := 580807210952410729323089

theorem tailTrace_1131118 : CollatzResearch.WordTrace tailWord_1131118 prefixEnd_1131118 580807210952410729323089 := by
  unfold tailWord_1131118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156907839520017552462251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27503508477440093613132005 5156907839520017552462251)
  ·
    refine ⟨7735361759280026328693377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5156907839520017552462251 7735361759280026328693377)
    ·
      refine ⟨5801521319460019746520033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7735361759280026328693377 5801521319460019746520033)
      ·
        refine ⟨4351140989595014809890025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5801521319460019746520033 4351140989595014809890025)
        ·
          refine ⟨3263355742196261107417519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4351140989595014809890025 3263355742196261107417519)
          ·
            refine ⟨4895033613294391661126279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263355742196261107417519 4895033613294391661126279)
            ·
              refine ⟨7342550419941587491689419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895033613294391661126279 7342550419941587491689419)
              ·
                refine ⟨11013825629912381237534129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342550419941587491689419 11013825629912381237534129)
                ·
                  refine ⟨8260369222434285928150597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11013825629912381237534129 8260369222434285928150597)
                  ·
                    refine ⟨1548819229206428611528237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8260369222434285928150597 1548819229206428611528237)
                    ·
                      refine ⟨580807210952410729323089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548819229206428611528237 580807210952410729323089)
                      ·
                        rfl

theorem cell23_1131118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1131118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131118 prefixEnd_1131118 := by exact prefixLift 1131118
  have htrace : WordTrace (prefixWord ++ tailWord_1131118) baseStart_1131118 baseEnd_1131118 := by
    simpa [prefixWord, tailWord_1131118, baseEnd_1131118] using wordTrace_append hprefix tailTrace_1131118
  have hstable : (prefixWord ++ tailWord_1131118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131118).length < 2 ^ (prefixWord ++ tailWord_1131118).sum := by decide
  have hdescent : baseEnd_1131118 < baseStart_1131118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131206 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1131206 : Nat := 118140960795 + 1131206 * 2 ^ 59
def prefixEnd_1131206 : Nat := 4983230072969 + 3 ^ 40 * 1131206 * 2
def baseEnd_1131206 : Nat := 64539155250000709446965

theorem tailTrace_1131206 : CollatzResearch.WordTrace tailWord_1131206 prefixEnd_1131206 64539155250000709446965 := by
  unfold tailWord_1131206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289327260620041607778171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27505648226560887632600981 1289327260620041607778171)
  ·
    refine ⟨1933990890930062411667257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289327260620041607778171 1933990890930062411667257)
    ·
      refine ⟨1450493168197546808750443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1933990890930062411667257 1450493168197546808750443)
      ·
        refine ⟨2175739752296320213125665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450493168197546808750443 2175739752296320213125665)
        ·
          refine ⟨1631804814222240159844249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175739752296320213125665 1631804814222240159844249)
          ·
            refine ⟨1223853610666680119883187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1631804814222240159844249 1223853610666680119883187)
            ·
              refine ⟨1835780416000020179824781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223853610666680119883187 1835780416000020179824781)
              ·
                refine ⟨688417656000007567434293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1835780416000020179824781 688417656000007567434293)
                ·
                  refine ⟨64539155250000709446965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 688417656000007567434293 64539155250000709446965)
                  ·
                    rfl

theorem cell23_1131206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1131206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131206 prefixEnd_1131206 := by exact prefixLift 1131206
  have htrace : WordTrace (prefixWord ++ tailWord_1131206) baseStart_1131206 baseEnd_1131206 := by
    simpa [prefixWord, tailWord_1131206, baseEnd_1131206] using wordTrace_append hprefix tailTrace_1131206
  have hstable : (prefixWord ++ tailWord_1131206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131206).length < 2 ^ (prefixWord ++ tailWord_1131206).sum := by decide
  have hdescent : baseEnd_1131206 < baseStart_1131206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131208 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_1131208 : Nat := 118140960795 + 1131208 * 2 ^ 59
def prefixEnd_1131208 : Nat := 4983230072969 + 3 ^ 40 * 1131208 * 2
def baseEnd_1131208 : Nat := 580853424211315377197675

theorem tailTrace_1131208 : CollatzResearch.WordTrace tailWord_1131208 prefixEnd_1131208 580853424211315377197675 := by
  unfold tailWord_1131208
  simp only [CollatzResearch.WordTrace]
  refine ⟨20629272642917042895237139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27505696857222723860316185 20629272642917042895237139)
  ·
    refine ⟨30943908964375564342855709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20629272642917042895237139 30943908964375564342855709)
    ·
      refine ⟨11603965861640836628570891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30943908964375564342855709 11603965861640836628570891)
      ·
        refine ⟨17405948792461254942856337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11603965861640836628570891 17405948792461254942856337)
        ·
          refine ⟨13054461594345941207142253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17405948792461254942856337 13054461594345941207142253)
          ·
            refine ⟨4895423097879727952678345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13054461594345941207142253 4895423097879727952678345)
            ·
              refine ⟨3671567323409795964508759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895423097879727952678345 3671567323409795964508759)
              ·
                refine ⟨5507350985114693946763139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671567323409795964508759 5507350985114693946763139)
                ·
                  refine ⟨8261026477672040920144709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507350985114693946763139 8261026477672040920144709)
                  ·
                    refine ⟨1548942464563507672527133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8261026477672040920144709 1548942464563507672527133)
                    ·
                      refine ⟨580853424211315377197675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1548942464563507672527133 580853424211315377197675)
                      ·
                        rfl

theorem cell23_1131208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_1131208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1131208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1131208 prefixEnd_1131208 := by exact prefixLift 1131208
  have htrace : WordTrace (prefixWord ++ tailWord_1131208) baseStart_1131208 baseEnd_1131208 := by
    simpa [prefixWord, tailWord_1131208, baseEnd_1131208] using wordTrace_append hprefix tailTrace_1131208
  have hstable : (prefixWord ++ tailWord_1131208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131208).length < 2 ^ (prefixWord ++ tailWord_1131208).sum := by decide
  have hdescent : baseEnd_1131208 < baseStart_1131208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
