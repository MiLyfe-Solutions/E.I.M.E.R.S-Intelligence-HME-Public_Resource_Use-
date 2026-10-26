import V185TrunkScan20Chunk099

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_608152 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_608152 : Nat := 118140960795 + 608152 * 2 ^ 59
def prefixEnd_608152 : Nat := 4983230072969 + 3 ^ 40 * 608152 * 2
def baseEnd_608152 : Nat := 277577143993964298847259

theorem tailTrace_608152 : CollatzResearch.WordTrace tailWord_608152 prefixEnd_608152 277577143993964298847259 := by
  unfold tailWord_608152
  simp only [CollatzResearch.WordTrace]
  refine ⟨11090562846388321468833355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14787417128517761958444473 11090562846388321468833355)
  ·
    refine ⟨16635844269582482203250033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11090562846388321468833355 16635844269582482203250033)
    ·
      refine ⟨12476883202186861652437525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16635844269582482203250033 12476883202186861652437525)
      ·
        refine ⟨584853900102509139958009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12476883202186861652437525 584853900102509139958009)
        ·
          refine ⟨438640425076881854968507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584853900102509139958009 438640425076881854968507)
          ·
            refine ⟨657960637615322782452761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438640425076881854968507 657960637615322782452761)
            ·
              refine ⟨493470478211492086839571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657960637615322782452761 493470478211492086839571)
              ·
                refine ⟨740205717317238130259357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493470478211492086839571 740205717317238130259357)
                ·
                  refine ⟨277577143993964298847259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740205717317238130259357 277577143993964298847259)
                  ·
                    rfl

theorem cell20_608152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_608152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608152 prefixEnd_608152 := by exact prefixLift 608152
  have htrace : WordTrace (prefixWord ++ tailWord_608152) baseStart_608152 baseEnd_608152 := by
    simpa [prefixWord, tailWord_608152, baseEnd_608152] using wordTrace_append hprefix tailTrace_608152
  have hstable : (prefixWord ++ tailWord_608152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608152).length < 2 ^ (prefixWord ++ tailWord_608152).sum := by decide
  have hdescent : baseEnd_608152 < baseStart_608152 := by decide
  rcases family_descends (prefixWord ++ tailWord_608152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608156 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_608156 : Nat := 118140960795 + 608156 * 2 ^ 59
def prefixEnd_608156 : Nat := 4983230072969 + 3 ^ 40 * 608156 * 2
def baseEnd_608156 : Nat := 277578969702958062713909

theorem tailTrace_608156 : CollatzResearch.WordTrace tailWord_608156 prefixEnd_608156 277578969702958062713909 := by
  unfold tailWord_608156
  simp only [CollatzResearch.WordTrace]
  refine ⟨11090635792381075810406161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14787514389841434413874881 11090635792381075810406161)
  ·
    refine ⟨8317976844285806857804621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11090635792381075810406161 8317976844285806857804621)
    ·
      refine ⟨3119241316607177571676733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8317976844285806857804621 3119241316607177571676733)
      ·
        refine ⟨1169715493727691589378775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3119241316607177571676733 1169715493727691589378775)
        ·
          refine ⟨1754573240591537384068163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169715493727691589378775 1754573240591537384068163)
          ·
            refine ⟨2631859860887306076102245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754573240591537384068163 2631859860887306076102245)
            ·
              refine ⟨493473723916369889269171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2631859860887306076102245 493473723916369889269171)
              ·
                refine ⟨740210585874554833903757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493473723916369889269171 740210585874554833903757)
                ·
                  refine ⟨277578969702958062713909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740210585874554833903757 277578969702958062713909)
                  ·
                    rfl

theorem cell20_608156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_608156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608156 prefixEnd_608156 := by exact prefixLift 608156
  have htrace : WordTrace (prefixWord ++ tailWord_608156) baseStart_608156 baseEnd_608156 := by
    simpa [prefixWord, tailWord_608156, baseEnd_608156] using wordTrace_append hprefix tailTrace_608156
  have hstable : (prefixWord ++ tailWord_608156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608156).length < 2 ^ (prefixWord ++ tailWord_608156).sum := by decide
  have hdescent : baseEnd_608156 < baseStart_608156 := by decide
  rcases family_descends (prefixWord ++ tailWord_608156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608184 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_608184 : Nat := 118140960795 + 608184 * 2 ^ 59
def prefixEnd_608184 : Nat := 4983230072969 + 3 ^ 40 * 608184 * 2
def baseEnd_608184 : Nat := 277591749665914409780461

theorem tailTrace_608184 : CollatzResearch.WordTrace tailWord_608184 prefixEnd_608184 277591749665914409780461 := by
  unfold tailWord_608184
  simp only [CollatzResearch.WordTrace]
  refine ⟨11091146414330356201415803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14788195219107141601887737 11091146414330356201415803)
  ·
    refine ⟨16636719621495534302123705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11091146414330356201415803 16636719621495534302123705)
    ·
      refine ⟨12477539716121650726592779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16636719621495534302123705 12477539716121650726592779)
      ·
        refine ⟨18716309574182476089889169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12477539716121650726592779 18716309574182476089889169)
        ·
          refine ⟨14037232180636857067416877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18716309574182476089889169 14037232180636857067416877)
          ·
            refine ⟨5263962067738821400281329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14037232180636857067416877 5263962067738821400281329)
            ·
              refine ⟨3947971550804116050210997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5263962067738821400281329 3947971550804116050210997)
              ·
                refine ⟨370122332887885879707281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3947971550804116050210997 370122332887885879707281)
                ·
                  refine ⟨277591749665914409780461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370122332887885879707281 277591749665914409780461)
                  ·
                    rfl

theorem cell20_608184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_608184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608184 prefixEnd_608184 := by exact prefixLift 608184
  have htrace : WordTrace (prefixWord ++ tailWord_608184) baseStart_608184 baseEnd_608184 := by
    simpa [prefixWord, tailWord_608184, baseEnd_608184] using wordTrace_append hprefix tailTrace_608184
  have hstable : (prefixWord ++ tailWord_608184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608184).length < 2 ^ (prefixWord ++ tailWord_608184).sum := by decide
  have hdescent : baseEnd_608184 < baseStart_608184 := by decide
  rcases family_descends (prefixWord ++ tailWord_608184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608284 : List Nat := [2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_608284 : Nat := 118140960795 + 608284 * 2 ^ 59
def prefixEnd_608284 : Nat := 4983230072969 + 3 ^ 40 * 608284 * 2
def baseEnd_608284 : Nat := 92545797463586168815573

theorem tailTrace_608284 : CollatzResearch.WordTrace tailWord_608284 prefixEnd_608284 92545797463586168815573 := by
  unfold tailWord_608284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092970064149214740735953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14790626752198952987647937 11092970064149214740735953)
  ·
    refine ⟨8319727548111911055551965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11092970064149214740735953 8319727548111911055551965)
    ·
      refine ⟨3119897830541966645831987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8319727548111911055551965 3119897830541966645831987)
      ·
        refine ⟨4679846745812949968747981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119897830541966645831987 4679846745812949968747981)
        ·
          refine ⟨1754942529679856238280493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4679846745812949968747981 1754942529679856238280493)
          ·
            refine ⟨658103448629946089355185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1754942529679856238280493 658103448629946089355185)
            ·
              refine ⟨493577586472459567016389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658103448629946089355185 493577586472459567016389)
              ·
                refine ⟨92545797463586168815573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493577586472459567016389 92545797463586168815573)
                ·
                  rfl

theorem cell20_608284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_608284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608284 prefixEnd_608284 := by exact prefixLift 608284
  have htrace : WordTrace (prefixWord ++ tailWord_608284) baseStart_608284 baseEnd_608284 := by
    simpa [prefixWord, tailWord_608284, baseEnd_608284] using wordTrace_append hprefix tailTrace_608284
  have hstable : (prefixWord ++ tailWord_608284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608284).length < 2 ^ (prefixWord ++ tailWord_608284).sum := by decide
  have hdescent : baseEnd_608284 < baseStart_608284 := by decide
  rcases family_descends (prefixWord ++ tailWord_608284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608319 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_608319 : Nat := 118140960795 + 608319 * 2 ^ 59
def prefixEnd_608319 : Nat := 4983230072969 + 3 ^ 40 * 608319 * 2
def baseEnd_608319 : Nat := 277653367344453940279909

theorem tailTrace_608319 : CollatzResearch.WordTrace tailWord_608319 prefixEnd_608319 277653367344453940279909 := by
  unfold tailWord_608319
  simp only [CollatzResearch.WordTrace]
  refine ⟨22187216683171630458996011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14791477788781086972664007 22187216683171630458996011)
  ·
    refine ⟨33280825024757445688494017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22187216683171630458996011 33280825024757445688494017)
    ·
      refine ⟨24960618768568084266370513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33280825024757445688494017 24960618768568084266370513)
      ·
        refine ⟨18720464076426063199777885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24960618768568084266370513 18720464076426063199777885)
        ·
          refine ⟨7020174028659773699916707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18720464076426063199777885 7020174028659773699916707)
          ·
            refine ⟨10530261042989660549875061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7020174028659773699916707 10530261042989660549875061)
            ·
              refine ⟨987211972780280676550787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10530261042989660549875061 987211972780280676550787)
              ·
                refine ⟨1480817959170421014826181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987211972780280676550787 1480817959170421014826181)
                ·
                  refine ⟨277653367344453940279909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480817959170421014826181 277653367344453940279909)
                  ·
                    rfl

theorem cell20_608319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_608319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608319 prefixEnd_608319 := by exact prefixLift 608319
  have htrace : WordTrace (prefixWord ++ tailWord_608319) baseStart_608319 baseEnd_608319 := by
    simpa [prefixWord, tailWord_608319, baseEnd_608319] using wordTrace_append hprefix tailTrace_608319
  have hstable : (prefixWord ++ tailWord_608319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608319).length < 2 ^ (prefixWord ++ tailWord_608319).sum := by decide
  have hdescent : baseEnd_608319 < baseStart_608319 := by decide
  rcases family_descends (prefixWord ++ tailWord_608319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608370 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_608370 : Nat := 118140960795 + 608370 * 2 ^ 59
def prefixEnd_608370 : Nat := 4983230072969 + 3 ^ 40 * 608370 * 2
def baseEnd_608370 : Nat := 277676645134124429579701

theorem tailTrace_608370 : CollatzResearch.WordTrace tailWord_608370 prefixEnd_608370 277676645134124429579701 := by
  unfold tailWord_608370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547269201496716542275641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14792717870657910779401709 5547269201496716542275641)
  ·
    refine ⟨4160451901122537406706731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5547269201496716542275641 4160451901122537406706731)
    ·
      refine ⟨6240677851683806110060097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160451901122537406706731 6240677851683806110060097)
      ·
        refine ⟨4680508388762854582545073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6240677851683806110060097 4680508388762854582545073)
        ·
          refine ⟨3510381291572140936908805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4680508388762854582545073 3510381291572140936908805)
          ·
            refine ⟨658196492169776425670401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3510381291572140936908805 658196492169776425670401)
            ·
              refine ⟨493647369127332319252801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658196492169776425670401 493647369127332319252801)
              ·
                refine ⟨370235526845499239439601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493647369127332319252801 370235526845499239439601)
                ·
                  refine ⟨277676645134124429579701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370235526845499239439601 277676645134124429579701)
                  ·
                    rfl

theorem cell20_608370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_608370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608370 prefixEnd_608370 := by exact prefixLift 608370
  have htrace : WordTrace (prefixWord ++ tailWord_608370) baseStart_608370 baseEnd_608370 := by
    simpa [prefixWord, tailWord_608370, baseEnd_608370] using wordTrace_append hprefix tailTrace_608370
  have hstable : (prefixWord ++ tailWord_608370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608370).length < 2 ^ (prefixWord ++ tailWord_608370).sum := by decide
  have hdescent : baseEnd_608370 < baseStart_608370 := by decide
  rcases family_descends (prefixWord ++ tailWord_608370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608378 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_608378 : Nat := 118140960795 + 608378 * 2 ^ 59
def prefixEnd_608378 : Nat := 4983230072969 + 3 ^ 40 * 608378 * 2
def baseEnd_608378 : Nat := 277680296552111957313001

theorem tailTrace_608378 : CollatzResearch.WordTrace tailWord_608378 prefixEnd_608378 277680296552111957313001 := by
  unfold tailWord_608378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547342147489470883848447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14792912393305255690262525 5547342147489470883848447)
  ·
    refine ⟨8321013221234206325772671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547342147489470883848447 8321013221234206325772671)
    ·
      refine ⟨12481519831851309488659007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321013221234206325772671 12481519831851309488659007)
      ·
        refine ⟨18722279747776964232988511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12481519831851309488659007 18722279747776964232988511)
        ·
          refine ⟨28083419621665446349482767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18722279747776964232988511 28083419621665446349482767)
          ·
            refine ⟨42125129432498169524224151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28083419621665446349482767 42125129432498169524224151)
            ·
              refine ⟨63187694148747254286336227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42125129432498169524224151 63187694148747254286336227)
              ·
                refine ⟨94781541223120881429504341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63187694148747254286336227 94781541223120881429504341)
                ·
                  refine ⟨277680296552111957313001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94781541223120881429504341 277680296552111957313001)
                  ·
                    rfl

theorem cell20_608378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_608378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608378 prefixEnd_608378 := by exact prefixLift 608378
  have htrace : WordTrace (prefixWord ++ tailWord_608378) baseStart_608378 baseEnd_608378 := by
    simpa [prefixWord, tailWord_608378, baseEnd_608378] using wordTrace_append hprefix tailTrace_608378
  have hstable : (prefixWord ++ tailWord_608378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608378).length < 2 ^ (prefixWord ++ tailWord_608378).sum := by decide
  have hdescent : baseEnd_608378 < baseStart_608378 := by decide
  rcases family_descends (prefixWord ++ tailWord_608378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608381 : List Nat := [1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_608381 : Nat := 118140960795 + 608381 * 2 ^ 59
def prefixEnd_608381 : Nat := 4983230072969 + 3 ^ 40 * 608381 * 2
def baseEnd_608381 : Nat := 92560555277952426737663

theorem tailTrace_608381 : CollatzResearch.WordTrace tailWord_608381 prefixEnd_608381 92560555277952426737663 := by
  unfold tailWord_608381
  simp only [CollatzResearch.WordTrace]
  refine ⟨22189478008947015047752997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14792985339298010031835331 22189478008947015047752997)
  ·
    refine ⟨4160527126677565321453687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22189478008947015047752997 4160527126677565321453687)
    ·
      refine ⟨6240790690016347982180531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160527126677565321453687 6240790690016347982180531)
      ·
        refine ⟨9361186035024521973270797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240790690016347982180531 9361186035024521973270797)
        ·
          refine ⟨3510444763134195739976549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9361186035024521973270797 3510444763134195739976549)
          ·
            refine ⟨658208393087661701245603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3510444763134195739976549 658208393087661701245603)
            ·
              refine ⟨987312589631492551868405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658208393087661701245603 987312589631492551868405)
              ·
                refine ⟨92560555277952426737663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 987312589631492551868405 92560555277952426737663)
                ·
                  rfl

theorem cell20_608381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_608381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608381 prefixEnd_608381 := by exact prefixLift 608381
  have htrace : WordTrace (prefixWord ++ tailWord_608381) baseStart_608381 baseEnd_608381 := by
    simpa [prefixWord, tailWord_608381, baseEnd_608381] using wordTrace_append hprefix tailTrace_608381
  have hstable : (prefixWord ++ tailWord_608381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608381).length < 2 ^ (prefixWord ++ tailWord_608381).sum := by decide
  have hdescent : baseEnd_608381 < baseStart_608381 := by decide
  rcases family_descends (prefixWord ++ tailWord_608381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608388 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_608388 : Nat := 118140960795 + 608388 * 2 ^ 59
def prefixEnd_608388 : Nat := 4983230072969 + 3 ^ 40 * 608388 * 2
def baseEnd_608388 : Nat := 277684860824596366979627

theorem tailTrace_608388 : CollatzResearch.WordTrace tailWord_608388 prefixEnd_608388 277684860824596366979627 := by
  unfold tailWord_608388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11094866659960827621628909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14793155546614436828838545 11094866659960827621628909)
  ·
    refine ⟨4160574997485310358110841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11094866659960827621628909 4160574997485310358110841)
    ·
      refine ⟨3120431248113982768583131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4160574997485310358110841 3120431248113982768583131)
      ·
        refine ⟨4680646872170974152874697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120431248113982768583131 4680646872170974152874697)
        ·
          refine ⟨3510485154128230614656023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4680646872170974152874697 3510485154128230614656023)
          ·
            refine ⟨5265727731192345921984035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510485154128230614656023 5265727731192345921984035)
            ·
              refine ⟨7898591596788518882976053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265727731192345921984035 7898591596788518882976053)
              ·
                refine ⟨740492962198923645279005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7898591596788518882976053 740492962198923645279005)
                ·
                  refine ⟨277684860824596366979627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740492962198923645279005 277684860824596366979627)
                  ·
                    rfl

theorem cell20_608388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_608388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608388 prefixEnd_608388 := by exact prefixLift 608388
  have htrace : WordTrace (prefixWord ++ tailWord_608388) baseStart_608388 baseEnd_608388 := by
    simpa [prefixWord, tailWord_608388, baseEnd_608388] using wordTrace_append hprefix tailTrace_608388
  have hstable : (prefixWord ++ tailWord_608388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608388).length < 2 ^ (prefixWord ++ tailWord_608388).sum := by decide
  have hdescent : baseEnd_608388 < baseStart_608388 := by decide
  rcases family_descends (prefixWord ++ tailWord_608388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608398 : List Nat := [4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_608398 : Nat := 118140960795 + 608398 * 2 ^ 59
def prefixEnd_608398 : Nat := 4983230072969 + 3 ^ 40 * 608398 * 2
def baseEnd_608398 : Nat := 92563141699026925548751

theorem tailTrace_608398 : CollatzResearch.WordTrace tailWord_608398 prefixEnd_608398 92563141699026925548751 := by
  unfold tailWord_608398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773762256235678368890231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14793398699923617967414565 2773762256235678368890231)
  ·
    refine ⟨4160643384353517553335347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773762256235678368890231 4160643384353517553335347)
    ·
      refine ⟨6240965076530276330003021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160643384353517553335347 6240965076530276330003021)
      ·
        refine ⟨2340361903698853623751133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6240965076530276330003021 2340361903698853623751133)
        ·
          refine ⟨877635713887070108906675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2340361903698853623751133 877635713887070108906675)
          ·
            refine ⟨1316453570830605163360013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877635713887070108906675 1316453570830605163360013)
            ·
              refine ⟨493670089061476936260005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1316453570830605163360013 493670089061476936260005)
              ·
                refine ⟨92563141699026925548751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493670089061476936260005 92563141699026925548751)
                ·
                  rfl

theorem cell20_608398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_608398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608398 prefixEnd_608398 := by exact prefixLift 608398
  have htrace : WordTrace (prefixWord ++ tailWord_608398) baseStart_608398 baseEnd_608398 := by
    simpa [prefixWord, tailWord_608398, baseEnd_608398] using wordTrace_append hprefix tailTrace_608398
  have hstable : (prefixWord ++ tailWord_608398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608398).length < 2 ^ (prefixWord ++ tailWord_608398).sum := by decide
  have hdescent : baseEnd_608398 < baseStart_608398 := by decide
  rcases family_descends (prefixWord ++ tailWord_608398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608429 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 2]
def baseStart_608429 : Nat := 118140960795 + 608429 * 2 ^ 59
def prefixEnd_608429 : Nat := 4983230072969 + 3 ^ 40 * 608429 * 2
def baseEnd_608429 : Nat := 277703574341782446612793

theorem tailTrace_608429 : CollatzResearch.WordTrace tailWord_608429 prefixEnd_608429 277703574341782446612793 := by
  unfold tailWord_608429
  simp only [CollatzResearch.WordTrace]
  refine ⟨22191228712773119245500341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14794152475182079497000227 22191228712773119245500341)
  ·
    refine ⟨2080427691822479929265657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22191228712773119245500341 2080427691822479929265657)
    ·
      refine ⟨1560320768866859946949243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2080427691822479929265657 1560320768866859946949243)
      ·
        refine ⟨2340481153300289920423865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560320768866859946949243 2340481153300289920423865)
        ·
          refine ⟨1755360864975217440317899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340481153300289920423865 1755360864975217440317899)
          ·
            refine ⟨2633041297462826160476849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755360864975217440317899 2633041297462826160476849)
            ·
              refine ⟨1974780973097119620357637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633041297462826160476849 1974780973097119620357637)
              ·
                refine ⟨370271432455709928817057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1974780973097119620357637 370271432455709928817057)
                ·
                  refine ⟨277703574341782446612793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370271432455709928817057 277703574341782446612793)
                  ·
                    rfl

theorem cell20_608429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_608429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608429 prefixEnd_608429 := by exact prefixLift 608429
  have htrace : WordTrace (prefixWord ++ tailWord_608429) baseStart_608429 baseEnd_608429 := by
    simpa [prefixWord, tailWord_608429, baseEnd_608429] using wordTrace_append hprefix tailTrace_608429
  have hstable : (prefixWord ++ tailWord_608429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608429).length < 2 ^ (prefixWord ++ tailWord_608429).sum := by decide
  have hdescent : baseEnd_608429 < baseStart_608429 := by decide
  rcases family_descends (prefixWord ++ tailWord_608429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608488 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_608488 : Nat := 118140960795 + 608488 * 2 ^ 59
def prefixEnd_608488 : Nat := 4983230072969 + 3 ^ 40 * 608488 * 2
def baseEnd_608488 : Nat := 277730503549440463645885

theorem tailTrace_608488 : CollatzResearch.WordTrace tailWord_608488 prefixEnd_608488 277730503549440463645885 := by
  unfold tailWord_608488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11096690309779686160949059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14795587079706248214598745 11096690309779686160949059)
  ·
    refine ⟨16645035464669529241423589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11096690309779686160949059 16645035464669529241423589)
    ·
      refine ⟨3120944149625536732766923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16645035464669529241423589 3120944149625536732766923)
      ·
        refine ⟨4681416224438305099150385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120944149625536732766923 4681416224438305099150385)
        ·
          refine ⟨3511062168328728824362789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4681416224438305099150385 3511062168328728824362789)
          ·
            refine ⟨658324156561636654568023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3511062168328728824362789 658324156561636654568023)
            ·
              refine ⟨987486234842454981852035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658324156561636654568023 987486234842454981852035)
              ·
                refine ⟨1481229352263682472778053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987486234842454981852035 1481229352263682472778053)
                ·
                  refine ⟨277730503549440463645885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481229352263682472778053 277730503549440463645885)
                  ·
                    rfl

theorem cell20_608488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_608488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608488 prefixEnd_608488 := by exact prefixLift 608488
  have htrace : WordTrace (prefixWord ++ tailWord_608488) baseStart_608488 baseEnd_608488 := by
    simpa [prefixWord, tailWord_608488, baseEnd_608488] using wordTrace_append hprefix tailTrace_608488
  have hstable : (prefixWord ++ tailWord_608488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608488).length < 2 ^ (prefixWord ++ tailWord_608488).sum := by decide
  have hdescent : baseEnd_608488 < baseStart_608488 := by decide
  rcases family_descends (prefixWord ++ tailWord_608488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608498 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_608498 : Nat := 118140960795 + 608498 * 2 ^ 59
def prefixEnd_608498 : Nat := 4983230072969 + 3 ^ 40 * 608498 * 2
def baseEnd_608498 : Nat := 277735067821924873312511

theorem tailTrace_608498 : CollatzResearch.WordTrace tailWord_608498 prefixEnd_608498 277735067821924873312511 := by
  unfold tailWord_608498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548436337380786007440537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14795830233015429353174765 5548436337380786007440537)
  ·
    refine ⟨4161327253035589505580403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5548436337380786007440537 4161327253035589505580403)
    ·
      refine ⟨6241990879553384258370605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161327253035589505580403 6241990879553384258370605)
      ·
        refine ⟨2340746579832519096888977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6241990879553384258370605 2340746579832519096888977)
        ·
          refine ⟨1755559934874389322666733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340746579832519096888977 1755559934874389322666733)
          ·
            refine ⟨658334975577895996000025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1755559934874389322666733 658334975577895996000025)
            ·
              refine ⟨493751231683421997000019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658334975577895996000025 493751231683421997000019)
              ·
                refine ⟨740626847525132995500029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493751231683421997000019 740626847525132995500029)
                ·
                  refine ⟨277735067821924873312511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740626847525132995500029 277735067821924873312511)
                  ·
                    rfl

theorem cell20_608498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_608498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608498 prefixEnd_608498 := by exact prefixLift 608498
  have htrace : WordTrace (prefixWord ++ tailWord_608498) baseStart_608498 baseEnd_608498 := by
    simpa [prefixWord, tailWord_608498, baseEnd_608498] using wordTrace_append hprefix tailTrace_608498
  have hstable : (prefixWord ++ tailWord_608498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608498).length < 2 ^ (prefixWord ++ tailWord_608498).sum := by decide
  have hdescent : baseEnd_608498 < baseStart_608498 := by decide
  rcases family_descends (prefixWord ++ tailWord_608498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608526 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_608526 : Nat := 118140960795 + 608526 * 2 ^ 59
def prefixEnd_608526 : Nat := 4983230072969 + 3 ^ 40 * 608526 * 2
def baseEnd_608526 : Nat := 277747847784881220379063

theorem tailTrace_608526 : CollatzResearch.WordTrace tailWord_608526 prefixEnd_608526 277747847784881220379063 := by
  unfold tailWord_608526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774345824177713101472679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14796511062281136541187621 2774345824177713101472679)
  ·
    refine ⟨4161518736266569652209019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774345824177713101472679 4161518736266569652209019)
    ·
      refine ⟨6242278104399854478313529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161518736266569652209019 6242278104399854478313529)
      ·
        refine ⟨4681708578299890858735147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6242278104399854478313529 4681708578299890858735147)
        ·
          refine ⟨7022562867449836288102721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681708578299890858735147 7022562867449836288102721)
          ·
            refine ⟨5266922150587377216077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022562867449836288102721 5266922150587377216077041)
            ·
              refine ⟨3950191612940532912057781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5266922150587377216077041 3950191612940532912057781)
              ·
                refine ⟨370330463713174960505417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3950191612940532912057781 370330463713174960505417)
                ·
                  refine ⟨277747847784881220379063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370330463713174960505417 277747847784881220379063)
                  ·
                    rfl

theorem cell20_608526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_608526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608526 prefixEnd_608526 := by exact prefixLift 608526
  have htrace : WordTrace (prefixWord ++ tailWord_608526) baseStart_608526 baseEnd_608526 := by
    simpa [prefixWord, tailWord_608526, baseEnd_608526] using wordTrace_append hprefix tailTrace_608526
  have hstable : (prefixWord ++ tailWord_608526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608526).length < 2 ^ (prefixWord ++ tailWord_608526).sum := by decide
  have hdescent : baseEnd_608526 < baseStart_608526 := by decide
  rcases family_descends (prefixWord ++ tailWord_608526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608543 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 2]
def baseStart_608543 : Nat := 118140960795 + 608543 * 2 ^ 59
def prefixEnd_608543 : Nat := 4983230072969 + 3 ^ 40 * 608543 * 2
def baseEnd_608543 : Nat := 277755607048104716812327

theorem tailTrace_608543 : CollatzResearch.WordTrace tailWord_608543 prefixEnd_608543 277755607048104716812327 := by
  unfold tailWord_608543
  simp only [CollatzResearch.WordTrace]
  refine ⟨22195386634360116715150283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14796924422906744476766855 22195386634360116715150283)
  ·
    refine ⟨33293079951540175072725425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22195386634360116715150283 33293079951540175072725425)
    ·
      refine ⟨24969809963655131304544069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33293079951540175072725425 24969809963655131304544069)
      ·
        refine ⟨4681839368185337119602013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24969809963655131304544069 4681839368185337119602013)
        ·
          refine ⟨1755689763069501419850755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4681839368185337119602013 1755689763069501419850755)
          ·
            refine ⟨2633534644604252129776133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755689763069501419850755 2633534644604252129776133)
            ·
              refine ⟨493787745863297274333025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2633534644604252129776133 493787745863297274333025)
              ·
                refine ⟨370340809397472955749769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493787745863297274333025 370340809397472955749769)
                ·
                  refine ⟨277755607048104716812327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370340809397472955749769 277755607048104716812327)
                  ·
                    rfl

theorem cell20_608543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2].length) (baseStart_608543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608543 prefixEnd_608543 := by exact prefixLift 608543
  have htrace : WordTrace (prefixWord ++ tailWord_608543) baseStart_608543 baseEnd_608543 := by
    simpa [prefixWord, tailWord_608543, baseEnd_608543] using wordTrace_append hprefix tailTrace_608543
  have hstable : (prefixWord ++ tailWord_608543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608543).length < 2 ^ (prefixWord ++ tailWord_608543).sum := by decide
  have hdescent : baseEnd_608543 < baseStart_608543 := by decide
  rcases family_descends (prefixWord ++ tailWord_608543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608564 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_608564 : Nat := 118140960795 + 608564 * 2 ^ 59
def prefixEnd_608564 : Nat := 4983230072969 + 3 ^ 40 * 608564 * 2
def baseEnd_608564 : Nat := 277765192020321977112241

theorem tailTrace_608564 : CollatzResearch.WordTrace tailWord_608564 prefixEnd_608564 277765192020321977112241 := by
  unfold tailWord_608564
  simp only [CollatzResearch.WordTrace]
  refine ⟨11098076283642018650832373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14797435044856024867776497 11098076283642018650832373)
  ·
    refine ⟨1040444651591439248515535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11098076283642018650832373 1040444651591439248515535)
    ·
      refine ⟨1560666977387158872773303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1040444651591439248515535 1560666977387158872773303)
      ·
        refine ⟨2341000466080738309159955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560666977387158872773303 2341000466080738309159955)
        ·
          refine ⟨3511500699121107463739933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341000466080738309159955 3511500699121107463739933)
          ·
            refine ⟨1316812762170415298902475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3511500699121107463739933 1316812762170415298902475)
            ·
              refine ⟨1975219143255622948353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316812762170415298902475 1975219143255622948353713)
              ·
                refine ⟨1481414357441717211265285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975219143255622948353713 1481414357441717211265285)
                ·
                  refine ⟨277765192020321977112241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481414357441717211265285 277765192020321977112241)
                  ·
                    rfl

theorem cell20_608564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_608564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608564 prefixEnd_608564 := by exact prefixLift 608564
  have htrace : WordTrace (prefixWord ++ tailWord_608564) baseStart_608564 baseEnd_608564 := by
    simpa [prefixWord, tailWord_608564, baseEnd_608564] using wordTrace_append hprefix tailTrace_608564
  have hstable : (prefixWord ++ tailWord_608564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608564).length < 2 ^ (prefixWord ++ tailWord_608564).sum := by decide
  have hdescent : baseEnd_608564 < baseStart_608564 := by decide
  rcases family_descends (prefixWord ++ tailWord_608564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608568 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_608568 : Nat := 118140960795 + 608568 * 2 ^ 59
def prefixEnd_608568 : Nat := 4983230072969 + 3 ^ 40 * 608568 * 2
def baseEnd_608568 : Nat := 277767017729315740978891

theorem tailTrace_608568 : CollatzResearch.WordTrace tailWord_608568 prefixEnd_608568 277767017729315740978891 := by
  unfold tailWord_608568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11098149229634772992405179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14797532306179697323206905 11098149229634772992405179)
  ·
    refine ⟨16647223844452159488607769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11098149229634772992405179 16647223844452159488607769)
    ·
      refine ⟨12485417883339119616455827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16647223844452159488607769 12485417883339119616455827)
      ·
        refine ⟨18728126825008679424683741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12485417883339119616455827 18728126825008679424683741)
        ·
          refine ⟨7023047559378254784256403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18728126825008679424683741 7023047559378254784256403)
          ·
            refine ⟨10534571339067382176384605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7023047559378254784256403 10534571339067382176384605)
            ·
              refine ⟨3950464252150268316144227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10534571339067382176384605 3950464252150268316144227)
              ·
                refine ⟨5925696378225402474216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950464252150268316144227 5925696378225402474216341)
                ·
                  refine ⟨277767017729315740978891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5925696378225402474216341 277767017729315740978891)
                  ·
                    rfl

theorem cell20_608568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_608568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608568 prefixEnd_608568 := by exact prefixLift 608568
  have htrace : WordTrace (prefixWord ++ tailWord_608568) baseStart_608568 baseEnd_608568 := by
    simpa [prefixWord, tailWord_608568, baseEnd_608568] using wordTrace_append hprefix tailTrace_608568
  have hstable : (prefixWord ++ tailWord_608568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608568).length < 2 ^ (prefixWord ++ tailWord_608568).sum := by decide
  have hdescent : baseEnd_608568 < baseStart_608568 := by decide
  rcases family_descends (prefixWord ++ tailWord_608568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608599 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_608599 : Nat := 118140960795 + 608599 * 2 ^ 59
def prefixEnd_608599 : Nat := 4983230072969 + 3 ^ 40 * 608599 * 2
def baseEnd_608599 : Nat := 277781166974017410945431

theorem tailTrace_608599 : CollatzResearch.WordTrace tailWord_608599 prefixEnd_608599 277781166974017410945431 := by
  unfold tailWord_608599
  simp only [CollatzResearch.WordTrace]
  refine ⟨22197429122157238279188851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14798286081438158852792567 22197429122157238279188851)
  ·
    refine ⟨33296143683235857418783277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22197429122157238279188851 33296143683235857418783277)
    ·
      refine ⟨12486053881213446532043729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33296143683235857418783277 12486053881213446532043729)
      ·
        refine ⟨9364540410910084899032797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12486053881213446532043729 9364540410910084899032797)
        ·
          refine ⟨3511702654091281837137299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9364540410910084899032797 3511702654091281837137299)
          ·
            refine ⟨5267553981136922755705949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511702654091281837137299 5267553981136922755705949)
            ·
              refine ⟨1975332742926346033389731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5267553981136922755705949 1975332742926346033389731)
              ·
                refine ⟨2962999114389519050084597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975332742926346033389731 2962999114389519050084597)
                ·
                  refine ⟨277781166974017410945431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962999114389519050084597 277781166974017410945431)
                  ·
                    rfl

theorem cell20_608599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_608599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608599 prefixEnd_608599 := by exact prefixLift 608599
  have htrace : WordTrace (prefixWord ++ tailWord_608599) baseStart_608599 baseEnd_608599 := by
    simpa [prefixWord, tailWord_608599, baseEnd_608599] using wordTrace_append hprefix tailTrace_608599
  have hstable : (prefixWord ++ tailWord_608599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608599).length < 2 ^ (prefixWord ++ tailWord_608599).sum := by decide
  have hdescent : baseEnd_608599 < baseStart_608599 := by decide
  rcases family_descends (prefixWord ++ tailWord_608599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608637 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_608637 : Nat := 118140960795 + 608637 * 2 ^ 59
def prefixEnd_608637 : Nat := 4983230072969 + 3 ^ 40 * 608637 * 2
def baseEnd_608637 : Nat := 277798511209458167678609

theorem tailTrace_608637 : CollatzResearch.WordTrace tailWord_608637 prefixEnd_608637 277798511209458167678609 := by
  unfold tailWord_608637
  simp only [CollatzResearch.WordTrace]
  refine ⟨22198815096019570769072165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14799210064013047179381443 22198815096019570769072165)
  ·
    refine ⟨4162277830503669519201031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22198815096019570769072165 4162277830503669519201031)
    ·
      refine ⟨6243416745755504278801547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162277830503669519201031 6243416745755504278801547)
      ·
        refine ⟨9365125118633256418202321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6243416745755504278801547 9365125118633256418202321)
        ·
          refine ⟨7023843838974942313651741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9365125118633256418202321 7023843838974942313651741)
          ·
            refine ⟨2633941439615603367619403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7023843838974942313651741 2633941439615603367619403)
            ·
              refine ⟨3950912159423405051429105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633941439615603367619403 3950912159423405051429105)
              ·
                refine ⟨2963184119567553788571829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950912159423405051429105 2963184119567553788571829)
                ·
                  refine ⟨277798511209458167678609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2963184119567553788571829 277798511209458167678609)
                  ·
                    rfl

theorem cell20_608637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_608637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608637 prefixEnd_608637 := by exact prefixLift 608637
  have htrace : WordTrace (prefixWord ++ tailWord_608637) baseStart_608637 baseEnd_608637 := by
    simpa [prefixWord, tailWord_608637, baseEnd_608637] using wordTrace_append hprefix tailTrace_608637
  have hstable : (prefixWord ++ tailWord_608637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608637).length < 2 ^ (prefixWord ++ tailWord_608637).sum := by decide
  have hdescent : baseEnd_608637 < baseStart_608637 := by decide
  rcases family_descends (prefixWord ++ tailWord_608637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608651 : List Nat := [1, 1, 1, 1, 4, 4, 8]
def baseStart_608651 : Nat := 118140960795 + 608651 * 2 ^ 59
def prefixEnd_608651 : Nat := 4983230072969 + 3 ^ 40 * 608651 * 2
def baseEnd_608651 : Nat := 30867211243437371245765

theorem tailTrace_608651 : CollatzResearch.WordTrace tailWord_608651 prefixEnd_608651 30867211243437371245765 := by
  unfold tailWord_608651
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199325717968851160081807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14799550478645900773387871 22199325717968851160081807)
  ·
    refine ⟨33298988576953276740122711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22199325717968851160081807 33298988576953276740122711)
    ·
      refine ⟨49948482865429915110184067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33298988576953276740122711 49948482865429915110184067)
      ·
        refine ⟨74922724298144872665276101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49948482865429915110184067 74922724298144872665276101)
        ·
          refine ⟨14048010805902163624739269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74922724298144872665276101 14048010805902163624739269)
          ·
            refine ⟨2634002026106655679638613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14048010805902163624739269 2634002026106655679638613)
            ·
              refine ⟨30867211243437371245765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2634002026106655679638613 30867211243437371245765)
              ·
                rfl

theorem cell20_608651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_608651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608651 prefixEnd_608651 := by exact prefixLift 608651
  have htrace : WordTrace (prefixWord ++ tailWord_608651) baseStart_608651 baseEnd_608651 := by
    simpa [prefixWord, tailWord_608651, baseEnd_608651] using wordTrace_append hprefix tailTrace_608651
  have hstable : (prefixWord ++ tailWord_608651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608651).length < 2 ^ (prefixWord ++ tailWord_608651).sum := by decide
  have hdescent : baseEnd_608651 < baseStart_608651 := by decide
  rcases family_descends (prefixWord ++ tailWord_608651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608654 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_608654 : Nat := 118140960795 + 608654 * 2 ^ 59
def prefixEnd_608654 : Nat := 4983230072969 + 3 ^ 40 * 608654 * 2
def baseEnd_608654 : Nat := 277806270472681664111873

theorem tailTrace_608654 : CollatzResearch.WordTrace tailWord_608654 prefixEnd_608654 277806270472681664111873 := by
  unfold tailWord_608654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774929392119747834055127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14799623424638655114960677 2774929392119747834055127)
  ·
    refine ⟨4162394088179621751082691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774929392119747834055127 4162394088179621751082691)
    ·
      refine ⟨6243591132269432626624037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162394088179621751082691 6243591132269432626624037)
      ·
        refine ⟨1170673337300518617492007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6243591132269432626624037 1170673337300518617492007)
        ·
          refine ⟨1756010005950777926238011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170673337300518617492007 1756010005950777926238011)
          ·
            refine ⟨2634015008926166889357017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756010005950777926238011 2634015008926166889357017)
            ·
              refine ⟨1975511256694625167017763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634015008926166889357017 1975511256694625167017763)
              ·
                refine ⟨2963266885041937750526645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975511256694625167017763 2963266885041937750526645)
                ·
                  refine ⟨277806270472681664111873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2963266885041937750526645 277806270472681664111873)
                  ·
                    rfl

theorem cell20_608654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_608654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608654 prefixEnd_608654 := by exact prefixLift 608654
  have htrace : WordTrace (prefixWord ++ tailWord_608654) baseStart_608654 baseEnd_608654 := by
    simpa [prefixWord, tailWord_608654, baseEnd_608654] using wordTrace_append hprefix tailTrace_608654
  have hstable : (prefixWord ++ tailWord_608654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608654).length < 2 ^ (prefixWord ++ tailWord_608654).sum := by decide
  have hdescent : baseEnd_608654 < baseStart_608654 := by decide
  rcases family_descends (prefixWord ++ tailWord_608654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608705 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 3]
def baseStart_608705 : Nat := 118140960795 + 608705 * 2 ^ 59
def prefixEnd_608705 : Nat := 4983230072969 + 3 ^ 40 * 608705 * 2
def baseEnd_608705 : Nat := 277829548262352153411665

theorem tailTrace_608705 : CollatzResearch.WordTrace tailWord_608705 prefixEnd_608705 277829548262352153411665 := by
  unfold tailWord_608705
  simp only [CollatzResearch.WordTrace]
  refine ⟨22201295259773218382547569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14800863506515478921698379 22201295259773218382547569)
  ·
    refine ⟨16650971444829913786910677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22201295259773218382547569 16650971444829913786910677)
    ·
      refine ⟨390257143238201104380719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16650971444829913786910677 390257143238201104380719)
      ·
        refine ⟨585385714857301656571079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390257143238201104380719 585385714857301656571079)
        ·
          refine ⟨878078572285952484856619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585385714857301656571079 878078572285952484856619)
          ·
            refine ⟨1317117858428928727284929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878078572285952484856619 1317117858428928727284929)
            ·
              refine ⟨987838393821696545463697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317117858428928727284929 987838393821696545463697)
              ·
                refine ⟨740878795366272409097773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987838393821696545463697 740878795366272409097773)
                ·
                  refine ⟨277829548262352153411665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740878795366272409097773 277829548262352153411665)
                  ·
                    rfl

theorem cell20_608705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_608705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608705 prefixEnd_608705 := by exact prefixLift 608705
  have htrace : WordTrace (prefixWord ++ tailWord_608705) baseStart_608705 baseEnd_608705 := by
    simpa [prefixWord, tailWord_608705, baseEnd_608705] using wordTrace_append hprefix tailTrace_608705
  have hstable : (prefixWord ++ tailWord_608705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608705).length < 2 ^ (prefixWord ++ tailWord_608705).sum := by decide
  have hdescent : baseEnd_608705 < baseStart_608705 := by decide
  rcases family_descends (prefixWord ++ tailWord_608705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608713 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_608713 : Nat := 118140960795 + 608713 * 2 ^ 59
def prefixEnd_608713 : Nat := 4983230072969 + 3 ^ 40 * 608713 * 2
def baseEnd_608713 : Nat := 277833199680339681144965

theorem tailTrace_608713 : CollatzResearch.WordTrace tailWord_608713 prefixEnd_608713 277833199680339681144965 := by
  unfold tailWord_608713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22201587043744235748838793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14801058029162823832559195 22201587043744235748838793)
  ·
    refine ⟨16651190282808176811629095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22201587043744235748838793 16651190282808176811629095)
    ·
      refine ⟨24976785424212265217443643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16651190282808176811629095 24976785424212265217443643)
      ·
        refine ⟨37465178136318397826165465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24976785424212265217443643 37465178136318397826165465)
        ·
          refine ⟨28098883602238798369624099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37465178136318397826165465 28098883602238798369624099)
          ·
            refine ⟨42148325403358197554436149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28098883602238798369624099 42148325403358197554436149)
            ·
              refine ⟨3951405506564831020728389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42148325403358197554436149 3951405506564831020728389)
              ·
                refine ⟨740888532480905816386573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3951405506564831020728389 740888532480905816386573)
                ·
                  refine ⟨277833199680339681144965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740888532480905816386573 277833199680339681144965)
                  ·
                    rfl

theorem cell20_608713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_608713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608713 prefixEnd_608713 := by exact prefixLift 608713
  have htrace : WordTrace (prefixWord ++ tailWord_608713) baseStart_608713 baseEnd_608713 := by
    simpa [prefixWord, tailWord_608713, baseEnd_608713] using wordTrace_append hprefix tailTrace_608713
  have hstable : (prefixWord ++ tailWord_608713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608713).length < 2 ^ (prefixWord ++ tailWord_608713).sum := by decide
  have hdescent : baseEnd_608713 < baseStart_608713 := by decide
  rcases family_descends (prefixWord ++ tailWord_608713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608765 : List Nat := [1, 4, 1, 1, 1, 3, 9]
def baseStart_608765 : Nat := 118140960795 + 608765 * 2 ^ 59
def prefixEnd_608765 : Nat := 4983230072969 + 3 ^ 40 * 608765 * 2
def baseEnd_608765 : Nat := 30872992655250956823491

theorem tailTrace_608765 : CollatzResearch.WordTrace tailWord_608765 prefixEnd_608765 30872992655250956823491 := by
  unfold tailWord_608765
  simp only [CollatzResearch.WordTrace]
  refine ⟨22203483639555848629731749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14802322426370565753154499 22203483639555848629731749)
  ·
    refine ⟨4163153182416721618074703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22203483639555848629731749 4163153182416721618074703)
    ·
      refine ⟨6244729773625082427112055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163153182416721618074703 6244729773625082427112055)
      ·
        refine ⟨9367094660437623640668083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244729773625082427112055 9367094660437623640668083)
        ·
          refine ⟨14050641990656435461002125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367094660437623640668083 14050641990656435461002125)
          ·
            refine ⟨5268990746496163297875797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14050641990656435461002125 5268990746496163297875797)
            ·
              refine ⟨30872992655250956823491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5268990746496163297875797 30872992655250956823491)
              ·
                rfl

theorem cell20_608765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_608765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608765 prefixEnd_608765 := by exact prefixLift 608765
  have htrace : WordTrace (prefixWord ++ tailWord_608765) baseStart_608765 baseEnd_608765 := by
    simpa [prefixWord, tailWord_608765, baseEnd_608765] using wordTrace_append hprefix tailTrace_608765
  have hstable : (prefixWord ++ tailWord_608765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608765).length < 2 ^ (prefixWord ++ tailWord_608765).sum := by decide
  have hdescent : baseEnd_608765 < baseStart_608765 := by decide
  rcases family_descends (prefixWord ++ tailWord_608765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608781 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 3]
def baseStart_608781 : Nat := 118140960795 + 608781 * 2 ^ 59
def prefixEnd_608781 : Nat := 4983230072969 + 3 ^ 40 * 608781 * 2
def baseEnd_608781 : Nat := 277864236733233666878021

theorem tailTrace_608781 : CollatzResearch.WordTrace tailWord_608781 prefixEnd_608781 277864236733233666878021 := by
  unfold tailWord_608781
  simp only [CollatzResearch.WordTrace]
  refine ⟨22204067207497883362314197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14802711471665255574876131 22204067207497883362314197)
  ·
    refine ⟨520407825175731641304239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22204067207497883362314197 520407825175731641304239)
    ·
      refine ⟨780611737763597461956359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 520407825175731641304239 780611737763597461956359)
      ·
        refine ⟨1170917606645396192934539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780611737763597461956359 1170917606645396192934539)
        ·
          refine ⟨1756376409968094289401809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170917606645396192934539 1756376409968094289401809)
          ·
            refine ⟨1317282307476070717051357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756376409968094289401809 1317282307476070717051357)
            ·
              refine ⟨493980865303526518894259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317282307476070717051357 493980865303526518894259)
              ·
                refine ⟨740971297955289778341389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493980865303526518894259 740971297955289778341389)
                ·
                  refine ⟨277864236733233666878021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740971297955289778341389 277864236733233666878021)
                  ·
                    rfl

theorem cell20_608781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_608781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608781 prefixEnd_608781 := by exact prefixLift 608781
  have htrace : WordTrace (prefixWord ++ tailWord_608781) baseStart_608781 baseEnd_608781 := by
    simpa [prefixWord, tailWord_608781, baseEnd_608781] using wordTrace_append hprefix tailTrace_608781
  have hstable : (prefixWord ++ tailWord_608781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608781).length < 2 ^ (prefixWord ++ tailWord_608781).sum := by decide
  have hdescent : baseEnd_608781 < baseStart_608781 := by decide
  rcases family_descends (prefixWord ++ tailWord_608781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608836 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_608836 : Nat := 118140960795 + 608836 * 2 ^ 59
def prefixEnd_608836 : Nat := 4983230072969 + 3 ^ 40 * 608836 * 2
def baseEnd_608836 : Nat := 277889340231897920044463

theorem tailTrace_608836 : CollatzResearch.WordTrace tailWord_608836 prefixEnd_608836 277889340231897920044463 := by
  unfold tailWord_608836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103036611149313877783181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14804048814865751837044241 11103036611149313877783181)
  ·
    refine ⟨4163638729180992704168693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11103036611149313877783181 4163638729180992704168693)
    ·
      refine ⟨390341130860718066015815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4163638729180992704168693 390341130860718066015815)
      ·
        refine ⟨585511696291077099023723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390341130860718066015815 585511696291077099023723)
        ·
          refine ⟨878267544436615648535585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585511696291077099023723 878267544436615648535585)
          ·
            refine ⟨658700658327461736401689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878267544436615648535585 658700658327461736401689)
            ·
              refine ⟨494025493745596302301267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658700658327461736401689 494025493745596302301267)
              ·
                refine ⟨741038240618394453451901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494025493745596302301267 741038240618394453451901)
                ·
                  refine ⟨277889340231897920044463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741038240618394453451901 277889340231897920044463)
                  ·
                    rfl

theorem cell20_608836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_608836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608836 prefixEnd_608836 := by exact prefixLift 608836
  have htrace : WordTrace (prefixWord ++ tailWord_608836) baseStart_608836 baseEnd_608836 := by
    simpa [prefixWord, tailWord_608836, baseEnd_608836] using wordTrace_append hprefix tailTrace_608836
  have hstable : (prefixWord ++ tailWord_608836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608836).length < 2 ^ (prefixWord ++ tailWord_608836).sum := by decide
  have hdescent : baseEnd_608836 < baseStart_608836 := by decide
  rcases family_descends (prefixWord ++ tailWord_608836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608848 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_608848 : Nat := 118140960795 + 608848 * 2 ^ 59
def prefixEnd_608848 : Nat := 4983230072969 + 3 ^ 40 * 608848 * 2
def baseEnd_608848 : Nat := 277894817358879211644413

theorem tailTrace_608848 : CollatzResearch.WordTrace tailWord_608848 prefixEnd_608848 277894817358879211644413 := by
  unfold tailWord_608848
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103255449127576902501599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14804340598836769203335465 11103255449127576902501599)
  ·
    refine ⟨16654883173691365353752399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11103255449127576902501599 16654883173691365353752399)
    ·
      refine ⟨24982324760537048030628599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654883173691365353752399 24982324760537048030628599)
      ·
        refine ⟨37473487140805572045942899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24982324760537048030628599 37473487140805572045942899)
        ·
          refine ⟨56210230711208358068914349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37473487140805572045942899 56210230711208358068914349)
          ·
            refine ⟨21078836516703134275842881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56210230711208358068914349 21078836516703134275842881)
            ·
              refine ⟨15809127387527350706882161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21078836516703134275842881 15809127387527350706882161)
              ·
                refine ⟨11856845540645513030161621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15809127387527350706882161 11856845540645513030161621)
                ·
                  refine ⟨277894817358879211644413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11856845540645513030161621 277894817358879211644413)
                  ·
                    rfl

theorem cell20_608848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_608848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608848 prefixEnd_608848 := by exact prefixLift 608848
  have htrace : WordTrace (prefixWord ++ tailWord_608848) baseStart_608848 baseEnd_608848 := by
    simpa [prefixWord, tailWord_608848, baseEnd_608848] using wordTrace_append hprefix tailTrace_608848
  have hstable : (prefixWord ++ tailWord_608848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608848).length < 2 ^ (prefixWord ++ tailWord_608848).sum := by decide
  have hdescent : baseEnd_608848 < baseStart_608848 := by decide
  rcases family_descends (prefixWord ++ tailWord_608848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608885 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 2]
def baseStart_608885 : Nat := 118140960795 + 608885 * 2 ^ 59
def prefixEnd_608885 : Nat := 4983230072969 + 3 ^ 40 * 608885 * 2
def baseEnd_608885 : Nat := 277911705167071527410929

theorem tailTrace_608885 : CollatzResearch.WordTrace tailWord_608885 prefixEnd_608885 277911705167071527410929 := by
  unfold tailWord_608885
  simp only [CollatzResearch.WordTrace]
  refine ⟨22207860399121109124100109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14805240266080739416066739 22207860399121109124100109)
  ·
    refine ⟨8327947649670415921537541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22207860399121109124100109 8327947649670415921537541)
    ·
      refine ⟨1561490184313202985288289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8327947649670415921537541 1561490184313202985288289)
      ·
        refine ⟨1171117638234902238966217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1561490184313202985288289 1171117638234902238966217)
        ·
          refine ⟨878338228676176679224663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1171117638234902238966217 878338228676176679224663)
          ·
            refine ⟨1317507343014265018836995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878338228676176679224663 1317507343014265018836995)
            ·
              refine ⟨1976261014521397528255493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317507343014265018836995 1976261014521397528255493)
              ·
                refine ⟨370548940222762036547905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1976261014521397528255493 370548940222762036547905)
                ·
                  refine ⟨277911705167071527410929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370548940222762036547905 277911705167071527410929)
                  ·
                    rfl

theorem cell20_608885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_608885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608885 prefixEnd_608885 := by exact prefixLift 608885
  have htrace : WordTrace (prefixWord ++ tailWord_608885) baseStart_608885 baseEnd_608885 := by
    simpa [prefixWord, tailWord_608885, baseEnd_608885] using wordTrace_append hprefix tailTrace_608885
  have hstable : (prefixWord ++ tailWord_608885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608885).length < 2 ^ (prefixWord ++ tailWord_608885).sum := by decide
  have hdescent : baseEnd_608885 < baseStart_608885 := by decide
  rcases family_descends (prefixWord ++ tailWord_608885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608896 : List Nat := [2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_608896 : Nat := 118140960795 + 608896 * 2 ^ 59
def prefixEnd_608896 : Nat := 4983230072969 + 3 ^ 40 * 608896 * 2
def baseEnd_608896 : Nat := 92638908622268126014739

theorem tailTrace_608896 : CollatzResearch.WordTrace tailWord_608896 prefixEnd_608896 92638908622268126014739 := by
  unfold tailWord_608896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11104130801040629001375271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14805507734720838668500361 11104130801040629001375271)
  ·
    refine ⟨16656196201560943502062907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11104130801040629001375271 16656196201560943502062907)
    ·
      refine ⟨24984294302341415253094361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16656196201560943502062907 24984294302341415253094361)
      ·
        refine ⟨18738220726756061439820771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24984294302341415253094361 18738220726756061439820771)
        ·
          refine ⟨28107331090134092159731157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18738220726756061439820771 28107331090134092159731157)
          ·
            refine ⟨658765572425017784993699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28107331090134092159731157 658765572425017784993699)
            ·
              refine ⟨988148358637526677490549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658765572425017784993699 988148358637526677490549)
              ·
                refine ⟨92638908622268126014739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988148358637526677490549 92638908622268126014739)
                ·
                  rfl

theorem cell20_608896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_608896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608896 prefixEnd_608896 := by exact prefixLift 608896
  have htrace : WordTrace (prefixWord ++ tailWord_608896) baseStart_608896 baseEnd_608896 := by
    simpa [prefixWord, tailWord_608896, baseEnd_608896] using wordTrace_append hprefix tailTrace_608896
  have hstable : (prefixWord ++ tailWord_608896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608896).length < 2 ^ (prefixWord ++ tailWord_608896).sum := by decide
  have hdescent : baseEnd_608896 < baseStart_608896 := by decide
  rcases family_descends (prefixWord ++ tailWord_608896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608903 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_608903 : Nat := 118140960795 + 608903 * 2 ^ 59
def prefixEnd_608903 : Nat := 4983230072969 + 3 ^ 40 * 608903 * 2
def baseEnd_608903 : Nat := 277919920857543464810855

theorem tailTrace_608903 : CollatzResearch.WordTrace tailWord_608903 prefixEnd_608903 277919920857543464810855 := by
  unfold tailWord_608903
  simp only [CollatzResearch.WordTrace]
  refine ⟨22208516913055898198255363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14805677942037265465503575 22208516913055898198255363)
  ·
    refine ⟨33312775369583847297383045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22208516913055898198255363 33312775369583847297383045)
    ·
      refine ⟨6246145381796971368259321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33312775369583847297383045 6246145381796971368259321)
      ·
        refine ⟨4684609036347728526194491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6246145381796971368259321 4684609036347728526194491)
        ·
          refine ⟨7026913554521592789291737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4684609036347728526194491 7026913554521592789291737)
          ·
            refine ⟨5270185165891194591968803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7026913554521592789291737 5270185165891194591968803)
            ·
              refine ⟨7905277748836791887953205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270185165891194591968803 7905277748836791887953205)
              ·
                refine ⟨741119788953449239495613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7905277748836791887953205 741119788953449239495613)
                ·
                  refine ⟨277919920857543464810855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741119788953449239495613 277919920857543464810855)
                  ·
                    rfl

theorem cell20_608903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_608903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608903 prefixEnd_608903 := by exact prefixLift 608903
  have htrace : WordTrace (prefixWord ++ tailWord_608903) baseStart_608903 baseEnd_608903 := by
    simpa [prefixWord, tailWord_608903, baseEnd_608903] using wordTrace_append hprefix tailTrace_608903
  have hstable : (prefixWord ++ tailWord_608903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608903).length < 2 ^ (prefixWord ++ tailWord_608903).sum := by decide
  have hdescent : baseEnd_608903 < baseStart_608903 := by decide
  rcases family_descends (prefixWord ++ tailWord_608903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608972 : List Nat := [2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_608972 : Nat := 118140960795 + 608972 * 2 ^ 59
def prefixEnd_608972 : Nat := 4983230072969 + 3 ^ 40 * 608972 * 2
def baseEnd_608972 : Nat := 92650471445895297170191

theorem tailTrace_608972 : CollatzResearch.WordTrace tailWord_608972 prefixEnd_608972 92650471445895297170191 := by
  unfold tailWord_608972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11105516774902961491258585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14807355699870615321678113 11105516774902961491258585)
  ·
    refine ⟨8329137581177221118443939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11105516774902961491258585 8329137581177221118443939)
    ·
      refine ⟨12493706371765831677665909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8329137581177221118443939 12493706371765831677665909)
      ·
        refine ⟨1171284972353046719781179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12493706371765831677665909 1171284972353046719781179)
        ·
          refine ⟨1756927458529570079671769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171284972353046719781179 1756927458529570079671769)
          ·
            refine ⟨1317695593897177559753827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756927458529570079671769 1317695593897177559753827)
            ·
              refine ⟨1976543390845766339630741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317695593897177559753827 1976543390845766339630741)
              ·
                refine ⟨92650471445895297170191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1976543390845766339630741 92650471445895297170191)
                ·
                  rfl

theorem cell20_608972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_608972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608972 prefixEnd_608972 := by exact prefixLift 608972
  have htrace : WordTrace (prefixWord ++ tailWord_608972) baseStart_608972 baseEnd_608972 := by
    simpa [prefixWord, tailWord_608972, baseEnd_608972] using wordTrace_append hprefix tailTrace_608972
  have hstable : (prefixWord ++ tailWord_608972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608972).length < 2 ^ (prefixWord ++ tailWord_608972).sum := by decide
  have hdescent : baseEnd_608972 < baseStart_608972 := by decide
  rcases family_descends (prefixWord ++ tailWord_608972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608978 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_608978 : Nat := 118140960795 + 608978 * 2 ^ 59
def prefixEnd_608978 : Nat := 4983230072969 + 3 ^ 40 * 608978 * 2
def baseEnd_608978 : Nat := 277954152901176537310549

theorem tailTrace_608978 : CollatzResearch.WordTrace tailWord_608978 prefixEnd_608978 277954152901176537310549 := by
  unfold tailWord_608978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552813096946046501808897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14807501591856124004823725 5552813096946046501808897)
  ·
    refine ⟨4164609822709534876356673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5552813096946046501808897 4164609822709534876356673)
    ·
      refine ⟨3123457367032151157267505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4164609822709534876356673 3123457367032151157267505)
      ·
        refine ⟨2342593025274113367950629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123457367032151157267505 2342593025274113367950629)
        ·
          refine ⟨439236192238896256490743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2342593025274113367950629 439236192238896256490743)
          ·
            refine ⟨658854288358344384736115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439236192238896256490743 658854288358344384736115)
            ·
              refine ⟨988281432537516577104173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658854288358344384736115 988281432537516577104173)
              ·
                refine ⟨370605537201568716414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988281432537516577104173 370605537201568716414065)
                ·
                  refine ⟨277954152901176537310549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370605537201568716414065 277954152901176537310549)
                  ·
                    rfl

theorem cell20_608978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_608978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608978 prefixEnd_608978 := by exact prefixLift 608978
  have htrace : WordTrace (prefixWord ++ tailWord_608978) baseStart_608978 baseEnd_608978 := by
    simpa [prefixWord, tailWord_608978, baseEnd_608978] using wordTrace_append hprefix tailTrace_608978
  have hstable : (prefixWord ++ tailWord_608978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608978).length < 2 ^ (prefixWord ++ tailWord_608978).sum := by decide
  have hdescent : baseEnd_608978 < baseStart_608978 := by decide
  rcases family_descends (prefixWord ++ tailWord_608978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_608993 : List Nat := [1, 2, 3, 1, 4, 1, 8]
def baseStart_608993 : Nat := 118140960795 + 608993 * 2 ^ 59
def prefixEnd_608993 : Nat := 4983230072969 + 3 ^ 40 * 608993 * 2
def baseEnd_608993 : Nat := 30884555478878127978943

theorem tailTrace_608993 : CollatzResearch.WordTrace tailWord_608993 prefixEnd_608993 30884555478878127978943 := by
  unfold tailWord_608993
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211799482729843569031633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14807866321819895712687755 22211799482729843569031633)
  ·
    refine ⟨16658849612047382676773725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22211799482729843569031633 16658849612047382676773725)
    ·
      refine ⟨6247068604517768503790147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16658849612047382676773725 6247068604517768503790147)
      ·
        refine ⟨9370602906776652755685221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6247068604517768503790147 9370602906776652755685221)
        ·
          refine ⟨1756988045020622391690979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9370602906776652755685221 1756988045020622391690979)
          ·
            refine ⟨2635482067530933587536469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756988045020622391690979 2635482067530933587536469)
            ·
              refine ⟨30884555478878127978943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2635482067530933587536469 30884555478878127978943)
              ·
                rfl

theorem cell20_608993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_608993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_608993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_608993 prefixEnd_608993 := by exact prefixLift 608993
  have htrace : WordTrace (prefixWord ++ tailWord_608993) baseStart_608993 baseEnd_608993 := by
    simpa [prefixWord, tailWord_608993, baseEnd_608993] using wordTrace_append hprefix tailTrace_608993
  have hstable : (prefixWord ++ tailWord_608993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_608993).length < 2 ^ (prefixWord ++ tailWord_608993).sum := by decide
  have hdescent : baseEnd_608993 < baseStart_608993 := by decide
  rcases family_descends (prefixWord ++ tailWord_608993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609010 : List Nat := [3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_609010 : Nat := 118140960795 + 609010 * 2 ^ 59
def prefixEnd_609010 : Nat := 4983230072969 + 3 ^ 40 * 609010 * 2
def baseEnd_609010 : Nat := 92656252857708882747917

theorem tailTrace_609010 : CollatzResearch.WordTrace tailWord_609010 prefixEnd_609010 92656252857708882747917 := by
  unfold tailWord_609010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553104880917063868100121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14808279682445503648266989 5553104880917063868100121)
  ·
    refine ⟨4164828660687797901075091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5553104880917063868100121 4164828660687797901075091)
    ·
      refine ⟨6247242991031696851612637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164828660687797901075091 6247242991031696851612637)
      ·
        refine ⟨2342716121636886319354739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6247242991031696851612637 2342716121636886319354739)
        ·
          refine ⟨3514074182455329479032109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342716121636886319354739 3514074182455329479032109)
          ·
            refine ⟨1317777818420748554637041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3514074182455329479032109 1317777818420748554637041)
            ·
              refine ⟨988333363815561415977781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317777818420748554637041 988333363815561415977781)
              ·
                refine ⟨92656252857708882747917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988333363815561415977781 92656252857708882747917)
                ·
                  rfl

theorem cell20_609010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_609010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609010 prefixEnd_609010 := by exact prefixLift 609010
  have htrace : WordTrace (prefixWord ++ tailWord_609010) baseStart_609010 baseEnd_609010 := by
    simpa [prefixWord, tailWord_609010, baseEnd_609010] using wordTrace_append hprefix tailTrace_609010
  have hstable : (prefixWord ++ tailWord_609010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609010).length < 2 ^ (prefixWord ++ tailWord_609010).sum := by decide
  have hdescent : baseEnd_609010 < baseStart_609010 := by decide
  rcases family_descends (prefixWord ++ tailWord_609010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609055 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_609055 : Nat := 118140960795 + 609055 * 2 ^ 59
def prefixEnd_609055 : Nat := 4983230072969 + 3 ^ 40 * 609055 * 2
def baseEnd_609055 : Nat := 277989297799306491743567

theorem tailTrace_609055 : CollatzResearch.WordTrace tailWord_609055 prefixEnd_609055 277989297799306491743567 := by
  unfold tailWord_609055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22214060808505228157788619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14809373872336818771859079 22214060808505228157788619)
  ·
    refine ⟨33321091212757842236682929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22214060808505228157788619 33321091212757842236682929)
    ·
      refine ⟨24990818409568381677512197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33321091212757842236682929 24990818409568381677512197)
      ·
        refine ⟨4685778451794071564533537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24990818409568381677512197 4685778451794071564533537)
        ·
          refine ⟨3514333838845553673400153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685778451794071564533537 3514333838845553673400153)
          ·
            refine ⟨2635750379134165255050115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3514333838845553673400153 2635750379134165255050115)
            ·
              refine ⟨3953625568701247882575173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635750379134165255050115 3953625568701247882575173)
              ·
                refine ⟨741304794131483977982845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3953625568701247882575173 741304794131483977982845)
                ·
                  refine ⟨277989297799306491743567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741304794131483977982845 277989297799306491743567)
                  ·
                    rfl

theorem cell20_609055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_609055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609055 prefixEnd_609055 := by exact prefixLift 609055
  have htrace : WordTrace (prefixWord ++ tailWord_609055) baseStart_609055 baseEnd_609055 := by
    simpa [prefixWord, tailWord_609055, baseEnd_609055] using wordTrace_append hprefix tailTrace_609055
  have hstable : (prefixWord ++ tailWord_609055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609055).length < 2 ^ (prefixWord ++ tailWord_609055).sum := by decide
  have hdescent : baseEnd_609055 < baseStart_609055 := by decide
  rcases family_descends (prefixWord ++ tailWord_609055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609058 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_609058 : Nat := 118140960795 + 609058 * 2 ^ 59
def prefixEnd_609058 : Nat := 4983230072969 + 3 ^ 40 * 609058 * 2
def baseEnd_609058 : Nat := 277990667081051814643555

theorem tailTrace_609058 : CollatzResearch.WordTrace tailWord_609058 prefixEnd_609058 277990667081051814643555 := by
  unfold tailWord_609058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553542556873589917536957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14809446818329573113431885 5553542556873589917536957)
  ·
    refine ⟨2082578458827596219076359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5553542556873589917536957 2082578458827596219076359)
    ·
      refine ⟨3123867688241394328614539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082578458827596219076359 3123867688241394328614539)
      ·
        refine ⟨4685801532362091492921809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123867688241394328614539 4685801532362091492921809)
        ·
          refine ⟨3514351149271568619691357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685801532362091492921809 3514351149271568619691357)
          ·
            refine ⟨1317881680976838232384259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3514351149271568619691357 1317881680976838232384259)
            ·
              refine ⟨1976822521465257348576389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317881680976838232384259 1976822521465257348576389)
              ·
                refine ⟨370654222774735752858073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1976822521465257348576389 370654222774735752858073)
                ·
                  refine ⟨277990667081051814643555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370654222774735752858073 277990667081051814643555)
                  ·
                    rfl

theorem cell20_609058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_609058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609058 prefixEnd_609058 := by exact prefixLift 609058
  have htrace : WordTrace (prefixWord ++ tailWord_609058) baseStart_609058 baseEnd_609058 := by
    simpa [prefixWord, tailWord_609058, baseEnd_609058] using wordTrace_append hprefix tailTrace_609058
  have hstable : (prefixWord ++ tailWord_609058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609058).length < 2 ^ (prefixWord ++ tailWord_609058).sum := by decide
  have hdescent : baseEnd_609058 < baseStart_609058 := by decide
  rcases family_descends (prefixWord ++ tailWord_609058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609092 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_609092 : Nat := 118140960795 + 609092 * 2 ^ 59
def prefixEnd_609092 : Nat := 4983230072969 + 3 ^ 40 * 609092 * 2
def baseEnd_609092 : Nat := 278006185607498807510083

theorem tailTrace_609092 : CollatzResearch.WordTrace tailWord_609092 prefixEnd_609092 278006185607498807510083 := by
  unfold tailWord_609092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107705154685591738442765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14810273539580788984590353 11107705154685591738442765)
  ·
    refine ⟨4165389433007096901916037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11107705154685591738442765 4165389433007096901916037)
    ·
      refine ⟨781010518688830669109257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4165389433007096901916037 781010518688830669109257)
      ·
        refine ⟨585757889016623001831943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781010518688830669109257 585757889016623001831943)
        ·
          refine ⟨878636833524934502747915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585757889016623001831943 878636833524934502747915)
          ·
            refine ⟨1317955250287401754121873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878636833524934502747915 1317955250287401754121873)
            ·
              refine ⟨988466437715551315591405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317955250287401754121873 988466437715551315591405)
              ·
                refine ⟨370674914143331743346777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988466437715551315591405 370674914143331743346777)
                ·
                  refine ⟨278006185607498807510083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370674914143331743346777 278006185607498807510083)
                  ·
                    rfl

theorem cell20_609092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_609092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609092 prefixEnd_609092 := by exact prefixLift 609092
  have htrace : WordTrace (prefixWord ++ tailWord_609092) baseStart_609092 baseEnd_609092 := by
    simpa [prefixWord, tailWord_609092, baseEnd_609092] using wordTrace_append hprefix tailTrace_609092
  have hstable : (prefixWord ++ tailWord_609092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609092).length < 2 ^ (prefixWord ++ tailWord_609092).sum := by decide
  have hdescent : baseEnd_609092 < baseStart_609092 := by decide
  rcases family_descends (prefixWord ++ tailWord_609092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609138 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_609138 : Nat := 118140960795 + 609138 * 2 ^ 59
def prefixEnd_609138 : Nat := 4983230072969 + 3 ^ 40 * 609138 * 2
def baseEnd_609138 : Nat := 278027181260927091976561

theorem tailTrace_609138 : CollatzResearch.WordTrace tailWord_609138 prefixEnd_609138 278027181260927091976561 := by
  unfold tailWord_609138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554272016801133333265017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14811392044803022222040045 5554272016801133333265017)
  ·
    refine ⟨4165704012600849999948763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5554272016801133333265017 4165704012600849999948763)
    ·
      refine ⟨6248556018901274999923145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165704012600849999948763 6248556018901274999923145)
      ·
        refine ⟨4686417014175956249942359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6248556018901274999923145 4686417014175956249942359)
        ·
          refine ⟨7029625521263934374913539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686417014175956249942359 7029625521263934374913539)
          ·
            refine ⟨10544438281895901562370309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7029625521263934374913539 10544438281895901562370309)
            ·
              refine ⟨1977082177855481542944433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10544438281895901562370309 1977082177855481542944433)
              ·
                refine ⟨1482811633391611157208325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977082177855481542944433 1482811633391611157208325)
                ·
                  refine ⟨278027181260927091976561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482811633391611157208325 278027181260927091976561)
                  ·
                    rfl

theorem cell20_609138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_609138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609138 prefixEnd_609138 := by exact prefixLift 609138
  have htrace : WordTrace (prefixWord ++ tailWord_609138) baseStart_609138 baseEnd_609138 := by
    simpa [prefixWord, tailWord_609138, baseEnd_609138] using wordTrace_append hprefix tailTrace_609138
  have hstable : (prefixWord ++ tailWord_609138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609138).length < 2 ^ (prefixWord ++ tailWord_609138).sum := by decide
  have hdescent : baseEnd_609138 < baseStart_609138 := by decide
  rcases family_descends (prefixWord ++ tailWord_609138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609141 : List Nat := [1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_609141 : Nat := 118140960795 + 609141 * 2 ^ 59
def prefixEnd_609141 : Nat := 4983230072969 + 3 ^ 40 * 609141 * 2
def baseEnd_609141 : Nat := 92676183514224138292183

theorem tailTrace_609141 : CollatzResearch.WordTrace tailWord_609141 prefixEnd_609141 92676183514224138292183 := by
  unfold tailWord_609141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217197486193664845419277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14811464990795776563612851 22217197486193664845419277)
  ·
    refine ⟨8331449057322624317032229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22217197486193664845419277 8331449057322624317032229)
    ·
      refine ⟨1562146698247992059443543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8331449057322624317032229 1562146698247992059443543)
      ·
        refine ⟨2343220047371988089165315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562146698247992059443543 2343220047371988089165315)
        ·
          refine ⟨3514830071057982133747973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343220047371988089165315 3514830071057982133747973)
          ·
            refine ⟨659030638323371650077745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3514830071057982133747973 659030638323371650077745)
            ·
              refine ⟨494272978742528737558309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659030638323371650077745 494272978742528737558309)
              ·
                refine ⟨92676183514224138292183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494272978742528737558309 92676183514224138292183)
                ·
                  rfl

theorem cell20_609141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_609141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609141 prefixEnd_609141 := by exact prefixLift 609141
  have htrace : WordTrace (prefixWord ++ tailWord_609141) baseStart_609141 baseEnd_609141 := by
    simpa [prefixWord, tailWord_609141, baseEnd_609141] using wordTrace_append hprefix tailTrace_609141
  have hstable : (prefixWord ++ tailWord_609141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609141).length < 2 ^ (prefixWord ++ tailWord_609141).sum := by decide
  have hdescent : baseEnd_609141 < baseStart_609141 := by decide
  rcases family_descends (prefixWord ++ tailWord_609141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609145 : List Nat := [1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_609145 : Nat := 118140960795 + 609145 * 2 ^ 59
def prefixEnd_609145 : Nat := 4983230072969 + 3 ^ 40 * 609145 * 2
def baseEnd_609145 : Nat := 92676792083888726247733

theorem tailTrace_609145 : CollatzResearch.WordTrace tailWord_609145 prefixEnd_609145 92676792083888726247733 := by
  unfold tailWord_609145
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217343378179173528564889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14811562252119449019043259 22217343378179173528564889)
  ·
    refine ⟨16663007533634380146423667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22217343378179173528564889 16663007533634380146423667)
    ·
      refine ⟨24994511300451570219635501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16663007533634380146423667 24994511300451570219635501)
      ·
        refine ⟨9372941737669338832363313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24994511300451570219635501 9372941737669338832363313)
        ·
          refine ⟨7029706303252004124272485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9372941737669338832363313 7029706303252004124272485)
          ·
            refine ⟨1318069931859750773301091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7029706303252004124272485 1318069931859750773301091)
            ·
              refine ⟨1977104897789626159951637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318069931859750773301091 1977104897789626159951637)
              ·
                refine ⟨92676792083888726247733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1977104897789626159951637 92676792083888726247733)
                ·
                  rfl

theorem cell20_609145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_609145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609145 prefixEnd_609145 := by exact prefixLift 609145
  have htrace : WordTrace (prefixWord ++ tailWord_609145) baseStart_609145 baseEnd_609145 := by
    simpa [prefixWord, tailWord_609145, baseEnd_609145] using wordTrace_append hprefix tailTrace_609145
  have hstable : (prefixWord ++ tailWord_609145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609145).length < 2 ^ (prefixWord ++ tailWord_609145).sum := by decide
  have hdescent : baseEnd_609145 < baseStart_609145 := by decide
  rcases family_descends (prefixWord ++ tailWord_609145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609162 : List Nat := [3, 1, 2, 4, 1, 3, 6]
def baseStart_609162 : Nat := 118140960795 + 609162 * 2 ^ 59
def prefixEnd_609162 : Nat := 4983230072969 + 3 ^ 40 * 609162 * 2
def baseEnd_609162 : Nat := 30893126168321075019607

theorem tailTrace_609162 : CollatzResearch.WordTrace tailWord_609162 prefixEnd_609162 30893126168321075019607 := by
  unfold tailWord_609162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554490854779396357983435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14811975612745056954622493 5554490854779396357983435)
  ·
    refine ⟨8331736282169094536975153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5554490854779396357983435 8331736282169094536975153)
    ·
      refine ⟨6248802211626820902731365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8331736282169094536975153 6248802211626820902731365)
      ·
        refine ⟨1171650414680028919262131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6248802211626820902731365 1171650414680028919262131)
        ·
          refine ⟨1757475622020043378893197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171650414680028919262131 1757475622020043378893197)
          ·
            refine ⟨659053358257516267084949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1757475622020043378893197 659053358257516267084949)
            ·
              refine ⟨30893126168321075019607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 659053358257516267084949 30893126168321075019607)
              ·
                rfl

theorem cell20_609162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_609162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609162 prefixEnd_609162 := by exact prefixLift 609162
  have htrace : WordTrace (prefixWord ++ tailWord_609162) baseStart_609162 baseEnd_609162 := by
    simpa [prefixWord, tailWord_609162, baseEnd_609162] using wordTrace_append hprefix tailTrace_609162
  have hstable : (prefixWord ++ tailWord_609162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609162).length < 2 ^ (prefixWord ++ tailWord_609162).sum := by decide
  have hdescent : baseEnd_609162 < baseStart_609162 := by decide
  rcases family_descends (prefixWord ++ tailWord_609162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609183 : List Nat := [1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_609183 : Nat := 118140960795 + 609183 * 2 ^ 59
def prefixEnd_609183 : Nat := 4983230072969 + 3 ^ 40 * 609183 * 2
def baseEnd_609183 : Nat := 92682573495702311825459

theorem tailTrace_609183 : CollatzResearch.WordTrace tailWord_609183 prefixEnd_609183 92682573495702311825459 := by
  unfold tailWord_609183
  simp only [CollatzResearch.WordTrace]
  refine ⟨22218729352041506018448203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14812486234694337345632135 22218729352041506018448203)
  ·
    refine ⟨33328094028062259027672305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22218729352041506018448203 33328094028062259027672305)
    ·
      refine ⟨24996070521046694270754229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33328094028062259027672305 24996070521046694270754229)
      ·
        refine ⟨2343381611348127587883209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24996070521046694270754229 2343381611348127587883209)
        ·
          refine ⟨1757536208511095690912407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343381611348127587883209 1757536208511095690912407)
          ·
            refine ⟨2636304312766643536368611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757536208511095690912407 2636304312766643536368611)
            ·
              refine ⟨3954456469149965304552917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636304312766643536368611 3954456469149965304552917)
              ·
                refine ⟨92682573495702311825459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3954456469149965304552917 92682573495702311825459)
                ·
                  rfl

theorem cell20_609183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_609183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609183 prefixEnd_609183 := by exact prefixLift 609183
  have htrace : WordTrace (prefixWord ++ tailWord_609183) baseStart_609183 baseEnd_609183 := by
    simpa [prefixWord, tailWord_609183, baseEnd_609183] using wordTrace_append hprefix tailTrace_609183
  have hstable : (prefixWord ++ tailWord_609183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609183).length < 2 ^ (prefixWord ++ tailWord_609183).sum := by decide
  have hdescent : baseEnd_609183 < baseStart_609183 := by decide
  rcases family_descends (prefixWord ++ tailWord_609183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609186 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_609186 : Nat := 118140960795 + 609186 * 2 ^ 59
def prefixEnd_609186 : Nat := 4983230072969 + 3 ^ 40 * 609186 * 2
def baseEnd_609186 : Nat := 278049089768852258376365

theorem tailTrace_609186 : CollatzResearch.WordTrace tailWord_609186 prefixEnd_609186 278049089768852258376365 := by
  unfold tailWord_609186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554709692757659382701853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14812559180687091687204941 5554709692757659382701853)
  ·
    refine ⟨2083016134784122268513195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5554709692757659382701853 2083016134784122268513195)
    ·
      refine ⟨3124524202176183402769793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083016134784122268513195 3124524202176183402769793)
      ·
        refine ⟨2343393151632137552077345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3124524202176183402769793 2343393151632137552077345)
        ·
          refine ⟨1757544863724103164058009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343393151632137552077345 1757544863724103164058009)
          ·
            refine ⟨1318158647793077373043507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757544863724103164058009 1318158647793077373043507)
            ·
              refine ⟨1977237971689616059565261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318158647793077373043507 1977237971689616059565261)
              ·
                refine ⟨741464239383606022336973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977237971689616059565261 741464239383606022336973)
                ·
                  refine ⟨278049089768852258376365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741464239383606022336973 278049089768852258376365)
                  ·
                    rfl

theorem cell20_609186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_609186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609186 prefixEnd_609186 := by exact prefixLift 609186
  have htrace : WordTrace (prefixWord ++ tailWord_609186) baseStart_609186 baseEnd_609186 := by
    simpa [prefixWord, tailWord_609186, baseEnd_609186] using wordTrace_append hprefix tailTrace_609186
  have hstable : (prefixWord ++ tailWord_609186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609186).length < 2 ^ (prefixWord ++ tailWord_609186).sum := by decide
  have hdescent : baseEnd_609186 < baseStart_609186 := by decide
  rcases family_descends (prefixWord ++ tailWord_609186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609224 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_609224 : Nat := 118140960795 + 609224 * 2 ^ 59
def prefixEnd_609224 : Nat := 4983230072969 + 3 ^ 40 * 609224 * 2
def baseEnd_609224 : Nat := 278066434004293015109543

theorem tailTrace_609224 : CollatzResearch.WordTrace tailWord_609224 prefixEnd_609224 278066434004293015109543 := by
  unfold tailWord_609224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110112372446485010345363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14813483163261980013793817 11110112372446485010345363)
  ·
    refine ⟨16665168558669727515518045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11110112372446485010345363 16665168558669727515518045)
    ·
      refine ⟨6249438209501147818319267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16665168558669727515518045 6249438209501147818319267)
      ·
        refine ⟨9374157314251721727478901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249438209501147818319267 9374157314251721727478901)
        ·
          refine ⟨878827248211098911951147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9374157314251721727478901 878827248211098911951147)
          ·
            refine ⟨1318240872316648367926721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878827248211098911951147 1318240872316648367926721)
            ·
              refine ⟨988680654237486275945041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318240872316648367926721 988680654237486275945041)
              ·
                refine ⟨741510490678114706958781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988680654237486275945041 741510490678114706958781)
                ·
                  refine ⟨278066434004293015109543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741510490678114706958781 278066434004293015109543)
                  ·
                    rfl

theorem cell20_609224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_609224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609224 prefixEnd_609224 := by exact prefixLift 609224
  have htrace : WordTrace (prefixWord ++ tailWord_609224) baseStart_609224 baseEnd_609224 := by
    simpa [prefixWord, tailWord_609224, baseEnd_609224] using wordTrace_append hprefix tailTrace_609224
  have hstable : (prefixWord ++ tailWord_609224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609224).length < 2 ^ (prefixWord ++ tailWord_609224).sum := by decide
  have hdescent : baseEnd_609224 < baseStart_609224 := by decide
  rcases family_descends (prefixWord ++ tailWord_609224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609231 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 2]
def baseStart_609231 : Nat := 118140960795 + 609231 * 2 ^ 59
def prefixEnd_609231 : Nat := 4983230072969 + 3 ^ 40 * 609231 * 2
def baseEnd_609231 : Nat := 278069628995032101876181

theorem tailTrace_609231 : CollatzResearch.WordTrace tailWord_609231 prefixEnd_609231 278069628995032101876181 := by
  unfold tailWord_609231
  simp only [CollatzResearch.WordTrace]
  refine ⟨22220480055867610216195547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14813653370578406810797031 22220480055867610216195547)
  ·
    refine ⟨33330720083801415324293321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22220480055867610216195547 33330720083801415324293321)
    ·
      refine ⟨24998040062851061493219991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33330720083801415324293321 24998040062851061493219991)
      ·
        refine ⟨37497060094276592239829987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24998040062851061493219991 37497060094276592239829987)
        ·
          refine ⟨56245590141414888359744981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37497060094276592239829987 56245590141414888359744981)
          ·
            refine ⟨1318256018939411445931523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56245590141414888359744981 1318256018939411445931523)
            ·
              refine ⟨1977384028409117168897285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318256018939411445931523 1977384028409117168897285)
              ·
                refine ⟨370759505326709469168241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1977384028409117168897285 370759505326709469168241)
                ·
                  refine ⟨278069628995032101876181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370759505326709469168241 278069628995032101876181)
                  ·
                    rfl

theorem cell20_609231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2].length) (baseStart_609231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609231 prefixEnd_609231 := by exact prefixLift 609231
  have htrace : WordTrace (prefixWord ++ tailWord_609231) baseStart_609231 baseEnd_609231 := by
    simpa [prefixWord, tailWord_609231, baseEnd_609231] using wordTrace_append hprefix tailTrace_609231
  have hstable : (prefixWord ++ tailWord_609231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609231).length < 2 ^ (prefixWord ++ tailWord_609231).sum := by decide
  have hdescent : baseEnd_609231 < baseStart_609231 := by decide
  rcases family_descends (prefixWord ++ tailWord_609231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609273 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_609273 : Nat := 118140960795 + 609273 * 2 ^ 59
def prefixEnd_609273 : Nat := 4983230072969 + 3 ^ 40 * 609273 * 2
def baseEnd_609273 : Nat := 278088798939466622476009

theorem tailTrace_609273 : CollatzResearch.WordTrace tailWord_609273 prefixEnd_609273 278088798939466622476009 := by
  unfold tailWord_609273
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222011921715451389224473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14814674614476967592816315 22222011921715451389224473)
  ·
    refine ⟨16666508941286588541918355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22222011921715451389224473 16666508941286588541918355)
    ·
      refine ⟨24999763411929882812877533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16666508941286588541918355 24999763411929882812877533)
      ·
        refine ⟨9374911279473706054829075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24999763411929882812877533 9374911279473706054829075)
        ·
          refine ⟨14062366919210559082243613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9374911279473706054829075 14062366919210559082243613)
          ·
            refine ⟨5273387594703959655841355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14062366919210559082243613 5273387594703959655841355)
            ·
              refine ⟨7910081392055939483762033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273387594703959655841355 7910081392055939483762033)
              ·
                refine ⟨5932561044041954612821525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7910081392055939483762033 5932561044041954612821525)
                ·
                  refine ⟨278088798939466622476009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5932561044041954612821525 278088798939466622476009)
                  ·
                    rfl

theorem cell20_609273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_609273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609273 prefixEnd_609273 := by exact prefixLift 609273
  have htrace : WordTrace (prefixWord ++ tailWord_609273) baseStart_609273 baseEnd_609273 := by
    simpa [prefixWord, tailWord_609273, baseEnd_609273] using wordTrace_append hprefix tailTrace_609273
  have hstable : (prefixWord ++ tailWord_609273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609273).length < 2 ^ (prefixWord ++ tailWord_609273).sum := by decide
  have hdescent : baseEnd_609273 < baseStart_609273 := by decide
  rcases family_descends (prefixWord ++ tailWord_609273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609290 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_609290 : Nat := 118140960795 + 609290 * 2 ^ 59
def prefixEnd_609290 : Nat := 4983230072969 + 3 ^ 40 * 609290 * 2
def baseEnd_609290 : Nat := 278096558202690118909273

theorem tailTrace_609290 : CollatzResearch.WordTrace tailWord_609290 prefixEnd_609290 278096558202690118909273 := by
  unfold tailWord_609290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555657990663465823148331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14815087975102575528395549 5555657990663465823148331)
  ·
    refine ⟨8333486985995198734722497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5555657990663465823148331 8333486985995198734722497)
    ·
      refine ⟨6250115239496399051041873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8333486985995198734722497 6250115239496399051041873)
      ·
        refine ⟨4687586429622299288281405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6250115239496399051041873 4687586429622299288281405)
        ·
          refine ⟨1757844911108362233105527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4687586429622299288281405 1757844911108362233105527)
          ·
            refine ⟨2636767366662543349658291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757844911108362233105527 2636767366662543349658291)
            ·
              refine ⟨3955151049993815024487437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636767366662543349658291 3955151049993815024487437)
              ·
                refine ⟨1483181643747680634182789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3955151049993815024487437 1483181643747680634182789)
                ·
                  refine ⟨278096558202690118909273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483181643747680634182789 278096558202690118909273)
                  ·
                    rfl

theorem cell20_609290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_609290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609290 prefixEnd_609290 := by exact prefixLift 609290
  have htrace : WordTrace (prefixWord ++ tailWord_609290) baseStart_609290 baseEnd_609290 := by
    simpa [prefixWord, tailWord_609290, baseEnd_609290] using wordTrace_append hprefix tailTrace_609290
  have hstable : (prefixWord ++ tailWord_609290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609290).length < 2 ^ (prefixWord ++ tailWord_609290).sum := by decide
  have hdescent : baseEnd_609290 < baseStart_609290 := by decide
  rcases family_descends (prefixWord ++ tailWord_609290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609314 : List Nat := [3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_609314 : Nat := 118140960795 + 609314 * 2 ^ 59
def prefixEnd_609314 : Nat := 4983230072969 + 3 ^ 40 * 609314 * 2
def baseEnd_609314 : Nat := 92702504152217567369725

theorem tailTrace_609314 : CollatzResearch.WordTrace tailWord_609314 prefixEnd_609314 92702504152217567369725 := by
  unfold tailWord_609314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555876828641728847866749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14815671543044610260977997 5555876828641728847866749)
  ·
    refine ⟨2083453810740648317950031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5555876828641728847866749 2083453810740648317950031)
    ·
      refine ⟨3125180716110972476925047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083453810740648317950031 3125180716110972476925047)
      ·
        refine ⟨4687771074166458715387571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125180716110972476925047 4687771074166458715387571)
        ·
          refine ⟨7031656611249688073081357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687771074166458715387571 7031656611249688073081357)
          ·
            refine ⟨2636871229218633027405509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7031656611249688073081357 2636871229218633027405509)
            ·
              refine ⟨494413355478493692638533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2636871229218633027405509 494413355478493692638533)
              ·
                refine ⟨92702504152217567369725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494413355478493692638533 92702504152217567369725)
                ·
                  rfl

theorem cell20_609314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_609314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609314 prefixEnd_609314 := by exact prefixLift 609314
  have htrace : WordTrace (prefixWord ++ tailWord_609314) baseStart_609314 baseEnd_609314 := by
    simpa [prefixWord, tailWord_609314, baseEnd_609314] using wordTrace_append hprefix tailTrace_609314
  have hstable : (prefixWord ++ tailWord_609314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609314).length < 2 ^ (prefixWord ++ tailWord_609314).sum := by decide
  have hdescent : baseEnd_609314 < baseStart_609314 := by decide
  rcases family_descends (prefixWord ++ tailWord_609314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609438 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_609438 : Nat := 118140960795 + 609438 * 2 ^ 59
def prefixEnd_609438 : Nat := 4983230072969 + 3 ^ 40 * 609438 * 2
def baseEnd_609438 : Nat := 278164109435459381975335

theorem tailTrace_609438 : CollatzResearch.WordTrace tailWord_609438 prefixEnd_609438 278164109435459381975335 := by
  unfold tailWord_609438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778503745764710571122621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14818686644078456379320645 2778503745764710571122621)
  ·
    refine ⟨1041938904661766464170983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2778503745764710571122621 1041938904661766464170983)
    ·
      refine ⟨1562908356992649696256475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041938904661766464170983 1562908356992649696256475)
      ·
        refine ⟨2344362535488974544384713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562908356992649696256475 2344362535488974544384713)
        ·
          refine ⟨1758271901616730908288535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344362535488974544384713 1758271901616730908288535)
          ·
            refine ⟨2637407852425096362432803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758271901616730908288535 2637407852425096362432803)
            ·
              refine ⟨3956111778637644543649205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637407852425096362432803 3956111778637644543649205)
              ·
                refine ⟨370885479247279175967113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3956111778637644543649205 370885479247279175967113)
                ·
                  refine ⟨278164109435459381975335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370885479247279175967113 278164109435459381975335)
                  ·
                    rfl

theorem cell20_609438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_609438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609438 prefixEnd_609438 := by exact prefixLift 609438
  have htrace : WordTrace (prefixWord ++ tailWord_609438) baseStart_609438 baseEnd_609438 := by
    simpa [prefixWord, tailWord_609438, baseEnd_609438] using wordTrace_append hprefix tailTrace_609438
  have hstable : (prefixWord ++ tailWord_609438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609438).length < 2 ^ (prefixWord ++ tailWord_609438).sum := by decide
  have hdescent : baseEnd_609438 < baseStart_609438 := by decide
  rcases family_descends (prefixWord ++ tailWord_609438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609508 : List Nat := [2, 3, 1, 1, 1, 2, 10]
def baseStart_609508 : Nat := 118140960795 + 609508 * 2 ^ 59
def prefixEnd_609508 : Nat := 4983230072969 + 3 ^ 40 * 609508 * 2
def baseEnd_609508 : Nat := 30910673260316694404635

theorem tailTrace_609508 : CollatzResearch.WordTrace tailWord_609508 prefixEnd_609508 30910673260316694404635 := by
  unfold tailWord_609508
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115291537932043262014589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14820388717242724349352785 11115291537932043262014589)
  ·
    refine ⟨4168234326724516223255471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11115291537932043262014589 4168234326724516223255471)
    ·
      refine ⟨6252351490086774334883207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4168234326724516223255471 6252351490086774334883207)
      ·
        refine ⟨9378527235130161502324811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6252351490086774334883207 9378527235130161502324811)
        ·
          refine ⟨14067790852695242253487217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9378527235130161502324811 14067790852695242253487217)
          ·
            refine ⟨10550843139521431690115413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14067790852695242253487217 10550843139521431690115413)
            ·
              refine ⟨30910673260316694404635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10550843139521431690115413 30910673260316694404635)
              ·
                rfl

theorem cell20_609508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_609508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609508 prefixEnd_609508 := by exact prefixLift 609508
  have htrace : WordTrace (prefixWord ++ tailWord_609508) baseStart_609508 baseEnd_609508 := by
    simpa [prefixWord, tailWord_609508, baseEnd_609508] using wordTrace_append hprefix tailTrace_609508
  have hstable : (prefixWord ++ tailWord_609508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609508).length < 2 ^ (prefixWord ++ tailWord_609508).sum := by decide
  have hdescent : baseEnd_609508 < baseStart_609508 := by decide
  rcases family_descends (prefixWord ++ tailWord_609508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609514 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_609514 : Nat := 118140960795 + 609514 * 2 ^ 59
def prefixEnd_609514 : Nat := 4983230072969 + 3 ^ 40 * 609514 * 2
def baseEnd_609514 : Nat := 278198797906340895441691

theorem tailTrace_609514 : CollatzResearch.WordTrace tailWord_609514 prefixEnd_609514 278198797906340895441691 := by
  unfold tailWord_609514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557700478460587387186899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14820534609228233032498397 5557700478460587387186899)
  ·
    refine ⟨8336550717690881080780349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5557700478460587387186899 8336550717690881080780349)
    ·
      refine ⟨3126206519134080405292631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8336550717690881080780349 3126206519134080405292631)
      ·
        refine ⟨4689309778701120607938947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126206519134080405292631 4689309778701120607938947)
        ·
          refine ⟨7033964668051680911908421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4689309778701120607938947 7033964668051680911908421)
          ·
            refine ⟨1318868375259690170982829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7033964668051680911908421 1318868375259690170982829)
            ·
              refine ⟨494575640722383814118561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1318868375259690170982829 494575640722383814118561)
              ·
                refine ⟨370931730541787860588921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494575640722383814118561 370931730541787860588921)
                ·
                  refine ⟨278198797906340895441691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370931730541787860588921 278198797906340895441691)
                  ·
                    rfl

theorem cell20_609514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_609514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609514 prefixEnd_609514 := by exact prefixLift 609514
  have htrace : WordTrace (prefixWord ++ tailWord_609514) baseStart_609514 baseEnd_609514 := by
    simpa [prefixWord, tailWord_609514, baseEnd_609514] using wordTrace_append hprefix tailTrace_609514
  have hstable : (prefixWord ++ tailWord_609514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609514).length < 2 ^ (prefixWord ++ tailWord_609514).sum := by decide
  have hdescent : baseEnd_609514 < baseStart_609514 := by decide
  rcases family_descends (prefixWord ++ tailWord_609514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609518 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_609518 : Nat := 118140960795 + 609518 * 2 ^ 59
def prefixEnd_609518 : Nat := 4983230072969 + 3 ^ 40 * 609518 * 2
def baseEnd_609518 : Nat := 278200623615334659308341

theorem tailTrace_609518 : CollatzResearch.WordTrace tailWord_609518 prefixEnd_609518 278200623615334659308341 := by
  unfold tailWord_609518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778868475728482278986651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14820631870551905487928805 2778868475728482278986651)
  ·
    refine ⟨4168302713592723418479977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2778868475728482278986651 4168302713592723418479977)
    ·
      refine ⟨3126227035194542563859983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4168302713592723418479977 3126227035194542563859983)
      ·
        refine ⟨4689340552791813845789975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126227035194542563859983 4689340552791813845789975)
        ·
          refine ⟨7034010829187720768684963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4689340552791813845789975 7034010829187720768684963)
          ·
            refine ⟨10551016243781581153027445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7034010829187720768684963 10551016243781581153027445)
            ·
              refine ⟨989157772854523233096323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10551016243781581153027445 989157772854523233096323)
              ·
                refine ⟨1483736659281784849644485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989157772854523233096323 1483736659281784849644485)
                ·
                  refine ⟨278200623615334659308341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483736659281784849644485 278200623615334659308341)
                  ·
                    rfl

theorem cell20_609518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_609518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609518 prefixEnd_609518 := by exact prefixLift 609518
  have htrace : WordTrace (prefixWord ++ tailWord_609518) baseStart_609518 baseEnd_609518 := by
    simpa [prefixWord, tailWord_609518, baseEnd_609518] using wordTrace_append hprefix tailTrace_609518
  have hstable : (prefixWord ++ tailWord_609518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609518).length < 2 ^ (prefixWord ++ tailWord_609518).sum := by decide
  have hdescent : baseEnd_609518 < baseStart_609518 := by decide
  rcases family_descends (prefixWord ++ tailWord_609518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609524 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_609524 : Nat := 118140960795 + 609524 * 2 ^ 59
def prefixEnd_609524 : Nat := 4983230072969 + 3 ^ 40 * 609524 * 2
def baseEnd_609524 : Nat := 278203362178825305108317

theorem tailTrace_609524 : CollatzResearch.WordTrace tailWord_609524 prefixEnd_609524 278203362178825305108317 := by
  unfold tailWord_609524
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115583321903060628305813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14820777762537414171074417 11115583321903060628305813)
  ·
    refine ⟨521042968214205966951835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11115583321903060628305813 521042968214205966951835)
    ·
      refine ⟨781564452321308950427753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521042968214205966951835 781564452321308950427753)
      ·
        refine ⟨586173339240981712820815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781564452321308950427753 586173339240981712820815)
        ·
          refine ⟨879260008861472569231223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586173339240981712820815 879260008861472569231223)
          ·
            refine ⟨1318890013292208853846835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879260008861472569231223 1318890013292208853846835)
            ·
              refine ⟨1978335019938313280770253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318890013292208853846835 1978335019938313280770253)
              ·
                refine ⟨741875632476867480288845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1978335019938313280770253 741875632476867480288845)
                ·
                  refine ⟨278203362178825305108317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741875632476867480288845 278203362178825305108317)
                  ·
                    rfl

theorem cell20_609524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_609524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609524 prefixEnd_609524 := by exact prefixLift 609524
  have htrace : WordTrace (prefixWord ++ tailWord_609524) baseStart_609524 baseEnd_609524 := by
    simpa [prefixWord, tailWord_609524, baseEnd_609524] using wordTrace_append hprefix tailTrace_609524
  have hstable : (prefixWord ++ tailWord_609524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609524).length < 2 ^ (prefixWord ++ tailWord_609524).sum := by decide
  have hdescent : baseEnd_609524 < baseStart_609524 := by decide
  rcases family_descends (prefixWord ++ tailWord_609524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609573 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 2]
def baseStart_609573 : Nat := 118140960795 + 609573 * 2 ^ 59
def prefixEnd_609573 : Nat := 4983230072969 + 3 ^ 40 * 609573 * 2
def baseEnd_609573 : Nat := 278225727113998912474783

theorem tailTrace_609573 : CollatzResearch.WordTrace tailWord_609573 prefixEnd_609573 278225727113998912474783 := by
  unfold tailWord_609573
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232953820628602625145373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14821969213752401750096915 22232953820628602625145373)
  ·
    refine ⟨8337357682735725984429515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22232953820628602625145373 8337357682735725984429515)
    ·
      refine ⟨12506036524103588976644273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8337357682735725984429515 12506036524103588976644273)
      ·
        refine ⟨9379527393077691732483205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12506036524103588976644273 9379527393077691732483205)
        ·
          refine ⟨1758661386202067199840601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9379527393077691732483205 1758661386202067199840601)
          ·
            refine ⟨1318996039651550399880451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758661386202067199840601 1318996039651550399880451)
            ·
              refine ⟨1978494059477325599820677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318996039651550399880451 1978494059477325599820677)
              ·
                refine ⟨370967636151998549966377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1978494059477325599820677 370967636151998549966377)
                ·
                  refine ⟨278225727113998912474783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370967636151998549966377 278225727113998912474783)
                  ·
                    rfl

theorem cell20_609573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_609573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609573 prefixEnd_609573 := by exact prefixLift 609573
  have htrace : WordTrace (prefixWord ++ tailWord_609573) baseStart_609573 baseEnd_609573 := by
    simpa [prefixWord, tailWord_609573, baseEnd_609573] using wordTrace_append hprefix tailTrace_609573
  have hstable : (prefixWord ++ tailWord_609573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609573).length < 2 ^ (prefixWord ++ tailWord_609573).sum := by decide
  have hdescent : baseEnd_609573 < baseStart_609573 := by decide
  rcases family_descends (prefixWord ++ tailWord_609573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609590 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_609590 : Nat := 118140960795 + 609590 * 2 ^ 59
def prefixEnd_609590 : Nat := 4983230072969 + 3 ^ 40 * 609590 * 2
def baseEnd_609590 : Nat := 278233486377222408908047

theorem tailTrace_609590 : CollatzResearch.WordTrace tailWord_609590 prefixEnd_609590 278233486377222408908047 := by
  unfold tailWord_609590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389598366347938408032139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14822382574378009685676149 1389598366347938408032139)
  ·
    refine ⟨2084397549521907612048209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1389598366347938408032139 2084397549521907612048209)
    ·
      refine ⟨1563298162141430709036157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2084397549521907612048209 1563298162141430709036157)
      ·
        refine ⟨586236810803036515888559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1563298162141430709036157 586236810803036515888559)
        ·
          refine ⟨879355216204554773832839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586236810803036515888559 879355216204554773832839)
          ·
            refine ⟨1319032824306832160749259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879355216204554773832839 1319032824306832160749259)
            ·
              refine ⟨1978549236460248241123889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319032824306832160749259 1978549236460248241123889)
              ·
                refine ⟨1483911927345186180842917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978549236460248241123889 1483911927345186180842917)
                ·
                  refine ⟨278233486377222408908047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483911927345186180842917 278233486377222408908047)
                  ·
                    rfl

theorem cell20_609590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_609590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609590 prefixEnd_609590 := by exact prefixLift 609590
  have htrace : WordTrace (prefixWord ++ tailWord_609590) baseStart_609590 baseEnd_609590 := by
    simpa [prefixWord, tailWord_609590, baseEnd_609590] using wordTrace_append hprefix tailTrace_609590
  have hstable : (prefixWord ++ tailWord_609590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609590).length < 2 ^ (prefixWord ++ tailWord_609590).sum := by decide
  have hdescent : baseEnd_609590 < baseStart_609590 := by decide
  rcases family_descends (prefixWord ++ tailWord_609590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609591 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_609591 : Nat := 118140960795 + 609591 * 2 ^ 59
def prefixEnd_609591 : Nat := 4983230072969 + 3 ^ 40 * 609591 * 2
def baseEnd_609591 : Nat := 278233942804470849874709

theorem tailTrace_609591 : CollatzResearch.WordTrace tailWord_609591 prefixEnd_609591 278233942804470849874709 := by
  unfold tailWord_609591
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233610334563391699300627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14822406889708927799533751 22233610334563391699300627)
  ·
    refine ⟨33350415501845087548950941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22233610334563391699300627 33350415501845087548950941)
    ·
      refine ⟨12506405813191907830856603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33350415501845087548950941 12506405813191907830856603)
      ·
        refine ⟨18759608719787861746284905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12506405813191907830856603 18759608719787861746284905)
        ·
          refine ⟨14069706539840896309713679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18759608719787861746284905 14069706539840896309713679)
          ·
            refine ⟨21104559809761344464570519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14069706539840896309713679 21104559809761344464570519)
            ·
              refine ⟨31656839714642016696855779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21104559809761344464570519 31656839714642016696855779)
              ·
                refine ⟨47485259571963025045283669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31656839714642016696855779 47485259571963025045283669)
                ·
                  refine ⟨278233942804470849874709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47485259571963025045283669 278233942804470849874709)
                  ·
                    rfl

theorem cell20_609591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_609591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609591 prefixEnd_609591 := by exact prefixLift 609591
  have htrace : WordTrace (prefixWord ++ tailWord_609591) baseStart_609591 baseEnd_609591 := by
    simpa [prefixWord, tailWord_609591, baseEnd_609591] using wordTrace_append hprefix tailTrace_609591
  have hstable : (prefixWord ++ tailWord_609591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609591).length < 2 ^ (prefixWord ++ tailWord_609591).sum := by decide
  have hdescent : baseEnd_609591 < baseStart_609591 := by decide
  rcases family_descends (prefixWord ++ tailWord_609591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609597 : List Nat := [1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_609597 : Nat := 118140960795 + 609597 * 2 ^ 59
def prefixEnd_609597 : Nat := 4983230072969 + 3 ^ 40 * 609597 * 2
def baseEnd_609597 : Nat := 92745560455987165224895

theorem tailTrace_609597 : CollatzResearch.WordTrace tailWord_609597 prefixEnd_609597 92745560455987165224895 := by
  unfold tailWord_609597
  simp only [CollatzResearch.WordTrace]
  refine ⟨22233829172541654724019045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14822552781694436482679363 22233829172541654724019045)
  ·
    refine ⟨4168842969851560260753571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22233829172541654724019045 4168842969851560260753571)
    ·
      refine ⟨6253264454777340391130357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4168842969851560260753571 6253264454777340391130357)
      ·
        refine ⟨586243542635375661668471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6253264454777340391130357 586243542635375661668471)
        ·
          refine ⟨879365313953063492502707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586243542635375661668471 879365313953063492502707)
          ·
            refine ⟨1319047970929595238754061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879365313953063492502707 1319047970929595238754061)
            ·
              refine ⟨494642989098598214532773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319047970929595238754061 494642989098598214532773)
              ·
                refine ⟨92745560455987165224895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494642989098598214532773 92745560455987165224895)
                ·
                  rfl

theorem cell20_609597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_609597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609597 prefixEnd_609597 := by exact prefixLift 609597
  have htrace : WordTrace (prefixWord ++ tailWord_609597) baseStart_609597 baseEnd_609597 := by
    simpa [prefixWord, tailWord_609597, baseEnd_609597] using wordTrace_append hprefix tailTrace_609597
  have hstable : (prefixWord ++ tailWord_609597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609597).length < 2 ^ (prefixWord ++ tailWord_609597).sum := by decide
  have hdescent : baseEnd_609597 < baseStart_609597 := by decide
  rcases family_descends (prefixWord ++ tailWord_609597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609632 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_609632 : Nat := 118140960795 + 609632 * 2 ^ 59
def prefixEnd_609632 : Nat := 4983230072969 + 3 ^ 40 * 609632 * 2
def baseEnd_609632 : Nat := 278252656321656929507875

theorem tailTrace_609632 : CollatzResearch.WordTrace tailWord_609632 prefixEnd_609632 278252656321656929507875 := by
  unfold tailWord_609632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11117552863707427850771575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14823403818276570467695433 11117552863707427850771575)
  ·
    refine ⟨16676329295561141776157363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11117552863707427850771575 16676329295561141776157363)
    ·
      refine ⟨25014493943341712664236045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16676329295561141776157363 25014493943341712664236045)
      ·
        refine ⟨9380435228753142249088517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25014493943341712664236045 9380435228753142249088517)
        ·
          refine ⟨1758831605391214171704097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9380435228753142249088517 1758831605391214171704097)
          ·
            refine ⟨1319123704043410628778073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758831605391214171704097 1319123704043410628778073)
            ·
              refine ⟨989342778032557971583555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319123704043410628778073 989342778032557971583555)
              ·
                refine ⟨1484014167048836957375333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989342778032557971583555 1484014167048836957375333)
                ·
                  refine ⟨278252656321656929507875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484014167048836957375333 278252656321656929507875)
                  ·
                    rfl

theorem cell20_609632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_609632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609632 prefixEnd_609632 := by exact prefixLift 609632
  have htrace : WordTrace (prefixWord ++ tailWord_609632) baseStart_609632 baseEnd_609632 := by
    simpa [prefixWord, tailWord_609632, baseEnd_609632] using wordTrace_append hprefix tailTrace_609632
  have hstable : (prefixWord ++ tailWord_609632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609632).length < 2 ^ (prefixWord ++ tailWord_609632).sum := by decide
  have hdescent : baseEnd_609632 < baseStart_609632 := by decide
  rcases family_descends (prefixWord ++ tailWord_609632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609660 : List Nat := [2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_609660 : Nat := 118140960795 + 609660 * 2 ^ 59
def prefixEnd_609660 : Nat := 4983230072969 + 3 ^ 40 * 609660 * 2
def baseEnd_609660 : Nat := 92755145428204425524809

theorem tailTrace_609660 : CollatzResearch.WordTrace tailWord_609660 prefixEnd_609660 92755145428204425524809 := by
  unfold tailWord_609660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11118063485656708241781217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14824084647542277655708289 11118063485656708241781217)
  ·
    refine ⟨8338547614242531181335913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11118063485656708241781217 8338547614242531181335913)
    ·
      refine ⟨6253910710681898386001935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8338547614242531181335913 6253910710681898386001935)
      ·
        refine ⟨9380866066022847579002903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6253910710681898386001935 9380866066022847579002903)
        ·
          refine ⟨14071299099034271368504355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9380866066022847579002903 14071299099034271368504355)
          ·
            refine ⟨21106948648551407052756533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14071299099034271368504355 21106948648551407052756533)
            ·
              refine ⟨1978776435801694411195925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21106948648551407052756533 1978776435801694411195925)
              ·
                refine ⟨92755145428204425524809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1978776435801694411195925 92755145428204425524809)
                ·
                  rfl

theorem cell20_609660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_609660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609660 prefixEnd_609660 := by exact prefixLift 609660
  have htrace : WordTrace (prefixWord ++ tailWord_609660) baseStart_609660 baseEnd_609660 := by
    simpa [prefixWord, tailWord_609660, baseEnd_609660] using wordTrace_append hprefix tailTrace_609660
  have hstable : (prefixWord ++ tailWord_609660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609660).length < 2 ^ (prefixWord ++ tailWord_609660).sum := by decide
  have hdescent : baseEnd_609660 < baseStart_609660 := by decide
  rcases family_descends (prefixWord ++ tailWord_609660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609662 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_609662 : Nat := 118140960795 + 609662 * 2 ^ 59
def prefixEnd_609662 : Nat := 4983230072969 + 3 ^ 40 * 609662 * 2
def baseEnd_609662 : Nat := 278266349139110158507753

theorem tailTrace_609662 : CollatzResearch.WordTrace tailWord_609662 prefixEnd_609662 278266349139110158507753 := by
  unfold tailWord_609662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779524989663271353141905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14824133278204113883423493 2779524989663271353141905)
  ·
    refine ⟨2084643742247453514856429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2779524989663271353141905 2084643742247453514856429)
    ·
      refine ⟨781741403342795068071161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2084643742247453514856429 781741403342795068071161)
      ·
        refine ⟨586306052507096301053371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781741403342795068071161 586306052507096301053371)
        ·
          refine ⟨879459078760644451580057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586306052507096301053371 879459078760644451580057)
          ·
            refine ⟨659594309070483338685043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879459078760644451580057 659594309070483338685043)
            ·
              refine ⟨989391463605725008027565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659594309070483338685043 989391463605725008027565)
              ·
                refine ⟨371021798852146878010337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989391463605725008027565 371021798852146878010337)
                ·
                  refine ⟨278266349139110158507753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371021798852146878010337 278266349139110158507753)
                  ·
                    rfl

theorem cell20_609662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_609662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609662 prefixEnd_609662 := by exact prefixLift 609662
  have htrace : WordTrace (prefixWord ++ tailWord_609662) baseStart_609662 baseEnd_609662 := by
    simpa [prefixWord, tailWord_609662, baseEnd_609662] using wordTrace_append hprefix tailTrace_609662
  have hstable : (prefixWord ++ tailWord_609662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609662).length < 2 ^ (prefixWord ++ tailWord_609662).sum := by decide
  have hdescent : baseEnd_609662 < baseStart_609662 := by decide
  rcases family_descends (prefixWord ++ tailWord_609662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609743 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_609743 : Nat := 118140960795 + 609743 * 2 ^ 59
def prefixEnd_609743 : Nat := 4983230072969 + 3 ^ 40 * 609743 * 2
def baseEnd_609743 : Nat := 278303319746233876807421

theorem tailTrace_609743 : CollatzResearch.WordTrace tailWord_609743 prefixEnd_609743 278303319746233876807421 := by
  unfold tailWord_609743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22239154230012721658833883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14826102820008481105889255 22239154230012721658833883)
  ·
    refine ⟨33358731345019082488250825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22239154230012721658833883 33358731345019082488250825)
    ·
      refine ⟨25019048508764311866188119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33358731345019082488250825 25019048508764311866188119)
      ·
        refine ⟨37528572763146467799282179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25019048508764311866188119 37528572763146467799282179)
        ·
          refine ⟨56292859144719701698923269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37528572763146467799282179 56292859144719701698923269)
          ·
            refine ⟨10554911089634944068548113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56292859144719701698923269 10554911089634944068548113)
            ·
              refine ⟨7916183317226208051411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10554911089634944068548113 7916183317226208051411085)
              ·
                refine ⟨2968568743959828019279157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916183317226208051411085 2968568743959828019279157)
                ·
                  refine ⟨278303319746233876807421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968568743959828019279157 278303319746233876807421)
                  ·
                    rfl

theorem cell20_609743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_609743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609743 prefixEnd_609743 := by exact prefixLift 609743
  have htrace : WordTrace (prefixWord ++ tailWord_609743) baseStart_609743 baseEnd_609743 := by
    simpa [prefixWord, tailWord_609743, baseEnd_609743] using wordTrace_append hprefix tailTrace_609743
  have hstable : (prefixWord ++ tailWord_609743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609743).length < 2 ^ (prefixWord ++ tailWord_609743).sum := by decide
  have hdescent : baseEnd_609743 < baseStart_609743 := by decide
  rcases family_descends (prefixWord ++ tailWord_609743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609753 : List Nat := [1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_609753 : Nat := 118140960795 + 609753 * 2 ^ 59
def prefixEnd_609753 : Nat := 4983230072969 + 3 ^ 40 * 609753 * 2
def baseEnd_609753 : Nat := 92769294672906095491349

theorem tailTrace_609753 : CollatzResearch.WordTrace tailWord_609753 prefixEnd_609753 92769294672906095491349 := by
  unfold tailWord_609753
  simp only [CollatzResearch.WordTrace]
  refine ⟨22239518959976493366697913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14826345973317662244465275 22239518959976493366697913)
  ·
    refine ⟨16679639219982370025023435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22239518959976493366697913 16679639219982370025023435)
    ·
      refine ⟨25019458829973555037535153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16679639219982370025023435 25019458829973555037535153)
      ·
        refine ⟨18764594122480166278151365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25019458829973555037535153 18764594122480166278151365)
        ·
          refine ⟨3518361397965031177153381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18764594122480166278151365 3518361397965031177153381)
          ·
            refine ⟨659692762118443345716259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3518361397965031177153381 659692762118443345716259)
            ·
              refine ⟨989539143177665018574389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659692762118443345716259 989539143177665018574389)
              ·
                refine ⟨92769294672906095491349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 989539143177665018574389 92769294672906095491349)
                ·
                  rfl

theorem cell20_609753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_609753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609753 prefixEnd_609753 := by exact prefixLift 609753
  have htrace : WordTrace (prefixWord ++ tailWord_609753) baseStart_609753 baseEnd_609753 := by
    simpa [prefixWord, tailWord_609753, baseEnd_609753] using wordTrace_append hprefix tailTrace_609753
  have hstable : (prefixWord ++ tailWord_609753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609753).length < 2 ^ (prefixWord ++ tailWord_609753).sum := by decide
  have hdescent : baseEnd_609753 < baseStart_609753 := by decide
  rcases family_descends (prefixWord ++ tailWord_609753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609767 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_609767 : Nat := 118140960795 + 609767 * 2 ^ 59
def prefixEnd_609767 : Nat := 4983230072969 + 3 ^ 40 * 609767 * 2
def baseEnd_609767 : Nat := 278314274000196460007323

theorem tailTrace_609767 : CollatzResearch.WordTrace tailWord_609767 prefixEnd_609767 278314274000196460007323 := by
  unfold tailWord_609767
  simp only [CollatzResearch.WordTrace]
  refine ⟨22240029581925773757707555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14826686387950515838471703 22240029581925773757707555)
  ·
    refine ⟨33360044372888660636561333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22240029581925773757707555 33360044372888660636561333)
    ·
      refine ⟨3127504159958311934677625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33360044372888660636561333 3127504159958311934677625)
      ·
        refine ⟨2345628119968733951008219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3127504159958311934677625 2345628119968733951008219)
        ·
          refine ⟨3518442179953100926512329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345628119968733951008219 3518442179953100926512329)
          ·
            refine ⟨2638831634964825694884247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518442179953100926512329 2638831634964825694884247)
            ·
              refine ⟨3958247452447238542326371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638831634964825694884247 3958247452447238542326371)
              ·
                refine ⟨5937371178670857813489557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958247452447238542326371 5937371178670857813489557)
                ·
                  refine ⟨278314274000196460007323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5937371178670857813489557 278314274000196460007323)
                  ·
                    rfl

theorem cell20_609767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_609767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609767 prefixEnd_609767 := by exact prefixLift 609767
  have htrace : WordTrace (prefixWord ++ tailWord_609767) baseStart_609767 baseEnd_609767 := by
    simpa [prefixWord, tailWord_609767, baseEnd_609767] using wordTrace_append hprefix tailTrace_609767
  have hstable : (prefixWord ++ tailWord_609767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609767).length < 2 ^ (prefixWord ++ tailWord_609767).sum := by decide
  have hdescent : baseEnd_609767 < baseStart_609767 := by decide
  rcases family_descends (prefixWord ++ tailWord_609767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609770 : List Nat := [3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_609770 : Nat := 118140960795 + 609770 * 2 ^ 59
def prefixEnd_609770 : Nat := 4983230072969 + 3 ^ 40 * 609770 * 2
def baseEnd_609770 : Nat := 92771881093980594302437

theorem tailTrace_609770 : CollatzResearch.WordTrace tailWord_609770 prefixEnd_609770 92771881093980594302437 := by
  unfold tailWord_609770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560034750228726317516691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14826759333943270180044509 5560034750228726317516691)
  ·
    refine ⟨8340052125343089476275037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5560034750228726317516691 8340052125343089476275037)
    ·
      refine ⟨3127519547003658553603139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8340052125343089476275037 3127519547003658553603139)
      ·
        refine ⟨4691279320505487830404709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127519547003658553603139 4691279320505487830404709)
        ·
          refine ⟨879614872594778968200883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4691279320505487830404709 879614872594778968200883)
          ·
            refine ⟨1319422308892168452301325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879614872594778968200883 1319422308892168452301325)
            ·
              refine ⟨494783365834563169612997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319422308892168452301325 494783365834563169612997)
              ·
                refine ⟨92771881093980594302437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494783365834563169612997 92771881093980594302437)
                ·
                  rfl

theorem cell20_609770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_609770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609770 prefixEnd_609770 := by exact prefixLift 609770
  have htrace : WordTrace (prefixWord ++ tailWord_609770) baseStart_609770 baseEnd_609770 := by
    simpa [prefixWord, tailWord_609770, baseEnd_609770] using wordTrace_append hprefix tailTrace_609770
  have hstable : (prefixWord ++ tailWord_609770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609770).length < 2 ^ (prefixWord ++ tailWord_609770).sum := by decide
  have hdescent : baseEnd_609770 < baseStart_609770 := by decide
  rcases family_descends (prefixWord ++ tailWord_609770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609784 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_609784 : Nat := 118140960795 + 609784 * 2 ^ 59
def prefixEnd_609784 : Nat := 4983230072969 + 3 ^ 40 * 609784 * 2
def baseEnd_609784 : Nat := 278322033263419956440587

theorem tailTrace_609784 : CollatzResearch.WordTrace tailWord_609784 prefixEnd_609784 278322033263419956440587 := by
  unfold tailWord_609784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120324811432092830538203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14827099748576123774050937 11120324811432092830538203)
  ·
    refine ⟨16680487217148139245807305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11120324811432092830538203 16680487217148139245807305)
    ·
      refine ⟨12510365412861104434355479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16680487217148139245807305 12510365412861104434355479)
      ·
        refine ⟨18765548119291656651533219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12510365412861104434355479 18765548119291656651533219)
        ·
          refine ⟨28148322178937484977299829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18765548119291656651533219 28148322178937484977299829)
          ·
            refine ⟨2638905204275389216621859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28148322178937484977299829 2638905204275389216621859)
            ·
              refine ⟨3958357806413083824932789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638905204275389216621859 3958357806413083824932789)
              ·
                refine ⟨371096044351226608587449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3958357806413083824932789 371096044351226608587449)
                ·
                  refine ⟨278322033263419956440587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371096044351226608587449 278322033263419956440587)
                  ·
                    rfl

theorem cell20_609784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_609784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609784 prefixEnd_609784 := by exact prefixLift 609784
  have htrace : WordTrace (prefixWord ++ tailWord_609784) baseStart_609784 baseEnd_609784 := by
    simpa [prefixWord, tailWord_609784, baseEnd_609784] using wordTrace_append hprefix tailTrace_609784
  have hstable : (prefixWord ++ tailWord_609784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609784).length < 2 ^ (prefixWord ++ tailWord_609784).sum := by decide
  have hdescent : baseEnd_609784 < baseStart_609784 := by decide
  rcases family_descends (prefixWord ++ tailWord_609784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609790 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_609790 : Nat := 118140960795 + 609790 * 2 ^ 59
def prefixEnd_609790 : Nat := 4983230072969 + 3 ^ 40 * 609790 * 2
def baseEnd_609790 : Nat := 278324771826910602240563

theorem tailTrace_609790 : CollatzResearch.WordTrace tailWord_609790 prefixEnd_609790 278324771826910602240563 := by
  unfold tailWord_609790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780108557605306085724353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14827245640561632457196549 2780108557605306085724353)
  ·
    refine ⟨2085081418203979564293265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2780108557605306085724353 2085081418203979564293265)
    ·
      refine ⟨1563811063652984673219949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2085081418203979564293265 1563811063652984673219949)
      ·
        refine ⟨586429148869869252457481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1563811063652984673219949 586429148869869252457481)
        ·
          refine ⟨439821861652401939343111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586429148869869252457481 439821861652401939343111)
          ·
            refine ⟨659732792478602909014667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439821861652401939343111 659732792478602909014667)
            ·
              refine ⟨989599188717904363522001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659732792478602909014667 989599188717904363522001)
              ·
                refine ⟨742199391538428272641501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989599188717904363522001 742199391538428272641501)
                ·
                  refine ⟨278324771826910602240563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742199391538428272641501 278324771826910602240563)
                  ·
                    rfl

theorem cell20_609790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_609790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609790 prefixEnd_609790 := by exact prefixLift 609790
  have htrace : WordTrace (prefixWord ++ tailWord_609790) baseStart_609790 baseEnd_609790 := by
    simpa [prefixWord, tailWord_609790, baseEnd_609790] using wordTrace_append hprefix tailTrace_609790
  have hstable : (prefixWord ++ tailWord_609790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609790).length < 2 ^ (prefixWord ++ tailWord_609790).sum := by decide
  have hdescent : baseEnd_609790 < baseStart_609790 := by decide
  rcases family_descends (prefixWord ++ tailWord_609790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609794 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_609794 : Nat := 118140960795 + 609794 * 2 ^ 59
def prefixEnd_609794 : Nat := 4983230072969 + 3 ^ 40 * 609794 * 2
def baseEnd_609794 : Nat := 278326597535904366107213

theorem tailTrace_609794 : CollatzResearch.WordTrace tailWord_609794 prefixEnd_609794 278326597535904366107213 := by
  unfold tailWord_609794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560253588206989342235109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14827342901885304912626957 5560253588206989342235109)
  ·
    refine ⟨1042547547788810501669083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5560253588206989342235109 1042547547788810501669083)
    ·
      refine ⟨1563821321683215752503625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042547547788810501669083 1563821321683215752503625)
      ·
        refine ⟨1172865991262411814377719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1563821321683215752503625 1172865991262411814377719)
        ·
          refine ⟨1759298986893617721566579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172865991262411814377719 1759298986893617721566579)
          ·
            refine ⟨2638948480340426582349869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759298986893617721566579 2638948480340426582349869)
            ·
              refine ⟨989605680127659968381201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2638948480340426582349869 989605680127659968381201)
              ·
                refine ⟨742204260095744976285901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989605680127659968381201 742204260095744976285901)
                ·
                  refine ⟨278326597535904366107213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742204260095744976285901 278326597535904366107213)
                  ·
                    rfl

theorem cell20_609794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_609794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609794 prefixEnd_609794 := by exact prefixLift 609794
  have htrace : WordTrace (prefixWord ++ tailWord_609794) baseStart_609794 baseEnd_609794 := by
    simpa [prefixWord, tailWord_609794, baseEnd_609794] using wordTrace_append hprefix tailTrace_609794
  have hstable : (prefixWord ++ tailWord_609794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609794).length < 2 ^ (prefixWord ++ tailWord_609794).sum := by decide
  have hdescent : baseEnd_609794 < baseStart_609794 := by decide
  rcases family_descends (prefixWord ++ tailWord_609794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609846 : List Nat := [5, 1, 2, 1, 3, 2, 6]
def baseStart_609846 : Nat := 118140960795 + 609846 * 2 ^ 59
def prefixEnd_609846 : Nat := 4983230072969 + 3 ^ 40 * 609846 * 2
def baseEnd_609846 : Nat := 30927814639202588485963

theorem tailTrace_609846 : CollatzResearch.WordTrace tailWord_609846 prefixEnd_609846 30927814639202588485963 := by
  unfold tailWord_609846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390181934289973140614587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14828607299093046833222261 1390181934289973140614587)
  ·
    refine ⟨2085272901434959710921881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1390181934289973140614587 2085272901434959710921881)
    ·
      refine ⟨1563954676076219783191411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2085272901434959710921881 1563954676076219783191411)
      ·
        refine ⟨2345932014114329674787117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563954676076219783191411 2345932014114329674787117)
        ·
          refine ⟨879724505292873628045169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2345932014114329674787117 879724505292873628045169)
          ·
            refine ⟨659793378969655221033877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879724505292873628045169 659793378969655221033877)
            ·
              refine ⟨30927814639202588485963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 659793378969655221033877 30927814639202588485963)
              ·
                rfl

theorem cell20_609846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_609846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609846 prefixEnd_609846 := by exact prefixLift 609846
  have htrace : WordTrace (prefixWord ++ tailWord_609846) baseStart_609846 baseEnd_609846 := by
    simpa [prefixWord, tailWord_609846, baseEnd_609846] using wordTrace_append hprefix tailTrace_609846
  have hstable : (prefixWord ++ tailWord_609846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609846).length < 2 ^ (prefixWord ++ tailWord_609846).sum := by decide
  have hdescent : baseEnd_609846 < baseStart_609846 := by decide
  rcases family_descends (prefixWord ++ tailWord_609846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609895 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_609895 : Nat := 118140960795 + 609895 * 2 ^ 59
def prefixEnd_609895 : Nat := 4983230072969 + 3 ^ 40 * 609895 * 2
def baseEnd_609895 : Nat := 278372696687996903740133

theorem tailTrace_609895 : CollatzResearch.WordTrace tailWord_609895 prefixEnd_609895 278372696687996903740133 := by
  unfold tailWord_609895
  simp only [CollatzResearch.WordTrace]
  refine ⟨22244698125462051618367139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14829798750308034412244759 22244698125462051618367139)
  ·
    refine ⟨33367047188193077427550709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22244698125462051618367139 33367047188193077427550709)
    ·
      refine ⟨3128160673893101008832879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33367047188193077427550709 3128160673893101008832879)
      ·
        refine ⟨4692241010839651513249319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128160673893101008832879 4692241010839651513249319)
        ·
          refine ⟨7038361516259477269873979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692241010839651513249319 7038361516259477269873979)
          ·
            refine ⟨10557542274389215904810969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038361516259477269873979 10557542274389215904810969)
            ·
              refine ⟨7918156705791911928608227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10557542274389215904810969 7918156705791911928608227)
              ·
                refine ⟨11877235058687867892912341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918156705791911928608227 11877235058687867892912341)
                ·
                  refine ⟨278372696687996903740133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11877235058687867892912341 278372696687996903740133)
                  ·
                    rfl

theorem cell20_609895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_609895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609895 prefixEnd_609895 := by exact prefixLift 609895
  have htrace : WordTrace (prefixWord ++ tailWord_609895) baseStart_609895 baseEnd_609895 := by
    simpa [prefixWord, tailWord_609895, baseEnd_609895] using wordTrace_append hprefix tailTrace_609895
  have hstable : (prefixWord ++ tailWord_609895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609895).length < 2 ^ (prefixWord ++ tailWord_609895).sum := by decide
  have hdescent : baseEnd_609895 < baseStart_609895 := by decide
  rcases family_descends (prefixWord ++ tailWord_609895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609943 : List Nat := [1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_609943 : Nat := 118140960795 + 609943 * 2 ^ 59
def prefixEnd_609943 : Nat := 4983230072969 + 3 ^ 40 * 609943 * 2
def baseEnd_609943 : Nat := 92798201731974023379979

theorem tailTrace_609943 : CollatzResearch.WordTrace tailWord_609943 prefixEnd_609943 92798201731974023379979 := by
  unfold tailWord_609943
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246448829288155816114483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14830965886192103877409655 22246448829288155816114483)
  ·
    refine ⟨33369673243932233724171725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22246448829288155816114483 33369673243932233724171725)
    ·
      refine ⟨12513627466474587646564397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33369673243932233724171725 12513627466474587646564397)
      ·
        refine ⟨4692610299927970367461649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12513627466474587646564397 4692610299927970367461649)
        ·
          refine ⟨3519457724945977775596237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4692610299927970367461649 3519457724945977775596237)
          ·
            refine ⟨1319796646854741665848589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3519457724945977775596237 1319796646854741665848589)
            ·
              refine ⟨494923742570528124693221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319796646854741665848589 494923742570528124693221)
              ·
                refine ⟨92798201731974023379979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 494923742570528124693221 92798201731974023379979)
                ·
                  rfl

theorem cell20_609943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_609943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609943 prefixEnd_609943 := by exact prefixLift 609943
  have htrace : WordTrace (prefixWord ++ tailWord_609943) baseStart_609943 baseEnd_609943 := by
    simpa [prefixWord, tailWord_609943, baseEnd_609943] using wordTrace_append hprefix tailTrace_609943
  have hstable : (prefixWord ++ tailWord_609943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609943).length < 2 ^ (prefixWord ++ tailWord_609943).sum := by decide
  have hdescent : baseEnd_609943 < baseStart_609943 := by decide
  rcases family_descends (prefixWord ++ tailWord_609943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609953 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 2]
def baseStart_609953 : Nat := 118140960795 + 609953 * 2 ^ 59
def prefixEnd_609953 : Nat := 4983230072969 + 3 ^ 40 * 609953 * 2
def baseEnd_609953 : Nat := 278399169468406479806563

theorem tailTrace_609953 : CollatzResearch.WordTrace tailWord_609953 prefixEnd_609953 278399169468406479806563 := by
  unfold tailWord_609953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246813559251927523978513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14831209039501285015985675 22246813559251927523978513)
  ·
    refine ⟨16685110169438945642983885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22246813559251927523978513 16685110169438945642983885)
    ·
      refine ⟨6256916313539604616118957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16685110169438945642983885 6256916313539604616118957)
      ·
        refine ⟨2346343617577351731044609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6256916313539604616118957 2346343617577351731044609)
        ·
          refine ⟨1759757713183013798283457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346343617577351731044609 1759757713183013798283457)
          ·
            refine ⟨1319818284887260348712593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759757713183013798283457 1319818284887260348712593)
            ·
              refine ⟨989863713665445261534445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319818284887260348712593 989863713665445261534445)
              ·
                refine ⟨371198892624541973075417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989863713665445261534445 371198892624541973075417)
                ·
                  refine ⟨278399169468406479806563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371198892624541973075417 278399169468406479806563)
                  ·
                    rfl

theorem cell20_609953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_609953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609953 prefixEnd_609953 := by exact prefixLift 609953
  have htrace : WordTrace (prefixWord ++ tailWord_609953) baseStart_609953 baseEnd_609953 := by
    simpa [prefixWord, tailWord_609953, baseEnd_609953] using wordTrace_append hprefix tailTrace_609953
  have hstable : (prefixWord ++ tailWord_609953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609953).length < 2 ^ (prefixWord ++ tailWord_609953).sum := by decide
  have hdescent : baseEnd_609953 < baseStart_609953 := by decide
  rcases family_descends (prefixWord ++ tailWord_609953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_609971 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_609971 : Nat := 118140960795 + 609971 * 2 ^ 59
def prefixEnd_609971 : Nat := 4983230072969 + 3 ^ 40 * 609971 * 2
def baseEnd_609971 : Nat := 278407385158878417206489

theorem tailTrace_609971 : CollatzResearch.WordTrace tailWord_609971 prefixEnd_609971 278407385158878417206489 := by
  unfold tailWord_609971
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247470073186716598133767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14831646715457811065422511 22247470073186716598133767)
  ·
    refine ⟨33371205109780074897200651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22247470073186716598133767 33371205109780074897200651)
    ·
      refine ⟨50056807664670112345800977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33371205109780074897200651 50056807664670112345800977)
      ·
        refine ⟨37542605748502584259350733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50056807664670112345800977 37542605748502584259350733)
        ·
          refine ⟨14078477155688469097256525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37542605748502584259350733 14078477155688469097256525)
          ·
            refine ⟨5279428933383175911471197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14078477155688469097256525 5279428933383175911471197)
            ·
              refine ⟨1979785850018690966801699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5279428933383175911471197 1979785850018690966801699)
              ·
                refine ⟨2969678775028036450202549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979785850018690966801699 2969678775028036450202549)
                ·
                  refine ⟨278407385158878417206489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969678775028036450202549 278407385158878417206489)
                  ·
                    rfl

theorem cell20_609971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_609971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_609971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_609971 prefixEnd_609971 := by exact prefixLift 609971
  have htrace : WordTrace (prefixWord ++ tailWord_609971) baseStart_609971 baseEnd_609971 := by
    simpa [prefixWord, tailWord_609971, baseEnd_609971] using wordTrace_append hprefix tailTrace_609971
  have hstable : (prefixWord ++ tailWord_609971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_609971).length < 2 ^ (prefixWord ++ tailWord_609971).sum := by decide
  have hdescent : baseEnd_609971 < baseStart_609971 := by decide
  rcases family_descends (prefixWord ++ tailWord_609971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610009 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_610009 : Nat := 118140960795 + 610009 * 2 ^ 59
def prefixEnd_610009 : Nat := 4983230072969 + 3 ^ 40 * 610009 * 2
def baseEnd_610009 : Nat := 278424729394319173939667

theorem tailTrace_610009 : CollatzResearch.WordTrace tailWord_610009 prefixEnd_610009 278424729394319173939667 := by
  unfold tailWord_610009
  simp only [CollatzResearch.WordTrace]
  refine ⟨22248856047049049088017081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14832570698032699392011387 22248856047049049088017081)
  ·
    refine ⟨16686642035286786816012811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22248856047049049088017081 16686642035286786816012811)
    ·
      refine ⟨25029963052930180224019217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16686642035286786816012811 25029963052930180224019217)
      ·
        refine ⟨18772472289697635168014413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25029963052930180224019217 18772472289697635168014413)
        ·
          refine ⟨7039677108636613188005405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18772472289697635168014413 7039677108636613188005405)
          ·
            refine ⟨2639878915738729945502027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7039677108636613188005405 2639878915738729945502027)
            ·
              refine ⟨3959818373608094918253041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639878915738729945502027 3959818373608094918253041)
              ·
                refine ⟨2969863780206071188689781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3959818373608094918253041 2969863780206071188689781)
                ·
                  refine ⟨278424729394319173939667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969863780206071188689781 278424729394319173939667)
                  ·
                    rfl

theorem cell20_610009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_610009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610009 prefixEnd_610009 := by exact prefixLift 610009
  have htrace : WordTrace (prefixWord ++ tailWord_610009) baseStart_610009 baseEnd_610009 := by
    simpa [prefixWord, tailWord_610009, baseEnd_610009] using wordTrace_append hprefix tailTrace_610009
  have hstable : (prefixWord ++ tailWord_610009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610009).length < 2 ^ (prefixWord ++ tailWord_610009).sum := by decide
  have hdescent : baseEnd_610009 < baseStart_610009 := by decide
  rcases family_descends (prefixWord ++ tailWord_610009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610016 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_610016 : Nat := 118140960795 + 610016 * 2 ^ 59
def prefixEnd_610016 : Nat := 4983230072969 + 3 ^ 40 * 610016 * 2
def baseEnd_610016 : Nat := 278427924385058260706305

theorem tailTrace_610016 : CollatzResearch.WordTrace tailWord_610016 prefixEnd_610016 278427924385058260706305 := by
  unfold tailWord_610016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124555679011844641760951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14832740905349126189014601 11124555679011844641760951)
  ·
    refine ⟨16686833518517766962641427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11124555679011844641760951 16686833518517766962641427)
    ·
      refine ⟨25030250277776650443962141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16686833518517766962641427 25030250277776650443962141)
      ·
        refine ⟨9386343854166243916485803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25030250277776650443962141 9386343854166243916485803)
        ·
          refine ⟨14079515781249365874728705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9386343854166243916485803 14079515781249365874728705)
          ·
            refine ⟨10559636835937024406046529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14079515781249365874728705 10559636835937024406046529)
            ·
              refine ⟨7919727626952768304534897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10559636835937024406046529 7919727626952768304534897)
              ·
                refine ⟨5939795720214576228401173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7919727626952768304534897 5939795720214576228401173)
                ·
                  refine ⟨278427924385058260706305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5939795720214576228401173 278427924385058260706305)
                  ·
                    rfl

theorem cell20_610016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_610016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610016 prefixEnd_610016 := by exact prefixLift 610016
  have htrace : WordTrace (prefixWord ++ tailWord_610016) baseStart_610016 baseEnd_610016 := by
    simpa [prefixWord, tailWord_610016, baseEnd_610016] using wordTrace_append hprefix tailTrace_610016
  have hstable : (prefixWord ++ tailWord_610016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610016).length < 2 ^ (prefixWord ++ tailWord_610016).sum := by decide
  have hdescent : baseEnd_610016 < baseStart_610016 := by decide
  rcases family_descends (prefixWord ++ tailWord_610016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610019 : List Nat := [1, 1, 1, 7, 2, 2, 6]
def baseStart_610019 : Nat := 118140960795 + 610019 * 2 ^ 59
def prefixEnd_610019 : Nat := 4983230072969 + 3 ^ 40 * 610019 * 2
def baseEnd_610019 : Nat := 30936588185200398178477

theorem tailTrace_610019 : CollatzResearch.WordTrace tailWord_610019 prefixEnd_610019 30936588185200398178477 := by
  unfold tailWord_610019
  simp only [CollatzResearch.WordTrace]
  refine ⟨22249220777012820795881111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14832813851341880530587407 22249220777012820795881111)
  ·
    refine ⟨33373831165519231193821667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22249220777012820795881111 33373831165519231193821667)
    ·
      refine ⟨50060746748278846790732501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33373831165519231193821667 50060746748278846790732501)
      ·
        refine ⟨1173298751912785471657793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 50060746748278846790732501 1173298751912785471657793)
        ·
          refine ⟨879974063934589103743345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173298751912785471657793 879974063934589103743345)
          ·
            refine ⟨659980547950941827807509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879974063934589103743345 659980547950941827807509)
            ·
              refine ⟨30936588185200398178477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 659980547950941827807509 30936588185200398178477)
              ·
                rfl

theorem cell20_610019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_610019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610019 prefixEnd_610019 := by exact prefixLift 610019
  have htrace : WordTrace (prefixWord ++ tailWord_610019) baseStart_610019 baseEnd_610019 := by
    simpa [prefixWord, tailWord_610019, baseEnd_610019] using wordTrace_append hprefix tailTrace_610019
  have hstable : (prefixWord ++ tailWord_610019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610019).length < 2 ^ (prefixWord ++ tailWord_610019).sum := by decide
  have hdescent : baseEnd_610019 < baseStart_610019 := by decide
  rcases family_descends (prefixWord ++ tailWord_610019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610033 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_610033 : Nat := 118140960795 + 610033 * 2 ^ 59
def prefixEnd_610033 : Nat := 4983230072969 + 3 ^ 40 * 610033 * 2
def baseEnd_610033 : Nat := 278435683648281757139569

theorem tailTrace_610033 : CollatzResearch.WordTrace tailWord_610033 prefixEnd_610033 278435683648281757139569 := by
  unfold tailWord_610033
  simp only [CollatzResearch.WordTrace]
  refine ⟨22249731398962101186890753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14833154265974734124593835 22249731398962101186890753)
  ·
    refine ⟨16687298549221575890168065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22249731398962101186890753 16687298549221575890168065)
    ·
      refine ⟨12515473911916181917626049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16687298549221575890168065 12515473911916181917626049)
      ·
        refine ⟨9386605433937136438219537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12515473911916181917626049 9386605433937136438219537)
        ·
          refine ⟨7039954075452852328664653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9386605433937136438219537 7039954075452852328664653)
          ·
            refine ⟨2639982778294819623249245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7039954075452852328664653 2639982778294819623249245)
            ·
              refine ⟨989993541860557358718467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2639982778294819623249245 989993541860557358718467)
              ·
                refine ⟨1484990312790836038077701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989993541860557358718467 1484990312790836038077701)
                ·
                  refine ⟨278435683648281757139569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484990312790836038077701 278435683648281757139569)
                  ·
                    rfl

theorem cell20_610033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_610033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610033 prefixEnd_610033 := by exact prefixLift 610033
  have htrace : WordTrace (prefixWord ++ tailWord_610033) baseStart_610033 baseEnd_610033 := by
    simpa [prefixWord, tailWord_610033, baseEnd_610033] using wordTrace_append hprefix tailTrace_610033
  have hstable : (prefixWord ++ tailWord_610033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610033).length < 2 ^ (prefixWord ++ tailWord_610033).sum := by decide
  have hdescent : baseEnd_610033 < baseStart_610033 := by decide
  rcases family_descends (prefixWord ++ tailWord_610033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610036 : List Nat := [2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_610036 : Nat := 118140960795 + 610036 * 2 ^ 59
def prefixEnd_610036 : Nat := 4983230072969 + 3 ^ 40 * 610036 * 2
def baseEnd_610036 : Nat := 92812350976675693346519

theorem tailTrace_610036 : CollatzResearch.WordTrace tailWord_610036 prefixEnd_610036 92812350976675693346519 := by
  unfold tailWord_610036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124920408975616349624981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14833227211967488466166641 11124920408975616349624981)
  ·
    refine ⟨521480644170732016388671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11124920408975616349624981 521480644170732016388671)
    ·
      refine ⟨782220966256098024583007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521480644170732016388671 782220966256098024583007)
      ·
        refine ⟨1173331449384147036874511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782220966256098024583007 1173331449384147036874511)
        ·
          refine ⟨1759997174076220555311767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173331449384147036874511 1759997174076220555311767)
          ·
            refine ⟨2639995761114330832967651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759997174076220555311767 2639995761114330832967651)
            ·
              refine ⟨3959993641671496249451477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639995761114330832967651 3959993641671496249451477)
              ·
                refine ⟨92812350976675693346519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3959993641671496249451477 92812350976675693346519)
                ·
                  rfl

theorem cell20_610036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_610036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610036 prefixEnd_610036 := by exact prefixLift 610036
  have htrace : WordTrace (prefixWord ++ tailWord_610036) baseStart_610036 baseEnd_610036 := by
    simpa [prefixWord, tailWord_610036, baseEnd_610036] using wordTrace_append hprefix tailTrace_610036
  have hstable : (prefixWord ++ tailWord_610036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610036).length < 2 ^ (prefixWord ++ tailWord_610036).sum := by decide
  have hdescent : baseEnd_610036 < baseStart_610036 := by decide
  rcases family_descends (prefixWord ++ tailWord_610036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610084 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_610084 : Nat := 118140960795 + 610084 * 2 ^ 59
def prefixEnd_610084 : Nat := 4983230072969 + 3 ^ 40 * 610084 * 2
def baseEnd_610084 : Nat := 278458961437952246439361

theorem tailTrace_610084 : CollatzResearch.WordTrace tailWord_610084 prefixEnd_610084 278458961437952246439361 := by
  unfold tailWord_610084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125795760888668448498653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14834394347851557931331537 11125795760888668448498653)
  ·
    refine ⟨4172173410333250668186995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11125795760888668448498653 4172173410333250668186995)
    ·
      refine ⟨6258260115499876002280493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172173410333250668186995 6258260115499876002280493)
      ·
        refine ⟨2346847543312453500855185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6258260115499876002280493 2346847543312453500855185)
        ·
          refine ⟨1760135657484340125641389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346847543312453500855185 1760135657484340125641389)
          ·
            refine ⟨660050871556627547115521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1760135657484340125641389 660050871556627547115521)
            ·
              refine ⟨495038153667470660336641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660050871556627547115521 495038153667470660336641)
              ·
                refine ⟨371278615250602995252481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495038153667470660336641 371278615250602995252481)
                ·
                  refine ⟨278458961437952246439361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371278615250602995252481 278458961437952246439361)
                  ·
                    rfl

theorem cell20_610084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_610084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610084 prefixEnd_610084 := by exact prefixLift 610084
  have htrace : WordTrace (prefixWord ++ tailWord_610084) baseStart_610084 baseEnd_610084 := by
    simpa [prefixWord, tailWord_610084, baseEnd_610084] using wordTrace_append hprefix tailTrace_610084
  have hstable : (prefixWord ++ tailWord_610084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610084).length < 2 ^ (prefixWord ++ tailWord_610084).sum := by decide
  have hdescent : baseEnd_610084 < baseStart_610084 := by decide
  rcases family_descends (prefixWord ++ tailWord_610084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610109 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_610109 : Nat := 118140960795 + 610109 * 2 ^ 59
def prefixEnd_610109 : Nat := 4983230072969 + 3 ^ 40 * 610109 * 2
def baseEnd_610109 : Nat := 278470372119163270605925

theorem tailTrace_610109 : CollatzResearch.WordTrace tailWord_610109 prefixEnd_610109 278470372119163270605925 := by
  unfold tailWord_610109
  simp only [CollatzResearch.WordTrace]
  refine ⟨22252503346686766166657381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14835002231124510777771587 22252503346686766166657381)
  ·
    refine ⟨4172344377503768656248259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22252503346686766166657381 4172344377503768656248259)
    ·
      refine ⟨6258516566255652984372389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172344377503768656248259 6258516566255652984372389)
      ·
        refine ⟨1173471856172934934569823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6258516566255652984372389 1173471856172934934569823)
        ·
          refine ⟨1760207784259402401854735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173471856172934934569823 1760207784259402401854735)
          ·
            refine ⟨2640311676389103602782103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760207784259402401854735 2640311676389103602782103)
            ·
              refine ⟨3960467514583655404173155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640311676389103602782103 3960467514583655404173155)
              ·
                refine ⟨5940701271875483106259733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960467514583655404173155 5940701271875483106259733)
                ·
                  refine ⟨278470372119163270605925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5940701271875483106259733 278470372119163270605925)
                  ·
                    rfl

theorem cell20_610109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_610109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610109 prefixEnd_610109 := by exact prefixLift 610109
  have htrace : WordTrace (prefixWord ++ tailWord_610109) baseStart_610109 baseEnd_610109 := by
    simpa [prefixWord, tailWord_610109, baseEnd_610109] using wordTrace_append hprefix tailTrace_610109
  have hstable : (prefixWord ++ tailWord_610109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610109).length < 2 ^ (prefixWord ++ tailWord_610109).sum := by decide
  have hdescent : baseEnd_610109 < baseStart_610109 := by decide
  rcases family_descends (prefixWord ++ tailWord_610109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610137 : List Nat := [1, 2, 1, 2, 2, 3, 9]
def baseStart_610137 : Nat := 118140960795 + 610137 * 2 ^ 59
def prefixEnd_610137 : Nat := 4983230072969 + 3 ^ 40 * 610137 * 2
def baseEnd_610137 : Nat := 30942572453568846408053

theorem tailTrace_610137 : CollatzResearch.WordTrace tailWord_610137 prefixEnd_610137 30942572453568846408053 := by
  unfold tailWord_610137
  simp only [CollatzResearch.WordTrace]
  refine ⟨22253524590585326948676665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14835683060390217965784443 22253524590585326948676665)
  ·
    refine ⟨16690143442938995211507499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22253524590585326948676665 16690143442938995211507499)
    ·
      refine ⟨25035215164408492817261249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16690143442938995211507499 25035215164408492817261249)
      ·
        refine ⟨18776411373306369612945937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25035215164408492817261249 18776411373306369612945937)
        ·
          refine ⟨14082308529979777209709453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18776411373306369612945937 14082308529979777209709453)
          ·
            refine ⟨5280865698742416453641045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14082308529979777209709453 5280865698742416453641045)
            ·
              refine ⟨30942572453568846408053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5280865698742416453641045 30942572453568846408053)
              ·
                rfl

theorem cell20_610137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_610137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610137 prefixEnd_610137 := by exact prefixLift 610137
  have htrace : WordTrace (prefixWord ++ tailWord_610137) baseStart_610137 baseEnd_610137 := by
    simpa [prefixWord, tailWord_610137, baseEnd_610137] using wordTrace_append hprefix tailTrace_610137
  have hstable : (prefixWord ++ tailWord_610137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610137).length < 2 ^ (prefixWord ++ tailWord_610137).sum := by decide
  have hdescent : baseEnd_610137 < baseStart_610137 := by decide
  rcases family_descends (prefixWord ++ tailWord_610137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610177 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 2]
def baseStart_610177 : Nat := 118140960795 + 610177 * 2 ^ 59
def prefixEnd_610177 : Nat := 4983230072969 + 3 ^ 40 * 610177 * 2
def baseEnd_610177 : Nat := 278501409172057256338981

theorem tailTrace_610177 : CollatzResearch.WordTrace tailWord_610177 prefixEnd_610177 278501409172057256338981 := by
  unfold tailWord_610177
  simp only [CollatzResearch.WordTrace]
  refine ⟨22254983510440413780132785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14836655673626942520088523 22254983510440413780132785)
  ·
    refine ⟨16691237632830310335099589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22254983510440413780132785 16691237632830310335099589)
    ·
      refine ⟨3129607056155683187831173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16691237632830310335099589 3129607056155683187831173)
      ·
        refine ⟨586801323029190597718345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3129607056155683187831173 586801323029190597718345)
        ·
          refine ⟨440100992271892948288759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586801323029190597718345 440100992271892948288759)
          ·
            refine ⟨660151488407839422433139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440100992271892948288759 660151488407839422433139)
            ·
              refine ⟨990227232611759133649709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660151488407839422433139 990227232611759133649709)
              ·
                refine ⟨371335212229409675118641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990227232611759133649709 371335212229409675118641)
                ·
                  refine ⟨278501409172057256338981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371335212229409675118641 278501409172057256338981)
                  ·
                    rfl

theorem cell20_610177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_610177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610177 prefixEnd_610177 := by exact prefixLift 610177
  have htrace : WordTrace (prefixWord ++ tailWord_610177) baseStart_610177 baseEnd_610177 := by
    simpa [prefixWord, tailWord_610177, baseEnd_610177] using wordTrace_append hprefix tailTrace_610177
  have hstable : (prefixWord ++ tailWord_610177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610177).length < 2 ^ (prefixWord ++ tailWord_610177).sum := by decide
  have hdescent : baseEnd_610177 < baseStart_610177 := by decide
  rcases family_descends (prefixWord ++ tailWord_610177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610199 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_610199 : Nat := 118140960795 + 610199 * 2 ^ 59
def prefixEnd_610199 : Nat := 4983230072969 + 3 ^ 40 * 610199 * 2
def baseEnd_610199 : Nat := 278511450571522957605557

theorem tailTrace_610199 : CollatzResearch.WordTrace tailWord_610199 prefixEnd_610199 278511450571522957605557 := by
  unfold tailWord_610199
  simp only [CollatzResearch.WordTrace]
  refine ⟨22255785916360711537433651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14837190610907141024955767 22255785916360711537433651)
  ·
    refine ⟨33383678874541067306150477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22255785916360711537433651 33383678874541067306150477)
    ·
      refine ⟨12518879577952900239806429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33383678874541067306150477 12518879577952900239806429)
      ·
        refine ⟨4694579841732337589927411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12518879577952900239806429 4694579841732337589927411)
        ·
          refine ⟨7041869762598506384891117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694579841732337589927411 7041869762598506384891117)
          ·
            refine ⟨2640701160974439894334169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7041869762598506384891117 2640701160974439894334169)
            ·
              refine ⟨1980525870730829920750627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640701160974439894334169 1980525870730829920750627)
              ·
                refine ⟨2970788806096244881125941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980525870730829920750627 2970788806096244881125941)
                ·
                  refine ⟨278511450571522957605557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2970788806096244881125941 278511450571522957605557)
                  ·
                    rfl

theorem cell20_610199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_610199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610199 prefixEnd_610199 := by exact prefixLift 610199
  have htrace : WordTrace (prefixWord ++ tailWord_610199) baseStart_610199 baseEnd_610199 := by
    simpa [prefixWord, tailWord_610199, baseEnd_610199] using wordTrace_append hprefix tailTrace_610199
  have hstable : (prefixWord ++ tailWord_610199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610199).length < 2 ^ (prefixWord ++ tailWord_610199).sum := by decide
  have hdescent : baseEnd_610199 < baseStart_610199 := by decide
  rcases family_descends (prefixWord ++ tailWord_610199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610202 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_610202 : Nat := 118140960795 + 610202 * 2 ^ 59
def prefixEnd_610202 : Nat := 4983230072969 + 3 ^ 40 * 610202 * 2
def baseEnd_610202 : Nat := 278512819853268280505545

theorem tailTrace_610202 : CollatzResearch.WordTrace tailWord_610202 prefixEnd_610202 278512819853268280505545 := by
  unfold tailWord_610202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563973833837460762448215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14837263556899895366528573 5563973833837460762448215)
  ·
    refine ⟨8345960750756191143672323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563973833837460762448215 8345960750756191143672323)
    ·
      refine ⟨12518941126134286715508485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8345960750756191143672323 12518941126134286715508485)
      ·
        refine ⟨2347301461150178759157841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12518941126134286715508485 2347301461150178759157841)
        ·
          refine ⟨1760476095862634069368381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347301461150178759157841 1760476095862634069368381)
          ·
            refine ⟨660178535948487776013143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1760476095862634069368381 660178535948487776013143)
            ·
              refine ⟨990267803922731664019715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660178535948487776013143 990267803922731664019715)
              ·
                refine ⟨1485401705884097496029573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990267803922731664019715 1485401705884097496029573)
                ·
                  refine ⟨278512819853268280505545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1485401705884097496029573 278512819853268280505545)
                  ·
                    rfl

theorem cell20_610202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_610202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610202 prefixEnd_610202 := by exact prefixLift 610202
  have htrace : WordTrace (prefixWord ++ tailWord_610202) baseStart_610202 baseEnd_610202 := by
    simpa [prefixWord, tailWord_610202, baseEnd_610202] using wordTrace_append hprefix tailTrace_610202
  have hstable : (prefixWord ++ tailWord_610202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610202).length < 2 ^ (prefixWord ++ tailWord_610202).sum := by decide
  have hdescent : baseEnd_610202 < baseStart_610202 := by decide
  rcases family_descends (prefixWord ++ tailWord_610202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610209 : List Nat := [1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_610209 : Nat := 118140960795 + 610209 * 2 ^ 59
def prefixEnd_610209 : Nat := 4983230072969 + 3 ^ 40 * 610209 * 2
def baseEnd_610209 : Nat := 92838671614669122424061

theorem tailTrace_610209 : CollatzResearch.WordTrace tailWord_610209 prefixEnd_610209 92838671614669122424061 := by
  unfold tailWord_610209
  simp only [CollatzResearch.WordTrace]
  refine ⟨22256150646324483245297681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14837433764216322163531787 22256150646324483245297681)
  ·
    refine ⟨16692112984743362433973261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22256150646324483245297681 16692112984743362433973261)
    ·
      refine ⟨6259542369278760912739973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16692112984743362433973261 6259542369278760912739973)
      ·
        refine ⟨1173664194239767671138745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6259542369278760912739973 1173664194239767671138745)
        ·
          refine ⟨880248145679825753354059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173664194239767671138745 880248145679825753354059)
          ·
            refine ⟨1320372218519738630031089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880248145679825753354059 1320372218519738630031089)
            ·
              refine ⟨990279163889803972523317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320372218519738630031089 990279163889803972523317)
              ·
                refine ⟨92838671614669122424061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 990279163889803972523317 92838671614669122424061)
                ·
                  rfl

theorem cell20_610209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_610209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610209 prefixEnd_610209 := by exact prefixLift 610209
  have htrace : WordTrace (prefixWord ++ tailWord_610209) baseStart_610209 baseEnd_610209 := by
    simpa [prefixWord, tailWord_610209, baseEnd_610209] using wordTrace_append hprefix tailTrace_610209
  have hstable : (prefixWord ++ tailWord_610209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610209).length < 2 ^ (prefixWord ++ tailWord_610209).sum := by decide
  have hdescent : baseEnd_610209 < baseStart_610209 := by decide
  rcases family_descends (prefixWord ++ tailWord_610209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610254 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_610254 : Nat := 118140960795 + 610254 * 2 ^ 59
def prefixEnd_610254 : Nat := 4983230072969 + 3 ^ 40 * 610254 * 2
def baseEnd_610254 : Nat := 278536554070187210771999

theorem tailTrace_610254 : CollatzResearch.WordTrace tailWord_610254 prefixEnd_610254 278536554070187210771999 := by
  unfold tailWord_610254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782223991395181991335727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14838527954107637287123877 2782223991395181991335727)
  ·
    refine ⟨4173335987092772987003591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782223991395181991335727 4173335987092772987003591)
    ·
      refine ⟨6260003980639159480505387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173335987092772987003591 6260003980639159480505387)
      ·
        refine ⟨9390005970958739220758081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260003980639159480505387 9390005970958739220758081)
        ·
          refine ⟨7042504478219054415568561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9390005970958739220758081 7042504478219054415568561)
          ·
            refine ⟨5281878358664290811676421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042504478219054415568561 5281878358664290811676421)
            ·
              refine ⟨990352192249554527189329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5281878358664290811676421 990352192249554527189329)
              ·
                refine ⟨742764144187165895391997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990352192249554527189329 742764144187165895391997)
                ·
                  refine ⟨278536554070187210771999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742764144187165895391997 278536554070187210771999)
                  ·
                    rfl

theorem cell20_610254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_610254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610254 prefixEnd_610254 := by exact prefixLift 610254
  have htrace : WordTrace (prefixWord ++ tailWord_610254) baseStart_610254 baseEnd_610254 := by
    simpa [prefixWord, tailWord_610254, baseEnd_610254] using wordTrace_append hprefix tailTrace_610254
  have hstable : (prefixWord ++ tailWord_610254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610254).length < 2 ^ (prefixWord ++ tailWord_610254).sum := by decide
  have hdescent : baseEnd_610254 < baseStart_610254 := by decide
  rcases family_descends (prefixWord ++ tailWord_610254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610299 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 2]
def baseStart_610299 : Nat := 118140960795 + 610299 * 2 ^ 59
def prefixEnd_610299 : Nat := 4983230072969 + 3 ^ 40 * 610299 * 2
def baseEnd_610299 : Nat := 278557093296367054271815

theorem tailTrace_610299 : CollatzResearch.WordTrace tailWord_610299 prefixEnd_610299 278557093296367054271815 := by
  unfold tailWord_610299
  simp only [CollatzResearch.WordTrace]
  refine ⟨22259433215998428616073951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14839622143998952410715967 22259433215998428616073951)
  ·
    refine ⟨33389149823997642924110927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22259433215998428616073951 33389149823997642924110927)
    ·
      refine ⟨50083724735996464386166391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33389149823997642924110927 50083724735996464386166391)
      ·
        refine ⟨75125587103994696579249587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50083724735996464386166391 75125587103994696579249587)
        ·
          refine ⟨112688380655992044868874381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75125587103994696579249587 112688380655992044868874381)
          ·
            refine ⟨42258142745997016825827893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112688380655992044868874381 42258142745997016825827893)
            ·
              refine ⟨3961700882437220327421365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42258142745997016825827893 3961700882437220327421365)
              ·
                refine ⟨371409457728489405695753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3961700882437220327421365 371409457728489405695753)
                ·
                  refine ⟨278557093296367054271815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371409457728489405695753 278557093296367054271815)
                  ·
                    rfl

theorem cell20_610299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 2].length) (baseStart_610299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610299 prefixEnd_610299 := by exact prefixLift 610299
  have htrace : WordTrace (prefixWord ++ tailWord_610299) baseStart_610299 baseEnd_610299 := by
    simpa [prefixWord, tailWord_610299, baseEnd_610299] using wordTrace_append hprefix tailTrace_610299
  have hstable : (prefixWord ++ tailWord_610299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610299).length < 2 ^ (prefixWord ++ tailWord_610299).sum := by decide
  have hdescent : baseEnd_610299 < baseStart_610299 := by decide
  rcases family_descends (prefixWord ++ tailWord_610299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610340 : List Nat := [2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_610340 : Nat := 118140960795 + 610340 * 2 ^ 59
def prefixEnd_610340 : Nat := 4983230072969 + 3 ^ 40 * 610340 * 2
def baseEnd_610340 : Nat := 92858602271184377968327

theorem tailTrace_610340 : CollatzResearch.WordTrace tailWord_610340 prefixEnd_610340 92858602271184377968327 := by
  unfold tailWord_610340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130464304424946309158237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14840619072566595078877649 11130464304424946309158237)
  ·
    refine ⟨4173924114159354865934339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11130464304424946309158237 4173924114159354865934339)
    ·
      refine ⟨6260886171239032298901509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173924114159354865934339 6260886171239032298901509)
      ·
        refine ⟨1173916157107318556044033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6260886171239032298901509 1173916157107318556044033)
        ·
          refine ⟨880437117830488917033025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173916157107318556044033 880437117830488917033025)
          ·
            refine ⟨660327838372866687774769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880437117830488917033025 660327838372866687774769)
            ·
              refine ⟨495245878779650015831077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660327838372866687774769 495245878779650015831077)
              ·
                refine ⟨92858602271184377968327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495245878779650015831077 92858602271184377968327)
                ·
                  rfl

theorem cell20_610340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_610340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610340 prefixEnd_610340 := by exact prefixLift 610340
  have htrace : WordTrace (prefixWord ++ tailWord_610340) baseStart_610340 baseEnd_610340 := by
    simpa [prefixWord, tailWord_610340, baseEnd_610340] using wordTrace_append hprefix tailTrace_610340
  have hstable : (prefixWord ++ tailWord_610340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610340).length < 2 ^ (prefixWord ++ tailWord_610340).sum := by decide
  have hdescent : baseEnd_610340 < baseStart_610340 := by decide
  rcases family_descends (prefixWord ++ tailWord_610340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610354 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_610354 : Nat := 118140960795 + 610354 * 2 ^ 59
def prefixEnd_610354 : Nat := 4983230072969 + 3 ^ 40 * 610354 * 2
def baseEnd_610354 : Nat := 278582196795031307438257

theorem tailTrace_610354 : CollatzResearch.WordTrace tailWord_610354 prefixEnd_610354 278582196795031307438257 := by
  unfold tailWord_610354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565359807699793252331529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14840959487199448672884077 5565359807699793252331529)
  ·
    refine ⟨4174019855774844939248647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5565359807699793252331529 4174019855774844939248647)
    ·
      refine ⟨6261029783662267408872971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4174019855774844939248647 6261029783662267408872971)
      ·
        refine ⟨9391544675493401113309457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261029783662267408872971 9391544675493401113309457)
        ·
          refine ⟨7043658506620050834982093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9391544675493401113309457 7043658506620050834982093)
          ·
            refine ⟨2641371939982519063118285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7043658506620050834982093 2641371939982519063118285)
            ·
              refine ⟨990514477493444648669357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2641371939982519063118285 990514477493444648669357)
              ·
                refine ⟨371442929060041743251009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990514477493444648669357 371442929060041743251009)
                ·
                  refine ⟨278582196795031307438257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371442929060041743251009 278582196795031307438257)
                  ·
                    rfl

theorem cell20_610354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_610354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610354 prefixEnd_610354 := by exact prefixLift 610354
  have htrace : WordTrace (prefixWord ++ tailWord_610354) baseStart_610354 baseEnd_610354 := by
    simpa [prefixWord, tailWord_610354, baseEnd_610354] using wordTrace_append hprefix tailTrace_610354
  have hstable : (prefixWord ++ tailWord_610354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610354).length < 2 ^ (prefixWord ++ tailWord_610354).sum := by decide
  have hdescent : baseEnd_610354 < baseStart_610354 := by decide
  rcases family_descends (prefixWord ++ tailWord_610354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610361 : List Nat := [1, 2, 1, 5, 4, 1, 6]
def baseStart_610361 : Nat := 118140960795 + 610361 * 2 ^ 59
def prefixEnd_610361 : Nat := 4983230072969 + 3 ^ 40 * 610361 * 2
def baseEnd_610361 : Nat := 30953932420641154911655

theorem tailTrace_610361 : CollatzResearch.WordTrace tailWord_610361 prefixEnd_610361 30953932420641154911655 := by
  unfold tailWord_610361
  simp only [CollatzResearch.WordTrace]
  refine ⟨22261694541773813204830937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14841129694515875469887291 22261694541773813204830937)
  ·
    refine ⟨16696270906330359903623203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22261694541773813204830937 16696270906330359903623203)
    ·
      refine ⟨25044406359495539855434805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16696270906330359903623203 25044406359495539855434805)
      ·
        refine ⟨2347913096202706861447013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25044406359495539855434805 2347913096202706861447013)
        ·
          refine ⟨440233705538007536521315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2347913096202706861447013 440233705538007536521315)
          ·
            refine ⟨660350558307011304781973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440233705538007536521315 660350558307011304781973)
            ·
              refine ⟨30953932420641154911655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 660350558307011304781973 30953932420641154911655)
              ·
                rfl

theorem cell20_610361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 6].length) (baseStart_610361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610361 prefixEnd_610361 := by exact prefixLift 610361
  have htrace : WordTrace (prefixWord ++ tailWord_610361) baseStart_610361 baseEnd_610361 := by
    simpa [prefixWord, tailWord_610361, baseEnd_610361] using wordTrace_append hprefix tailTrace_610361
  have hstable : (prefixWord ++ tailWord_610361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610361).length < 2 ^ (prefixWord ++ tailWord_610361).sum := by decide
  have hdescent : baseEnd_610361 < baseStart_610361 := by decide
  rcases family_descends (prefixWord ++ tailWord_610361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610382 : List Nat := [4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_610382 : Nat := 118140960795 + 610382 * 2 ^ 59
def prefixEnd_610382 : Nat := 4983230072969 + 3 ^ 40 * 610382 * 2
def baseEnd_610382 : Nat := 92864992252662551501603

theorem tailTrace_610382 : CollatzResearch.WordTrace tailWord_610382 prefixEnd_610382 92864992252662551501603 := by
  unfold tailWord_610382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782807559337216723918175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14841640316465155860896933 2782807559337216723918175)
  ·
    refine ⟨4174211339005825085877263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782807559337216723918175 4174211339005825085877263)
    ·
      refine ⟨6261317008508737628815895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4174211339005825085877263 6261317008508737628815895)
      ·
        refine ⟨9391975512763106443223843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261317008508737628815895 9391975512763106443223843)
        ·
          refine ⟨14087963269144659664835765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9391975512763106443223843 14087963269144659664835765)
          ·
            refine ⟨1320746556482311843578353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14087963269144659664835765 1320746556482311843578353)
            ·
              refine ⟨990559917361733882683765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320746556482311843578353 990559917361733882683765)
              ·
                refine ⟨92864992252662551501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 990559917361733882683765 92864992252662551501603)
                ·
                  rfl

theorem cell20_610382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_610382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610382 prefixEnd_610382 := by exact prefixLift 610382
  have htrace : WordTrace (prefixWord ++ tailWord_610382) baseStart_610382 baseEnd_610382 := by
    simpa [prefixWord, tailWord_610382, baseEnd_610382] using wordTrace_append hprefix tailTrace_610382
  have hstable : (prefixWord ++ tailWord_610382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610382).length < 2 ^ (prefixWord ++ tailWord_610382).sum := by decide
  have hdescent : baseEnd_610382 < baseStart_610382 := by decide
  rcases family_descends (prefixWord ++ tailWord_610382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610403 : List Nat := [1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_610403 : Nat := 118140960795 + 610403 * 2 ^ 59
def prefixEnd_610403 : Nat := 4983230072969 + 3 ^ 40 * 610403 * 2
def baseEnd_610403 : Nat := 92868187243401638268241

theorem tailTrace_610403 : CollatzResearch.WordTrace tailWord_610403 prefixEnd_610403 92868187243401638268241 := by
  unfold tailWord_610403
  simp only [CollatzResearch.WordTrace]
  refine ⟨22263226407621654377859863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14842150938414436251906575 22263226407621654377859863)
  ·
    refine ⟨33394839611432481566789795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22263226407621654377859863 33394839611432481566789795)
    ·
      refine ⟨50092259417148722350184693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33394839611432481566789795 50092259417148722350184693)
      ·
        refine ⟨4696149320357692720329815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50092259417148722350184693 4696149320357692720329815)
        ·
          refine ⟨7044223980536539080494723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4696149320357692720329815 7044223980536539080494723)
          ·
            refine ⟨10566335970804808620742085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7044223980536539080494723 10566335970804808620742085)
            ·
              refine ⟨1981187994525901616389141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10566335970804808620742085 1981187994525901616389141)
              ·
                refine ⟨92868187243401638268241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1981187994525901616389141 92868187243401638268241)
                ·
                  rfl

theorem cell20_610403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_610403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610403 prefixEnd_610403 := by exact prefixLift 610403
  have htrace : WordTrace (prefixWord ++ tailWord_610403) baseStart_610403 baseEnd_610403 := by
    simpa [prefixWord, tailWord_610403, baseEnd_610403] using wordTrace_append hprefix tailTrace_610403
  have hstable : (prefixWord ++ tailWord_610403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610403).length < 2 ^ (prefixWord ++ tailWord_610403).sum := by decide
  have hdescent : baseEnd_610403 < baseStart_610403 := by decide
  rcases family_descends (prefixWord ++ tailWord_610403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610489 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 2]
def baseStart_610489 : Nat := 118140960795 + 610489 * 2 ^ 59
def prefixEnd_610489 : Nat := 4983230072969 + 3 ^ 40 * 610489 * 2
def baseEnd_610489 : Nat := 278643814473570837937705

theorem tailTrace_610489 : CollatzResearch.WordTrace tailWord_610489 prefixEnd_610489 278643814473570837937705 := by
  unfold tailWord_610489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266363085310091065490521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14844242056873394043660347 22266363085310091065490521)
  ·
    refine ⟨16699772313982568299117891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22266363085310091065490521 16699772313982568299117891)
    ·
      refine ⟨25049658470973852448676837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16699772313982568299117891 25049658470973852448676837)
      ·
        refine ⟨4696810963307597334126907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25049658470973852448676837 4696810963307597334126907)
        ·
          refine ⟨7045216444961396001190361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4696810963307597334126907 7045216444961396001190361)
          ·
            refine ⟨5283912333721047000892771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7045216444961396001190361 5283912333721047000892771)
            ·
              refine ⟨7925868500581570501339157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283912333721047000892771 7925868500581570501339157)
              ·
                refine ⟨371525085964761117250273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7925868500581570501339157 371525085964761117250273)
                ·
                  refine ⟨278643814473570837937705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371525085964761117250273 278643814473570837937705)
                  ·
                    rfl

theorem cell20_610489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_610489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610489 prefixEnd_610489 := by exact prefixLift 610489
  have htrace : WordTrace (prefixWord ++ tailWord_610489) baseStart_610489 baseEnd_610489 := by
    simpa [prefixWord, tailWord_610489, baseEnd_610489] using wordTrace_append hprefix tailTrace_610489
  have hstable : (prefixWord ++ tailWord_610489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610489).length < 2 ^ (prefixWord ++ tailWord_610489).sum := by decide
  have hdescent : baseEnd_610489 < baseStart_610489 := by decide
  rcases family_descends (prefixWord ++ tailWord_610489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610558 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_610558 : Nat := 118140960795 + 610558 * 2 ^ 59
def prefixEnd_610558 : Nat := 4983230072969 + 3 ^ 40 * 610558 * 2
def baseEnd_610558 : Nat := 278675307953713264637423

theorem tailTrace_610558 : CollatzResearch.WordTrace tailWord_610558 prefixEnd_610558 278675307953713264637423 := by
  unfold tailWord_610558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783609965257514481219041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14845919814706743899834885 2783609965257514481219041)
  ·
    refine ⟨2087707473943135860914281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2783609965257514481219041 2087707473943135860914281)
    ·
      refine ⟨1565780605457351895685711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2087707473943135860914281 1565780605457351895685711)
      ·
        refine ⟨2348670908186027843528567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565780605457351895685711 2348670908186027843528567)
        ·
          refine ⟨3523006362279041765292851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348670908186027843528567 3523006362279041765292851)
          ·
            refine ⟨5284509543418562647939277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523006362279041765292851 5284509543418562647939277)
            ·
              refine ⟨1981691078781960992977229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5284509543418562647939277 1981691078781960992977229)
              ·
                refine ⟨743134154543235372366461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1981691078781960992977229 743134154543235372366461)
                ·
                  refine ⟨278675307953713264637423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743134154543235372366461 278675307953713264637423)
                  ·
                    rfl

theorem cell20_610558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_610558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610558 prefixEnd_610558 := by exact prefixLift 610558
  have htrace : WordTrace (prefixWord ++ tailWord_610558) baseStart_610558 baseEnd_610558 := by
    simpa [prefixWord, tailWord_610558, baseEnd_610558] using wordTrace_append hprefix tailTrace_610558
  have hstable : (prefixWord ++ tailWord_610558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610558).length < 2 ^ (prefixWord ++ tailWord_610558).sum := by decide
  have hdescent : baseEnd_610558 < baseStart_610558 := by decide
  rcases family_descends (prefixWord ++ tailWord_610558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610596 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_610596 : Nat := 118140960795 + 610596 * 2 ^ 59
def prefixEnd_610596 : Nat := 4983230072969 + 3 ^ 40 * 610596 * 2
def baseEnd_610596 : Nat := 278692652189154021370601

theorem tailTrace_610596 : CollatzResearch.WordTrace tailWord_610596 prefixEnd_610596 278692652189154021370601 := by
  unfold tailWord_610596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11135132847961224169817821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14846843797281632226423761 11135132847961224169817821)
  ·
    refine ⟨4175674817985459063681683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11135132847961224169817821 4175674817985459063681683)
    ·
      refine ⟨6263512226978188595522525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175674817985459063681683 6263512226978188595522525)
      ·
        refine ⟨2348817085116820723320947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6263512226978188595522525 2348817085116820723320947)
        ·
          refine ⟨3523225627675231084981421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348817085116820723320947 3523225627675231084981421)
          ·
            refine ⟨1321209610378211656868033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3523225627675231084981421 1321209610378211656868033)
            ·
              refine ⟨990907207783658742651025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321209610378211656868033 990907207783658742651025)
              ·
                refine ⟨743180405837744056988269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990907207783658742651025 743180405837744056988269)
                ·
                  refine ⟨278692652189154021370601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743180405837744056988269 278692652189154021370601)
                  ·
                    rfl

theorem cell20_610596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_610596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610596 prefixEnd_610596 := by exact prefixLift 610596
  have htrace : WordTrace (prefixWord ++ tailWord_610596) baseStart_610596 baseEnd_610596 := by
    simpa [prefixWord, tailWord_610596, baseEnd_610596] using wordTrace_append hprefix tailTrace_610596
  have hstable : (prefixWord ++ tailWord_610596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610596).length < 2 ^ (prefixWord ++ tailWord_610596).sum := by decide
  have hdescent : baseEnd_610596 < baseStart_610596 := by decide
  rcases family_descends (prefixWord ++ tailWord_610596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610606 : List Nat := [4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_610606 : Nat := 118140960795 + 610606 * 2 ^ 59
def prefixEnd_610606 : Nat := 4983230072969 + 3 ^ 40 * 610606 * 2
def baseEnd_610606 : Nat := 92899072153879477012409

theorem tailTrace_610606 : CollatzResearch.WordTrace tailWord_610606 prefixEnd_610606 92899072153879477012409 := by
  unfold tailWord_610606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783828803235777505937459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14847086950590813364999781 2783828803235777505937459)
  ·
    refine ⟨4175743204853666258906189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783828803235777505937459 4175743204853666258906189)
    ·
      refine ⟨1565903701820124847089821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4175743204853666258906189 1565903701820124847089821)
      ·
        refine ⟨587213888182546817658683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1565903701820124847089821 587213888182546817658683)
        ·
          refine ⟨880820832273820226488025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587213888182546817658683 880820832273820226488025)
          ·
            refine ⟨660615624205365169866019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880820832273820226488025 660615624205365169866019)
            ·
              refine ⟨990923436308047754799029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660615624205365169866019 990923436308047754799029)
              ·
                refine ⟨92899072153879477012409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 990923436308047754799029 92899072153879477012409)
                ·
                  rfl

theorem cell20_610606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_610606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610606 prefixEnd_610606 := by exact prefixLift 610606
  have htrace : WordTrace (prefixWord ++ tailWord_610606) baseStart_610606 baseEnd_610606 := by
    simpa [prefixWord, tailWord_610606, baseEnd_610606] using wordTrace_append hprefix tailTrace_610606
  have hstable : (prefixWord ++ tailWord_610606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610606).length < 2 ^ (prefixWord ++ tailWord_610606).sum := by decide
  have hdescent : baseEnd_610606 < baseStart_610606 := by decide
  rcases family_descends (prefixWord ++ tailWord_610606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610641 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 2]
def baseStart_610641 : Nat := 118140960795 + 610641 * 2 ^ 59
def prefixEnd_610641 : Nat := 4983230072969 + 3 ^ 40 * 610641 * 2
def baseEnd_610641 : Nat := 278713191415333864870417

theorem tailTrace_610641 : CollatzResearch.WordTrace tailWord_610641 prefixEnd_610641 278713191415333864870417 := by
  unfold tailWord_610641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22271906980759421025023777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14847937987172947350015851 22271906980759421025023777)
  ·
    refine ⟨16703930235569565768767833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22271906980759421025023777 16703930235569565768767833)
    ·
      refine ⟨12527947676677174326575875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16703930235569565768767833 12527947676677174326575875)
      ·
        refine ⟨18791921515015761489863813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527947676677174326575875 18791921515015761489863813)
        ·
          refine ⟨3523485284065455279349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18791921515015761489863813 3523485284065455279349465)
          ·
            refine ⟨2642613963049091459512099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3523485284065455279349465 2642613963049091459512099)
            ·
              refine ⟨3963920944573637189268149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642613963049091459512099 3963920944573637189268149)
              ·
                refine ⟨371617588553778486493889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3963920944573637189268149 371617588553778486493889)
                ·
                  refine ⟨278713191415333864870417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371617588553778486493889 278713191415333864870417)
                  ·
                    rfl

theorem cell20_610641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_610641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610641 prefixEnd_610641 := by exact prefixLift 610641
  have htrace : WordTrace (prefixWord ++ tailWord_610641) baseStart_610641 baseEnd_610641 := by
    simpa [prefixWord, tailWord_610641, baseEnd_610641] using wordTrace_append hprefix tailTrace_610641
  have hstable : (prefixWord ++ tailWord_610641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610641).length < 2 ^ (prefixWord ++ tailWord_610641).sum := by decide
  have hdescent : baseEnd_610641 < baseStart_610641 := by decide
  rcases family_descends (prefixWord ++ tailWord_610641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610655 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_610655 : Nat := 118140960795 + 610655 * 2 ^ 59
def prefixEnd_610655 : Nat := 4983230072969 + 3 ^ 40 * 610655 * 2
def baseEnd_610655 : Nat := 278719581396812038403693

theorem tailTrace_610655 : CollatzResearch.WordTrace tailWord_610655 prefixEnd_610655 278719581396812038403693 := by
  unfold tailWord_610655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22272417602708701416033419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14848278401805800944022279 22272417602708701416033419)
  ·
    refine ⟨33408626404063052124050129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22272417602708701416033419 33408626404063052124050129)
    ·
      refine ⟨25056469803047289093037597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33408626404063052124050129 25056469803047289093037597)
      ·
        refine ⟨9396176176142733409889099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25056469803047289093037597 9396176176142733409889099)
        ·
          refine ⟨14094264264214100114833649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396176176142733409889099 14094264264214100114833649)
          ·
            refine ⟨10570698198160575086125237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14094264264214100114833649 10570698198160575086125237)
            ·
              refine ⟨991002956077553914324241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10570698198160575086125237 991002956077553914324241)
              ·
                refine ⟨743252217058165435743181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 991002956077553914324241 743252217058165435743181)
                ·
                  refine ⟨278719581396812038403693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743252217058165435743181 278719581396812038403693)
                  ·
                    rfl

theorem cell20_610655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_610655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610655 prefixEnd_610655 := by exact prefixLift 610655
  have htrace : WordTrace (prefixWord ++ tailWord_610655) baseStart_610655 baseEnd_610655 := by
    simpa [prefixWord, tailWord_610655, baseEnd_610655] using wordTrace_append hprefix tailTrace_610655
  have hstable : (prefixWord ++ tailWord_610655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610655).length < 2 ^ (prefixWord ++ tailWord_610655).sum := by decide
  have hdescent : baseEnd_610655 < baseStart_610655 := by decide
  rcases family_descends (prefixWord ++ tailWord_610655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610658 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_610658 : Nat := 118140960795 + 610658 * 2 ^ 59
def prefixEnd_610658 : Nat := 4983230072969 + 3 ^ 40 * 610658 * 2
def baseEnd_610658 : Nat := 278720950678557361303681

theorem tailTrace_610658 : CollatzResearch.WordTrace tailWord_610658 prefixEnd_610658 278720950678557361303681 := by
  unfold tailWord_610658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568131755424458232098157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14848351347798555285595085 5568131755424458232098157)
  ·
    refine ⟨2088049408284171837036809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5568131755424458232098157 2088049408284171837036809)
    ·
      refine ⟨1566037056213128877777607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088049408284171837036809 1566037056213128877777607)
      ·
        refine ⟨2349055584319693316666411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566037056213128877777607 2349055584319693316666411)
        ·
          refine ⟨3523583376479539974999617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349055584319693316666411 3523583376479539974999617)
          ·
            refine ⟨2642687532359654981249713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3523583376479539974999617 2642687532359654981249713)
            ·
              refine ⟨1982015649269741235937285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642687532359654981249713 1982015649269741235937285)
              ·
                refine ⟨371627934238076481738241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1982015649269741235937285 371627934238076481738241)
                ·
                  refine ⟨278720950678557361303681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371627934238076481738241 278720950678557361303681)
                  ·
                    rfl

theorem cell20_610658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_610658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610658 prefixEnd_610658 := by exact prefixLift 610658
  have htrace : WordTrace (prefixWord ++ tailWord_610658) baseStart_610658 baseEnd_610658 := by
    simpa [prefixWord, tailWord_610658, baseEnd_610658] using wordTrace_append hprefix tailTrace_610658
  have hstable : (prefixWord ++ tailWord_610658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610658).length < 2 ^ (prefixWord ++ tailWord_610658).sum := by decide
  have hdescent : baseEnd_610658 < baseStart_610658 := by decide
  rcases family_descends (prefixWord ++ tailWord_610658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610669 : List Nat := [1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_610669 : Nat := 118140960795 + 610669 * 2 ^ 59
def prefixEnd_610669 : Nat := 4983230072969 + 3 ^ 40 * 610669 * 2
def baseEnd_610669 : Nat := 92908657126096737312323

theorem tailTrace_610669 : CollatzResearch.WordTrace tailWord_610669 prefixEnd_610669 92908657126096737312323 := by
  unfold tailWord_610669
  simp only [CollatzResearch.WordTrace]
  refine ⟨22272928224657981807043061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14848618816438654538028707 22272928224657981807043061)
  ·
    refine ⟨2088087021061685794410287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22272928224657981807043061 2088087021061685794410287)
    ·
      refine ⟨3132130531592528691615431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2088087021061685794410287 3132130531592528691615431)
      ·
        refine ⟨4698195797388793037423147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132130531592528691615431 4698195797388793037423147)
        ·
          refine ⟨7047293696083189556134721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698195797388793037423147 7047293696083189556134721)
          ·
            refine ⟨5285470272062392167101041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7047293696083189556134721 5285470272062392167101041)
            ·
              refine ⟨3964102704046794125325781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5285470272062392167101041 3964102704046794125325781)
              ·
                refine ⟨92908657126096737312323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3964102704046794125325781 92908657126096737312323)
                ·
                  rfl

theorem cell20_610669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_610669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610669 prefixEnd_610669 := by exact prefixLift 610669
  have htrace : WordTrace (prefixWord ++ tailWord_610669) baseStart_610669 baseEnd_610669 := by
    simpa [prefixWord, tailWord_610669, baseEnd_610669] using wordTrace_append hprefix tailTrace_610669
  have hstable : (prefixWord ++ tailWord_610669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610669).length < 2 ^ (prefixWord ++ tailWord_610669).sum := by decide
  have hdescent : baseEnd_610669 < baseStart_610669 := by decide
  rcases family_descends (prefixWord ++ tailWord_610669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610672 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_610672 : Nat := 118140960795 + 610672 * 2 ^ 59
def prefixEnd_610672 : Nat := 4983230072969 + 3 ^ 40 * 610672 * 2
def baseEnd_610672 : Nat := 278727340660035534836957

theorem tailTrace_610672 : CollatzResearch.WordTrace tailWord_610672 prefixEnd_610672 278727340660035534836957 := by
  unfold tailWord_610672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136518821823556659701135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14848691762431408879601513 11136518821823556659701135)
  ·
    refine ⟨16704778232735334989551703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11136518821823556659701135 16704778232735334989551703)
    ·
      refine ⟨25057167349103002484327555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16704778232735334989551703 25057167349103002484327555)
      ·
        refine ⟨37585751023654503726491333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25057167349103002484327555 37585751023654503726491333)
        ·
          refine ⟨7047328316935219448717125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37585751023654503726491333 7047328316935219448717125)
          ·
            refine ⟨1321374059425353646634461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7047328316935219448717125 1321374059425353646634461)
            ·
              refine ⟨495515272284507617487923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1321374059425353646634461 495515272284507617487923)
              ·
                refine ⟨743272908426761426231885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495515272284507617487923 743272908426761426231885)
                ·
                  refine ⟨278727340660035534836957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743272908426761426231885 278727340660035534836957)
                  ·
                    rfl

theorem cell20_610672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_610672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610672 prefixEnd_610672 := by exact prefixLift 610672
  have htrace : WordTrace (prefixWord ++ tailWord_610672) baseStart_610672 baseEnd_610672 := by
    simpa [prefixWord, tailWord_610672, baseEnd_610672] using wordTrace_append hprefix tailTrace_610672
  have hstable : (prefixWord ++ tailWord_610672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610672).length < 2 ^ (prefixWord ++ tailWord_610672).sum := by decide
  have hdescent : baseEnd_610672 < baseStart_610672 := by decide
  rcases family_descends (prefixWord ++ tailWord_610672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610727 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 3]
def baseStart_610727 : Nat := 118140960795 + 610727 * 2 ^ 59
def prefixEnd_610727 : Nat := 4983230072969 + 3 ^ 40 * 610727 * 2
def baseEnd_610727 : Nat := 278752444158699788003399

theorem tailTrace_610727 : CollatzResearch.WordTrace tailWord_610727 prefixEnd_610727 278752444158699788003399 := by
  unfold tailWord_610727
  simp only [CollatzResearch.WordTrace]
  refine ⟨22275043658447857712654435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14850029105631905141769623 22275043658447857712654435)
  ·
    refine ⟨33412565487671786568981653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22275043658447857712654435 33412565487671786568981653)
    ·
      refine ⟨1566214007234614995421015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33412565487671786568981653 1566214007234614995421015)
      ·
        refine ⟨2349321010851922493131523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566214007234614995421015 2349321010851922493131523)
        ·
          refine ⟨3523981516277883739697285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349321010851922493131523 3523981516277883739697285)
          ·
            refine ⟨660746534302103201193241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3523981516277883739697285 660746534302103201193241)
            ·
              refine ⟨495559900726577400894931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660746534302103201193241 495559900726577400894931)
              ·
                refine ⟨743339851089866101342397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495559900726577400894931 743339851089866101342397)
                ·
                  refine ⟨278752444158699788003399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743339851089866101342397 278752444158699788003399)
                  ·
                    rfl

theorem cell20_610727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_610727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610727 prefixEnd_610727 := by exact prefixLift 610727
  have htrace : WordTrace (prefixWord ++ tailWord_610727) baseStart_610727 baseEnd_610727 := by
    simpa [prefixWord, tailWord_610727, baseEnd_610727] using wordTrace_append hprefix tailTrace_610727
  have hstable : (prefixWord ++ tailWord_610727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610727).length < 2 ^ (prefixWord ++ tailWord_610727).sum := by decide
  have hdescent : baseEnd_610727 < baseStart_610727 := by decide
  rcases family_descends (prefixWord ++ tailWord_610727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610745 : List Nat := [1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_610745 : Nat := 118140960795 + 610745 * 2 ^ 59
def prefixEnd_610745 : Nat := 4983230072969 + 3 ^ 40 * 610745 * 2
def baseEnd_610745 : Nat := 92920219949723908467775

theorem tailTrace_610745 : CollatzResearch.WordTrace tailWord_610745 prefixEnd_610745 92920219949723908467775 := by
  unfold tailWord_610745
  simp only [CollatzResearch.WordTrace]
  refine ⟨22275700172382646786809689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14850466781588431191206459 22275700172382646786809689)
  ·
    refine ⟨16706775129286985090107267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22275700172382646786809689 16706775129286985090107267)
    ·
      refine ⟨25060162693930477635160901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16706775129286985090107267 25060162693930477635160901)
      ·
        refine ⟨4698780505111964556592669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25060162693930477635160901 4698780505111964556592669)
        ·
          refine ⟨1762042689416986708722251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4698780505111964556592669 1762042689416986708722251)
          ·
            refine ⟨2643064034125480063083377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762042689416986708722251 2643064034125480063083377)
            ·
              refine ⟨1982298025594110047312533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2643064034125480063083377 1982298025594110047312533)
              ·
                refine ⟨92920219949723908467775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1982298025594110047312533 92920219949723908467775)
                ·
                  rfl

theorem cell20_610745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_610745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610745 prefixEnd_610745 := by exact prefixLift 610745
  have htrace : WordTrace (prefixWord ++ tailWord_610745) baseStart_610745 baseEnd_610745 := by
    simpa [prefixWord, tailWord_610745, baseEnd_610745] using wordTrace_append hprefix tailTrace_610745
  have hstable : (prefixWord ++ tailWord_610745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610745).length < 2 ^ (prefixWord ++ tailWord_610745).sum := by decide
  have hdescent : baseEnd_610745 < baseStart_610745 := by decide
  rcases family_descends (prefixWord ++ tailWord_610745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610772 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_610772 : Nat := 118140960795 + 610772 * 2 ^ 59
def prefixEnd_610772 : Nat := 4983230072969 + 3 ^ 40 * 610772 * 2
def baseEnd_610772 : Nat := 278772983384879631503215

theorem tailTrace_610772 : CollatzResearch.WordTrace tailWord_610772 prefixEnd_610772 278772983384879631503215 := by
  unfold tailWord_610772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138342471642415199021285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14851123295523220265361713 11138342471642415199021285)
  ·
    refine ⟨2088439213432952849816491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11138342471642415199021285 2088439213432952849816491)
    ·
      refine ⟨3132658820149429274724737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2088439213432952849816491 3132658820149429274724737)
      ·
        refine ⟨2349494115112071956043553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3132658820149429274724737 2349494115112071956043553)
        ·
          refine ⟨1762120586334053967032665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2349494115112071956043553 1762120586334053967032665)
          ·
            refine ⟨1321590439750540475274499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762120586334053967032665 1321590439750540475274499)
            ·
              refine ⟨1982385659625810712911749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321590439750540475274499 1982385659625810712911749)
              ·
                refine ⟨371697311179839508670953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1982385659625810712911749 371697311179839508670953)
                ·
                  refine ⟨278772983384879631503215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371697311179839508670953 278772983384879631503215)
                  ·
                    rfl

theorem cell20_610772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_610772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610772 prefixEnd_610772 := by exact prefixLift 610772
  have htrace : WordTrace (prefixWord ++ tailWord_610772) baseStart_610772 baseEnd_610772 := by
    simpa [prefixWord, tailWord_610772, baseEnd_610772] using wordTrace_append hprefix tailTrace_610772
  have hstable : (prefixWord ++ tailWord_610772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610772).length < 2 ^ (prefixWord ++ tailWord_610772).sum := by decide
  have hdescent : baseEnd_610772 < baseStart_610772 := by decide
  rcases family_descends (prefixWord ++ tailWord_610772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610783 : List Nat := [1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_610783 : Nat := 118140960795 + 610783 * 2 ^ 59
def prefixEnd_610783 : Nat := 4983230072969 + 3 ^ 40 * 610783 * 2
def baseEnd_610783 : Nat := 92926001361537494045501

theorem tailTrace_610783 : CollatzResearch.WordTrace tailWord_610783 prefixEnd_610783 92926001361537494045501 := by
  unfold tailWord_610783
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277086146244979276693003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14851390764163319517795335 22277086146244979276693003)
  ·
    refine ⟨33415629219367468915039505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22277086146244979276693003 33415629219367468915039505)
    ·
      refine ⟨25061721914525601686279629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33415629219367468915039505 25061721914525601686279629)
      ·
        refine ⟨9398145717947100632354861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25061721914525601686279629 9398145717947100632354861)
        ·
          refine ⟨3524304644230162737133073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9398145717947100632354861 3524304644230162737133073)
          ·
            refine ⟨2643228483172622052849805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3524304644230162737133073 2643228483172622052849805)
            ·
              refine ⟨991210681189733269818677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2643228483172622052849805 991210681189733269818677)
              ·
                refine ⟨92926001361537494045501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 991210681189733269818677 92926001361537494045501)
                ·
                  rfl

theorem cell20_610783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_610783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610783 prefixEnd_610783 := by exact prefixLift 610783
  have htrace : WordTrace (prefixWord ++ tailWord_610783) baseStart_610783 baseEnd_610783 := by
    simpa [prefixWord, tailWord_610783, baseEnd_610783] using wordTrace_append hprefix tailTrace_610783
  have hstable : (prefixWord ++ tailWord_610783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610783).length < 2 ^ (prefixWord ++ tailWord_610783).sum := by decide
  have hdescent : baseEnd_610783 < baseStart_610783 := by decide
  rcases family_descends (prefixWord ++ tailWord_610783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610855 : List Nat := [1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_610855 : Nat := 118140960795 + 610855 * 2 ^ 59
def prefixEnd_610855 : Nat := 4983230072969 + 3 ^ 40 * 610855 * 2
def baseEnd_610855 : Nat := 92936955615500077245403

theorem tailTrace_610855 : CollatzResearch.WordTrace tailWord_610855 prefixEnd_610855 92936955615500077245403 := by
  unfold tailWord_610855
  simp only [CollatzResearch.WordTrace]
  refine ⟨22279712201984135573314019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14853141467989423715542679 22279712201984135573314019)
  ·
    refine ⟨33419568302976203359971029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22279712201984135573314019 33419568302976203359971029)
    ·
      refine ⟨783271132101004766249321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33419568302976203359971029 783271132101004766249321)
      ·
        refine ⟨587453349075753574686991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 783271132101004766249321 587453349075753574686991)
        ·
          refine ⟨881180023613630362030487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587453349075753574686991 881180023613630362030487)
          ·
            refine ⟨1321770035420445543045731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881180023613630362030487 1321770035420445543045731)
            ·
              refine ⟨1982655053130668314568597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321770035420445543045731 1982655053130668314568597)
              ·
                refine ⟨92936955615500077245403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1982655053130668314568597 92936955615500077245403)
                ·
                  rfl

theorem cell20_610855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_610855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610855 prefixEnd_610855 := by exact prefixLift 610855
  have htrace : WordTrace (prefixWord ++ tailWord_610855) baseStart_610855 baseEnd_610855 := by
    simpa [prefixWord, tailWord_610855, baseEnd_610855] using wordTrace_append hprefix tailTrace_610855
  have hstable : (prefixWord ++ tailWord_610855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610855).length < 2 ^ (prefixWord ++ tailWord_610855).sum := by decide
  have hdescent : baseEnd_610855 < baseStart_610855 := by decide
  rcases family_descends (prefixWord ++ tailWord_610855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610861 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 2]
def baseStart_610861 : Nat := 118140960795 + 610861 * 2 ^ 59
def prefixEnd_610861 : Nat := 4983230072969 + 3 ^ 40 * 610861 * 2
def baseEnd_610861 : Nat := 278813605409990877536185

theorem tailTrace_610861 : CollatzResearch.WordTrace tailWord_610861 prefixEnd_610861 278813605409990877536185 := by
  unfold tailWord_610861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22279931039962398598032437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14853287359974932398688291 22279931039962398598032437)
  ·
    refine ⟨2088743534996474868565541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22279931039962398598032437 2088743534996474868565541)
    ·
      refine ⟨391639412811839037856039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2088743534996474868565541 391639412811839037856039)
      ·
        refine ⟨587459119217758556784059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391639412811839037856039 587459119217758556784059)
        ·
          refine ⟨881188678826637835176089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587459119217758556784059 881188678826637835176089)
          ·
            refine ⟨660891509119978376382067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881188678826637835176089 660891509119978376382067)
            ·
              refine ⟨991337263679967564573101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660891509119978376382067 991337263679967564573101)
              ·
                refine ⟨371751473879987836714913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991337263679967564573101 371751473879987836714913)
                ·
                  refine ⟨278813605409990877536185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371751473879987836714913 278813605409990877536185)
                  ·
                    rfl

theorem cell20_610861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_610861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610861 prefixEnd_610861 := by exact prefixLift 610861
  have htrace : WordTrace (prefixWord ++ tailWord_610861) baseStart_610861 baseEnd_610861 := by
    simpa [prefixWord, tailWord_610861, baseEnd_610861] using wordTrace_append hprefix tailTrace_610861
  have hstable : (prefixWord ++ tailWord_610861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610861).length < 2 ^ (prefixWord ++ tailWord_610861).sum := by decide
  have hdescent : baseEnd_610861 < baseStart_610861 := by decide
  rcases family_descends (prefixWord ++ tailWord_610861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610866 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_610866 : Nat := 118140960795 + 610866 * 2 ^ 59
def prefixEnd_610866 : Nat := 4983230072969 + 3 ^ 40 * 610866 * 2
def baseEnd_610866 : Nat := 278815887546233082369497

theorem tailTrace_610866 : CollatzResearch.WordTrace tailWord_610866 prefixEnd_610866 278815887546233082369497 := by
  unfold tailWord_610866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570028351236071112991113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14853408936629522967976301 5570028351236071112991113)
  ·
    refine ⟨4177521263427053334743335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5570028351236071112991113 4177521263427053334743335)
    ·
      refine ⟨6266281895140580002115003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177521263427053334743335 6266281895140580002115003)
      ·
        refine ⟨9399422842710870003172505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266281895140580002115003 9399422842710870003172505)
        ·
          refine ⟨7049567132033152502379379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9399422842710870003172505 7049567132033152502379379)
          ·
            refine ⟨10574350698049728753569069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7049567132033152502379379 10574350698049728753569069)
            ·
              refine ⟨3965381511768648282588401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10574350698049728753569069 3965381511768648282588401)
              ·
                refine ⟨2974036133826486211941301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3965381511768648282588401 2974036133826486211941301)
                ·
                  refine ⟨278815887546233082369497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2974036133826486211941301 278815887546233082369497)
                  ·
                    rfl

theorem cell20_610866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_610866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610866 prefixEnd_610866 := by exact prefixLift 610866
  have htrace : WordTrace (prefixWord ++ tailWord_610866) baseStart_610866 baseEnd_610866 := by
    simpa [prefixWord, tailWord_610866, baseEnd_610866] using wordTrace_append hprefix tailTrace_610866
  have hstable : (prefixWord ++ tailWord_610866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610866).length < 2 ^ (prefixWord ++ tailWord_610866).sum := by decide
  have hdescent : baseEnd_610866 < baseStart_610866 := by decide
  rcases family_descends (prefixWord ++ tailWord_610866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610880 : List Nat := [2, 1, 1, 2, 2, 2, 10]
def baseStart_610880 : Nat := 118140960795 + 610880 * 2 ^ 59
def prefixEnd_610880 : Nat := 4983230072969 + 3 ^ 40 * 610880 * 2
def baseEnd_610880 : Nat := 30980253058634583989197

theorem tailTrace_610880 : CollatzResearch.WordTrace tailWord_610880 prefixEnd_610880 30980253058634583989197 := by
  unfold tailWord_610880
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140312013446782421487047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14853749351262376561982729 11140312013446782421487047)
  ·
    refine ⟨16710468020170173632230571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11140312013446782421487047 16710468020170173632230571)
    ·
      refine ⟨25065702030255260448345857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16710468020170173632230571 25065702030255260448345857)
      ·
        refine ⟨18799276522691445336259393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25065702030255260448345857 18799276522691445336259393)
        ·
          refine ⟨14099457392018584002194545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18799276522691445336259393 14099457392018584002194545)
          ·
            refine ⟨10574593044013938001645909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14099457392018584002194545 10574593044013938001645909)
            ·
              refine ⟨30980253058634583989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10574593044013938001645909 30980253058634583989197)
              ·
                rfl

theorem cell20_610880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_610880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610880 prefixEnd_610880 := by exact prefixLift 610880
  have htrace : WordTrace (prefixWord ++ tailWord_610880) baseStart_610880 baseEnd_610880 := by
    simpa [prefixWord, tailWord_610880, baseEnd_610880] using wordTrace_append hprefix tailTrace_610880
  have hstable : (prefixWord ++ tailWord_610880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610880).length < 2 ^ (prefixWord ++ tailWord_610880).sum := by decide
  have hdescent : baseEnd_610880 < baseStart_610880 := by decide
  rcases family_descends (prefixWord ++ tailWord_610880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610886 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_610886 : Nat := 118140960795 + 610886 * 2 ^ 59
def prefixEnd_610886 : Nat := 4983230072969 + 3 ^ 40 * 610886 * 2
def baseEnd_610886 : Nat := 278825016091201901702749

theorem tailTrace_610886 : CollatzResearch.WordTrace tailWord_610886 prefixEnd_610886 278825016091201901702749 := by
  unfold tailWord_610886
  simp only [CollatzResearch.WordTrace]
  refine ⟨696276339527244620865391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14853895243247885245128341 696276339527244620865391)
  ·
    refine ⟨1044414509290866931298087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696276339527244620865391 1044414509290866931298087)
    ·
      refine ⟨1566621763936300396947131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044414509290866931298087 1566621763936300396947131)
      ·
        refine ⟨2349932645904450595420697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566621763936300396947131 2349932645904450595420697)
        ·
          refine ⟨1762449484428337946565523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2349932645904450595420697 1762449484428337946565523)
          ·
            refine ⟨2643674226642506919848285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762449484428337946565523 2643674226642506919848285)
            ·
              refine ⟨991377834990940094943107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2643674226642506919848285 991377834990940094943107)
              ·
                refine ⟨1487066752486410142414661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991377834990940094943107 1487066752486410142414661)
                ·
                  refine ⟨278825016091201901702749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487066752486410142414661 278825016091201901702749)
                  ·
                    rfl

theorem cell20_610886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_610886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610886 prefixEnd_610886 := by exact prefixLift 610886
  have htrace : WordTrace (prefixWord ++ tailWord_610886) baseStart_610886 baseEnd_610886 := by
    simpa [prefixWord, tailWord_610886, baseEnd_610886] using wordTrace_append hprefix tailTrace_610886
  have hstable : (prefixWord ++ tailWord_610886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610886).length < 2 ^ (prefixWord ++ tailWord_610886).sum := by decide
  have hdescent : baseEnd_610886 < baseStart_610886 := by decide
  rcases family_descends (prefixWord ++ tailWord_610886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610890 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_610890 : Nat := 118140960795 + 610890 * 2 ^ 59
def prefixEnd_610890 : Nat := 4983230072969 + 3 ^ 40 * 610890 * 2
def baseEnd_610890 : Nat := 278826841800195665569399

theorem tailTrace_610890 : CollatzResearch.WordTrace tailWord_610890 prefixEnd_610890 278826841800195665569399 := by
  unfold tailWord_610890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570247189214334137709531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14853992504571557700558749 5570247189214334137709531)
  ·
    refine ⟨8355370783821501206564297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5570247189214334137709531 8355370783821501206564297)
    ·
      refine ⟨6266528087866125904923223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8355370783821501206564297 6266528087866125904923223)
      ·
        refine ⟨9399792131799188857384835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266528087866125904923223 9399792131799188857384835)
        ·
          refine ⟨14099688197698783286077253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9399792131799188857384835 14099688197698783286077253)
          ·
            refine ⟨2643691537068521866139485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14099688197698783286077253 2643691537068521866139485)
            ·
              refine ⟨991384326400695699802307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2643691537068521866139485 991384326400695699802307)
              ·
                refine ⟨1487076489601043549703461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991384326400695699802307 1487076489601043549703461)
                ·
                  refine ⟨278826841800195665569399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487076489601043549703461 278826841800195665569399)
                  ·
                    rfl

theorem cell20_610890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_610890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610890 prefixEnd_610890 := by exact prefixLift 610890
  have htrace : WordTrace (prefixWord ++ tailWord_610890) baseStart_610890 baseEnd_610890 := by
    simpa [prefixWord, tailWord_610890, baseEnd_610890] using wordTrace_append hprefix tailTrace_610890
  have hstable : (prefixWord ++ tailWord_610890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610890).length < 2 ^ (prefixWord ++ tailWord_610890).sum := by decide
  have hdescent : baseEnd_610890 < baseStart_610890 := by decide
  rcases family_descends (prefixWord ++ tailWord_610890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610897 : List Nat := [1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_610897 : Nat := 118140960795 + 610897 * 2 ^ 59
def prefixEnd_610897 : Nat := 4983230072969 + 3 ^ 40 * 610897 * 2
def baseEnd_610897 : Nat := 92943345596978250778679

theorem tailTrace_610897 : CollatzResearch.WordTrace tailWord_610897 prefixEnd_610897 92943345596978250778679 := by
  unfold tailWord_610897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22281244067831976746342945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14854162711887984497561963 22281244067831976746342945)
  ·
    refine ⟨16710933050873982559757209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22281244067831976746342945 16710933050873982559757209)
    ·
      refine ⟨12533199788155486919817907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16710933050873982559757209 12533199788155486919817907)
      ·
        refine ⟨18799799682233230379726861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533199788155486919817907 18799799682233230379726861)
        ·
          refine ⟨7049924880837461392397573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18799799682233230379726861 7049924880837461392397573)
          ·
            refine ⟨1321860915157024011074545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7049924880837461392397573 1321860915157024011074545)
            ·
              refine ⟨991395686367768008305909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321860915157024011074545 991395686367768008305909)
              ·
                refine ⟨92943345596978250778679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 991395686367768008305909 92943345596978250778679)
                ·
                  rfl

theorem cell20_610897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_610897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610897 prefixEnd_610897 := by exact prefixLift 610897
  have htrace : WordTrace (prefixWord ++ tailWord_610897) baseStart_610897 baseEnd_610897 := by
    simpa [prefixWord, tailWord_610897, baseEnd_610897] using wordTrace_append hprefix tailTrace_610897
  have hstable : (prefixWord ++ tailWord_610897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610897).length < 2 ^ (prefixWord ++ tailWord_610897).sum := by decide
  have hdescent : baseEnd_610897 < baseStart_610897 := by decide
  rcases family_descends (prefixWord ++ tailWord_610897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610900 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_610900 : Nat := 118140960795 + 610900 * 2 ^ 59
def prefixEnd_610900 : Nat := 4983230072969 + 3 ^ 40 * 610900 * 2
def baseEnd_610900 : Nat := 278831406072680075236025

theorem tailTrace_610900 : CollatzResearch.WordTrace tailWord_610900 prefixEnd_610900 278831406072680075236025 := by
  unfold tailWord_610900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140676743410554129351077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14854235657880738839134769 11140676743410554129351077)
  ·
    refine ⟨2088876889389478899253327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11140676743410554129351077 2088876889389478899253327)
    ·
      refine ⟨3133315334084218348879991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2088876889389478899253327 3133315334084218348879991)
      ·
        refine ⟨4699973001126327523319987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133315334084218348879991 4699973001126327523319987)
        ·
          refine ⟨7049959501689491284979981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699973001126327523319987 7049959501689491284979981)
          ·
            refine ⟨2643734813133559231867493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7049959501689491284979981 2643734813133559231867493)
            ·
              refine ⟨495700277462542355975155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2643734813133559231867493 495700277462542355975155)
              ·
                refine ⟨743550416193813533962733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495700277462542355975155 743550416193813533962733)
                ·
                  refine ⟨278831406072680075236025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743550416193813533962733 278831406072680075236025)
                  ·
                    rfl

theorem cell20_610900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_610900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610900 prefixEnd_610900 := by exact prefixLift 610900
  have htrace : WordTrace (prefixWord ++ tailWord_610900) baseStart_610900 baseEnd_610900 := by
    simpa [prefixWord, tailWord_610900, baseEnd_610900] using wordTrace_append hprefix tailTrace_610900
  have hstable : (prefixWord ++ tailWord_610900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610900).length < 2 ^ (prefixWord ++ tailWord_610900).sum := by decide
  have hdescent : baseEnd_610900 < baseStart_610900 := by decide
  rcases family_descends (prefixWord ++ tailWord_610900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610911 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_610911 : Nat := 118140960795 + 610911 * 2 ^ 59
def prefixEnd_610911 : Nat := 4983230072969 + 3 ^ 40 * 610911 * 2
def baseEnd_610911 : Nat := 278836426772412925869313

theorem tailTrace_610911 : CollatzResearch.WordTrace tailWord_610911 prefixEnd_610911 278836426772412925869313 := by
  unfold tailWord_610911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22281754689781257137352587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14854503126520838091568391 22281754689781257137352587)
  ·
    refine ⟨33422632034671885706028881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22281754689781257137352587 33422632034671885706028881)
    ·
      refine ⟨25066974026003914279521661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33422632034671885706028881 25066974026003914279521661)
      ·
        refine ⟨9400115259751467854820623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25066974026003914279521661 9400115259751467854820623)
        ·
          refine ⟨14100172889627201782230935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9400115259751467854820623 14100172889627201782230935)
          ·
            refine ⟨21150259334440802673346403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14100172889627201782230935 21150259334440802673346403)
            ·
              refine ⟨31725389001661204010019605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21150259334440802673346403 31725389001661204010019605)
              ·
                refine ⟨1487127609452868937969669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31725389001661204010019605 1487127609452868937969669)
                ·
                  refine ⟨278836426772412925869313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487127609452868937969669 278836426772412925869313)
                  ·
                    rfl

theorem cell20_610911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_610911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610911 prefixEnd_610911 := by exact prefixLift 610911
  have htrace : WordTrace (prefixWord ++ tailWord_610911) baseStart_610911 baseEnd_610911 := by
    simpa [prefixWord, tailWord_610911, baseEnd_610911] using wordTrace_append hprefix tailTrace_610911
  have hstable : (prefixWord ++ tailWord_610911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610911).length < 2 ^ (prefixWord ++ tailWord_610911).sum := by decide
  have hdescent : baseEnd_610911 < baseStart_610911 := by decide
  rcases family_descends (prefixWord ++ tailWord_610911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610941 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 2]
def baseStart_610941 : Nat := 118140960795 + 610941 * 2 ^ 59
def prefixEnd_610941 : Nat := 4983230072969 + 3 ^ 40 * 610941 * 2
def baseEnd_610941 : Nat := 278850119589866154869191

theorem tailTrace_610941 : CollatzResearch.WordTrace tailWord_610941 prefixEnd_610941 278850119589866154869191 := by
  unfold tailWord_610941
  simp only [CollatzResearch.WordTrace]
  refine ⟨22282848879672572260944677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14855232586448381507296451 22282848879672572260944677)
  ·
    refine ⟨4178034164938607298927127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22282848879672572260944677 4178034164938607298927127)
    ·
      refine ⟨6267051247407910948390691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178034164938607298927127 6267051247407910948390691)
      ·
        refine ⟨9400576871111866422586037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267051247407910948390691 9400576871111866422586037)
        ·
          refine ⟨881304081666737477117441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9400576871111866422586037 881304081666737477117441)
          ·
            refine ⟨660978061250053107838081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881304081666737477117441 660978061250053107838081)
            ·
              refine ⟨495733545937539830878561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660978061250053107838081 495733545937539830878561)
              ·
                refine ⟨371800159453154873158921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495733545937539830878561 371800159453154873158921)
                ·
                  refine ⟨278850119589866154869191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371800159453154873158921 278850119589866154869191)
                  ·
                    rfl

theorem cell20_610941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_610941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610941 prefixEnd_610941 := by exact prefixLift 610941
  have htrace : WordTrace (prefixWord ++ tailWord_610941) baseStart_610941 baseEnd_610941 := by
    simpa [prefixWord, tailWord_610941, baseEnd_610941] using wordTrace_append hprefix tailTrace_610941
  have hstable : (prefixWord ++ tailWord_610941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610941).length < 2 ^ (prefixWord ++ tailWord_610941).sum := by decide
  have hdescent : baseEnd_610941 < baseStart_610941 := by decide
  rcases family_descends (prefixWord ++ tailWord_610941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610945 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 2]
def baseStart_610945 : Nat := 118140960795 + 610945 * 2 ^ 59
def prefixEnd_610945 : Nat := 4983230072969 + 3 ^ 40 * 610945 * 2
def baseEnd_610945 : Nat := 278851945298859918735841

theorem tailTrace_610945 : CollatzResearch.WordTrace tailWord_610945 prefixEnd_610945 278851945298859918735841 := by
  unfold tailWord_610945
  simp only [CollatzResearch.WordTrace]
  refine ⟨22282994771658080944090289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14855329847772053962726859 22282994771658080944090289)
  ·
    refine ⟨16712246078743560708067717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22282994771658080944090289 16712246078743560708067717)
    ·
      refine ⟨3133546139764417632762697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16712246078743560708067717 3133546139764417632762697)
      ·
        refine ⟨2350159604823313224572023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3133546139764417632762697 2350159604823313224572023)
        ·
          refine ⟨3525239407234969836858035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350159604823313224572023 3525239407234969836858035)
          ·
            refine ⟨5287859110852454755287053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525239407234969836858035 5287859110852454755287053)
            ·
              refine ⟨1982947166569670533232645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5287859110852454755287053 1982947166569670533232645)
              ·
                refine ⟨371802593731813224981121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1982947166569670533232645 371802593731813224981121)
                ·
                  refine ⟨278851945298859918735841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371802593731813224981121 278851945298859918735841)
                  ·
                    rfl

theorem cell20_610945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_610945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610945 prefixEnd_610945 := by exact prefixLift 610945
  have htrace : WordTrace (prefixWord ++ tailWord_610945) baseStart_610945 baseEnd_610945 := by
    simpa [prefixWord, tailWord_610945, baseEnd_610945] using wordTrace_append hprefix tailTrace_610945
  have hstable : (prefixWord ++ tailWord_610945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610945).length < 2 ^ (prefixWord ++ tailWord_610945).sum := by decide
  have hdescent : baseEnd_610945 < baseStart_610945 := by decide
  rcases family_descends (prefixWord ++ tailWord_610945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610956 : List Nat := [2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_610956 : Nat := 118140960795 + 610956 * 2 ^ 59
def prefixEnd_610956 : Nat := 4983230072969 + 3 ^ 40 * 610956 * 2
def baseEnd_610956 : Nat := 92952321999530923123043

theorem tailTrace_610956 : CollatzResearch.WordTrace tailWord_610956 prefixEnd_610956 92952321999530923123043 := by
  unfold tailWord_610956
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141697987309114911370361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14855597316412153215160481 11141697987309114911370361)
  ·
    refine ⟨8356273490481836183527771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11141697987309114911370361 8356273490481836183527771)
    ·
      refine ⟨12534410235722754275291657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8356273490481836183527771 12534410235722754275291657)
      ·
        refine ⟨9400807676792065706468743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12534410235722754275291657 9400807676792065706468743)
        ·
          refine ⟨14101211515188098559703115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9400807676792065706468743 14101211515188098559703115)
          ·
            refine ⟨21151817272782147839554673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14101211515188098559703115 21151817272782147839554673)
            ·
              refine ⟨15863862954586610879666005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21151817272782147839554673 15863862954586610879666005)
              ·
                refine ⟨92952321999530923123043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15863862954586610879666005 92952321999530923123043)
                ·
                  rfl

theorem cell20_610956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_610956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610956 prefixEnd_610956 := by exact prefixLift 610956
  have htrace : WordTrace (prefixWord ++ tailWord_610956) baseStart_610956 baseEnd_610956 := by
    simpa [prefixWord, tailWord_610956, baseEnd_610956] using wordTrace_append hprefix tailTrace_610956
  have hstable : (prefixWord ++ tailWord_610956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610956).length < 2 ^ (prefixWord ++ tailWord_610956).sum := by decide
  have hdescent : baseEnd_610956 < baseStart_610956 := by decide
  rcases family_descends (prefixWord ++ tailWord_610956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610980 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_610980 : Nat := 118140960795 + 610980 * 2 ^ 59
def prefixEnd_610980 : Nat := 4983230072969 + 3 ^ 40 * 610980 * 2
def baseEnd_610980 : Nat := 278867920252555352569031

theorem tailTrace_610980 : CollatzResearch.WordTrace tailWord_610980 prefixEnd_610980 278867920252555352569031 := by
  unfold tailWord_610980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142135663265640960807197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14856180884354187947742929 11142135663265640960807197)
  ·
    refine ⟨4178300873724615360302699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11142135663265640960807197 4178300873724615360302699)
    ·
      refine ⟨6267451310586923040454049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178300873724615360302699 6267451310586923040454049)
      ·
        refine ⟨4700588482940192280340537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6267451310586923040454049 4700588482940192280340537)
        ·
          refine ⟨3525441362205144210255403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700588482940192280340537 3525441362205144210255403)
          ·
            refine ⟨5288162043307716315383105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525441362205144210255403 5288162043307716315383105)
            ·
              refine ⟨3966121532480787236537329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288162043307716315383105 3966121532480787236537329)
              ·
                refine ⟨2974591149360590427402997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966121532480787236537329 2974591149360590427402997)
                ·
                  refine ⟨278867920252555352569031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2974591149360590427402997 278867920252555352569031)
                  ·
                    rfl

theorem cell20_610980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_610980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610980 prefixEnd_610980 := by exact prefixLift 610980
  have htrace : WordTrace (prefixWord ++ tailWord_610980) baseStart_610980 baseEnd_610980 := by
    simpa [prefixWord, tailWord_610980, baseEnd_610980] using wordTrace_append hprefix tailTrace_610980
  have hstable : (prefixWord ++ tailWord_610980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610980).length < 2 ^ (prefixWord ++ tailWord_610980).sum := by decide
  have hdescent : baseEnd_610980 < baseStart_610980 := by decide
  rcases family_descends (prefixWord ++ tailWord_610980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610990 : List Nat := [4, 1, 4, 1, 1, 2, 7]
def baseStart_610990 : Nat := 118140960795 + 610990 * 2 ^ 59
def prefixEnd_610990 : Nat := 4983230072969 + 3 ^ 40 * 610990 * 2
def baseEnd_610990 : Nat := 30985831613893306915073

theorem tailTrace_610990 : CollatzResearch.WordTrace tailWord_610990 prefixEnd_610990 30985831613893306915073 := by
  unfold tailWord_610990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785579507061881703684803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14856424037663369086318949 2785579507061881703684803)
  ·
    refine ⟨4178369260592822555527205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2785579507061881703684803 4178369260592822555527205)
    ·
      refine ⟨783444236361154229161351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4178369260592822555527205 783444236361154229161351)
      ·
        refine ⟨1175166354541731343742027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783444236361154229161351 1175166354541731343742027)
        ·
          refine ⟨1762749531812597015613041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175166354541731343742027 1762749531812597015613041)
          ·
            refine ⟨1322062148859447761709781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762749531812597015613041 1322062148859447761709781)
            ·
              refine ⟨30985831613893306915073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1322062148859447761709781 30985831613893306915073)
              ·
                rfl

theorem cell20_610990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_610990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610990 prefixEnd_610990 := by exact prefixLift 610990
  have htrace : WordTrace (prefixWord ++ tailWord_610990) baseStart_610990 baseEnd_610990 := by
    simpa [prefixWord, tailWord_610990, baseEnd_610990] using wordTrace_append hprefix tailTrace_610990
  have hstable : (prefixWord ++ tailWord_610990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610990).length < 2 ^ (prefixWord ++ tailWord_610990).sum := by decide
  have hdescent : baseEnd_610990 < baseStart_610990 := by decide
  rcases family_descends (prefixWord ++ tailWord_610990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610993 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_610993 : Nat := 118140960795 + 610993 * 2 ^ 59
def prefixEnd_610993 : Nat := 4983230072969 + 3 ^ 40 * 610993 * 2
def baseEnd_610993 : Nat := 278873853806785085135645

theorem tailTrace_610993 : CollatzResearch.WordTrace tailWord_610993 prefixEnd_610993 278873853806785085135645 := by
  unfold tailWord_610993
  simp only [CollatzResearch.WordTrace]
  refine ⟨22284745475484185141837633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14856496983656123427891755 22284745475484185141837633)
  ·
    refine ⟨16713559106613138856378225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22284745475484185141837633 16713559106613138856378225)
    ·
      refine ⟨12535169329959854142283669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16713559106613138856378225 12535169329959854142283669)
      ·
        refine ⟨587586062341868162919547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12535169329959854142283669 587586062341868162919547)
        ·
          refine ⟨881379093512802244379321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587586062341868162919547 881379093512802244379321)
          ·
            refine ⟨661034320134601683284491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881379093512802244379321 661034320134601683284491)
            ·
              refine ⟨991551480201902524926737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661034320134601683284491 991551480201902524926737)
              ·
                refine ⟨743663610151426893695053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 991551480201902524926737 743663610151426893695053)
                ·
                  refine ⟨278873853806785085135645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743663610151426893695053 278873853806785085135645)
                  ·
                    rfl

theorem cell20_610993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_610993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610993 prefixEnd_610993 := by exact prefixLift 610993
  have htrace : WordTrace (prefixWord ++ tailWord_610993) baseStart_610993 baseEnd_610993 := by
    simpa [prefixWord, tailWord_610993, baseEnd_610993] using wordTrace_append hprefix tailTrace_610993
  have hstable : (prefixWord ++ tailWord_610993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610993).length < 2 ^ (prefixWord ++ tailWord_610993).sum := by decide
  have hdescent : baseEnd_610993 < baseStart_610993 := by decide
  rcases family_descends (prefixWord ++ tailWord_610993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_610997 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_610997 : Nat := 118140960795 + 610997 * 2 ^ 59
def prefixEnd_610997 : Nat := 4983230072969 + 3 ^ 40 * 610997 * 2
def baseEnd_610997 : Nat := 278875679515778849002295

theorem tailTrace_610997 : CollatzResearch.WordTrace tailWord_610997 prefixEnd_610997 278875679515778849002295 := by
  unfold tailWord_610997
  simp only [CollatzResearch.WordTrace]
  refine ⟨22284891367469693824983245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14856594244979795883322163 22284891367469693824983245)
  ·
    refine ⟨8356834262801135184368717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22284891367469693824983245 8356834262801135184368717)
    ·
      refine ⟨3133812848550425694138269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8356834262801135184368717 3133812848550425694138269)
      ·
        refine ⟨1175179818206409635301851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3133812848550425694138269 1175179818206409635301851)
        ·
          refine ⟨1762769727309614452952777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175179818206409635301851 1762769727309614452952777)
          ·
            refine ⟨1322077295482210839714583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762769727309614452952777 1322077295482210839714583)
            ·
              refine ⟨1983115943223316259571875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322077295482210839714583 1983115943223316259571875)
              ·
                refine ⟨2974673914834974389357813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983115943223316259571875 2974673914834974389357813)
                ·
                  refine ⟨278875679515778849002295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2974673914834974389357813 278875679515778849002295)
                  ·
                    rfl

theorem cell20_610997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_610997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_610997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_610997 prefixEnd_610997 := by exact prefixLift 610997
  have htrace : WordTrace (prefixWord ++ tailWord_610997) baseStart_610997 baseEnd_610997 := by
    simpa [prefixWord, tailWord_610997, baseEnd_610997] using wordTrace_append hprefix tailTrace_610997
  have hstable : (prefixWord ++ tailWord_610997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_610997).length < 2 ^ (prefixWord ++ tailWord_610997).sum := by decide
  have hdescent : baseEnd_610997 < baseStart_610997 := by decide
  rcases family_descends (prefixWord ++ tailWord_610997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611004 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_611004 : Nat := 118140960795 + 611004 * 2 ^ 59
def prefixEnd_611004 : Nat := 4983230072969 + 3 ^ 40 * 611004 * 2
def baseEnd_611004 : Nat := 278878874506517935768933

theorem tailTrace_611004 : CollatzResearch.WordTrace tailWord_611004 prefixEnd_611004 278878874506517935768933 := by
  unfold tailWord_611004
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142573339222167010244033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14856764452296222680325377 11142573339222167010244033)
  ·
    refine ⟨8356930004416625257683025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11142573339222167010244033 8356930004416625257683025)
    ·
      refine ⟨6267697503312468943262269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8356930004416625257683025 6267697503312468943262269)
      ·
        refine ⟨2350386563742175853723351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6267697503312468943262269 2350386563742175853723351)
        ·
          refine ⟨3525579845613263780585027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350386563742175853723351 3525579845613263780585027)
          ·
            refine ⟨5288369768419895670877541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525579845613263780585027 5288369768419895670877541)
            ·
              refine ⟨991569331578730438289539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5288369768419895670877541 991569331578730438289539)
              ·
                refine ⟨1487353997368095657434309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991569331578730438289539 1487353997368095657434309)
                ·
                  refine ⟨278878874506517935768933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487353997368095657434309 278878874506517935768933)
                  ·
                    rfl

theorem cell20_611004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_611004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611004 prefixEnd_611004 := by exact prefixLift 611004
  have htrace : WordTrace (prefixWord ++ tailWord_611004) baseStart_611004 baseEnd_611004 := by
    simpa [prefixWord, tailWord_611004, baseEnd_611004] using wordTrace_append hprefix tailTrace_611004
  have hstable : (prefixWord ++ tailWord_611004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611004).length < 2 ^ (prefixWord ++ tailWord_611004).sum := by decide
  have hdescent : baseEnd_611004 < baseStart_611004 := by decide
  rcases family_descends (prefixWord ++ tailWord_611004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611025 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_611025 : Nat := 118140960795 + 611025 * 2 ^ 59
def prefixEnd_611025 : Nat := 4983230072969 + 3 ^ 40 * 611025 * 2
def baseEnd_611025 : Nat := 278888459478735196068847

theorem tailTrace_611025 : CollatzResearch.WordTrace tailWord_611025 prefixEnd_611025 278888459478735196068847 := by
  unfold tailWord_611025
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285912611368254607002529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14857275074245503071335019 22285912611368254607002529)
  ·
    refine ⟨16714434458526190955251897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22285912611368254607002529 16714434458526190955251897)
    ·
      refine ⟨12535825843894643216438923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16714434458526190955251897 12535825843894643216438923)
      ·
        refine ⟨18803738765841964824658385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12535825843894643216438923 18803738765841964824658385)
        ·
          refine ⟨14102804074381473618493789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18803738765841964824658385 14102804074381473618493789)
          ·
            refine ⟨5288551527893052606935171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14102804074381473618493789 5288551527893052606935171)
            ·
              refine ⟨7932827291839578910402757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288551527893052606935171 7932827291839578910402757)
              ·
                refine ⟨1487405117219921045700517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7932827291839578910402757 1487405117219921045700517)
                ·
                  refine ⟨278888459478735196068847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487405117219921045700517 278888459478735196068847)
                  ·
                    rfl

theorem cell20_611025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_611025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611025 prefixEnd_611025 := by exact prefixLift 611025
  have htrace : WordTrace (prefixWord ++ tailWord_611025) baseStart_611025 baseEnd_611025 := by
    simpa [prefixWord, tailWord_611025, baseEnd_611025] using wordTrace_append hprefix tailTrace_611025
  have hstable : (prefixWord ++ tailWord_611025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611025).length < 2 ^ (prefixWord ++ tailWord_611025).sum := by decide
  have hdescent : baseEnd_611025 < baseStart_611025 := by decide
  rcases family_descends (prefixWord ++ tailWord_611025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611028 : List Nat := [2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_611028 : Nat := 118140960795 + 611028 * 2 ^ 59
def prefixEnd_611028 : Nat := 4983230072969 + 3 ^ 40 * 611028 * 2
def baseEnd_611028 : Nat := 92963276253493506322945

theorem tailTrace_611028 : CollatzResearch.WordTrace tailWord_611028 prefixEnd_611028 92963276253493506322945 := by
  unfold tailWord_611028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143011015178693059680869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14857348020238257412907825 11143011015178693059680869)
  ·
    refine ⟨2089314565346004948690163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11143011015178693059680869 2089314565346004948690163)
    ·
      refine ⟨3133971848019007423035245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2089314565346004948690163 3133971848019007423035245)
      ·
        refine ⟨1175239443007127783638217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3133971848019007423035245 1175239443007127783638217)
        ·
          refine ⟨881429582255345837728663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1175239443007127783638217 881429582255345837728663)
          ·
            refine ⟨1322144373383018756592995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881429582255345837728663 1322144373383018756592995)
            ·
              refine ⟨1983216560074528134889493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322144373383018756592995 1983216560074528134889493)
              ·
                refine ⟨92963276253493506322945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1983216560074528134889493 92963276253493506322945)
                ·
                  rfl

theorem cell20_611028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_611028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611028 prefixEnd_611028 := by exact prefixLift 611028
  have htrace : WordTrace (prefixWord ++ tailWord_611028) baseStart_611028 baseEnd_611028 := by
    simpa [prefixWord, tailWord_611028, baseEnd_611028] using wordTrace_append hprefix tailTrace_611028
  have hstable : (prefixWord ++ tailWord_611028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611028).length < 2 ^ (prefixWord ++ tailWord_611028).sum := by decide
  have hdescent : baseEnd_611028 < baseStart_611028 := by decide
  rcases family_descends (prefixWord ++ tailWord_611028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611056 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_611056 : Nat := 118140960795 + 611056 * 2 ^ 59
def prefixEnd_611056 : Nat := 4983230072969 + 3 ^ 40 * 611056 * 2
def baseEnd_611056 : Nat := 278902608723436866035387

theorem tailTrace_611056 : CollatzResearch.WordTrace tailWord_611056 prefixEnd_611056 278902608723436866035387 := by
  unfold tailWord_611056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143521637127973450690511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14858028849503964600920681 11143521637127973450690511)
  ·
    refine ⟨16715282455691960176035767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11143521637127973450690511 16715282455691960176035767)
    ·
      refine ⟨25072923683537940264053651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715282455691960176035767 25072923683537940264053651)
      ·
        refine ⟨37609385525306910396080477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25072923683537940264053651 37609385525306910396080477)
        ·
          refine ⟨14103519571990091398530179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37609385525306910396080477 14103519571990091398530179)
          ·
            refine ⟨21155279357985137097795269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14103519571990091398530179 21155279357985137097795269)
            ·
              refine ⟨3966614879622213205836613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21155279357985137097795269 3966614879622213205836613)
              ·
                refine ⟨743740289929164976094365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3966614879622213205836613 743740289929164976094365)
                ·
                  refine ⟨278902608723436866035387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743740289929164976094365 278902608723436866035387)
                  ·
                    rfl

theorem cell20_611056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_611056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611056 prefixEnd_611056 := by exact prefixLift 611056
  have htrace : WordTrace (prefixWord ++ tailWord_611056) baseStart_611056 baseEnd_611056 := by
    simpa [prefixWord, tailWord_611056, baseEnd_611056] using wordTrace_append hprefix tailTrace_611056
  have hstable : (prefixWord ++ tailWord_611056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611056).length < 2 ^ (prefixWord ++ tailWord_611056).sum := by decide
  have hdescent : baseEnd_611056 < baseStart_611056 := by decide
  rcases family_descends (prefixWord ++ tailWord_611056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611108 : List Nat := [2, 3, 1, 3, 11]
def baseStart_611108 : Nat := 118140960795 + 611108 * 2 ^ 59
def prefixEnd_611108 : Nat := 4983230072969 + 3 ^ 40 * 611108 * 2
def baseEnd_611108 : Nat := 3443535098029083904961

theorem tailTrace_611108 : CollatzResearch.WordTrace tailWord_611108 prefixEnd_611108 3443535098029083904961 := by
  unfold tailWord_611108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11144469935033779891136989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14859293246711706521515985 11144469935033779891136989)
  ·
    refine ⟨4179176225637667459176371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11144469935033779891136989 4179176225637667459176371)
    ·
      refine ⟨6268764338456501188764557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179176225637667459176371 6268764338456501188764557)
      ·
        refine ⟨2350786626921187945786709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6268764338456501188764557 2350786626921187945786709)
        ·
          refine ⟨3443535098029083904961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2350786626921187945786709 3443535098029083904961)
          ·
            rfl

theorem cell20_611108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 11].length) (baseStart_611108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611108 prefixEnd_611108 := by exact prefixLift 611108
  have htrace : WordTrace (prefixWord ++ tailWord_611108) baseStart_611108 baseEnd_611108 := by
    simpa [prefixWord, tailWord_611108, baseEnd_611108] using wordTrace_append hprefix tailTrace_611108
  have hstable : (prefixWord ++ tailWord_611108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611108).length < 2 ^ (prefixWord ++ tailWord_611108).sum := by decide
  have hdescent : baseEnd_611108 < baseStart_611108 := by decide
  rcases family_descends (prefixWord ++ tailWord_611108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611125 : List Nat := [1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_611125 : Nat := 118140960795 + 611125 * 2 ^ 59
def prefixEnd_611125 : Nat := 4983230072969 + 3 ^ 40 * 611125 * 2
def baseEnd_611125 : Nat := 92978034067859764245035

theorem tailTrace_611125 : CollatzResearch.WordTrace tailWord_611125 prefixEnd_611125 92978034067859764245035 := by
  unfold tailWord_611125
  simp only [CollatzResearch.WordTrace]
  refine ⟨22289559911005971685642829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14859706607337314457095219 22289559911005971685642829)
  ·
    refine ⟨8358584966627239382116061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22289559911005971685642829 8358584966627239382116061)
    ·
      refine ⟨3134469362485214768293523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8358584966627239382116061 3134469362485214768293523)
      ·
        refine ⟨4701704043727822152440285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3134469362485214768293523 4701704043727822152440285)
        ·
          refine ⟨1763139016397933307165107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4701704043727822152440285 1763139016397933307165107)
          ·
            refine ⟨2644708524596899960747661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763139016397933307165107 2644708524596899960747661)
            ·
              refine ⟨991765696723837485280373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2644708524596899960747661 991765696723837485280373)
              ·
                refine ⟨92978034067859764245035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 991765696723837485280373 92978034067859764245035)
                ·
                  rfl

theorem cell20_611125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_611125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611125 prefixEnd_611125 := by exact prefixLift 611125
  have htrace : WordTrace (prefixWord ++ tailWord_611125) baseStart_611125 baseEnd_611125 := by
    simpa [prefixWord, tailWord_611125, baseEnd_611125] using wordTrace_append hprefix tailTrace_611125
  have hstable : (prefixWord ++ tailWord_611125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611125).length < 2 ^ (prefixWord ++ tailWord_611125).sum := by decide
  have hdescent : baseEnd_611125 < baseStart_611125 := by decide
  rcases family_descends (prefixWord ++ tailWord_611125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611139 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_611139 : Nat := 118140960795 + 611139 * 2 ^ 59
def prefixEnd_611139 : Nat := 4983230072969 + 3 ^ 40 * 611139 * 2
def baseEnd_611139 : Nat := 278940492185057466268381

theorem tailTrace_611139 : CollatzResearch.WordTrace tailWord_611139 prefixEnd_611139 278940492185057466268381 := by
  unfold tailWord_611139
  simp only [CollatzResearch.WordTrace]
  refine ⟨22290070532955252076652471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14860047021970168051101647 22290070532955252076652471)
  ·
    refine ⟨33435105799432878114978707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22290070532955252076652471 33435105799432878114978707)
    ·
      refine ⟨50152658699149317172468061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33435105799432878114978707 50152658699149317172468061)
      ·
        refine ⟨18807247012180993939675523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50152658699149317172468061 18807247012180993939675523)
        ·
          refine ⟨28210870518271490909513285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18807247012180993939675523 28210870518271490909513285)
          ·
            refine ⟨5289538222175904545533741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28210870518271490909513285 5289538222175904545533741)
            ·
              refine ⟨1983576833315964204575153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5289538222175904545533741 1983576833315964204575153)
              ·
                refine ⟨1487682624986973153431365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983576833315964204575153 1487682624986973153431365)
                ·
                  refine ⟨278940492185057466268381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487682624986973153431365 278940492185057466268381)
                  ·
                    rfl

theorem cell20_611139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_611139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611139 prefixEnd_611139 := by exact prefixLift 611139
  have htrace : WordTrace (prefixWord ++ tailWord_611139) baseStart_611139 baseEnd_611139 := by
    simpa [prefixWord, tailWord_611139, baseEnd_611139] using wordTrace_append hprefix tailTrace_611139
  have hstable : (prefixWord ++ tailWord_611139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611139).length < 2 ^ (prefixWord ++ tailWord_611139).sum := by decide
  have hdescent : baseEnd_611139 < baseStart_611139 := by decide
  rcases family_descends (prefixWord ++ tailWord_611139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611208 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_611208 : Nat := 118140960795 + 611208 * 2 ^ 59
def prefixEnd_611208 : Nat := 4983230072969 + 3 ^ 40 * 611208 * 2
def baseEnd_611208 : Nat := 278971985665199892968099

theorem tailTrace_611208 : CollatzResearch.WordTrace tailWord_611208 prefixEnd_611208 278971985665199892968099 := by
  unfold tailWord_611208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146293584852638430457139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14861724779803517907276185 11146293584852638430457139)
  ·
    refine ⟨16719440377278957645685709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11146293584852638430457139 16719440377278957645685709)
    ·
      refine ⟨6269790141479609117132141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16719440377278957645685709 6269790141479609117132141)
      ·
        refine ⟨2351171303054853418924553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6269790141479609117132141 2351171303054853418924553)
        ·
          refine ⟨1763378477291140064193415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351171303054853418924553 1763378477291140064193415)
          ·
            refine ⟨2645067715936710096290123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763378477291140064193415 2645067715936710096290123)
            ·
              refine ⟨3967601573905065144435185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645067715936710096290123 3967601573905065144435185)
              ·
                refine ⟨2975701180428798858326389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967601573905065144435185 2975701180428798858326389)
                ·
                  refine ⟨278971985665199892968099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2975701180428798858326389 278971985665199892968099)
                  ·
                    rfl

theorem cell20_611208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_611208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611208 prefixEnd_611208 := by exact prefixLift 611208
  have htrace : WordTrace (prefixWord ++ tailWord_611208) baseStart_611208 baseEnd_611208 := by
    simpa [prefixWord, tailWord_611208, baseEnd_611208] using wordTrace_append hprefix tailTrace_611208
  have hstable : (prefixWord ++ tailWord_611208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611208).length < 2 ^ (prefixWord ++ tailWord_611208).sum := by decide
  have hdescent : baseEnd_611208 < baseStart_611208 := by decide
  rcases family_descends (prefixWord ++ tailWord_611208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611218 : List Nat := [3, 2, 3, 2, 2, 2, 6]
def baseStart_611218 : Nat := 118140960795 + 611218 * 2 ^ 59
def prefixEnd_611218 : Nat := 4983230072969 + 3 ^ 40 * 611218 * 2
def baseEnd_611218 : Nat := 30997394437520478070525

theorem tailTrace_611218 : CollatzResearch.WordTrace tailWord_611218 prefixEnd_611218 30997394437520478070525 := by
  unfold tailWord_611218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573237974917262142194577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14861967933112699045852205 5573237974917262142194577)
  ·
    refine ⟨4179928481187946606645933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5573237974917262142194577 4179928481187946606645933)
    ·
      refine ⟨1567473180445479977492225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4179928481187946606645933 1567473180445479977492225)
      ·
        refine ⟨1175604885334109983119169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567473180445479977492225 1175604885334109983119169)
        ·
          refine ⟨881703664000582487339377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1175604885334109983119169 881703664000582487339377)
          ·
            refine ⟨661277748000436865504533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881703664000582487339377 661277748000436865504533)
            ·
              refine ⟨30997394437520478070525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 661277748000436865504533 30997394437520478070525)
              ·
                rfl

theorem cell20_611218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_611218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611218 prefixEnd_611218 := by exact prefixLift 611218
  have htrace : WordTrace (prefixWord ++ tailWord_611218) baseStart_611218 baseEnd_611218 := by
    simpa [prefixWord, tailWord_611218, baseEnd_611218] using wordTrace_append hprefix tailTrace_611218
  have hstable : (prefixWord ++ tailWord_611218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611218).length < 2 ^ (prefixWord ++ tailWord_611218).sum := by decide
  have hdescent : baseEnd_611218 < baseStart_611218 := by decide
  rcases family_descends (prefixWord ++ tailWord_611218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611228 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_611228 : Nat := 118140960795 + 611228 * 2 ^ 59
def prefixEnd_611228 : Nat := 4983230072969 + 3 ^ 40 * 611228 * 2
def baseEnd_611228 : Nat := 278981114210168712301351

theorem tailTrace_611228 : CollatzResearch.WordTrace tailWord_611228 prefixEnd_611228 278981114210168712301351 := by
  unfold tailWord_611228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146658314816410138321169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14862211086421880184428225 11146658314816410138321169)
  ·
    refine ⟨8359993736112307603740877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11146658314816410138321169 8359993736112307603740877)
    ·
      refine ⟨3134997651042115351402829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8359993736112307603740877 3134997651042115351402829)
      ·
        refine ⟨1175624119140793256776061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3134997651042115351402829 1175624119140793256776061)
        ·
          refine ⟨440859044677797471291023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1175624119140793256776061 440859044677797471291023)
          ·
            refine ⟨661288567016696206936535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440859044677797471291023 661288567016696206936535)
            ·
              refine ⟨991932850525044310404803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661288567016696206936535 991932850525044310404803)
              ·
                refine ⟨1487899275787566465607205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991932850525044310404803 1487899275787566465607205)
                ·
                  refine ⟨278981114210168712301351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487899275787566465607205 278981114210168712301351)
                  ·
                    rfl

theorem cell20_611228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_611228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611228 prefixEnd_611228 := by exact prefixLift 611228
  have htrace : WordTrace (prefixWord ++ tailWord_611228) baseStart_611228 baseEnd_611228 := by
    simpa [prefixWord, tailWord_611228, baseEnd_611228] using wordTrace_append hprefix tailTrace_611228
  have hstable : (prefixWord ++ tailWord_611228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611228).length < 2 ^ (prefixWord ++ tailWord_611228).sum := by decide
  have hdescent : baseEnd_611228 < baseStart_611228 := by decide
  rcases family_descends (prefixWord ++ tailWord_611228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611232 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_611232 : Nat := 118140960795 + 611232 * 2 ^ 59
def prefixEnd_611232 : Nat := 4983230072969 + 3 ^ 40 * 611232 * 2
def baseEnd_611232 : Nat := 278982939919162476168001

theorem tailTrace_611232 : CollatzResearch.WordTrace tailWord_611232 prefixEnd_611232 278982939919162476168001 := by
  unfold tailWord_611232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146731260809164479893975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14862308347745552639858633 11146731260809164479893975)
  ·
    refine ⟨16720096891213746719840963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11146731260809164479893975 16720096891213746719840963)
    ·
      refine ⟨25080145336820620079761445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16720096891213746719840963 25080145336820620079761445)
      ·
        refine ⟨4702527250653866264955271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25080145336820620079761445 4702527250653866264955271)
        ·
          refine ⟨7053790875980799397432907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4702527250653866264955271 7053790875980799397432907)
          ·
            refine ⟨10580686313971199096149361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053790875980799397432907 10580686313971199096149361)
            ·
              refine ⟨7935514735478399322112021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580686313971199096149361 7935514735478399322112021)
              ·
                refine ⟨371977253225549968224001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7935514735478399322112021 371977253225549968224001)
                ·
                  refine ⟨278982939919162476168001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371977253225549968224001 278982939919162476168001)
                  ·
                    rfl

theorem cell20_611232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_611232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611232 prefixEnd_611232 := by exact prefixLift 611232
  have htrace : WordTrace (prefixWord ++ tailWord_611232) baseStart_611232 baseEnd_611232 := by
    simpa [prefixWord, tailWord_611232, baseEnd_611232] using wordTrace_append hprefix tailTrace_611232
  have hstable : (prefixWord ++ tailWord_611232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611232).length < 2 ^ (prefixWord ++ tailWord_611232).sum := by decide
  have hdescent : baseEnd_611232 < baseStart_611232 := by decide
  rcases family_descends (prefixWord ++ tailWord_611232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611253 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_611253 : Nat := 118140960795 + 611253 * 2 ^ 59
def prefixEnd_611253 : Nat := 4983230072969 + 3 ^ 40 * 611253 * 2
def baseEnd_611253 : Nat := 278992524891379736467915

theorem tailTrace_611253 : CollatzResearch.WordTrace tailWord_611253 prefixEnd_611253 278992524891379736467915 := by
  unfold tailWord_611253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22294228454542249546302413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14862818969694833030868275 22294228454542249546302413)
  ·
    refine ⟨8360335670453343579863405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22294228454542249546302413 8360335670453343579863405)
    ·
      refine ⟨3135125876420003842448777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8360335670453343579863405 3135125876420003842448777)
      ·
        refine ⟨2351344407315002881836583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3135125876420003842448777 2351344407315002881836583)
        ·
          refine ⟨3527016610972504322754875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351344407315002881836583 3527016610972504322754875)
          ·
            refine ⟨5290524916458756484132313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527016610972504322754875 5290524916458756484132313)
            ·
              refine ⟨3967893687344067363099235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290524916458756484132313 3967893687344067363099235)
              ·
                refine ⟨5951840531016101044648853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967893687344067363099235 5951840531016101044648853)
                ·
                  refine ⟨278992524891379736467915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5951840531016101044648853 278992524891379736467915)
                  ·
                    rfl

theorem cell20_611253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_611253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611253 prefixEnd_611253 := by exact prefixLift 611253
  have htrace : WordTrace (prefixWord ++ tailWord_611253) baseStart_611253 baseEnd_611253 := by
    simpa [prefixWord, tailWord_611253, baseEnd_611253] using wordTrace_append hprefix tailTrace_611253
  have hstable : (prefixWord ++ tailWord_611253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611253).length < 2 ^ (prefixWord ++ tailWord_611253).sum := by decide
  have hdescent : baseEnd_611253 < baseStart_611253 := by decide
  rcases family_descends (prefixWord ++ tailWord_611253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611336 : List Nat := [2, 1, 3, 2, 1, 4, 7]
def baseStart_611336 : Nat := 118140960795 + 611336 * 2 ^ 59
def prefixEnd_611336 : Nat := 4983230072969 + 3 ^ 40 * 611336 * 2
def baseEnd_611336 : Nat := 31003378705888926300101

theorem tailTrace_611336 : CollatzResearch.WordTrace tailWord_611336 prefixEnd_611336 31003378705888926300101 := by
  unfold tailWord_611336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148627856620777360786931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14864837142161036481049241 11148627856620777360786931)
  ·
    refine ⟨16722941784931166041180397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11148627856620777360786931 16722941784931166041180397)
    ·
      refine ⟨6271103169349187265442649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16722941784931166041180397 6271103169349187265442649)
      ·
        refine ⟨4703327377011890449081987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6271103169349187265442649 4703327377011890449081987)
        ·
          refine ⟨7054991065517835673622981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703327377011890449081987 7054991065517835673622981)
          ·
            refine ⟨1322810824784594188804309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7054991065517835673622981 1322810824784594188804309)
            ·
              refine ⟨31003378705888926300101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1322810824784594188804309 31003378705888926300101)
              ·
                rfl

theorem cell20_611336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_611336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611336 prefixEnd_611336 := by exact prefixLift 611336
  have htrace : WordTrace (prefixWord ++ tailWord_611336) baseStart_611336 baseEnd_611336 := by
    simpa [prefixWord, tailWord_611336, baseEnd_611336] using wordTrace_append hprefix tailTrace_611336
  have hstable : (prefixWord ++ tailWord_611336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611336).length < 2 ^ (prefixWord ++ tailWord_611336).sum := by decide
  have hdescent : baseEnd_611336 < baseStart_611336 := by decide
  rcases family_descends (prefixWord ++ tailWord_611336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611339 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_611339 : Nat := 118140960795 + 611339 * 2 ^ 59
def prefixEnd_611339 : Nat := 4983230072969 + 3 ^ 40 * 611339 * 2
def baseEnd_611339 : Nat := 279031777634745659600897

theorem tailTrace_611339 : CollatzResearch.WordTrace tailWord_611339 prefixEnd_611339 279031777634745659600897 := by
  unfold tailWord_611339
  simp only [CollatzResearch.WordTrace]
  refine ⟨22297365132230686233933071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14864910088153790822622047 22297365132230686233933071)
  ·
    refine ⟨33446047698346029350899607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22297365132230686233933071 33446047698346029350899607)
    ·
      refine ⟨50169071547519044026349411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33446047698346029350899607 50169071547519044026349411)
      ·
        refine ⟨75253607321278566039524117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50169071547519044026349411 75253607321278566039524117)
        ·
          refine ⟨3527512843184932783102693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75253607321278566039524117 3527512843184932783102693)
          ·
            refine ⟨661408658097174896831755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3527512843184932783102693 661408658097174896831755)
            ·
              refine ⟨992112987145762345247633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661408658097174896831755 992112987145762345247633)
              ·
                refine ⟨744084740359321758935725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992112987145762345247633 744084740359321758935725)
                ·
                  refine ⟨279031777634745659600897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744084740359321758935725 279031777634745659600897)
                  ·
                    rfl

theorem cell20_611339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_611339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611339 prefixEnd_611339 := by exact prefixLift 611339
  have htrace : WordTrace (prefixWord ++ tailWord_611339) baseStart_611339 baseEnd_611339 := by
    simpa [prefixWord, tailWord_611339, baseEnd_611339] using wordTrace_append hprefix tailTrace_611339
  have hstable : (prefixWord ++ tailWord_611339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611339).length < 2 ^ (prefixWord ++ tailWord_611339).sum := by decide
  have hdescent : baseEnd_611339 < baseStart_611339 := by decide
  rcases family_descends (prefixWord ++ tailWord_611339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611356 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_611356 : Nat := 118140960795 + 611356 * 2 ^ 59
def prefixEnd_611356 : Nat := 4983230072969 + 3 ^ 40 * 611356 * 2
def baseEnd_611356 : Nat := 279039536897969156034161

theorem tailTrace_611356 : CollatzResearch.WordTrace tailWord_611356 prefixEnd_611356 279039536897969156034161 := by
  unfold tailWord_611356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148992586584549068650961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14865323448779398758201281 11148992586584549068650961)
  ·
    refine ⟨8361744439938411801488221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11148992586584549068650961 8361744439938411801488221)
    ·
      refine ⟨3135654164976904425558083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8361744439938411801488221 3135654164976904425558083)
      ·
        refine ⟨4703481247465356638337125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135654164976904425558083 4703481247465356638337125)
        ·
          refine ⟨881902733899754369688211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4703481247465356638337125 881902733899754369688211)
          ·
            refine ⟨1322854100849631554532317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881902733899754369688211 1322854100849631554532317)
            ·
              refine ⟨496070287818611832949619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1322854100849631554532317 496070287818611832949619)
              ·
                refine ⟨744105431727917749424429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496070287818611832949619 744105431727917749424429)
                ·
                  refine ⟨279039536897969156034161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744105431727917749424429 279039536897969156034161)
                  ·
                    rfl

theorem cell20_611356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_611356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611356 prefixEnd_611356 := by exact prefixLift 611356
  have htrace : WordTrace (prefixWord ++ tailWord_611356) baseStart_611356 baseEnd_611356 := by
    simpa [prefixWord, tailWord_611356, baseEnd_611356] using wordTrace_append hprefix tailTrace_611356
  have hstable : (prefixWord ++ tailWord_611356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611356).length < 2 ^ (prefixWord ++ tailWord_611356).sum := by decide
  have hdescent : baseEnd_611356 < baseStart_611356 := by decide
  rcases family_descends (prefixWord ++ tailWord_611356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611380 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_611380 : Nat := 118140960795 + 611380 * 2 ^ 59
def prefixEnd_611380 : Nat := 4983230072969 + 3 ^ 40 * 611380 * 2
def baseEnd_611380 : Nat := 279050491151931739234063

theorem tailTrace_611380 : CollatzResearch.WordTrace tailWord_611380 prefixEnd_611380 279050491151931739234063 := by
  unfold tailWord_611380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149430262541075118087797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14865907016721433490783729 11149430262541075118087797)
  ·
    refine ⟨1045259087113225792320731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11149430262541075118087797 1045259087113225792320731)
    ·
      refine ⟨1567888630669838688481097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045259087113225792320731 1567888630669838688481097)
      ·
        refine ⟨1175916473002379016360823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567888630669838688481097 1175916473002379016360823)
        ·
          refine ⟨1763874709503568524541235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175916473002379016360823 1763874709503568524541235)
          ·
            refine ⟨2645812064255352786811853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763874709503568524541235 2645812064255352786811853)
            ·
              refine ⟨992179524095757295054445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2645812064255352786811853 992179524095757295054445)
              ·
                refine ⟨372067321535908985645417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 992179524095757295054445 372067321535908985645417)
                ·
                  refine ⟨279050491151931739234063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372067321535908985645417 279050491151931739234063)
                  ·
                    rfl

theorem cell20_611380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_611380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611380 prefixEnd_611380 := by exact prefixLift 611380
  have htrace : WordTrace (prefixWord ++ tailWord_611380) baseStart_611380 baseEnd_611380 := by
    simpa [prefixWord, tailWord_611380, baseEnd_611380] using wordTrace_append hprefix tailTrace_611380
  have hstable : (prefixWord ++ tailWord_611380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611380).length < 2 ^ (prefixWord ++ tailWord_611380).sum := by decide
  have hdescent : baseEnd_611380 < baseStart_611380 := by decide
  rcases family_descends (prefixWord ++ tailWord_611380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611412 : List Nat := [2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_611412 : Nat := 118140960795 + 611412 * 2 ^ 59
def prefixEnd_611412 : Nat := 4983230072969 + 3 ^ 40 * 611412 * 2
def baseEnd_611412 : Nat := 93021698941293950055755

theorem tailTrace_611412 : CollatzResearch.WordTrace tailWord_611412 prefixEnd_611412 93021698941293950055755 := by
  unfold tailWord_611412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150013830483109850670245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14866685107310813134226993 11150013830483109850670245)
  ·
    refine ⟨2090627593215583097000671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11150013830483109850670245 2090627593215583097000671)
    ·
      refine ⟨3135941389823374645501007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090627593215583097000671 3135941389823374645501007)
      ·
        refine ⟨4703912084735061968251511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135941389823374645501007 4703912084735061968251511)
        ·
          refine ⟨7055868127102592952377267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703912084735061968251511 7055868127102592952377267)
          ·
            refine ⟨10583802190653889428565901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055868127102592952377267 10583802190653889428565901)
            ·
              refine ⟨3968925821495208535712213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10583802190653889428565901 3968925821495208535712213)
              ·
                refine ⟨93021698941293950055755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3968925821495208535712213 93021698941293950055755)
                ·
                  rfl

theorem cell20_611412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_611412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611412 prefixEnd_611412 := by exact prefixLift 611412
  have htrace : WordTrace (prefixWord ++ tailWord_611412) baseStart_611412 baseEnd_611412 := by
    simpa [prefixWord, tailWord_611412, baseEnd_611412] using wordTrace_append hprefix tailTrace_611412
  have hstable : (prefixWord ++ tailWord_611412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611412).length < 2 ^ (prefixWord ++ tailWord_611412).sum := by decide
  have hdescent : baseEnd_611412 < baseStart_611412 := by decide
  rcases family_descends (prefixWord ++ tailWord_611412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611549 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 2]
def baseStart_611549 : Nat := 118140960795 + 611549 * 2 ^ 59
def prefixEnd_611549 : Nat := 4983230072969 + 3 ^ 40 * 611549 * 2
def baseEnd_611549 : Nat := 279127627356918262600039

theorem tailTrace_611549 : CollatzResearch.WordTrace tailWord_611549 prefixEnd_611549 279127627356918262600039 := by
  unfold tailWord_611549
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305024461469892099077701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14870016307646594732718467 22305024461469892099077701)
  ·
    refine ⟨4182192086525604768577069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22305024461469892099077701 4182192086525604768577069)
    ·
      refine ⟨1568322032447101788216401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4182192086525604768577069 1568322032447101788216401)
      ·
        refine ⟨1176241524335326341162301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568322032447101788216401 1176241524335326341162301)
        ·
          refine ⟨441090571625747377935863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1176241524335326341162301 441090571625747377935863)
          ·
            refine ⟨661635857438621066903795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441090571625747377935863 661635857438621066903795)
            ·
              refine ⟨992453786157931600355693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661635857438621066903795 992453786157931600355693)
              ·
                refine ⟨372170169809224350133385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 992453786157931600355693 372170169809224350133385)
                ·
                  refine ⟨279127627356918262600039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372170169809224350133385 279127627356918262600039)
                  ·
                    rfl

theorem cell20_611549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_611549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611549 prefixEnd_611549 := by exact prefixLift 611549
  have htrace : WordTrace (prefixWord ++ tailWord_611549) baseStart_611549 baseEnd_611549 := by
    simpa [prefixWord, tailWord_611549, baseEnd_611549] using wordTrace_append hprefix tailTrace_611549
  have hstable : (prefixWord ++ tailWord_611549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611549).length < 2 ^ (prefixWord ++ tailWord_611549).sum := by decide
  have hdescent : baseEnd_611549 < baseStart_611549 := by decide
  rcases family_descends (prefixWord ++ tailWord_611549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611553 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 2]
def baseStart_611553 : Nat := 118140960795 + 611553 * 2 ^ 59
def prefixEnd_611553 : Nat := 4983230072969 + 3 ^ 40 * 611553 * 2
def baseEnd_611553 : Nat := 279129453065912026466689

theorem tailTrace_611553 : CollatzResearch.WordTrace tailWord_611553 prefixEnd_611553 279129453065912026466689 := by
  unfold tailWord_611553
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305170353455400782223313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14870113568970267188148875 22305170353455400782223313)
  ·
    refine ⟨16728877765091550586667485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22305170353455400782223313 16728877765091550586667485)
    ·
      refine ⟨6273329161909331470000307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16728877765091550586667485 6273329161909331470000307)
      ·
        refine ⟨9409993742863997205000461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273329161909331470000307 9409993742863997205000461)
        ·
          refine ⟨3528747653573998951875173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9409993742863997205000461 3528747653573998951875173)
          ·
            refine ⟨661640185045124803476595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3528747653573998951875173 661640185045124803476595)
            ·
              refine ⟨992460277567687205214893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661640185045124803476595 992460277567687205214893)
              ·
                refine ⟨372172604087882701955585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 992460277567687205214893 372172604087882701955585)
                ·
                  refine ⟨279129453065912026466689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372172604087882701955585 279129453065912026466689)
                  ·
                    rfl

theorem cell20_611553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_611553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611553 prefixEnd_611553 := by exact prefixLift 611553
  have htrace : WordTrace (prefixWord ++ tailWord_611553) baseStart_611553 baseEnd_611553 := by
    simpa [prefixWord, tailWord_611553, baseEnd_611553] using wordTrace_append hprefix tailTrace_611553
  have hstable : (prefixWord ++ tailWord_611553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611553).length < 2 ^ (prefixWord ++ tailWord_611553).sum := by decide
  have hdescent : baseEnd_611553 < baseStart_611553 := by decide
  rcases family_descends (prefixWord ++ tailWord_611553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611564 : List Nat := [2, 2, 1, 1, 2, 6, 6]
def baseStart_611564 : Nat := 118140960795 + 611564 * 2 ^ 59
def prefixEnd_611564 : Nat := 4983230072969 + 3 ^ 40 * 611564 * 2
def baseEnd_611564 : Nat := 31014941529516097455553

theorem tailTrace_611564 : CollatzResearch.WordTrace tailWord_611564 prefixEnd_611564 31014941529516097455553 := by
  unfold tailWord_611564
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152785778207774830436873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14870381037610366440582497 11152785778207774830436873)
  ·
    refine ⟨8364589333655831122827655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11152785778207774830436873 8364589333655831122827655)
    ·
      refine ⟨12546884000483746684241483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8364589333655831122827655 12546884000483746684241483)
      ·
        refine ⟨18820326000725620026362225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12546884000483746684241483 18820326000725620026362225)
        ·
          refine ⟨14115244500544215019771669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18820326000725620026362225 14115244500544215019771669)
          ·
            refine ⟨661652085963010079051797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14115244500544215019771669 661652085963010079051797)
            ·
              refine ⟨31014941529516097455553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 661652085963010079051797 31014941529516097455553)
              ·
                rfl

theorem cell20_611564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_611564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611564 prefixEnd_611564 := by exact prefixLift 611564
  have htrace : WordTrace (prefixWord ++ tailWord_611564) baseStart_611564 baseEnd_611564 := by
    simpa [prefixWord, tailWord_611564, baseEnd_611564] using wordTrace_append hprefix tailTrace_611564
  have hstable : (prefixWord ++ tailWord_611564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611564).length < 2 ^ (prefixWord ++ tailWord_611564).sum := by decide
  have hdescent : baseEnd_611564 < baseStart_611564 := by decide
  rcases family_descends (prefixWord ++ tailWord_611564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611570 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_611570 : Nat := 118140960795 + 611570 * 2 ^ 59
def prefixEnd_611570 : Nat := 4983230072969 + 3 ^ 40 * 611570 * 2
def baseEnd_611570 : Nat := 279137212329135522899953

theorem tailTrace_611570 : CollatzResearch.WordTrace tailWord_611570 prefixEnd_611570 279137212329135522899953 := by
  unfold tailWord_611570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576447598598453171398041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14870526929595875123728109 5576447598598453171398041)
  ·
    refine ⟨4182335698948839878548531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5576447598598453171398041 4182335698948839878548531)
    ·
      refine ⟨6273503548423259817822797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182335698948839878548531 6273503548423259817822797)
      ·
        refine ⟨2352563830658722431683549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6273503548423259817822797 2352563830658722431683549)
        ·
          refine ⟨882211436497020911881331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2352563830658722431683549 882211436497020911881331)
          ·
            refine ⟨1323317154745531367821997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882211436497020911881331 1323317154745531367821997)
            ·
              refine ⟨496243933029574262933249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1323317154745531367821997 496243933029574262933249)
              ·
                refine ⟨372182949772180697199937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496243933029574262933249 372182949772180697199937)
                ·
                  refine ⟨279137212329135522899953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372182949772180697199937 279137212329135522899953)
                  ·
                    rfl

theorem cell20_611570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_611570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611570 prefixEnd_611570 := by exact prefixLift 611570
  have htrace : WordTrace (prefixWord ++ tailWord_611570) baseStart_611570 baseEnd_611570 := by
    simpa [prefixWord, tailWord_611570, baseEnd_611570] using wordTrace_append hprefix tailTrace_611570
  have hstable : (prefixWord ++ tailWord_611570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611570).length < 2 ^ (prefixWord ++ tailWord_611570).sum := by decide
  have hdescent : baseEnd_611570 < baseStart_611570 := by decide
  rcases family_descends (prefixWord ++ tailWord_611570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611571 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_611571 : Nat := 118140960795 + 611571 * 2 ^ 59
def prefixEnd_611571 : Nat := 4983230072969 + 3 ^ 40 * 611571 * 2
def baseEnd_611571 : Nat := 279137668756383963866615

theorem tailTrace_611571 : CollatzResearch.WordTrace tailWord_611571 prefixEnd_611571 279137668756383963866615 := by
  unfold tailWord_611571
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305826867390189856378567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14870551244926793237585711 22305826867390189856378567)
  ·
    refine ⟨33458740301085284784567851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22305826867390189856378567 33458740301085284784567851)
    ·
      refine ⟨50188110451627927176851777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33458740301085284784567851 50188110451627927176851777)
      ·
        refine ⟨37641082838720945382638833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50188110451627927176851777 37641082838720945382638833)
        ·
          refine ⟨28230812129040709036979125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37641082838720945382638833 28230812129040709036979125)
          ·
            refine ⟨2646638637097566472216793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28230812129040709036979125 2646638637097566472216793)
            ·
              refine ⟨1984978977823174854162595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646638637097566472216793 1984978977823174854162595)
              ·
                refine ⟨2977468466734762281243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984978977823174854162595 2977468466734762281243893)
                ·
                  refine ⟨279137668756383963866615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2977468466734762281243893 279137668756383963866615)
                  ·
                    rfl

theorem cell20_611571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_611571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611571 prefixEnd_611571 := by exact prefixLift 611571
  have htrace : WordTrace (prefixWord ++ tailWord_611571) baseStart_611571 baseEnd_611571 := by
    simpa [prefixWord, tailWord_611571, baseEnd_611571] using wordTrace_append hprefix tailTrace_611571
  have hstable : (prefixWord ++ tailWord_611571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611571).length < 2 ^ (prefixWord ++ tailWord_611571).sum := by decide
  have hdescent : baseEnd_611571 < baseStart_611571 := by decide
  rcases family_descends (prefixWord ++ tailWord_611571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611685 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_611685 : Nat := 118140960795 + 611685 * 2 ^ 59
def prefixEnd_611685 : Nat := 4983230072969 + 3 ^ 40 * 611685 * 2
def baseEnd_611685 : Nat := 279189701462706234066149

theorem tailTrace_611685 : CollatzResearch.WordTrace tailWord_611685 prefixEnd_611685 279189701462706234066149 := by
  unfold tailWord_611685
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309984788977187326028509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14873323192651458217352339 22309984788977187326028509)
  ·
    refine ⟨8366244295866445247260691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22309984788977187326028509 8366244295866445247260691)
    ·
      refine ⟨12549366443799667870891037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8366244295866445247260691 12549366443799667870891037)
      ·
        refine ⟨4706012416424875451584139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12549366443799667870891037 4706012416424875451584139)
        ·
          refine ⟨7059018624637313177376209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706012416424875451584139 7059018624637313177376209)
          ·
            refine ⟨5294263968477984883032157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059018624637313177376209 5294263968477984883032157)
            ·
              refine ⟨1985348988179244331137059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5294263968477984883032157 1985348988179244331137059)
              ·
                refine ⟨2978023482268866496705589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985348988179244331137059 2978023482268866496705589)
                ·
                  refine ⟨279189701462706234066149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978023482268866496705589 279189701462706234066149)
                  ·
                    rfl

theorem cell20_611685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_611685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611685 prefixEnd_611685 := by exact prefixLift 611685
  have htrace : WordTrace (prefixWord ++ tailWord_611685) baseStart_611685 baseEnd_611685 := by
    simpa [prefixWord, tailWord_611685, baseEnd_611685] using wordTrace_append hprefix tailTrace_611685
  have hstable : (prefixWord ++ tailWord_611685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611685).length < 2 ^ (prefixWord ++ tailWord_611685).sum := by decide
  have hdescent : baseEnd_611685 < baseStart_611685 := by decide
  rcases family_descends (prefixWord ++ tailWord_611685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611688 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_611688 : Nat := 118140960795 + 611688 * 2 ^ 59
def prefixEnd_611688 : Nat := 4983230072969 + 3 ^ 40 * 611688 * 2
def baseEnd_611688 : Nat := 279191070744451556966137

theorem tailTrace_611688 : CollatzResearch.WordTrace tailWord_611688 prefixEnd_611688 279191070744451556966137 := by
  unfold tailWord_611688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155047103983159419193859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14873396138644212558925145 11155047103983159419193859)
  ·
    refine ⟨16732570655974739128790789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11155047103983159419193859 16732570655974739128790789)
    ·
      refine ⟨3137356997995263586648273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16732570655974739128790789 3137356997995263586648273)
      ·
        refine ⟨2353017748496447689986205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3137356997995263586648273 2353017748496447689986205)
        ·
          refine ⟨882381655686167883744827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2353017748496447689986205 882381655686167883744827)
          ·
            refine ⟨1323572483529251825617241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882381655686167883744827 1323572483529251825617241)
            ·
              refine ⟨992679362646938869212931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323572483529251825617241 992679362646938869212931)
              ·
                refine ⟨1489019043970408303819397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992679362646938869212931 1489019043970408303819397)
                ·
                  refine ⟨279191070744451556966137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489019043970408303819397 279191070744451556966137)
                  ·
                    rfl

theorem cell20_611688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_611688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611688 prefixEnd_611688 := by exact prefixLift 611688
  have htrace : WordTrace (prefixWord ++ tailWord_611688) baseStart_611688 baseEnd_611688 := by
    simpa [prefixWord, tailWord_611688, baseEnd_611688] using wordTrace_append hprefix tailTrace_611688
  have hstable : (prefixWord ++ tailWord_611688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611688).length < 2 ^ (prefixWord ++ tailWord_611688).sum := by decide
  have hdescent : baseEnd_611688 < baseStart_611688 := by decide
  rcases family_descends (prefixWord ++ tailWord_611688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611716 : List Nat := [2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_611716 : Nat := 118140960795 + 611716 * 2 ^ 59
def prefixEnd_611716 : Nat := 4983230072969 + 3 ^ 40 * 611716 * 2
def baseEnd_611716 : Nat := 93067950235802634677563

theorem tailTrace_611716 : CollatzResearch.WordTrace tailWord_611716 prefixEnd_611716 93067950235802634677563 := by
  unfold tailWord_611716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155557725932439810203501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14874076967909919746938001 11155557725932439810203501)
  ·
    refine ⟨4183334147224664928826313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11155557725932439810203501 4183334147224664928826313)
    ·
      refine ⟨3137500610418498696619735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4183334147224664928826313 3137500610418498696619735)
      ·
        refine ⟨4706250915627748044929603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3137500610418498696619735 4706250915627748044929603)
        ·
          refine ⟨7059376373441622067394405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706250915627748044929603 7059376373441622067394405)
          ·
            refine ⟨1323633070020304137636451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7059376373441622067394405 1323633070020304137636451)
            ·
              refine ⟨1985449605030456206454677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323633070020304137636451 1985449605030456206454677)
              ·
                refine ⟨93067950235802634677563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1985449605030456206454677 93067950235802634677563)
                ·
                  rfl

theorem cell20_611716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_611716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611716 prefixEnd_611716 := by exact prefixLift 611716
  have htrace : WordTrace (prefixWord ++ tailWord_611716) baseStart_611716 baseEnd_611716 := by
    simpa [prefixWord, tailWord_611716, baseEnd_611716] using wordTrace_append hprefix tailTrace_611716
  have hstable : (prefixWord ++ tailWord_611716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611716).length < 2 ^ (prefixWord ++ tailWord_611716).sum := by decide
  have hdescent : baseEnd_611716 < baseStart_611716 := by decide
  rcases family_descends (prefixWord ++ tailWord_611716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611737 : List Nat := [1, 2, 1, 2, 1, 5, 8]
def baseStart_611737 : Nat := 118140960795 + 611737 * 2 ^ 59
def prefixEnd_611737 : Nat := 4983230072969 + 3 ^ 40 * 611737 * 2
def baseEnd_611737 : Nat := 31023715075513907148067

theorem tailTrace_611737 : CollatzResearch.WordTrace tailWord_611737 prefixEnd_611737 31023715075513907148067 := by
  unfold tailWord_611737
  simp only [CollatzResearch.WordTrace]
  refine ⟨22311881384788800206921465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14874587589859200137947643 22311881384788800206921465)
  ·
    refine ⟨16733911038591600155191099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22311881384788800206921465 16733911038591600155191099)
    ·
      refine ⟨25100866557887400232786649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16733911038591600155191099 25100866557887400232786649)
      ·
        refine ⟨18825649918415550174589987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25100866557887400232786649 18825649918415550174589987)
        ·
          refine ⟨28238474877623325261884981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18825649918415550174589987 28238474877623325261884981)
          ·
            refine ⟨2647357019777186743301717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28238474877623325261884981 2647357019777186743301717)
            ·
              refine ⟨31023715075513907148067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2647357019777186743301717 31023715075513907148067)
              ·
                rfl

theorem cell20_611737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_611737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611737 prefixEnd_611737 := by exact prefixLift 611737
  have htrace : WordTrace (prefixWord ++ tailWord_611737) baseStart_611737 baseEnd_611737 := by
    simpa [prefixWord, tailWord_611737, baseEnd_611737] using wordTrace_append hprefix tailTrace_611737
  have hstable : (prefixWord ++ tailWord_611737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611737).length < 2 ^ (prefixWord ++ tailWord_611737).sum := by decide
  have hdescent : baseEnd_611737 < baseStart_611737 := by decide
  rcases family_descends (prefixWord ++ tailWord_611737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611743 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 2]
def baseStart_611743 : Nat := 118140960795 + 611743 * 2 ^ 59
def prefixEnd_611743 : Nat := 4983230072969 + 3 ^ 40 * 611743 * 2
def baseEnd_611743 : Nat := 279216174243115810132579

theorem tailTrace_611743 : CollatzResearch.WordTrace tailWord_611743 prefixEnd_611743 279216174243115810132579 := by
  unfold tailWord_611743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22312100222767063231639883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14874733481844708821093255 22312100222767063231639883)
  ·
    refine ⟨33468150334150594847459825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22312100222767063231639883 33468150334150594847459825)
    ·
      refine ⟨25101112750612946135594869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33468150334150594847459825 25101112750612946135594869)
      ·
        refine ⟨2353229320369963700212019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25101112750612946135594869 2353229320369963700212019)
        ·
          refine ⟨3529843980554945550318029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353229320369963700212019 3529843980554945550318029)
          ·
            refine ⟨1323691492708104581369261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3529843980554945550318029 1323691492708104581369261)
            ·
              refine ⟨496384309765539218013473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1323691492708104581369261 496384309765539218013473)
              ·
                refine ⟨372288232324154413510105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496384309765539218013473 372288232324154413510105)
                ·
                  refine ⟨279216174243115810132579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372288232324154413510105 279216174243115810132579)
                  ·
                    rfl

theorem cell20_611743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2].length) (baseStart_611743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611743 prefixEnd_611743 := by exact prefixLift 611743
  have htrace : WordTrace (prefixWord ++ tailWord_611743) baseStart_611743 baseEnd_611743 := by
    simpa [prefixWord, tailWord_611743, baseEnd_611743] using wordTrace_append hprefix tailTrace_611743
  have hstable : (prefixWord ++ tailWord_611743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611743).length < 2 ^ (prefixWord ++ tailWord_611743).sum := by decide
  have hdescent : baseEnd_611743 < baseStart_611743 := by decide
  rcases family_descends (prefixWord ++ tailWord_611743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611757 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_611757 : Nat := 118140960795 + 611757 * 2 ^ 59
def prefixEnd_611757 : Nat := 4983230072969 + 3 ^ 40 * 611757 * 2
def baseEnd_611757 : Nat := 279222564224593983665855

theorem tailTrace_611757 : CollatzResearch.WordTrace tailWord_611757 prefixEnd_611757 279222564224593983665855 := by
  unfold tailWord_611757
  simp only [CollatzResearch.WordTrace]
  refine ⟨22312610844716343622649525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14875073896477562415099683 22312610844716343622649525)
  ·
    refine ⟨2091807266692157214623393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22312610844716343622649525 2091807266692157214623393)
    ·
      refine ⟨1568855450019117910967545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2091807266692157214623393 1568855450019117910967545)
      ·
        refine ⟨1176641587514338433225659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568855450019117910967545 1176641587514338433225659)
        ·
          refine ⟨1764962381271507649838489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176641587514338433225659 1764962381271507649838489)
          ·
            refine ⟨1323721785953630737378867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1764962381271507649838489 1323721785953630737378867)
            ·
              refine ⟨1985582678930446106068301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323721785953630737378867 1985582678930446106068301)
              ·
                refine ⟨744593504598917289775613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1985582678930446106068301 744593504598917289775613)
                ·
                  refine ⟨279222564224593983665855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744593504598917289775613 279222564224593983665855)
                  ·
                    rfl

theorem cell20_611757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_611757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611757 prefixEnd_611757 := by exact prefixLift 611757
  have htrace : WordTrace (prefixWord ++ tailWord_611757) baseStart_611757 baseEnd_611757 := by
    simpa [prefixWord, tailWord_611757, baseEnd_611757] using wordTrace_append hprefix tailTrace_611757
  have hstable : (prefixWord ++ tailWord_611757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611757).length < 2 ^ (prefixWord ++ tailWord_611757).sum := by decide
  have hdescent : baseEnd_611757 < baseStart_611757 := by decide
  rcases family_descends (prefixWord ++ tailWord_611757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611768 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_611768 : Nat := 118140960795 + 611768 * 2 ^ 59
def prefixEnd_611768 : Nat := 4983230072969 + 3 ^ 40 * 611768 * 2
def baseEnd_611768 : Nat := 279227584924326834299143

theorem tailTrace_611768 : CollatzResearch.WordTrace tailWord_611768 prefixEnd_611768 279227584924326834299143 := by
  unfold tailWord_611768
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156506023838246250649979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14875341365117661667533305 11156506023838246250649979)
  ·
    refine ⟨16734759035757369375974969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11156506023838246250649979 16734759035757369375974969)
    ·
      refine ⟨12551069276818027031981227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16734759035757369375974969 12551069276818027031981227)
      ·
        refine ⟨18826603915227040547971841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12551069276818027031981227 18826603915227040547971841)
        ·
          refine ⟨14119952936420280410978881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18826603915227040547971841 14119952936420280410978881)
          ·
            refine ⟨10589964702315210308234161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14119952936420280410978881 10589964702315210308234161)
            ·
              refine ⟨7942473526736407731175621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10589964702315210308234161 7942473526736407731175621)
              ·
                refine ⟨1489213786263076449595429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7942473526736407731175621 1489213786263076449595429)
                ·
                  refine ⟨279227584924326834299143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489213786263076449595429 279227584924326834299143)
                  ·
                    rfl

theorem cell20_611768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_611768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611768 prefixEnd_611768 := by exact prefixLift 611768
  have htrace : WordTrace (prefixWord ++ tailWord_611768) baseStart_611768 baseEnd_611768 := by
    simpa [prefixWord, tailWord_611768, baseEnd_611768] using wordTrace_append hprefix tailTrace_611768
  have hstable : (prefixWord ++ tailWord_611768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611768).length < 2 ^ (prefixWord ++ tailWord_611768).sum := by decide
  have hdescent : baseEnd_611768 < baseStart_611768 := by decide
  rcases family_descends (prefixWord ++ tailWord_611768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611785 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 2]
def baseStart_611785 : Nat := 118140960795 + 611785 * 2 ^ 59
def prefixEnd_611785 : Nat := 4983230072969 + 3 ^ 40 * 611785 * 2
def baseEnd_611785 : Nat := 279235344187550330732407

theorem tailTrace_611785 : CollatzResearch.WordTrace tailWord_611785 prefixEnd_611785 279235344187550330732407 := by
  unfold tailWord_611785
  simp only [CollatzResearch.WordTrace]
  refine ⟨22313632088614904404668809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14875754725743269603112539 22313632088614904404668809)
  ·
    refine ⟨16735224066461178303501607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22313632088614904404668809 16735224066461178303501607)
    ·
      refine ⟨25102836099691767455252411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16735224066461178303501607 25102836099691767455252411)
      ·
        refine ⟨37654254149537651182878617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25102836099691767455252411 37654254149537651182878617)
        ·
          refine ⟨28240690612153238387158963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37654254149537651182878617 28240690612153238387158963)
          ·
            refine ⟨42361035918229857580738445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28240690612153238387158963 42361035918229857580738445)
            ·
              refine ⟨15885388469336196592776917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42361035918229857580738445 15885388469336196592776917)
              ·
                refine ⟨372313792250067107643209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15885388469336196592776917 372313792250067107643209)
                ·
                  refine ⟨279235344187550330732407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372313792250067107643209 279235344187550330732407)
                  ·
                    rfl

theorem cell20_611785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_611785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611785 prefixEnd_611785 := by exact prefixLift 611785
  have htrace : WordTrace (prefixWord ++ tailWord_611785) baseStart_611785 baseEnd_611785 := by
    simpa [prefixWord, tailWord_611785, baseEnd_611785] using wordTrace_append hprefix tailTrace_611785
  have hstable : (prefixWord ++ tailWord_611785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611785).length < 2 ^ (prefixWord ++ tailWord_611785).sum := by decide
  have hdescent : baseEnd_611785 < baseStart_611785 := by decide
  rcases family_descends (prefixWord ++ tailWord_611785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611798 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_611798 : Nat := 118140960795 + 611798 * 2 ^ 59
def prefixEnd_611798 : Nat := 4983230072969 + 3 ^ 40 * 611798 * 2
def baseEnd_611798 : Nat := 279241277741780063299021

theorem tailTrace_611798 : CollatzResearch.WordTrace tailWord_611798 prefixEnd_611798 279241277741780063299021 := by
  unfold tailWord_611798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394631639847987976555753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14876070825045205083261365 1394631639847987976555753)
  ·
    refine ⟨1045973729885990982416815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1394631639847987976555753 1045973729885990982416815)
    ·
      refine ⟨1568960594828986473625223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045973729885990982416815 1568960594828986473625223)
      ·
        refine ⟨2353440892243479710437835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568960594828986473625223 2353440892243479710437835)
        ·
          refine ⟨3530161338365219565656753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353440892243479710437835 3530161338365219565656753)
          ·
            refine ⟨2647621003773914674242565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530161338365219565656753 2647621003773914674242565)
            ·
              refine ⟨496428938207609001420481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2647621003773914674242565 496428938207609001420481)
              ·
                refine ⟨372321703655706751065361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496428938207609001420481 372321703655706751065361)
                ·
                  refine ⟨279241277741780063299021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372321703655706751065361 279241277741780063299021)
                  ·
                    rfl

theorem cell20_611798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_611798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611798 prefixEnd_611798 := by exact prefixLift 611798
  have htrace : WordTrace (prefixWord ++ tailWord_611798) baseStart_611798 baseEnd_611798 := by
    simpa [prefixWord, tailWord_611798, baseEnd_611798] using wordTrace_append hprefix tailTrace_611798
  have hstable : (prefixWord ++ tailWord_611798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611798).length < 2 ^ (prefixWord ++ tailWord_611798).sum := by decide
  have hdescent : baseEnd_611798 < baseStart_611798 := by decide
  rcases family_descends (prefixWord ++ tailWord_611798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611802 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_611802 : Nat := 118140960795 + 611802 * 2 ^ 59
def prefixEnd_611802 : Nat := 4983230072969 + 3 ^ 40 * 611802 * 2
def baseEnd_611802 : Nat := 279243103450773827165671

theorem tailTrace_611802 : CollatzResearch.WordTrace tailWord_611802 prefixEnd_611802 279243103450773827165671 := by
  unfold tailWord_611802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578563032388329077009415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14876168086368877538691773 5578563032388329077009415)
  ·
    refine ⟨8367844548582493615514123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5578563032388329077009415 8367844548582493615514123)
    ·
      refine ⟨12551766822873740423271185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8367844548582493615514123 12551766822873740423271185)
      ·
        refine ⟨9413825117155305317453389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12551766822873740423271185 9413825117155305317453389)
        ·
          refine ⟨3530184418933239494045021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9413825117155305317453389 3530184418933239494045021)
          ·
            refine ⟨1323819157099964810266883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3530184418933239494045021 1323819157099964810266883)
            ·
              refine ⟨1985728735649947215400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323819157099964810266883 1985728735649947215400325)
              ·
                refine ⟨372324137934365102887561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1985728735649947215400325 372324137934365102887561)
                ·
                  refine ⟨279243103450773827165671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372324137934365102887561 279243103450773827165671)
                  ·
                    rfl

theorem cell20_611802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_611802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611802 prefixEnd_611802 := by exact prefixLift 611802
  have htrace : WordTrace (prefixWord ++ tailWord_611802) baseStart_611802 baseEnd_611802 := by
    simpa [prefixWord, tailWord_611802, baseEnd_611802] using wordTrace_append hprefix tailTrace_611802
  have hstable : (prefixWord ++ tailWord_611802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611802).length < 2 ^ (prefixWord ++ tailWord_611802).sum := by decide
  have hdescent : baseEnd_611802 < baseStart_611802 := by decide
  rcases family_descends (prefixWord ++ tailWord_611802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611846 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_611846 : Nat := 118140960795 + 611846 * 2 ^ 59
def prefixEnd_611846 : Nat := 4983230072969 + 3 ^ 40 * 611846 * 2
def baseEnd_611846 : Nat := 279263186249705229698825

theorem tailTrace_611846 : CollatzResearch.WordTrace tailWord_611846 prefixEnd_611846 279263186249705229698825 := by
  unfold tailWord_611846
  simp only [CollatzResearch.WordTrace]
  refine ⟨697370529418559744457481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14877237960929274548426261 697370529418559744457481)
  ·
    refine ⟨523027897063919808343111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 697370529418559744457481 523027897063919808343111)
    ·
      refine ⟨784541845595879712514667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523027897063919808343111 784541845595879712514667)
      ·
        refine ⟨1176812768393819568772001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784541845595879712514667 1176812768393819568772001)
        ·
          refine ⟨882609576295364676579001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176812768393819568772001 882609576295364676579001)
          ·
            refine ⟨661957182221523507434251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882609576295364676579001 661957182221523507434251)
            ·
              refine ⟨992935773332285261151377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661957182221523507434251 992935773332285261151377)
              ·
                refine ⟨744701829999213945863533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992935773332285261151377 744701829999213945863533)
                ·
                  refine ⟨279263186249705229698825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744701829999213945863533 279263186249705229698825)
                  ·
                    rfl

theorem cell20_611846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_611846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611846 prefixEnd_611846 := by exact prefixLift 611846
  have htrace : WordTrace (prefixWord ++ tailWord_611846) baseStart_611846 baseEnd_611846 := by
    simpa [prefixWord, tailWord_611846, baseEnd_611846] using wordTrace_append hprefix tailTrace_611846
  have hstable : (prefixWord ++ tailWord_611846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611846).length < 2 ^ (prefixWord ++ tailWord_611846).sum := by decide
  have hdescent : baseEnd_611846 < baseStart_611846 := by decide
  rcases family_descends (prefixWord ++ tailWord_611846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611854 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_611854 : Nat := 118140960795 + 611854 * 2 ^ 59
def prefixEnd_611854 : Nat := 4983230072969 + 3 ^ 40 * 611854 * 2
def baseEnd_611854 : Nat := 279266837667692757432125

theorem tailTrace_611854 : CollatzResearch.WordTrace tailWord_611854 prefixEnd_611854 279266837667692757432125 := by
  unfold tailWord_611854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789518590670616148616327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14877432483576619459287077 2789518590670616148616327)
  ·
    refine ⟨4184277886005924222924491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2789518590670616148616327 4184277886005924222924491)
    ·
      refine ⟨6276416829008886334386737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4184277886005924222924491 6276416829008886334386737)
      ·
        refine ⟨4707312621756664750790053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6276416829008886334386737 4707312621756664750790053)
        ·
          refine ⟨882621116579374640773135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4707312621756664750790053 882621116579374640773135)
          ·
            refine ⟨1323931674869061961159703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882621116579374640773135 1323931674869061961159703)
            ·
              refine ⟨1985897512303592941739555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323931674869061961159703 1985897512303592941739555)
              ·
                refine ⟨2978846268455389412609333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985897512303592941739555 2978846268455389412609333)
                ·
                  refine ⟨279266837667692757432125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978846268455389412609333 279266837667692757432125)
                  ·
                    rfl

theorem cell20_611854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_611854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611854 prefixEnd_611854 := by exact prefixLift 611854
  have htrace : WordTrace (prefixWord ++ tailWord_611854) baseStart_611854 baseEnd_611854 := by
    simpa [prefixWord, tailWord_611854, baseEnd_611854] using wordTrace_append hprefix tailTrace_611854
  have hstable : (prefixWord ++ tailWord_611854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611854).length < 2 ^ (prefixWord ++ tailWord_611854).sum := by decide
  have hdescent : baseEnd_611854 < baseStart_611854 := by decide
  rcases family_descends (prefixWord ++ tailWord_611854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611861 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_611861 : Nat := 118140960795 + 611861 * 2 ^ 59
def prefixEnd_611861 : Nat := 4983230072969 + 3 ^ 40 * 611861 * 2
def baseEnd_611861 : Nat := 279270032658431844198763

theorem tailTrace_611861 : CollatzResearch.WordTrace tailWord_611861 prefixEnd_611861 279270032658431844198763 := by
  unfold tailWord_611861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316404036339569384435437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14877602690893046256290291 22316404036339569384435437)
  ·
    refine ⟨8368651513627338519163289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22316404036339569384435437 8368651513627338519163289)
    ·
      refine ⟨6276488635220503889372467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8368651513627338519163289 6276488635220503889372467)
      ·
        refine ⟨9414732952830755834058701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276488635220503889372467 9414732952830755834058701)
        ·
          refine ⟨3530524857311533437772013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9414732952830755834058701 3530524857311533437772013)
          ·
            refine ⟨1323946821491825039164505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3530524857311533437772013 1323946821491825039164505)
            ·
              refine ⟨992960116118868779373379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323946821491825039164505 992960116118868779373379)
              ·
                refine ⟨1489440174178303169060069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992960116118868779373379 1489440174178303169060069)
                ·
                  refine ⟨279270032658431844198763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489440174178303169060069 279270032658431844198763)
                  ·
                    rfl

theorem cell20_611861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_611861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611861 prefixEnd_611861 := by exact prefixLift 611861
  have htrace : WordTrace (prefixWord ++ tailWord_611861) baseStart_611861 baseEnd_611861 := by
    simpa [prefixWord, tailWord_611861, baseEnd_611861] using wordTrace_append hprefix tailTrace_611861
  have hstable : (prefixWord ++ tailWord_611861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611861).length < 2 ^ (prefixWord ++ tailWord_611861).sum := by decide
  have hdescent : baseEnd_611861 < baseStart_611861 := by decide
  rcases family_descends (prefixWord ++ tailWord_611861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611927 : List Nat := [1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_611927 : Nat := 118140960795 + 611927 * 2 ^ 59
def prefixEnd_611927 : Nat := 4983230072969 + 3 ^ 40 * 611927 * 2
def baseEnd_611927 : Nat := 93100052285609649332831

theorem tailTrace_611927 : CollatzResearch.WordTrace tailWord_611927 prefixEnd_611927 93100052285609649332831 := by
  unfold tailWord_611927
  simp only [CollatzResearch.WordTrace]
  refine ⟨22318811254100462656338035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14879207502733641770892023 22318811254100462656338035)
  ·
    refine ⟨33478216881150693984507053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22318811254100462656338035 33478216881150693984507053)
    ·
      refine ⟨12554331330431510244190145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33478216881150693984507053 12554331330431510244190145)
      ·
        refine ⟨9415748497823632683142609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12554331330431510244190145 9415748497823632683142609)
        ·
          refine ⟨7061811373367724512356957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9415748497823632683142609 7061811373367724512356957)
          ·
            refine ⟨2648179265012896692133859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7061811373367724512356957 2648179265012896692133859)
            ·
              refine ⟨3972268897519345038200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648179265012896692133859 3972268897519345038200789)
              ·
                refine ⟨93100052285609649332831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3972268897519345038200789 93100052285609649332831)
                ·
                  rfl

theorem cell20_611927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_611927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611927 prefixEnd_611927 := by exact prefixLift 611927
  have htrace : WordTrace (prefixWord ++ tailWord_611927) baseStart_611927 baseEnd_611927 := by
    simpa [prefixWord, tailWord_611927, baseEnd_611927] using wordTrace_append hprefix tailTrace_611927
  have hstable : (prefixWord ++ tailWord_611927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611927).length < 2 ^ (prefixWord ++ tailWord_611927).sum := by decide
  have hdescent : baseEnd_611927 < baseStart_611927 := by decide
  rcases family_descends (prefixWord ++ tailWord_611927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611944 : List Nat := [2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_611944 : Nat := 118140960795 + 611944 * 2 ^ 59
def prefixEnd_611944 : Nat := 4983230072969 + 3 ^ 40 * 611944 * 2
def baseEnd_611944 : Nat := 93102638706684148143919

theorem tailTrace_611944 : CollatzResearch.WordTrace tailWord_611944 prefixEnd_611944 93102638706684148143919 := by
  unfold tailWord_611944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159715647519437279853443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14879620863359249706471257 11159715647519437279853443)
  ·
    refine ⟨16739573471279155919780165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11159715647519437279853443 16739573471279155919780165)
    ·
      refine ⟨3138670025864841734958781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16739573471279155919780165 3138670025864841734958781)
      ·
        refine ⟨1177001259699315650609543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3138670025864841734958781 1177001259699315650609543)
        ·
          refine ⟨1765501889548973475914315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177001259699315650609543 1765501889548973475914315)
          ·
            refine ⟨2648252834323460213871473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765501889548973475914315 2648252834323460213871473)
            ·
              refine ⟨1986189625742595160403605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648252834323460213871473 1986189625742595160403605)
              ·
                refine ⟨93102638706684148143919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1986189625742595160403605 93102638706684148143919)
                ·
                  rfl

theorem cell20_611944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_611944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611944 prefixEnd_611944 := by exact prefixLift 611944
  have htrace : WordTrace (prefixWord ++ tailWord_611944) baseStart_611944 baseEnd_611944 := by
    simpa [prefixWord, tailWord_611944, baseEnd_611944] using wordTrace_append hprefix tailTrace_611944
  have hstable : (prefixWord ++ tailWord_611944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611944).length < 2 ^ (prefixWord ++ tailWord_611944).sum := by decide
  have hdescent : baseEnd_611944 < baseStart_611944 := by decide
  rcases family_descends (prefixWord ++ tailWord_611944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611965 : List Nat := [1, 4, 1, 1, 4, 9]
def baseStart_611965 : Nat := 118140960795 + 611965 * 2 ^ 59
def prefixEnd_611965 : Nat := 4983230072969 + 3 ^ 40 * 611965 * 2
def baseEnd_611965 : Nat := 10345092633047026101173

theorem tailTrace_611965 : CollatzResearch.WordTrace tailWord_611965 prefixEnd_611965 10345092633047026101173 := by
  unfold tailWord_611965
  simp only [CollatzResearch.WordTrace]
  refine ⟨22320197227962795146221349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14880131485308530097480899 22320197227962795146221349)
  ·
    refine ⟨4185036980243024089916503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22320197227962795146221349 4185036980243024089916503)
    ·
      refine ⟨6277555470364536134874755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4185036980243024089916503 6277555470364536134874755)
      ·
        refine ⟨9416333205546804202312133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277555470364536134874755 9416333205546804202312133)
        ·
          refine ⟨1765562476040025787933525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9416333205546804202312133 1765562476040025787933525)
          ·
            refine ⟨10345092633047026101173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1765562476040025787933525 10345092633047026101173)
            ·
              rfl

theorem cell20_611965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 9].length) (baseStart_611965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611965 prefixEnd_611965 := by exact prefixLift 611965
  have htrace : WordTrace (prefixWord ++ tailWord_611965) baseStart_611965 baseEnd_611965 := by
    simpa [prefixWord, tailWord_611965, baseEnd_611965] using wordTrace_append hprefix tailTrace_611965
  have hstable : (prefixWord ++ tailWord_611965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611965).length < 2 ^ (prefixWord ++ tailWord_611965).sum := by decide
  have hdescent : baseEnd_611965 < baseStart_611965 := by decide
  rcases family_descends (prefixWord ++ tailWord_611965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611982 : List Nat := [4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_611982 : Nat := 118140960795 + 611982 * 2 ^ 59
def prefixEnd_611982 : Nat := 4983230072969 + 3 ^ 40 * 611982 * 2
def baseEnd_611982 : Nat := 93108420118497733721645

theorem tailTrace_611982 : CollatzResearch.WordTrace tailWord_611982 prefixEnd_611982 93108420118497733721645 := by
  unfold tailWord_611982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790102158612650881198775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14880544845934138033060133 2790102158612650881198775)
  ·
    refine ⟨4185153237918976321798163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2790102158612650881198775 4185153237918976321798163)
    ·
      refine ⟨6277729856878464482697245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4185153237918976321798163 6277729856878464482697245)
      ·
        refine ⟨2354148696329424181011467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6277729856878464482697245 2354148696329424181011467)
        ·
          refine ⟨3531223044494136271517201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354148696329424181011467 3531223044494136271517201)
          ·
            refine ⟨2648417283370602203637901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3531223044494136271517201 2648417283370602203637901)
            ·
              refine ⟨993156481263975826364213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648417283370602203637901 993156481263975826364213)
              ·
                refine ⟨93108420118497733721645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 993156481263975826364213 93108420118497733721645)
                ·
                  rfl

theorem cell20_611982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_611982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_611982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_611982 prefixEnd_611982 := by exact prefixLift 611982
  have htrace : WordTrace (prefixWord ++ tailWord_611982) baseStart_611982 baseEnd_611982 := by
    simpa [prefixWord, tailWord_611982, baseEnd_611982] using wordTrace_append hprefix tailTrace_611982
  have hstable : (prefixWord ++ tailWord_611982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611982).length < 2 ^ (prefixWord ++ tailWord_611982).sum := by decide
  have hdescent : baseEnd_611982 < baseStart_611982 := by decide
  rcases family_descends (prefixWord ++ tailWord_611982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612030 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_612030 : Nat := 118140960795 + 612030 * 2 ^ 59
def prefixEnd_612030 : Nat := 4983230072969 + 3 ^ 40 * 612030 * 2
def baseEnd_612030 : Nat := 279347168863418367564739

theorem tailTrace_612030 : CollatzResearch.WordTrace tailWord_612030 prefixEnd_612030 279347168863418367564739 := by
  unfold tailWord_612030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790320996590913905917193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14881711981818207498225029 2790320996590913905917193)
  ·
    refine ⟨2092740747443185429437895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2790320996590913905917193 2092740747443185429437895)
    ·
      refine ⟨3139111121164778144156843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092740747443185429437895 3139111121164778144156843)
      ·
        refine ⟨4708666681747167216235265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139111121164778144156843 4708666681747167216235265)
        ·
          refine ⟨3531500011310375412176449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4708666681747167216235265 3531500011310375412176449)
          ·
            refine ⟨2648625008482781559132337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3531500011310375412176449 2648625008482781559132337)
            ·
              refine ⟨1986468756362086169349253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648625008482781559132337 1986468756362086169349253)
              ·
                refine ⟨372462891817891156752985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1986468756362086169349253 372462891817891156752985)
                ·
                  refine ⟨279347168863418367564739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372462891817891156752985 279347168863418367564739)
                  ·
                    rfl

theorem cell20_612030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_612030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612030 prefixEnd_612030 := by exact prefixLift 612030
  have htrace : WordTrace (prefixWord ++ tailWord_612030) baseStart_612030 baseEnd_612030 := by
    simpa [prefixWord, tailWord_612030, baseEnd_612030] using wordTrace_append hprefix tailTrace_612030
  have hstable : (prefixWord ++ tailWord_612030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612030).length < 2 ^ (prefixWord ++ tailWord_612030).sum := by decide
  have hdescent : baseEnd_612030 < baseStart_612030 := by decide
  rcases family_descends (prefixWord ++ tailWord_612030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612054 : List Nat := [5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_612054 : Nat := 118140960795 + 612054 * 2 ^ 59
def prefixEnd_612054 : Nat := 4983230072969 + 3 ^ 40 * 612054 * 2
def baseEnd_612054 : Nat := 93119374372460316921547

theorem tailTrace_612054 : CollatzResearch.WordTrace tailWord_612054 prefixEnd_612054 93119374372460316921547 := by
  unfold tailWord_612054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395215207790022709138201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14882295549760242230807477 1395215207790022709138201)
  ·
    refine ⟨1046411405842517031853651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1395215207790022709138201 1046411405842517031853651)
    ·
      refine ⟨1569617108763775547780477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046411405842517031853651 1569617108763775547780477)
      ·
        refine ⟨588606415786415830417679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1569617108763775547780477 588606415786415830417679)
        ·
          refine ⟨882909623679623745626519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588606415786415830417679 882909623679623745626519)
          ·
            refine ⟨1324364435519435618439779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882909623679623745626519 1324364435519435618439779)
            ·
              refine ⟨1986546653279153427659669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324364435519435618439779 1986546653279153427659669)
              ·
                refine ⟨93119374372460316921547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1986546653279153427659669 93119374372460316921547)
                ·
                  rfl

theorem cell20_612054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_612054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612054 prefixEnd_612054 := by exact prefixLift 612054
  have htrace : WordTrace (prefixWord ++ tailWord_612054) baseStart_612054 baseEnd_612054 := by
    simpa [prefixWord, tailWord_612054, baseEnd_612054] using wordTrace_append hprefix tailTrace_612054
  have hstable : (prefixWord ++ tailWord_612054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612054).length < 2 ^ (prefixWord ++ tailWord_612054).sum := by decide
  have hdescent : baseEnd_612054 < baseStart_612054 := by decide
  rcases family_descends (prefixWord ++ tailWord_612054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612058 : List Nat := [3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_612058 : Nat := 118140960795 + 612058 * 2 ^ 59
def prefixEnd_612058 : Nat := 4983230072969 + 3 ^ 40 * 612058 * 2
def baseEnd_612058 : Nat := 93119982942124904877097

theorem tailTrace_612058 : CollatzResearch.WordTrace tailWord_612058 prefixEnd_612058 93119982942124904877097 := by
  unfold tailWord_612058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580897304156468007339207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14882392811083914686237885 5580897304156468007339207)
  ·
    refine ⟨8371345956234702011008811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580897304156468007339207 8371345956234702011008811)
    ·
      refine ⟨12557018934352053016513217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371345956234702011008811 12557018934352053016513217)
      ·
        refine ⟨9417764200764039762384913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12557018934352053016513217 9417764200764039762384913)
        ·
          refine ⟨7063323150573029821788685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9417764200764039762384913 7063323150573029821788685)
          ·
            refine ⟨2648746181464886183170757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7063323150573029821788685 2648746181464886183170757)
            ·
              refine ⟨496639909024666159344517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2648746181464886183170757 496639909024666159344517)
              ·
                refine ⟨93119982942124904877097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496639909024666159344517 93119982942124904877097)
                ·
                  rfl

theorem cell20_612058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_612058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612058 prefixEnd_612058 := by exact prefixLift 612058
  have htrace : WordTrace (prefixWord ++ tailWord_612058) baseStart_612058 baseEnd_612058 := by
    simpa [prefixWord, tailWord_612058, baseEnd_612058] using wordTrace_append hprefix tailTrace_612058
  have hstable : (prefixWord ++ tailWord_612058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612058).length < 2 ^ (prefixWord ++ tailWord_612058).sum := by decide
  have hdescent : baseEnd_612058 < baseStart_612058 := by decide
  rcases family_descends (prefixWord ++ tailWord_612058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612110 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_612110 : Nat := 118140960795 + 612110 * 2 ^ 59
def prefixEnd_612110 : Nat := 4983230072969 + 3 ^ 40 * 612110 * 2
def baseEnd_612110 : Nat := 279383683043293644897745

theorem tailTrace_612110 : CollatzResearch.WordTrace tailWord_612110 prefixEnd_612110 279383683043293644897745 := by
  unfold tailWord_612110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790685726554685613781223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14883657208291656606833189 2790685726554685613781223)
  ·
    refine ⟨4186028589832028420671835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2790685726554685613781223 4186028589832028420671835)
    ·
      refine ⟨6279042884748042631007753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4186028589832028420671835 6279042884748042631007753)
      ·
        refine ⟨4709282163561031973255815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6279042884748042631007753 4709282163561031973255815)
        ·
          refine ⟨7063923245341547959883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709282163561031973255815 7063923245341547959883723)
          ·
            refine ⟨10595884868012321939825585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063923245341547959883723 10595884868012321939825585)
            ·
              refine ⟨7946913651009241454869189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10595884868012321939825585 7946913651009241454869189)
              ·
                refine ⟨1490046309564232772787973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7946913651009241454869189 1490046309564232772787973)
                ·
                  refine ⟨279383683043293644897745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490046309564232772787973 279383683043293644897745)
                  ·
                    rfl

theorem cell20_612110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_612110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612110 prefixEnd_612110 := by exact prefixLift 612110
  have htrace : WordTrace (prefixWord ++ tailWord_612110) baseStart_612110 baseEnd_612110 := by
    simpa [prefixWord, tailWord_612110, baseEnd_612110] using wordTrace_append hprefix tailTrace_612110
  have hstable : (prefixWord ++ tailWord_612110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612110).length < 2 ^ (prefixWord ++ tailWord_612110).sum := by decide
  have hdescent : baseEnd_612110 < baseStart_612110 := by decide
  rcases family_descends (prefixWord ++ tailWord_612110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612117 : List Nat := [1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_612117 : Nat := 118140960795 + 612117 * 2 ^ 59
def prefixEnd_612117 : Nat := 4983230072969 + 3 ^ 40 * 612117 * 2
def baseEnd_612117 : Nat := 93128959344677577221461

theorem tailTrace_612117 : CollatzResearch.WordTrace tailWord_612117 prefixEnd_612117 93128959344677577221461 := by
  unfold tailWord_612117
  simp only [CollatzResearch.WordTrace]
  refine ⟨22325741123412125105754605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14883827415608083403836403 22325741123412125105754605)
  ·
    refine ⟨8372152921279546914657977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22325741123412125105754605 8372152921279546914657977)
    ·
      refine ⟨6279114690959660185993483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8372152921279546914657977 6279114690959660185993483)
      ·
        refine ⟨9418672036439490278990225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6279114690959660185993483 9418672036439490278990225)
        ·
          refine ⟨7064004027329617709242669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9418672036439490278990225 7064004027329617709242669)
          ·
            refine ⟨2649001510248606640966001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7064004027329617709242669 2649001510248606640966001)
            ·
              refine ⟨1986751132686454980724501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649001510248606640966001 1986751132686454980724501)
              ·
                refine ⟨93128959344677577221461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1986751132686454980724501 93128959344677577221461)
                ·
                  rfl

theorem cell20_612117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_612117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612117 prefixEnd_612117 := by exact prefixLift 612117
  have htrace : WordTrace (prefixWord ++ tailWord_612117) baseStart_612117 baseEnd_612117 := by
    simpa [prefixWord, tailWord_612117, baseEnd_612117] using wordTrace_append hprefix tailTrace_612117
  have hstable : (prefixWord ++ tailWord_612117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612117).length < 2 ^ (prefixWord ++ tailWord_612117).sum := by decide
  have hdescent : baseEnd_612117 < baseStart_612117 := by decide
  rcases family_descends (prefixWord ++ tailWord_612117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612127 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 2]
def baseStart_612127 : Nat := 118140960795 + 612127 * 2 ^ 59
def prefixEnd_612127 : Nat := 4983230072969 + 3 ^ 40 * 612127 * 2
def baseEnd_612127 : Nat := 279391442306517141331009

theorem tailTrace_612127 : CollatzResearch.WordTrace tailWord_612127 prefixEnd_612127 279391442306517141331009 := by
  unfold tailWord_612127
  simp only [CollatzResearch.WordTrace]
  refine ⟨22326105853375896813618635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14884070568917264542412423 22326105853375896813618635)
  ·
    refine ⟨33489158780063845220427953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22326105853375896813618635 33489158780063845220427953)
    ·
      refine ⟨25116869085047883915320965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33489158780063845220427953 25116869085047883915320965)
      ·
        refine ⟨4709412953446478234122681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25116869085047883915320965 4709412953446478234122681)
        ·
          refine ⟨3532059715084858675592011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4709412953446478234122681 3532059715084858675592011)
          ·
            refine ⟨5298089572627288013388017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532059715084858675592011 5298089572627288013388017)
            ·
              refine ⟨3973567179470466010041013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5298089572627288013388017 3973567179470466010041013)
              ·
                refine ⟨372521923075356188441345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3973567179470466010041013 372521923075356188441345)
                ·
                  refine ⟨279391442306517141331009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372521923075356188441345 279391442306517141331009)
                  ·
                    rfl

theorem cell20_612127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 2].length) (baseStart_612127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612127 prefixEnd_612127 := by exact prefixLift 612127
  have htrace : WordTrace (prefixWord ++ tailWord_612127) baseStart_612127 baseEnd_612127 := by
    simpa [prefixWord, tailWord_612127, baseEnd_612127] using wordTrace_append hprefix tailTrace_612127
  have hstable : (prefixWord ++ tailWord_612127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612127).length < 2 ^ (prefixWord ++ tailWord_612127).sum := by decide
  have hdescent : baseEnd_612127 < baseStart_612127 := by decide
  rcases family_descends (prefixWord ++ tailWord_612127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612158 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_612158 : Nat := 118140960795 + 612158 * 2 ^ 59
def prefixEnd_612158 : Nat := 4983230072969 + 3 ^ 40 * 612158 * 2
def baseEnd_612158 : Nat := 279405591551218811297549

theorem tailTrace_612158 : CollatzResearch.WordTrace tailWord_612158 prefixEnd_612158 279405591551218811297549 := by
  unfold tailWord_612158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790904564532948638499641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14884824344175726071998085 2790904564532948638499641)
  ·
    refine ⟨2093178423399711478874731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2790904564532948638499641 2093178423399711478874731)
    ·
      refine ⟨3139767635099567218312097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093178423399711478874731 3139767635099567218312097)
      ·
        refine ⟨2354825726324675413734073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139767635099567218312097 2354825726324675413734073)
        ·
          refine ⟨1766119294743506560300555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354825726324675413734073 1766119294743506560300555)
          ·
            refine ⟨2649178942115259840450833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766119294743506560300555 2649178942115259840450833)
            ·
              refine ⟨1986884206586444880338125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649178942115259840450833 1986884206586444880338125)
              ·
                refine ⟨745081577469916830126797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1986884206586444880338125 745081577469916830126797)
                ·
                  refine ⟨279405591551218811297549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745081577469916830126797 279405591551218811297549)
                  ·
                    rfl

theorem cell20_612158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_612158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612158 prefixEnd_612158 := by exact prefixLift 612158
  have htrace : WordTrace (prefixWord ++ tailWord_612158) baseStart_612158 baseEnd_612158 := by
    simpa [prefixWord, tailWord_612158, baseEnd_612158] using wordTrace_append hprefix tailTrace_612158
  have hstable : (prefixWord ++ tailWord_612158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612158).length < 2 ^ (prefixWord ++ tailWord_612158).sum := by decide
  have hdescent : baseEnd_612158 < baseStart_612158 := by decide
  rcases family_descends (prefixWord ++ tailWord_612158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612241 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 2]
def baseStart_612241 : Nat := 118140960795 + 612241 * 2 ^ 59
def prefixEnd_612241 : Nat := 4983230072969 + 3 ^ 40 * 612241 * 2
def baseEnd_612241 : Nat := 279443475012839411530543

theorem tailTrace_612241 : CollatzResearch.WordTrace tailWord_612241 prefixEnd_612241 279443475012839411530543 := by
  unfold tailWord_612241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22330263774962894283268577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14886842516641929522179051 22330263774962894283268577)
  ·
    refine ⟨16747697831222170712451433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22330263774962894283268577 16747697831222170712451433)
    ·
      refine ⟨12560773373416628034338575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16747697831222170712451433 12560773373416628034338575)
      ·
        refine ⟨18841160060124942051507863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560773373416628034338575 18841160060124942051507863)
        ·
          refine ⟨28261740090187413077261795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18841160060124942051507863 28261740090187413077261795)
          ·
            refine ⟨42392610135281119615892693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28261740090187413077261795 42392610135281119615892693)
            ·
              refine ⟨993576800045651240997485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42392610135281119615892693 993576800045651240997485)
              ·
                refine ⟨372591300017119215374057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 993576800045651240997485 372591300017119215374057)
                ·
                  refine ⟨279443475012839411530543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372591300017119215374057 279443475012839411530543)
                  ·
                    rfl

theorem cell20_612241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_612241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612241 prefixEnd_612241 := by exact prefixLift 612241
  have htrace : WordTrace (prefixWord ++ tailWord_612241) baseStart_612241 baseEnd_612241 := by
    simpa [prefixWord, tailWord_612241, baseEnd_612241] using wordTrace_append hprefix tailTrace_612241
  have hstable : (prefixWord ++ tailWord_612241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612241).length < 2 ^ (prefixWord ++ tailWord_612241).sum := by decide
  have hdescent : baseEnd_612241 < baseStart_612241 := by decide
  rcases family_descends (prefixWord ++ tailWord_612241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612254 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_612254 : Nat := 118140960795 + 612254 * 2 ^ 59
def prefixEnd_612254 : Nat := 4983230072969 + 3 ^ 40 * 612254 * 2
def baseEnd_612254 : Nat := 279449408567069144097157

theorem tailTrace_612254 : CollatzResearch.WordTrace tailWord_612254 prefixEnd_612254 279449408567069144097157 := by
  unfold tailWord_612254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2791342240489474687936477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14887158615943865002327877 2791342240489474687936477)
  ·
    refine ⟨1046753340183553007976179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2791342240489474687936477 1046753340183553007976179)
    ·
      refine ⟨1570130010275329511964269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046753340183553007976179 1570130010275329511964269)
      ·
        refine ⟨588798753853248566986601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1570130010275329511964269 588798753853248566986601)
        ·
          refine ⟨441599065389936425239951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588798753853248566986601 441599065389936425239951)
          ·
            refine ⟨662398598084904637859927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441599065389936425239951 662398598084904637859927)
            ·
              refine ⟨993597897127356956789891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662398598084904637859927 993597897127356956789891)
              ·
                refine ⟨1490396845691035435184837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993597897127356956789891 1490396845691035435184837)
                ·
                  refine ⟨279449408567069144097157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490396845691035435184837 279449408567069144097157)
                  ·
                    rfl

theorem cell20_612254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_612254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612254 prefixEnd_612254 := by exact prefixLift 612254
  have htrace : WordTrace (prefixWord ++ tailWord_612254) baseStart_612254 baseEnd_612254 := by
    simpa [prefixWord, tailWord_612254, baseEnd_612254] using wordTrace_append hprefix tailTrace_612254
  have hstable : (prefixWord ++ tailWord_612254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612254).length < 2 ^ (prefixWord ++ tailWord_612254).sum := by decide
  have hdescent : baseEnd_612254 < baseStart_612254 := by decide
  rcases family_descends (prefixWord ++ tailWord_612254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612258 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_612258 : Nat := 118140960795 + 612258 * 2 ^ 59
def prefixEnd_612258 : Nat := 4983230072969 + 3 ^ 40 * 612258 * 2
def baseEnd_612258 : Nat := 279451234276062907963807

theorem tailTrace_612258 : CollatzResearch.WordTrace tailWord_612258 prefixEnd_612258 279451234276062907963807 := by
  unfold tailWord_612258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582720953975326546659357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14887255877267537457758285 5582720953975326546659357)
  ·
    refine ⟨2093520357740747454997259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5582720953975326546659357 2093520357740747454997259)
    ·
      refine ⟨3140280536611121182495889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093520357740747454997259 3140280536611121182495889)
      ·
        refine ⟨2355210402458340886871917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3140280536611121182495889 2355210402458340886871917)
        ·
          refine ⟨883203900921877832576969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2355210402458340886871917 883203900921877832576969)
          ·
            refine ⟨662402925691408374432727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883203900921877832576969 662402925691408374432727)
            ·
              refine ⟨993604388537112561649091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662402925691408374432727 993604388537112561649091)
              ·
                refine ⟨1490406582805668842473637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993604388537112561649091 1490406582805668842473637)
                ·
                  refine ⟨279451234276062907963807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490406582805668842473637 279451234276062907963807)
                  ·
                    rfl

theorem cell20_612258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_612258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612258 prefixEnd_612258 := by exact prefixLift 612258
  have htrace : WordTrace (prefixWord ++ tailWord_612258) baseStart_612258 baseEnd_612258 := by
    simpa [prefixWord, tailWord_612258, baseEnd_612258] using wordTrace_append hprefix tailTrace_612258
  have hstable : (prefixWord ++ tailWord_612258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612258).length < 2 ^ (prefixWord ++ tailWord_612258).sum := by decide
  have hdescent : baseEnd_612258 < baseStart_612258 := by decide
  rcases family_descends (prefixWord ++ tailWord_612258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612313 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 2]
def baseStart_612313 : Nat := 118140960795 + 612313 * 2 ^ 59
def prefixEnd_612313 : Nat := 4983230072969 + 3 ^ 40 * 612313 * 2
def baseEnd_612313 : Nat := 279476337774727161130249

theorem tailTrace_612313 : CollatzResearch.WordTrace tailWord_612313 prefixEnd_612313 279476337774727161130249 := by
  unfold tailWord_612313
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332889830702050579889593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14888593220468033719926395 22332889830702050579889593)
  ·
    refine ⟨16749667373026537934917195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22332889830702050579889593 16749667373026537934917195)
    ·
      refine ⟨25124501059539806902375793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16749667373026537934917195 25124501059539806902375793)
      ·
        refine ⟨18843375794654855176781845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25124501059539806902375793 18843375794654855176781845)
        ·
          refine ⟨883283240374446336411649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18843375794654855176781845 883283240374446336411649)
          ·
            refine ⟨662462430280834752308737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883283240374446336411649 662462430280834752308737)
            ·
              refine ⟨496846822710626064231553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662462430280834752308737 496846822710626064231553)
              ·
                refine ⟨372635117032969548173665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496846822710626064231553 372635117032969548173665)
                ·
                  refine ⟨279476337774727161130249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372635117032969548173665 279476337774727161130249)
                  ·
                    rfl

theorem cell20_612313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_612313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612313 prefixEnd_612313 := by exact prefixLift 612313
  have htrace : WordTrace (prefixWord ++ tailWord_612313) baseStart_612313 baseEnd_612313 := by
    simpa [prefixWord, tailWord_612313, baseEnd_612313] using wordTrace_append hprefix tailTrace_612313
  have hstable : (prefixWord ++ tailWord_612313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612313).length < 2 ^ (prefixWord ++ tailWord_612313).sum := by decide
  have hdescent : baseEnd_612313 < baseStart_612313 := by decide
  rcases family_descends (prefixWord ++ tailWord_612313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612376 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_612376 : Nat := 118140960795 + 612376 * 2 ^ 59
def prefixEnd_612376 : Nat := 4983230072969 + 3 ^ 40 * 612376 * 2
def baseEnd_612376 : Nat := 279505092691378942029991

theorem tailTrace_612376 : CollatzResearch.WordTrace tailWord_612376 prefixEnd_612376 279505092691378942029991 := by
  unfold tailWord_612376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167593814736906169716491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14890125086315874892955321 11167593814736906169716491)
  ·
    refine ⟨16751390722105359254574737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11167593814736906169716491 16751390722105359254574737)
    ·
      refine ⟨12563543041579019440931053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16751390722105359254574737 12563543041579019440931053)
      ·
        refine ⟨4711328640592132290349145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12563543041579019440931053 4711328640592132290349145)
        ·
          refine ⟨3533496480444099217761859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4711328640592132290349145 3533496480444099217761859)
          ·
            refine ⟨5300244720666148826642789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3533496480444099217761859 5300244720666148826642789)
            ·
              refine ⟨993795885124902904995523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5300244720666148826642789 993795885124902904995523)
              ·
                refine ⟨1490693827687354357493285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993795885124902904995523 1490693827687354357493285)
                ·
                  refine ⟨279505092691378942029991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1490693827687354357493285 279505092691378942029991)
                  ·
                    rfl

theorem cell20_612376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_612376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612376 prefixEnd_612376 := by exact prefixLift 612376
  have htrace : WordTrace (prefixWord ++ tailWord_612376) baseStart_612376 baseEnd_612376 := by
    simpa [prefixWord, tailWord_612376, baseEnd_612376] using wordTrace_append hprefix tailTrace_612376
  have hstable : (prefixWord ++ tailWord_612376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612376).length < 2 ^ (prefixWord ++ tailWord_612376).sum := by decide
  have hdescent : baseEnd_612376 < baseStart_612376 := by decide
  rcases family_descends (prefixWord ++ tailWord_612376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612386 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_612386 : Nat := 118140960795 + 612386 * 2 ^ 59
def prefixEnd_612386 : Nat := 4983230072969 + 3 ^ 40 * 612386 * 2
def baseEnd_612386 : Nat := 279509656963863351696617

theorem tailTrace_612386 : CollatzResearch.WordTrace tailWord_612386 prefixEnd_612386 279509656963863351696617 := by
  unfold tailWord_612386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5583888089859396011824253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14890368239625056031531341 5583888089859396011824253)
  ·
    refine ⟨2093958033697273504434095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5583888089859396011824253 2093958033697273504434095)
    ·
      refine ⟨3140937050545910256651143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093958033697273504434095 3140937050545910256651143)
      ·
        refine ⟨4711405575818865384976715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3140937050545910256651143 4711405575818865384976715)
        ·
          refine ⟨7067108363728298077465073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711405575818865384976715 7067108363728298077465073)
          ·
            refine ⟨5300331272796223558098805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7067108363728298077465073 5300331272796223558098805)
            ·
              refine ⟨496906056824645958571763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5300331272796223558098805 496906056824645958571763)
              ·
                refine ⟨745359085236968937857645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496906056824645958571763 745359085236968937857645)
                ·
                  refine ⟨279509656963863351696617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745359085236968937857645 279509656963863351696617)
                  ·
                    rfl

theorem cell20_612386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_612386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612386 prefixEnd_612386 := by exact prefixLift 612386
  have htrace : WordTrace (prefixWord ++ tailWord_612386) baseStart_612386 baseEnd_612386 := by
    simpa [prefixWord, tailWord_612386, baseEnd_612386] using wordTrace_append hprefix tailTrace_612386
  have hstable : (prefixWord ++ tailWord_612386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612386).length < 2 ^ (prefixWord ++ tailWord_612386).sum := by decide
  have hdescent : baseEnd_612386 < baseStart_612386 := by decide
  rcases family_descends (prefixWord ++ tailWord_612386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612400 : List Nat := [2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_612400 : Nat := 118140960795 + 612400 * 2 ^ 59
def prefixEnd_612400 : Nat := 4983230072969 + 3 ^ 40 * 612400 * 2
def baseEnd_612400 : Nat := 93172015648447175076631

theorem tailTrace_612400 : CollatzResearch.WordTrace tailWord_612400 prefixEnd_612400 93172015648447175076631 := by
  unfold tailWord_612400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168031490693432219153327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14890708654257909625537769 11168031490693432219153327)
  ·
    refine ⟨16752047236040148328729991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11168031490693432219153327 16752047236040148328729991)
    ·
      refine ⟨25128070854060222493094987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16752047236040148328729991 25128070854060222493094987)
      ·
        refine ⟨37692106281090333739642481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25128070854060222493094987 37692106281090333739642481)
        ·
          refine ⟨28269079710817750304731861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37692106281090333739642481 28269079710817750304731861)
          ·
            refine ⟨662556555722291022767153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28269079710817750304731861 662556555722291022767153)
            ·
              refine ⟨496917416791718267075365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662556555722291022767153 496917416791718267075365)
              ·
                refine ⟨93172015648447175076631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 496917416791718267075365 93172015648447175076631)
                ·
                  rfl

theorem cell20_612400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_612400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612400 prefixEnd_612400 := by exact prefixLift 612400
  have htrace : WordTrace (prefixWord ++ tailWord_612400) baseStart_612400 baseEnd_612400 := by
    simpa [prefixWord, tailWord_612400, baseEnd_612400] using wordTrace_append hprefix tailTrace_612400
  have hstable : (prefixWord ++ tailWord_612400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612400).length < 2 ^ (prefixWord ++ tailWord_612400).sum := by decide
  have hdescent : baseEnd_612400 < baseStart_612400 := by decide
  rcases family_descends (prefixWord ++ tailWord_612400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612428 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_612428 : Nat := 118140960795 + 612428 * 2 ^ 59
def prefixEnd_612428 : Nat := 4983230072969 + 3 ^ 40 * 612428 * 2
def baseEnd_612428 : Nat := 279528826908297872296445

theorem tailTrace_612428 : CollatzResearch.WordTrace tailWord_612428 prefixEnd_612428 279528826908297872296445 := by
  unfold tailWord_612428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168542112642712610162969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14891389483523616813550625 11168542112642712610162969)
  ·
    refine ⟨8376406584482034457622227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11168542112642712610162969 8376406584482034457622227)
    ·
      refine ⟨12564609876723051686433341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8376406584482034457622227 12564609876723051686433341)
      ·
        refine ⟨4711728703771144382412503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12564609876723051686433341 4711728703771144382412503)
        ·
          refine ⟨7067593055656716573618755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711728703771144382412503 7067593055656716573618755)
          ·
            refine ⟨10601389583485074860428133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7067593055656716573618755 10601389583485074860428133)
            ·
              refine ⟨1987760546903451536330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10601389583485074860428133 1987760546903451536330275)
              ·
                refine ⟨2981640820355177304495413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987760546903451536330275 2981640820355177304495413)
                ·
                  refine ⟨279528826908297872296445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2981640820355177304495413 279528826908297872296445)
                  ·
                    rfl

theorem cell20_612428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_612428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612428 prefixEnd_612428 := by exact prefixLift 612428
  have htrace : WordTrace (prefixWord ++ tailWord_612428) baseStart_612428 baseEnd_612428 := by
    simpa [prefixWord, tailWord_612428, baseEnd_612428] using wordTrace_append hprefix tailTrace_612428
  have hstable : (prefixWord ++ tailWord_612428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612428).length < 2 ^ (prefixWord ++ tailWord_612428).sum := by decide
  have hdescent : baseEnd_612428 < baseStart_612428 := by decide
  rcases family_descends (prefixWord ++ tailWord_612428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612483 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_612483 : Nat := 118140960795 + 612483 * 2 ^ 59
def prefixEnd_612483 : Nat := 4983230072969 + 3 ^ 40 * 612483 * 2
def baseEnd_612483 : Nat := 279553930406962125462887

theorem tailTrace_612483 : CollatzResearch.WordTrace tailWord_612483 prefixEnd_612483 279553930406962125462887 := by
  unfold tailWord_612483
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339090240086169613578103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14892726826724113075718735 22339090240086169613578103)
  ·
    refine ⟨33508635360129254420367155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22339090240086169613578103 33508635360129254420367155)
    ·
      refine ⟨50262953040193881630550733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33508635360129254420367155 50262953040193881630550733)
      ·
        refine ⟨18848607390072705611456525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50262953040193881630550733 18848607390072705611456525)
        ·
          refine ⟨7068227771277264604296197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18848607390072705611456525 7068227771277264604296197)
          ·
            refine ⟨1325292707114487113305537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7068227771277264604296197 1325292707114487113305537)
            ·
              refine ⟨993969530335865334979153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325292707114487113305537 993969530335865334979153)
              ·
                refine ⟨745477147751899001234365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993969530335865334979153 745477147751899001234365)
                ·
                  refine ⟨279553930406962125462887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745477147751899001234365 279553930406962125462887)
                  ·
                    rfl

theorem cell20_612483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_612483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612483 prefixEnd_612483 := by exact prefixLift 612483
  have htrace : WordTrace (prefixWord ++ tailWord_612483) baseStart_612483 baseEnd_612483 := by
    simpa [prefixWord, tailWord_612483, baseEnd_612483] using wordTrace_append hprefix tailTrace_612483
  have hstable : (prefixWord ++ tailWord_612483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612483).length < 2 ^ (prefixWord ++ tailWord_612483).sum := by decide
  have hdescent : baseEnd_612483 < baseStart_612483 := by decide
  rcases family_descends (prefixWord ++ tailWord_612483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612549 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_612549 : Nat := 118140960795 + 612549 * 2 ^ 59
def prefixEnd_612549 : Nat := 4983230072969 + 3 ^ 40 * 612549 * 2
def baseEnd_612549 : Nat := 279584054605359229262617

theorem tailTrace_612549 : CollatzResearch.WordTrace tailWord_612549 prefixEnd_612549 279584054605359229262617 := by
  unfold tailWord_612549
  simp only [CollatzResearch.WordTrace]
  refine ⟨22341497457847062885480701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14894331638564708590320467 22341497457847062885480701)
  ·
    refine ⟨8378061546692648582055263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22341497457847062885480701 8378061546692648582055263)
    ·
      refine ⟨12567092320038972873082895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8378061546692648582055263 12567092320038972873082895)
      ·
        refine ⟨18850638480058459309624343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12567092320038972873082895 18850638480058459309624343)
        ·
          refine ⟨28275957720087688964436515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18850638480058459309624343 28275957720087688964436515)
          ·
            refine ⟨42413936580131533446654773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28275957720087688964436515 42413936580131533446654773)
            ·
              refine ⟨3976306554387331260623885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42413936580131533446654773 3976306554387331260623885)
              ·
                refine ⟨1491114957895249222733957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3976306554387331260623885 1491114957895249222733957)
                ·
                  refine ⟨279584054605359229262617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491114957895249222733957 279584054605359229262617)
                  ·
                    rfl

theorem cell20_612549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_612549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612549 prefixEnd_612549 := by exact prefixLift 612549
  have htrace : WordTrace (prefixWord ++ tailWord_612549) baseStart_612549 baseEnd_612549 := by
    simpa [prefixWord, tailWord_612549, baseEnd_612549] using wordTrace_append hprefix tailTrace_612549
  have hstable : (prefixWord ++ tailWord_612549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612549).length < 2 ^ (prefixWord ++ tailWord_612549).sum := by decide
  have hdescent : baseEnd_612549 < baseStart_612549 := by decide
  rcases family_descends (prefixWord ++ tailWord_612549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612559 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 3]
def baseStart_612559 : Nat := 118140960795 + 612559 * 2 ^ 59
def prefixEnd_612559 : Nat := 4983230072969 + 3 ^ 40 * 612559 * 2
def baseEnd_612559 : Nat := 279588618877843638929243

theorem tailTrace_612559 : CollatzResearch.WordTrace tailWord_612559 prefixEnd_612559 279588618877843638929243 := by
  unfold tailWord_612559
  simp only [CollatzResearch.WordTrace]
  refine ⟨22341862187810834593344731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14894574791873889728896487 22341862187810834593344731)
  ·
    refine ⟨33512793281716251890017097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22341862187810834593344731 33512793281716251890017097)
    ·
      refine ⟨25134594961287188917512823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33512793281716251890017097 25134594961287188917512823)
      ·
        refine ⟨37701892441930783376269235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25134594961287188917512823 37701892441930783376269235)
        ·
          refine ⟨56552838662896175064403853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37701892441930783376269235 56552838662896175064403853)
          ·
            refine ⟨21207314498586065649151445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56552838662896175064403853 21207314498586065649151445)
            ·
              refine ⟨497046433560610913651987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21207314498586065649151445 497046433560610913651987)
              ·
                refine ⟨745569650340916370477981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497046433560610913651987 745569650340916370477981)
                ·
                  refine ⟨279588618877843638929243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745569650340916370477981 279588618877843638929243)
                  ·
                    rfl

theorem cell20_612559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_612559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612559 prefixEnd_612559 := by exact prefixLift 612559
  have htrace : WordTrace (prefixWord ++ tailWord_612559) baseStart_612559 baseEnd_612559 := by
    simpa [prefixWord, tailWord_612559, baseEnd_612559] using wordTrace_append hprefix tailTrace_612559
  have hstable : (prefixWord ++ tailWord_612559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612559).length < 2 ^ (prefixWord ++ tailWord_612559).sum := by decide
  have hdescent : baseEnd_612559 < baseStart_612559 := by decide
  rcases family_descends (prefixWord ++ tailWord_612559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612563 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_612563 : Nat := 118140960795 + 612563 * 2 ^ 59
def prefixEnd_612563 : Nat := 4983230072969 + 3 ^ 40 * 612563 * 2
def baseEnd_612563 : Nat := 279590444586837402795893

theorem tailTrace_612563 : CollatzResearch.WordTrace tailWord_612563 prefixEnd_612563 279590444586837402795893 := by
  unfold tailWord_612563
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342008079796343276490343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14894672053197562184326895 22342008079796343276490343)
  ·
    refine ⟨33513012119694514914735515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22342008079796343276490343 33513012119694514914735515)
    ·
      refine ⟨50269518179541772372103273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33513012119694514914735515 50269518179541772372103273)
      ·
        refine ⟨37702138634656329279077455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50269518179541772372103273 37702138634656329279077455)
        ·
          refine ⟨56553207951984493918616183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37702138634656329279077455 56553207951984493918616183)
          ·
            refine ⟨84829811927976740877924275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56553207951984493918616183 84829811927976740877924275)
            ·
              refine ⟨127244717891965111316886413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84829811927976740877924275 127244717891965111316886413)
              ·
                refine ⟨47716769209486916743832405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127244717891965111316886413 47716769209486916743832405)
                ·
                  refine ⟨279590444586837402795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47716769209486916743832405 279590444586837402795893)
                  ·
                    rfl

theorem cell20_612563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_612563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612563 prefixEnd_612563 := by exact prefixLift 612563
  have htrace : WordTrace (prefixWord ++ tailWord_612563) baseStart_612563 baseEnd_612563 := by
    simpa [prefixWord, tailWord_612563, baseEnd_612563] using wordTrace_append hprefix tailTrace_612563
  have hstable : (prefixWord ++ tailWord_612563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612563).length < 2 ^ (prefixWord ++ tailWord_612563).sum := by decide
  have hdescent : baseEnd_612563 < baseStart_612563 := by decide
  rcases family_descends (prefixWord ++ tailWord_612563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612579 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 2]
def baseStart_612579 : Nat := 118140960795 + 612579 * 2 ^ 59
def prefixEnd_612579 : Nat := 4983230072969 + 3 ^ 40 * 612579 * 2
def baseEnd_612579 : Nat := 279597747422812458262495

theorem tailTrace_612579 : CollatzResearch.WordTrace tailWord_612579 prefixEnd_612579 279597747422812458262495 := by
  unfold tailWord_612579
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342591647738378009072791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14895061098492252006048527 22342591647738378009072791)
  ·
    refine ⟨33513887471607567013609187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22342591647738378009072791 33513887471607567013609187)
    ·
      refine ⟨50270831207411350520413781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33513887471607567013609187 50270831207411350520413781)
      ·
        refine ⟨589111303211851763911099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 50270831207411350520413781 589111303211851763911099)
        ·
          refine ⟨883666954817777645866649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589111303211851763911099 883666954817777645866649)
          ·
            refine ⟨662750216113333234399987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883666954817777645866649 662750216113333234399987)
            ·
              refine ⟨994125324169999851599981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662750216113333234399987 994125324169999851599981)
              ·
                refine ⟨372796996563749944349993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 994125324169999851599981 372796996563749944349993)
                ·
                  refine ⟨279597747422812458262495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372796996563749944349993 279597747422812458262495)
                  ·
                    rfl

theorem cell20_612579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2].length) (baseStart_612579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612579 prefixEnd_612579 := by exact prefixLift 612579
  have htrace : WordTrace (prefixWord ++ tailWord_612579) baseStart_612579 baseEnd_612579 := by
    simpa [prefixWord, tailWord_612579, baseEnd_612579] using wordTrace_append hprefix tailTrace_612579
  have hstable : (prefixWord ++ tailWord_612579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612579).length < 2 ^ (prefixWord ++ tailWord_612579).sum := by decide
  have hdescent : baseEnd_612579 < baseStart_612579 := by decide
  rcases family_descends (prefixWord ++ tailWord_612579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612604 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_612604 : Nat := 118140960795 + 612604 * 2 ^ 59
def prefixEnd_612604 : Nat := 4983230072969 + 3 ^ 40 * 612604 * 2
def baseEnd_612604 : Nat := 279609158104023482429059

theorem tailTrace_612604 : CollatzResearch.WordTrace tailWord_612604 prefixEnd_612604 279609158104023482429059 := by
  unfold tailWord_612604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11171751736323903639366433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14895668981765204852488577 11171751736323903639366433)
  ·
    refine ⟨8378813802242927729524825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11171751736323903639366433 8378813802242927729524825)
    ·
      refine ⟨6284110351682195797143619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8378813802242927729524825 6284110351682195797143619)
      ·
        refine ⟨9426165527523293695715429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284110351682195797143619 9426165527523293695715429)
        ·
          refine ⟨1767406036410617567946643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9426165527523293695715429 1767406036410617567946643)
          ·
            refine ⟨2651109054615926351919965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767406036410617567946643 2651109054615926351919965)
            ·
              refine ⟨994165895480972381969987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2651109054615926351919965 994165895480972381969987)
              ·
                refine ⟨1491248843221458572954981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994165895480972381969987 1491248843221458572954981)
                ·
                  refine ⟨279609158104023482429059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491248843221458572954981 279609158104023482429059)
                  ·
                    rfl

theorem cell20_612604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_612604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612604 prefixEnd_612604 := by exact prefixLift 612604
  have htrace : WordTrace (prefixWord ++ tailWord_612604) baseStart_612604 baseEnd_612604 := by
    simpa [prefixWord, tailWord_612604, baseEnd_612604] using wordTrace_append hprefix tailTrace_612604
  have hstable : (prefixWord ++ tailWord_612604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612604).length < 2 ^ (prefixWord ++ tailWord_612604).sum := by decide
  have hdescent : baseEnd_612604 < baseStart_612604 := by decide
  rcases family_descends (prefixWord ++ tailWord_612604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612632 : List Nat := [2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_612632 : Nat := 118140960795 + 612632 * 2 ^ 59
def prefixEnd_612632 : Nat := 4983230072969 + 3 ^ 40 * 612632 * 2
def baseEnd_612632 : Nat := 93207312688993276498537

theorem tailTrace_612632 : CollatzResearch.WordTrace tailWord_612632 prefixEnd_612632 93207312688993276498537 := by
  unfold tailWord_612632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11172262358273184030376075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14896349811030912040501433 11172262358273184030376075)
  ·
    refine ⟨16758393537409776045564113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11172262358273184030376075 16758393537409776045564113)
    ·
      refine ⟨12568795153057332034173085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16758393537409776045564113 12568795153057332034173085)
      ·
        refine ⟨4713298182396499512814907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12568795153057332034173085 4713298182396499512814907)
        ·
          refine ⟨7069947273594749269222361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713298182396499512814907 7069947273594749269222361)
          ·
            refine ⟨5302460455196061951916771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7069947273594749269222361 5302460455196061951916771)
            ·
              refine ⟨7953690682794092927875157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302460455196061951916771 7953690682794092927875157)
              ·
                refine ⟨93207312688993276498537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7953690682794092927875157 93207312688993276498537)
                ·
                  rfl

theorem cell20_612632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_612632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612632 prefixEnd_612632 := by exact prefixLift 612632
  have htrace : WordTrace (prefixWord ++ tailWord_612632) baseStart_612632 baseEnd_612632 := by
    simpa [prefixWord, tailWord_612632, baseEnd_612632] using wordTrace_append hprefix tailTrace_612632
  have hstable : (prefixWord ++ tailWord_612632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612632).length < 2 ^ (prefixWord ++ tailWord_612632).sum := by decide
  have hdescent : baseEnd_612632 < baseStart_612632 := by decide
  rcases family_descends (prefixWord ++ tailWord_612632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612677 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_612677 : Nat := 118140960795 + 612677 * 2 ^ 59
def prefixEnd_612677 : Nat := 4983230072969 + 3 ^ 40 * 612677 * 2
def baseEnd_612677 : Nat := 279642477293159672995427

theorem tailTrace_612677 : CollatzResearch.WordTrace tailWord_612677 prefixEnd_612677 279642477293159672995427 := by
  unfold tailWord_612677
  simp only [CollatzResearch.WordTrace]
  refine ⟨22346166001383340746140285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14897444000922227164093523 22346166001383340746140285)
  ·
    refine ⟨8379812250518752779802607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22346166001383340746140285 8379812250518752779802607)
    ·
      refine ⟨12569718375778129169703911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8379812250518752779802607 12569718375778129169703911)
      ·
        refine ⟨18854577563667193754555867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12569718375778129169703911 18854577563667193754555867)
        ·
          refine ⟨28281866345500790631833801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18854577563667193754555867 28281866345500790631833801)
          ·
            refine ⟨21211399759125592973875351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28281866345500790631833801 21211399759125592973875351)
            ·
              refine ⟨31817099638688389460813027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21211399759125592973875351 31817099638688389460813027)
              ·
                refine ⟨47725649458032584191219541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31817099638688389460813027 47725649458032584191219541)
                ·
                  refine ⟨279642477293159672995427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47725649458032584191219541 279642477293159672995427)
                  ·
                    rfl

theorem cell20_612677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_612677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612677 prefixEnd_612677 := by exact prefixLift 612677
  have htrace : WordTrace (prefixWord ++ tailWord_612677) baseStart_612677 baseEnd_612677 := by
    simpa [prefixWord, tailWord_612677, baseEnd_612677] using wordTrace_append hprefix tailTrace_612677
  have hstable : (prefixWord ++ tailWord_612677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612677).length < 2 ^ (prefixWord ++ tailWord_612677).sum := by decide
  have hdescent : baseEnd_612677 < baseStart_612677 := by decide
  rcases family_descends (prefixWord ++ tailWord_612677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612708 : List Nat := [2, 3, 1, 1, 3, 1, 9]
def baseStart_612708 : Nat := 118140960795 + 612708 * 2 ^ 59
def prefixEnd_612708 : Nat := 4983230072969 + 3 ^ 40 * 612708 * 2
def baseEnd_612708 : Nat := 31072958504206815884663

theorem tailTrace_612708 : CollatzResearch.WordTrace tailWord_612708 prefixEnd_612708 31072958504206815884663 := by
  unfold tailWord_612708
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173648332135516520259389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14898197776180688693679185 11173648332135516520259389)
  ·
    refine ⟨4190118124550818695097271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11173648332135516520259389 4190118124550818695097271)
    ·
      refine ⟨6285177186826228042645907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4190118124550818695097271 6285177186826228042645907)
      ·
        refine ⟨9427765780239342063968861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285177186826228042645907 9427765780239342063968861)
        ·
          refine ⟨3535412167589753273988323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9427765780239342063968861 3535412167589753273988323)
          ·
            refine ⟨5303118251384629910982485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535412167589753273988323 5303118251384629910982485)
            ·
              refine ⟨31072958504206815884663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5303118251384629910982485 31072958504206815884663)
              ·
                rfl

theorem cell20_612708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_612708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612708 prefixEnd_612708 := by exact prefixLift 612708
  have htrace : WordTrace (prefixWord ++ tailWord_612708) baseStart_612708 baseEnd_612708 := by
    simpa [prefixWord, tailWord_612708, baseEnd_612708] using wordTrace_append hprefix tailTrace_612708
  have hstable : (prefixWord ++ tailWord_612708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612708).length < 2 ^ (prefixWord ++ tailWord_612708).sum := by decide
  have hdescent : baseEnd_612708 < baseStart_612708 := by decide
  rcases family_descends (prefixWord ++ tailWord_612708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612711 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_612711 : Nat := 118140960795 + 612711 * 2 ^ 59
def prefixEnd_612711 : Nat := 4983230072969 + 3 ^ 40 * 612711 * 2
def baseEnd_612711 : Nat := 279657995819606665861955

theorem tailTrace_612711 : CollatzResearch.WordTrace tailWord_612711 prefixEnd_612711 279657995819606665861955 := by
  unfold tailWord_612711
  simp only [CollatzResearch.WordTrace]
  refine ⟨22347406083260164552877987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14898270722173443035251991 22347406083260164552877987)
  ·
    refine ⟨33521109124890246829316981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22347406083260164552877987 33521109124890246829316981)
    ·
      refine ⟨3142603980458460640248467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33521109124890246829316981 3142603980458460640248467)
      ·
        refine ⟨4713905970687690960372701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142603980458460640248467 4713905970687690960372701)
        ·
          refine ⟨1767714739007884110139763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4713905970687690960372701 1767714739007884110139763)
          ·
            refine ⟨2651572108511826165209645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767714739007884110139763 2651572108511826165209645)
            ·
              refine ⟨994339540691934811953617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2651572108511826165209645 994339540691934811953617)
              ·
                refine ⟨745754655518951108965213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994339540691934811953617 745754655518951108965213)
                ·
                  refine ⟨279657995819606665861955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745754655518951108965213 279657995819606665861955)
                  ·
                    rfl

theorem cell20_612711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_612711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612711 prefixEnd_612711 := by exact prefixLift 612711
  have htrace : WordTrace (prefixWord ++ tailWord_612711) baseStart_612711 baseEnd_612711 := by
    simpa [prefixWord, tailWord_612711, baseEnd_612711] using wordTrace_append hprefix tailTrace_612711
  have hstable : (prefixWord ++ tailWord_612711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612711).length < 2 ^ (prefixWord ++ tailWord_612711).sum := by decide
  have hdescent : baseEnd_612711 < baseStart_612711 := by decide
  rcases family_descends (prefixWord ++ tailWord_612711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612715 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_612715 : Nat := 118140960795 + 612715 * 2 ^ 59
def prefixEnd_612715 : Nat := 4983230072969 + 3 ^ 40 * 612715 * 2
def baseEnd_612715 : Nat := 279659821528600429728605

theorem tailTrace_612715 : CollatzResearch.WordTrace tailWord_612715 prefixEnd_612715 279659821528600429728605 := by
  unfold tailWord_612715
  simp only [CollatzResearch.WordTrace]
  refine ⟨22347551975245673236023599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14898367983497115490682399 22347551975245673236023599)
  ·
    refine ⟨33521327962868509854035399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22347551975245673236023599 33521327962868509854035399)
    ·
      refine ⟨50281991944302764781053099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33521327962868509854035399 50281991944302764781053099)
      ·
        refine ⟨75422987916454147171579649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50281991944302764781053099 75422987916454147171579649)
        ·
          refine ⟨56567240937340610378684737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75422987916454147171579649 56567240937340610378684737)
          ·
            refine ⟨42425430703005457784013553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56567240937340610378684737 42425430703005457784013553)
            ·
              refine ⟨31819073027254093338010165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42425430703005457784013553 31819073027254093338010165)
              ·
                refine ⟨2983038096305071250438453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31819073027254093338010165 2983038096305071250438453)
                ·
                  refine ⟨279659821528600429728605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2983038096305071250438453 279659821528600429728605)
                  ·
                    rfl

theorem cell20_612715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_612715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612715 prefixEnd_612715 := by exact prefixLift 612715
  have htrace : WordTrace (prefixWord ++ tailWord_612715) baseStart_612715 baseEnd_612715 := by
    simpa [prefixWord, tailWord_612715, baseEnd_612715] using wordTrace_append hprefix tailTrace_612715
  have hstable : (prefixWord ++ tailWord_612715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612715).length < 2 ^ (prefixWord ++ tailWord_612715).sum := by decide
  have hdescent : baseEnd_612715 < baseStart_612715 := by decide
  rcases family_descends (prefixWord ++ tailWord_612715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612738 : List Nat := [3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_612738 : Nat := 118140960795 + 612738 * 2 ^ 59
def prefixEnd_612738 : Nat := 4983230072969 + 3 ^ 40 * 612738 * 2
def baseEnd_612738 : Nat := 93223439785104857320615

theorem tailTrace_612738 : CollatzResearch.WordTrace tailWord_612738 prefixEnd_612738 93223439785104857320615 := by
  unfold tailWord_612738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587097713540587041027717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14898927236108232109407245 5587097713540587041027717)
  ·
    refine ⟨1047580821288860070192697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5587097713540587041027717 1047580821288860070192697)
    ·
      refine ⟨785685615966645052644523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1047580821288860070192697 785685615966645052644523)
      ·
        refine ⟨1178528423949967578966785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785685615966645052644523 1178528423949967578966785)
        ·
          refine ⟨883896317962475684225089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178528423949967578966785 883896317962475684225089)
          ·
            refine ⟨662922238471856763168817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883896317962475684225089 662922238471856763168817)
            ·
              refine ⟨497191678853892572376613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662922238471856763168817 497191678853892572376613)
              ·
                refine ⟨93223439785104857320615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497191678853892572376613 93223439785104857320615)
                ·
                  rfl

theorem cell20_612738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_612738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612738 prefixEnd_612738 := by exact prefixLift 612738
  have htrace : WordTrace (prefixWord ++ tailWord_612738) baseStart_612738 baseEnd_612738 := by
    simpa [prefixWord, tailWord_612738, baseEnd_612738] using wordTrace_append hprefix tailTrace_612738
  have hstable : (prefixWord ++ tailWord_612738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612738).length < 2 ^ (prefixWord ++ tailWord_612738).sum := by decide
  have hdescent : baseEnd_612738 < baseStart_612738 := by decide
  rcases family_descends (prefixWord ++ tailWord_612738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612769 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 2]
def baseStart_612769 : Nat := 118140960795 + 612769 * 2 ^ 59
def prefixEnd_612769 : Nat := 4983230072969 + 3 ^ 40 * 612769 * 2
def baseEnd_612769 : Nat := 279684468600016241928385

theorem tailTrace_612769 : CollatzResearch.WordTrace tailWord_612769 prefixEnd_612769 279684468600016241928385 := by
  unfold tailWord_612769
  simp only [CollatzResearch.WordTrace]
  refine ⟨22349521517050040458489361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14899681011366693638992907 22349521517050040458489361)
  ·
    refine ⟨16762141137787530343867021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22349521517050040458489361 16762141137787530343867021)
    ·
      refine ⟨6285802926670323878950133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16762141137787530343867021 6285802926670323878950133)
      ·
        refine ⟨589294024375342863651575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6285802926670323878950133 589294024375342863651575)
        ·
          refine ⟨883941036563014295477363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589294024375342863651575 883941036563014295477363)
          ·
            refine ⟨1325911554844521443216045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883941036563014295477363 1325911554844521443216045)
            ·
              refine ⟨497216833066695541206017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1325911554844521443216045 497216833066695541206017)
              ·
                refine ⟨372912624800021655904513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497216833066695541206017 372912624800021655904513)
                ·
                  refine ⟨279684468600016241928385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372912624800021655904513 279684468600016241928385)
                  ·
                    rfl

theorem cell20_612769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_612769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612769 prefixEnd_612769 := by exact prefixLift 612769
  have htrace : WordTrace (prefixWord ++ tailWord_612769) baseStart_612769 baseEnd_612769 := by
    simpa [prefixWord, tailWord_612769, baseEnd_612769] using wordTrace_append hprefix tailTrace_612769
  have hstable : (prefixWord ++ tailWord_612769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612769).length < 2 ^ (prefixWord ++ tailWord_612769).sum := by decide
  have hdescent : baseEnd_612769 < baseStart_612769 := by decide
  rcases family_descends (prefixWord ++ tailWord_612769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612770 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_612770 : Nat := 118140960795 + 612770 * 2 ^ 59
def prefixEnd_612770 : Nat := 4983230072969 + 3 ^ 40 * 612770 * 2
def baseEnd_612770 : Nat := 279684925027264682895047

theorem tailTrace_612770 : CollatzResearch.WordTrace tailWord_612770 prefixEnd_612770 279684925027264682895047 := by
  unfold tailWord_612770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587389497511604407318941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14899705326697611752850509 5587389497511604407318941)
  ·
    refine ⟨2095271061566851652744603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5587389497511604407318941 2095271061566851652744603)
    ·
      refine ⟨3142906592350277479116905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095271061566851652744603 3142906592350277479116905)
      ·
        refine ⟨2357179944262708109337679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142906592350277479116905 2357179944262708109337679)
        ·
          refine ⟨3535769916394062164006519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357179944262708109337679 3535769916394062164006519)
          ·
            refine ⟨5303654874591093246009779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535769916394062164006519 5303654874591093246009779)
            ·
              refine ⟨7955482311886639869014669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303654874591093246009779 7955482311886639869014669)
              ·
                refine ⟨2983305866957489950880501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7955482311886639869014669 2983305866957489950880501)
                ·
                  refine ⟨279684925027264682895047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2983305866957489950880501 279684925027264682895047)
                  ·
                    rfl

theorem cell20_612770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_612770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612770 prefixEnd_612770 := by exact prefixLift 612770
  have htrace : WordTrace (prefixWord ++ tailWord_612770) baseStart_612770 baseEnd_612770 := by
    simpa [prefixWord, tailWord_612770, baseEnd_612770] using wordTrace_append hprefix tailTrace_612770
  have hstable : (prefixWord ++ tailWord_612770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612770).length < 2 ^ (prefixWord ++ tailWord_612770).sum := by decide
  have hdescent : baseEnd_612770 < baseStart_612770 := by decide
  rcases family_descends (prefixWord ++ tailWord_612770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612773 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 2]
def baseStart_612773 : Nat := 118140960795 + 612773 * 2 ^ 59
def prefixEnd_612773 : Nat := 4983230072969 + 3 ^ 40 * 612773 * 2
def baseEnd_612773 : Nat := 279686294309010005795035

theorem tailTrace_612773 : CollatzResearch.WordTrace tailWord_612773 prefixEnd_612773 279686294309010005795035 := by
  unfold tailWord_612773
  simp only [CollatzResearch.WordTrace]
  refine ⟨22349667409035549141634973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14899778272690366094423315 22349667409035549141634973)
  ·
    refine ⟨8381125278388330928113115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22349667409035549141634973 8381125278388330928113115)
    ·
      refine ⟨12571687917582496392169673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8381125278388330928113115 12571687917582496392169673)
      ·
        refine ⟨9428765938186872294127255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12571687917582496392169673 9428765938186872294127255)
        ·
          refine ⟨14143148907280308441190883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428765938186872294127255 14143148907280308441190883)
          ·
            refine ⟨21214723360920462661786325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14143148907280308441190883 21214723360920462661786325)
            ·
              refine ⟨497220078771573343635617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21214723360920462661786325 497220078771573343635617)
              ·
                refine ⟨372915059078680007726713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497220078771573343635617 372915059078680007726713)
                ·
                  refine ⟨279686294309010005795035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372915059078680007726713 279686294309010005795035)
                  ·
                    rfl

theorem cell20_612773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_612773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612773 prefixEnd_612773 := by exact prefixLift 612773
  have htrace : WordTrace (prefixWord ++ tailWord_612773) baseStart_612773 baseEnd_612773 := by
    simpa [prefixWord, tailWord_612773, baseEnd_612773] using wordTrace_append hprefix tailTrace_612773
  have hstable : (prefixWord ++ tailWord_612773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612773).length < 2 ^ (prefixWord ++ tailWord_612773).sum := by decide
  have hdescent : baseEnd_612773 < baseStart_612773 := by decide
  rcases family_descends (prefixWord ++ tailWord_612773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612818 : List Nat := [3, 2, 2, 4, 2, 7]
def baseStart_612818 : Nat := 118140960795 + 612818 * 2 ^ 59
def prefixEnd_612818 : Nat := 4983230072969 + 3 ^ 40 * 612818 * 2
def baseEnd_612818 : Nat := 10359512353155179603513

theorem tailTrace_612818 : CollatzResearch.WordTrace tailWord_612818 prefixEnd_612818 10359512353155179603513 := by
  unfold tailWord_612818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587827173468130456755777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14900872462581681218015405 5587827173468130456755777)
  ·
    refine ⟨4190870380101097842566833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5587827173468130456755777 4190870380101097842566833)
    ·
      refine ⟨3143152785075823381925125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4190870380101097842566833 3143152785075823381925125)
      ·
        refine ⟨589341147201716884110961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3143152785075823381925125 589341147201716884110961)
        ·
          refine ⟨442005860401287663083221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589341147201716884110961 442005860401287663083221)
          ·
            refine ⟨10359512353155179603513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 442005860401287663083221 10359512353155179603513)
            ·
              rfl

theorem cell20_612818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 7].length) (baseStart_612818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612818 prefixEnd_612818 := by exact prefixLift 612818
  have htrace : WordTrace (prefixWord ++ tailWord_612818) baseStart_612818 baseEnd_612818 := by
    simpa [prefixWord, tailWord_612818, baseEnd_612818] using wordTrace_append hprefix tailTrace_612818
  have hstable : (prefixWord ++ tailWord_612818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612818).length < 2 ^ (prefixWord ++ tailWord_612818).sum := by decide
  have hdescent : baseEnd_612818 < baseStart_612818 := by decide
  rcases family_descends (prefixWord ++ tailWord_612818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612832 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_612832 : Nat := 118140960795 + 612832 * 2 ^ 59
def prefixEnd_612832 : Nat := 4983230072969 + 3 ^ 40 * 612832 * 2
def baseEnd_612832 : Nat := 279713223516668022828127

theorem tailTrace_612832 : CollatzResearch.WordTrace tailWord_612832 prefixEnd_612832 279713223516668022828127 := by
  unfold tailWord_612832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11175909657910901109016375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14901212877214534812021833 11175909657910901109016375)
  ·
    refine ⟨16763864486866351663524563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11175909657910901109016375 16763864486866351663524563)
    ·
      refine ⟨25145796730299527495286845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16763864486866351663524563 25145796730299527495286845)
      ·
        refine ⟨9429673773862322810732567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25145796730299527495286845 9429673773862322810732567)
        ·
          refine ⟨14144510660793484216098851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9429673773862322810732567 14144510660793484216098851)
          ·
            refine ⟨21216765991190226324148277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14144510660793484216098851 21216765991190226324148277)
            ·
              refine ⟨1989071811674083717888901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21216765991190226324148277 1989071811674083717888901)
              ·
                refine ⟨372950964688890697104169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1989071811674083717888901 372950964688890697104169)
                ·
                  refine ⟨279713223516668022828127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372950964688890697104169 279713223516668022828127)
                  ·
                    rfl

theorem cell20_612832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_612832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612832 prefixEnd_612832 := by exact prefixLift 612832
  have htrace : WordTrace (prefixWord ++ tailWord_612832) baseStart_612832 baseEnd_612832 := by
    simpa [prefixWord, tailWord_612832, baseEnd_612832] using wordTrace_append hprefix tailTrace_612832
  have hstable : (prefixWord ++ tailWord_612832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612832).length < 2 ^ (prefixWord ++ tailWord_612832).sum := by decide
  have hdescent : baseEnd_612832 < baseStart_612832 := by decide
  rcases family_descends (prefixWord ++ tailWord_612832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612867 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_612867 : Nat := 118140960795 + 612867 * 2 ^ 59
def prefixEnd_612867 : Nat := 4983230072969 + 3 ^ 40 * 612867 * 2
def baseEnd_612867 : Nat := 279729198470363456661317

theorem tailTrace_612867 : CollatzResearch.WordTrace tailWord_612867 prefixEnd_612867 279729198470363456661317 := by
  unfold tailWord_612867
  simp only [CollatzResearch.WordTrace]
  refine ⟨22353095870695003195556855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14902063913796668797037903 22353095870695003195556855)
  ·
    refine ⟨33529643806042504793335283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22353095870695003195556855 33529643806042504793335283)
    ·
      refine ⟨50294465709063757190002925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33529643806042504793335283 50294465709063757190002925)
      ·
        refine ⟨18860424640898908946251097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50294465709063757190002925 18860424640898908946251097)
        ·
          refine ⟨14145318480674181709688323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18860424640898908946251097 14145318480674181709688323)
          ·
            refine ⟨21217977721011272564532485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14145318480674181709688323 21217977721011272564532485)
            ·
              refine ⟨3978370822689613605849841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21217977721011272564532485 3978370822689613605849841)
              ·
                refine ⟨2983778117017210204387381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3978370822689613605849841 2983778117017210204387381)
                ·
                  refine ⟨279729198470363456661317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2983778117017210204387381 279729198470363456661317)
                  ·
                    rfl

theorem cell20_612867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_612867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612867 prefixEnd_612867 := by exact prefixLift 612867
  have htrace : WordTrace (prefixWord ++ tailWord_612867) baseStart_612867 baseEnd_612867 := by
    simpa [prefixWord, tailWord_612867, baseEnd_612867] using wordTrace_append hprefix tailTrace_612867
  have hstable : (prefixWord ++ tailWord_612867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612867).length < 2 ^ (prefixWord ++ tailWord_612867).sum := by decide
  have hdescent : baseEnd_612867 < baseStart_612867 := by decide
  rcases family_descends (prefixWord ++ tailWord_612867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612887 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_612887 : Nat := 118140960795 + 612887 * 2 ^ 59
def prefixEnd_612887 : Nat := 4983230072969 + 3 ^ 40 * 612887 * 2
def baseEnd_612887 : Nat := 279738327015332275994569

theorem tailTrace_612887 : CollatzResearch.WordTrace tailWord_612887 prefixEnd_612887 279738327015332275994569 := by
  unfold tailWord_612887
  simp only [CollatzResearch.WordTrace]
  refine ⟨22353825330622546611284915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14902550220415031074189943 22353825330622546611284915)
  ·
    refine ⟨33530737995933819916927373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22353825330622546611284915 33530737995933819916927373)
    ·
      refine ⟨12574026748475182468847765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33530737995933819916927373 12574026748475182468847765)
      ·
        refine ⟨589407503834774178227239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12574026748475182468847765 589407503834774178227239)
        ·
          refine ⟨884111255752161267340859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589407503834774178227239 884111255752161267340859)
          ·
            refine ⟨1326166883628241901011289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884111255752161267340859 1326166883628241901011289)
            ·
              refine ⟨994625162721181425758467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326166883628241901011289 994625162721181425758467)
              ·
                refine ⟨1491937744081772138637701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994625162721181425758467 1491937744081772138637701)
                ·
                  refine ⟨279738327015332275994569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491937744081772138637701 279738327015332275994569)
                  ·
                    rfl

theorem cell20_612887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_612887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612887 prefixEnd_612887 := by exact prefixLift 612887
  have htrace : WordTrace (prefixWord ++ tailWord_612887) baseStart_612887 baseEnd_612887 := by
    simpa [prefixWord, tailWord_612887, baseEnd_612887] using wordTrace_append hprefix tailTrace_612887
  have hstable : (prefixWord ++ tailWord_612887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612887).length < 2 ^ (prefixWord ++ tailWord_612887).sum := by decide
  have hdescent : baseEnd_612887 < baseStart_612887 := by decide
  rcases family_descends (prefixWord ++ tailWord_612887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612898 : List Nat := [3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_612898 : Nat := 118140960795 + 612898 * 2 ^ 59
def prefixEnd_612898 : Nat := 4983230072969 + 3 ^ 40 * 612898 * 2
def baseEnd_612898 : Nat := 93247782571688375542619

theorem tailTrace_612898 : CollatzResearch.WordTrace tailWord_612898 prefixEnd_612898 93247782571688375542619 := by
  unfold tailWord_612898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588556633395673872483837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14902817689055130326623565 5588556633395673872483837)
  ·
    refine ⟨2095708737523377702181439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5588556633395673872483837 2095708737523377702181439)
    ·
      refine ⟨3143563106285066553272159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095708737523377702181439 3143563106285066553272159)
      ·
        refine ⟨4715344659427599829908239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3143563106285066553272159 4715344659427599829908239)
        ·
          refine ⟨7073016989141399744862359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715344659427599829908239 7073016989141399744862359)
          ·
            refine ⟨10609525483712099617293539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073016989141399744862359 10609525483712099617293539)
            ·
              refine ⟨15914288225568149425940309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10609525483712099617293539 15914288225568149425940309)
              ·
                refine ⟨93247782571688375542619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15914288225568149425940309 93247782571688375542619)
                ·
                  rfl

theorem cell20_612898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_612898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612898 prefixEnd_612898 := by exact prefixLift 612898
  have htrace : WordTrace (prefixWord ++ tailWord_612898) baseStart_612898 baseEnd_612898 := by
    simpa [prefixWord, tailWord_612898, baseEnd_612898] using wordTrace_append hprefix tailTrace_612898
  have hstable : (prefixWord ++ tailWord_612898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612898).length < 2 ^ (prefixWord ++ tailWord_612898).sum := by decide
  have hdescent : baseEnd_612898 < baseStart_612898 := by decide
  rcases family_descends (prefixWord ++ tailWord_612898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612925 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 2]
def baseStart_612925 : Nat := 118140960795 + 612925 * 2 ^ 59
def prefixEnd_612925 : Nat := 4983230072969 + 3 ^ 40 * 612925 * 2
def baseEnd_612925 : Nat := 279755671250773032727747

theorem tailTrace_612925 : CollatzResearch.WordTrace tailWord_612925 prefixEnd_612925 279755671250773032727747 := by
  unfold tailWord_612925
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355211304484879101168229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14903474202989919400778819 22355211304484879101168229)
  ·
    refine ⟨4191602119590914831469043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22355211304484879101168229 4191602119590914831469043)
    ·
      refine ⟨6287403179386372247203565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191602119590914831469043 6287403179386372247203565)
      ·
        refine ⟨2357776192269889592701337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6287403179386372247203565 2357776192269889592701337)
        ·
          refine ⟨1768332144202417194526003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357776192269889592701337 1768332144202417194526003)
          ·
            refine ⟨2652498216303625791789005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768332144202417194526003 2652498216303625791789005)
            ·
              refine ⟨994686831113859671920877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2652498216303625791789005 994686831113859671920877)
              ·
                refine ⟨373007561667697376970329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 994686831113859671920877 373007561667697376970329)
                ·
                  refine ⟨279755671250773032727747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373007561667697376970329 279755671250773032727747)
                  ·
                    rfl

theorem cell20_612925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_612925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612925 prefixEnd_612925 := by exact prefixLift 612925
  have htrace : WordTrace (prefixWord ++ tailWord_612925) baseStart_612925 baseEnd_612925 := by
    simpa [prefixWord, tailWord_612925, baseEnd_612925] using wordTrace_append hprefix tailTrace_612925
  have hstable : (prefixWord ++ tailWord_612925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612925).length < 2 ^ (prefixWord ++ tailWord_612925).sum := by decide
  have hdescent : baseEnd_612925 < baseStart_612925 := by decide
  rcases family_descends (prefixWord ++ tailWord_612925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612943 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_612943 : Nat := 118140960795 + 612943 * 2 ^ 59
def prefixEnd_612943 : Nat := 4983230072969 + 3 ^ 40 * 612943 * 2
def baseEnd_612943 : Nat := 279763886941244970127673

theorem tailTrace_612943 : CollatzResearch.WordTrace tailWord_612943 prefixEnd_612943 279763886941244970127673 := by
  unfold tailWord_612943
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355867818419668175323483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14903911878946445450215655 22355867818419668175323483)
  ·
    refine ⟨33533801727629502262985225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22355867818419668175323483 33533801727629502262985225)
    ·
      refine ⟨25150351295722126697238919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33533801727629502262985225 25150351295722126697238919)
      ·
        refine ⟨37725526943583190045858379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25150351295722126697238919 37725526943583190045858379)
        ·
          refine ⟨56588290415374785068787569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37725526943583190045858379 56588290415374785068787569)
          ·
            refine ⟨42441217811531088801590677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56588290415374785068787569 42441217811531088801590677)
            ·
              refine ⟨1989432084915519787574563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42441217811531088801590677 1989432084915519787574563)
              ·
                refine ⟨2984148127373279681361845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989432084915519787574563 2984148127373279681361845)
                ·
                  refine ⟨279763886941244970127673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2984148127373279681361845 279763886941244970127673)
                  ·
                    rfl

theorem cell20_612943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_612943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_612943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_612943 prefixEnd_612943 := by exact prefixLift 612943
  have htrace : WordTrace (prefixWord ++ tailWord_612943) baseStart_612943 baseEnd_612943 := by
    simpa [prefixWord, tailWord_612943, baseEnd_612943] using wordTrace_append hprefix tailTrace_612943
  have hstable : (prefixWord ++ tailWord_612943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612943).length < 2 ^ (prefixWord ++ tailWord_612943).sum := by decide
  have hdescent : baseEnd_612943 < baseStart_612943 := by decide
  rcases family_descends (prefixWord ++ tailWord_612943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613022 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_613022 : Nat := 118140960795 + 613022 * 2 ^ 59
def prefixEnd_613022 : Nat := 4983230072969 + 3 ^ 40 * 613022 * 2
def baseEnd_613022 : Nat := 279799944693871806494017

theorem tailTrace_613022 : CollatzResearch.WordTrace tailWord_613022 prefixEnd_613022 279799944693871806494017 := by
  unfold tailWord_613022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794843648141683083431165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14905832790088976444966213 2794843648141683083431165)
  ·
    refine ⟨1048066368053131156286687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2794843648141683083431165 1048066368053131156286687)
    ·
      refine ⟨1572099552079696734430031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048066368053131156286687 1572099552079696734430031)
      ·
        refine ⟨2358149328119545101645047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572099552079696734430031 2358149328119545101645047)
        ·
          refine ⟨3537223992179317652467571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358149328119545101645047 3537223992179317652467571)
          ·
            refine ⟨5305835988268976478701357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537223992179317652467571 5305835988268976478701357)
            ·
              refine ⟨1989688495600866179513009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5305835988268976478701357 1989688495600866179513009)
              ·
                refine ⟨1492266371700649634634757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989688495600866179513009 1492266371700649634634757)
                ·
                  refine ⟨279799944693871806494017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492266371700649634634757 279799944693871806494017)
                  ·
                    rfl

theorem cell20_613022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_613022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613022 prefixEnd_613022 := by exact prefixLift 613022
  have htrace : WordTrace (prefixWord ++ tailWord_613022) baseStart_613022 baseEnd_613022 := by
    simpa [prefixWord, tailWord_613022, baseEnd_613022] using wordTrace_append hprefix tailTrace_613022
  have hstable : (prefixWord ++ tailWord_613022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613022).length < 2 ^ (prefixWord ++ tailWord_613022).sum := by decide
  have hdescent : baseEnd_613022 < baseStart_613022 := by decide
  rcases family_descends (prefixWord ++ tailWord_613022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613046 : List Nat := [5, 1, 3, 1, 2, 1, 7]
def baseStart_613046 : Nat := 118140960795 + 613046 * 2 ^ 59
def prefixEnd_613046 : Nat := 4983230072969 + 3 ^ 40 * 613046 * 2
def baseEnd_613046 : Nat := 31090099883092709965991

theorem tailTrace_613046 : CollatzResearch.WordTrace tailWord_613046 prefixEnd_613046 31090099883092709965991 := by
  unfold tailWord_613046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397476533565407297895187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14906416358031011177548661 1397476533565407297895187)
  ·
    refine ⟨2096214800348110946842781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397476533565407297895187 2096214800348110946842781)
    ·
      refine ⟨786080550130541605066043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2096214800348110946842781 786080550130541605066043)
      ·
        refine ⟨1179120825195812407599065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786080550130541605066043 1179120825195812407599065)
        ·
          refine ⟨884340618896859305699299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179120825195812407599065 884340618896859305699299)
          ·
            refine ⟨1326510928345288958548949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884340618896859305699299 1326510928345288958548949)
            ·
              refine ⟨31090099883092709965991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1326510928345288958548949 31090099883092709965991)
              ·
                rfl

theorem cell20_613046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_613046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613046 prefixEnd_613046 := by exact prefixLift 613046
  have htrace : WordTrace (prefixWord ++ tailWord_613046) baseStart_613046 baseEnd_613046 := by
    simpa [prefixWord, tailWord_613046, baseEnd_613046] using wordTrace_append hprefix tailTrace_613046
  have hstable : (prefixWord ++ tailWord_613046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613046).length < 2 ^ (prefixWord ++ tailWord_613046).sum := by decide
  have hdescent : baseEnd_613046 < baseStart_613046 := by decide
  rcases family_descends (prefixWord ++ tailWord_613046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613053 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_613053 : Nat := 118140960795 + 613053 * 2 ^ 59
def prefixEnd_613053 : Nat := 4983230072969 + 3 ^ 40 * 613053 * 2
def baseEnd_613053 : Nat := 279814093938573476460557

theorem tailTrace_613053 : CollatzResearch.WordTrace tailWord_613053 prefixEnd_613053 279814093938573476460557 := by
  unfold tailWord_613053
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359879848021156961827813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14906586565347437974551875 22359879848021156961827813)
  ·
    refine ⟨4192477471503966930342715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22359879848021156961827813 4192477471503966930342715)
    ·
      refine ⟨6288716207255950395514073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192477471503966930342715 6288716207255950395514073)
      ·
        refine ⟨4716537155441962796635555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6288716207255950395514073 4716537155441962796635555)
        ·
          refine ⟨7074805733162944194953333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716537155441962796635555 7074805733162944194953333)
          ·
            refine ⟨663263037484026018276875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7074805733162944194953333 663263037484026018276875)
            ·
              refine ⟨994894556226039027415313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663263037484026018276875 994894556226039027415313)
              ·
                refine ⟨746170917169529270561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994894556226039027415313 746170917169529270561485)
                ·
                  refine ⟨279814093938573476460557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746170917169529270561485 279814093938573476460557)
                  ·
                    rfl

theorem cell20_613053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_613053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613053 prefixEnd_613053 := by exact prefixLift 613053
  have htrace : WordTrace (prefixWord ++ tailWord_613053) baseStart_613053 baseEnd_613053 := by
    simpa [prefixWord, tailWord_613053, baseEnd_613053] using wordTrace_append hprefix tailTrace_613053
  have hstable : (prefixWord ++ tailWord_613053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613053).length < 2 ^ (prefixWord ++ tailWord_613053).sum := by decide
  have hdescent : baseEnd_613053 < baseStart_613053 := by decide
  rcases family_descends (prefixWord ++ tailWord_613053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613060 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_613060 : Nat := 118140960795 + 613060 * 2 ^ 59
def prefixEnd_613060 : Nat := 4983230072969 + 3 ^ 40 * 613060 * 2
def baseEnd_613060 : Nat := 279817288929312563227195

theorem tailTrace_613060 : CollatzResearch.WordTrace tailWord_613060 prefixEnd_613060 279817288929312563227195 := by
  unfold tailWord_613060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180067579497898578666317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14906756772663864771555089 11180067579497898578666317)
  ·
    refine ⟨4192525342311711966999869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11180067579497898578666317 4192525342311711966999869)
    ·
      refine ⟨1572197003366891987624951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4192525342311711966999869 1572197003366891987624951)
      ·
        refine ⟨2358295505050337981437427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572197003366891987624951 2358295505050337981437427)
        ·
          refine ⟨3537443257575506972156141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358295505050337981437427 3537443257575506972156141)
          ·
            refine ⟨1326541221590815114558553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3537443257575506972156141 1326541221590815114558553)
            ·
              refine ⟨994905916193111335918915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326541221590815114558553 994905916193111335918915)
              ·
                refine ⟨1492358874289667003878373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994905916193111335918915 1492358874289667003878373)
                ·
                  refine ⟨279817288929312563227195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492358874289667003878373 279817288929312563227195)
                  ·
                    rfl

theorem cell20_613060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_613060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613060 prefixEnd_613060 := by exact prefixLift 613060
  have htrace : WordTrace (prefixWord ++ tailWord_613060) baseStart_613060 baseEnd_613060 := by
    simpa [prefixWord, tailWord_613060, baseEnd_613060] using wordTrace_append hprefix tailTrace_613060
  have hstable : (prefixWord ++ tailWord_613060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613060).length < 2 ^ (prefixWord ++ tailWord_613060).sum := by decide
  have hdescent : baseEnd_613060 < baseStart_613060 := by decide
  rcases family_descends (prefixWord ++ tailWord_613060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613084 : List Nat := [2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_613084 : Nat := 118140960795 + 613084 * 2 ^ 59
def prefixEnd_613084 : Nat := 4983230072969 + 3 ^ 40 * 613084 * 2
def baseEnd_613084 : Nat := 93276081061091715475699

theorem tailTrace_613084 : CollatzResearch.WordTrace tailWord_613084 prefixEnd_613084 93276081061091715475699 := by
  unfold tailWord_613084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180505255454424628103153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14907340340605899504137537 11180505255454424628103153)
  ·
    refine ⟨8385378941590818471077365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11180505255454424628103153 8385378941590818471077365)
    ·
      refine ⟨786129275774139231663503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8385378941590818471077365 786129275774139231663503)
      ·
        refine ⟨1179193913661208847495255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786129275774139231663503 1179193913661208847495255)
        ·
          refine ⟨1768790870491813271242883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179193913661208847495255 1768790870491813271242883)
          ·
            refine ⟨2653186305737719906864325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768790870491813271242883 2653186305737719906864325)
            ·
              refine ⟨497472432325822482537061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2653186305737719906864325 497472432325822482537061)
              ·
                refine ⟨93276081061091715475699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497472432325822482537061 93276081061091715475699)
                ·
                  rfl

theorem cell20_613084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_613084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613084 prefixEnd_613084 := by exact prefixLift 613084
  have htrace : WordTrace (prefixWord ++ tailWord_613084) baseStart_613084 baseEnd_613084 := by
    simpa [prefixWord, tailWord_613084, baseEnd_613084] using wordTrace_append hprefix tailTrace_613084
  have hstable : (prefixWord ++ tailWord_613084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613084).length < 2 ^ (prefixWord ++ tailWord_613084).sum := by decide
  have hdescent : baseEnd_613084 < baseStart_613084 := by decide
  rcases family_descends (prefixWord ++ tailWord_613084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613216 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_613216 : Nat := 118140960795 + 613216 * 2 ^ 59
def prefixEnd_613216 : Nat := 4983230072969 + 3 ^ 40 * 613216 * 2
def baseEnd_613216 : Nat := 279888491580069354026557

theorem tailTrace_613216 : CollatzResearch.WordTrace tailWord_613216 prefixEnd_613216 279888491580069354026557 := by
  unfold tailWord_613216
  simp only [CollatzResearch.WordTrace]
  refine ⟨11182912473215317900005751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14910549964287090533341001 11182912473215317900005751)
  ·
    refine ⟨16774368709822976850008627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11182912473215317900005751 16774368709822976850008627)
    ·
      refine ⟨25161553064734465275012941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16774368709822976850008627 25161553064734465275012941)
      ·
        refine ⟨9435582399275424478129853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25161553064734465275012941 9435582399275424478129853)
        ·
          refine ⟨3538343399728284179298695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9435582399275424478129853 3538343399728284179298695)
          ·
            refine ⟨5307515099592426268948043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538343399728284179298695 5307515099592426268948043)
            ·
              refine ⟨7961272649388639403422065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307515099592426268948043 7961272649388639403422065)
              ·
                refine ⟨5970954487041479552566549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7961272649388639403422065 5970954487041479552566549)
                ·
                  refine ⟨279888491580069354026557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5970954487041479552566549 279888491580069354026557)
                  ·
                    rfl

theorem cell20_613216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_613216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613216 prefixEnd_613216 := by exact prefixLift 613216
  have htrace : WordTrace (prefixWord ++ tailWord_613216) baseStart_613216 baseEnd_613216 := by
    simpa [prefixWord, tailWord_613216, baseEnd_613216] using wordTrace_append hprefix tailTrace_613216
  have hstable : (prefixWord ++ tailWord_613216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613216).length < 2 ^ (prefixWord ++ tailWord_613216).sum := by decide
  have hdescent : baseEnd_613216 < baseStart_613216 := by decide
  rcases family_descends (prefixWord ++ tailWord_613216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613233 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_613233 : Nat := 118140960795 + 613233 * 2 ^ 59
def prefixEnd_613233 : Nat := 4983230072969 + 3 ^ 40 * 613233 * 2
def baseEnd_613233 : Nat := 279896250843292850459821

theorem tailTrace_613233 : CollatzResearch.WordTrace tailWord_613233 prefixEnd_613233 279896250843292850459821 := by
  unfold tailWord_613233
  simp only [CollatzResearch.WordTrace]
  refine ⟨22366444987369047703380353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14910963324912698468920235 22366444987369047703380353)
  ·
    refine ⟨16774833740526785777535265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22366444987369047703380353 16774833740526785777535265)
    ·
      refine ⟨12581125305395089333151449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16774833740526785777535265 12581125305395089333151449)
      ·
        refine ⟨9435843979046316999863587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12581125305395089333151449 9435843979046316999863587)
        ·
          refine ⟨14153765968569475499795381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435843979046316999863587 14153765968569475499795381)
          ·
            refine ⟨1326915559553388328105817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14153765968569475499795381 1326915559553388328105817)
            ·
              refine ⟨995186669665041246079363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326915559553388328105817 995186669665041246079363)
              ·
                refine ⟨1492780004497561869119045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995186669665041246079363 1492780004497561869119045)
                ·
                  refine ⟨279896250843292850459821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492780004497561869119045 279896250843292850459821)
                  ·
                    rfl

theorem cell20_613233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_613233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613233 prefixEnd_613233 := by exact prefixLift 613233
  have htrace : WordTrace (prefixWord ++ tailWord_613233) baseStart_613233 baseEnd_613233 := by
    simpa [prefixWord, tailWord_613233, baseEnd_613233] using wordTrace_append hprefix tailTrace_613233
  have hstable : (prefixWord ++ tailWord_613233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613233).length < 2 ^ (prefixWord ++ tailWord_613233).sum := by decide
  have hdescent : baseEnd_613233 < baseStart_613233 := by decide
  rcases family_descends (prefixWord ++ tailWord_613233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613247 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_613247 : Nat := 118140960795 + 613247 * 2 ^ 59
def prefixEnd_613247 : Nat := 4983230072969 + 3 ^ 40 * 613247 * 2
def baseEnd_613247 : Nat := 279902640824771023993097

theorem tailTrace_613247 : CollatzResearch.WordTrace tailWord_613247 prefixEnd_613247 279902640824771023993097 := by
  unfold tailWord_613247
  simp only [CollatzResearch.WordTrace]
  refine ⟨22366955609318328094389995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911303739545552062926663 22366955609318328094389995)
  ·
    refine ⟨33550433413977492141584993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22366955609318328094389995 33550433413977492141584993)
    ·
      refine ⟨25162825060483119106188745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33550433413977492141584993 25162825060483119106188745)
      ·
        refine ⟨18872118795362339329641559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25162825060483119106188745 18872118795362339329641559)
        ·
          refine ⟨28308178193043508994462339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18872118795362339329641559 28308178193043508994462339)
          ·
            refine ⟨42462267289565263491693509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28308178193043508994462339 42462267289565263491693509)
            ·
              refine ⟨7961675116793486904692533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42462267289565263491693509 7961675116793486904692533)
              ·
                refine ⟨746407042199389397314925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7961675116793486904692533 746407042199389397314925)
                ·
                  refine ⟨279902640824771023993097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746407042199389397314925 279902640824771023993097)
                  ·
                    rfl

theorem cell20_613247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_613247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613247 prefixEnd_613247 := by exact prefixLift 613247
  have htrace : WordTrace (prefixWord ++ tailWord_613247) baseStart_613247 baseEnd_613247 := by
    simpa [prefixWord, tailWord_613247, baseEnd_613247] using wordTrace_append hprefix tailTrace_613247
  have hstable : (prefixWord ++ tailWord_613247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613247).length < 2 ^ (prefixWord ++ tailWord_613247).sum := by decide
  have hdescent : baseEnd_613247 < baseStart_613247 := by decide
  rcases family_descends (prefixWord ++ tailWord_613247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613257 : List Nat := [1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_613257 : Nat := 118140960795 + 613257 * 2 ^ 59
def prefixEnd_613257 : Nat := 4983230072969 + 3 ^ 40 * 613257 * 2
def baseEnd_613257 : Nat := 93302401699085144553241

theorem tailTrace_613257 : CollatzResearch.WordTrace tailWord_613257 prefixEnd_613257 93302401699085144553241 := by
  unfold tailWord_613257
  simp only [CollatzResearch.WordTrace]
  refine ⟨22367320339282099802254025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911546892854733201502683 22367320339282099802254025)
  ·
    refine ⟨16775490254461574851690519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22367320339282099802254025 16775490254461574851690519)
    ·
      refine ⟨25163235381692362277535779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16775490254461574851690519 25163235381692362277535779)
      ·
        refine ⟨37744853072538543416303669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25163235381692362277535779 37744853072538543416303669)
        ·
          refine ⟨3538579975550488445278469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37744853072538543416303669 3538579975550488445278469)
          ·
            refine ⟨663483745415716583489713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3538579975550488445278469 663483745415716583489713)
            ·
              refine ⟨497612809061787437617285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663483745415716583489713 497612809061787437617285)
              ·
                refine ⟨93302401699085144553241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497612809061787437617285 93302401699085144553241)
                ·
                  rfl

theorem cell20_613257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_613257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613257 prefixEnd_613257 := by exact prefixLift 613257
  have htrace : WordTrace (prefixWord ++ tailWord_613257) baseStart_613257 baseEnd_613257 := by
    simpa [prefixWord, tailWord_613257, baseEnd_613257] using wordTrace_append hprefix tailTrace_613257
  have hstable : (prefixWord ++ tailWord_613257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613257).length < 2 ^ (prefixWord ++ tailWord_613257).sum := by decide
  have hdescent : baseEnd_613257 < baseStart_613257 := by decide
  rcases family_descends (prefixWord ++ tailWord_613257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613337 : List Nat := [1, 2, 1, 2, 5, 9]
def baseStart_613337 : Nat := 118140960795 + 613337 * 2 ^ 59
def prefixEnd_613337 : Nat := 4983230072969 + 3 ^ 40 * 613337 * 2
def baseEnd_613337 : Nat := 10368285899152989296027

theorem tailTrace_613337 : CollatzResearch.WordTrace tailWord_613337 prefixEnd_613337 10368285899152989296027 := by
  unfold tailWord_613337
  simp only [CollatzResearch.WordTrace]
  refine ⟨22370238178992273465166265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14913492119328182310110843 22370238178992273465166265)
  ·
    refine ⟨16777678634244205098874699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22370238178992273465166265 16777678634244205098874699)
    ·
      refine ⟨25166517951366307648312049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16777678634244205098874699 25166517951366307648312049)
      ·
        refine ⟨18874888463524730736234037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25166517951366307648312049 18874888463524730736234037)
        ·
          refine ⟨1769520793455443506521941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18874888463524730736234037 1769520793455443506521941)
          ·
            refine ⟨10368285899152989296027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1769520793455443506521941 10368285899152989296027)
            ·
              rfl

theorem cell20_613337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 9].length) (baseStart_613337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613337 prefixEnd_613337 := by exact prefixLift 613337
  have htrace : WordTrace (prefixWord ++ tailWord_613337) baseStart_613337 baseEnd_613337 := by
    simpa [prefixWord, tailWord_613337, baseEnd_613337] using wordTrace_append hprefix tailTrace_613337
  have hstable : (prefixWord ++ tailWord_613337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613337).length < 2 ^ (prefixWord ++ tailWord_613337).sum := by decide
  have hdescent : baseEnd_613337 < baseStart_613337 := by decide
  rcases family_descends (prefixWord ++ tailWord_613337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613354 : List Nat := [3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_613354 : Nat := 118140960795 + 613354 * 2 ^ 59
def prefixEnd_613354 : Nat := 4983230072969 + 3 ^ 40 * 613354 * 2
def baseEnd_613354 : Nat := 93317159513451402475331

theorem tailTrace_613354 : CollatzResearch.WordTrace tailWord_613354 prefixEnd_613354 93317159513451402475331 := by
  unfold tailWord_613354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5592714554982671342133779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14913905479953790245690077 5592714554982671342133779)
  ·
    refine ⟨8389071832474007013200669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5592714554982671342133779 8389071832474007013200669)
    ·
      refine ⟨3145901937177752629950251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8389071832474007013200669 3145901937177752629950251)
      ·
        refine ⟨4718852905766628944925377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145901937177752629950251 4718852905766628944925377)
        ·
          refine ⟨3539139679324971708694033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4718852905766628944925377 3539139679324971708694033)
          ·
            refine ⟨2654354759493728781520525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539139679324971708694033 2654354759493728781520525)
            ·
              refine ⟨995383034810148293070197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2654354759493728781520525 995383034810148293070197)
              ·
                refine ⟨93317159513451402475331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995383034810148293070197 93317159513451402475331)
                ·
                  rfl

theorem cell20_613354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_613354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613354 prefixEnd_613354 := by exact prefixLift 613354
  have htrace : WordTrace (prefixWord ++ tailWord_613354) baseStart_613354 baseEnd_613354 := by
    simpa [prefixWord, tailWord_613354, baseEnd_613354] using wordTrace_append hprefix tailTrace_613354
  have hstable : (prefixWord ++ tailWord_613354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613354).length < 2 ^ (prefixWord ++ tailWord_613354).sum := by decide
  have hdescent : baseEnd_613354 < baseStart_613354 := by decide
  rcases family_descends (prefixWord ++ tailWord_613354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613413 : List Nat := [1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_613413 : Nat := 118140960795 + 613413 * 2 ^ 59
def prefixEnd_613413 : Nat := 4983230072969 + 3 ^ 40 * 613413 * 2
def baseEnd_613413 : Nat := 93326135916004074819695

theorem tailTrace_613413 : CollatzResearch.WordTrace tailWord_613413 prefixEnd_613413 93326135916004074819695 := by
  unfold tailWord_613413
  simp only [CollatzResearch.WordTrace]
  refine ⟨22373010126716938444932893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14915340084477958963288595 22373010126716938444932893)
  ·
    refine ⟨8389878797518851916849835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22373010126716938444932893 8389878797518851916849835)
    ·
      refine ⟨12584818196278277875274753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8389878797518851916849835 12584818196278277875274753)
      ·
        refine ⟨9438613647208708406456065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12584818196278277875274753 9438613647208708406456065)
        ·
          refine ⟨7078960235406531304842049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9438613647208708406456065 7078960235406531304842049)
          ·
            refine ⟨5309220176554898478631537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7078960235406531304842049 5309220176554898478631537)
            ·
              refine ⟨3981915132416173858973653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5309220176554898478631537 3981915132416173858973653)
              ·
                refine ⟨93326135916004074819695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3981915132416173858973653 93326135916004074819695)
                ·
                  rfl

theorem cell20_613413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_613413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613413 prefixEnd_613413 := by exact prefixLift 613413
  have htrace : WordTrace (prefixWord ++ tailWord_613413) baseStart_613413 baseEnd_613413 := by
    simpa [prefixWord, tailWord_613413, baseEnd_613413] using wordTrace_append hprefix tailTrace_613413
  have hstable : (prefixWord ++ tailWord_613413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613413).length < 2 ^ (prefixWord ++ tailWord_613413).sum := by decide
  have hdescent : baseEnd_613413 < baseStart_613413 := by decide
  rcases family_descends (prefixWord ++ tailWord_613413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613437 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_613437 : Nat := 118140960795 + 613437 * 2 ^ 59
def prefixEnd_613437 : Nat := 4983230072969 + 3 ^ 40 * 613437 * 2
def baseEnd_613437 : Nat := 279989362001974807658987

theorem tailTrace_613437 : CollatzResearch.WordTrace tailWord_613437 prefixEnd_613437 279989362001974807658987 := by
  unfold tailWord_613437
  simp only [CollatzResearch.WordTrace]
  refine ⟨22373885478629990543806565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14915923652419993695871043 22373885478629990543806565)
  ·
    refine ⟨4195103527243123226963731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22373885478629990543806565 4195103527243123226963731)
    ·
      refine ⟨6292655290864684840445597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4195103527243123226963731 6292655290864684840445597)
      ·
        refine ⟨2359745734074256815167099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6292655290864684840445597 2359745734074256815167099)
        ·
          refine ⟨3539618601111385222750649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359745734074256815167099 3539618601111385222750649)
          ·
            refine ⟨2654713950833538917062987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539618601111385222750649 2654713950833538917062987)
            ·
              refine ⟨3982070926250308375594481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654713950833538917062987 3982070926250308375594481)
              ·
                refine ⟨2986553194687731281695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982070926250308375594481 2986553194687731281695861)
                ·
                  refine ⟨279989362001974807658987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2986553194687731281695861 279989362001974807658987)
                  ·
                    rfl

theorem cell20_613437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_613437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613437 prefixEnd_613437 := by exact prefixLift 613437
  have htrace : WordTrace (prefixWord ++ tailWord_613437) baseStart_613437 baseEnd_613437 := by
    simpa [prefixWord, tailWord_613437, baseEnd_613437] using wordTrace_append hprefix tailTrace_613437
  have hstable : (prefixWord ++ tailWord_613437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613437).length < 2 ^ (prefixWord ++ tailWord_613437).sum := by decide
  have hdescent : baseEnd_613437 < baseStart_613437 := by decide
  rcases family_descends (prefixWord ++ tailWord_613437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613468 : List Nat := [2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_613468 : Nat := 118140960795 + 613468 * 2 ^ 59
def prefixEnd_613468 : Nat := 4983230072969 + 3 ^ 40 * 613468 * 2
def baseEnd_613468 : Nat := 93334503748892159208509

theorem tailTrace_613468 : CollatzResearch.WordTrace tailWord_613468 prefixEnd_613468 93334503748892159208509 := by
  unfold tailWord_613468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11187508070758841419092529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14916677427678455225456705 11187508070758841419092529)
  ·
    refine ⟨8390631053069131064319397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11187508070758841419092529 8390631053069131064319397)
    ·
      refine ⟨1573243322450462074559887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8390631053069131064319397 1573243322450462074559887)
      ·
        refine ⟨2359864983675693111839831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573243322450462074559887 2359864983675693111839831)
        ·
          refine ⟨3539797475513539667759747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359864983675693111839831 3539797475513539667759747)
          ·
            refine ⟨5309696213270309501639621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539797475513539667759747 5309696213270309501639621)
            ·
              refine ⟨995568039988183031557429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5309696213270309501639621 995568039988183031557429)
              ·
                refine ⟨93334503748892159208509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995568039988183031557429 93334503748892159208509)
                ·
                  rfl

theorem cell20_613468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_613468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613468 prefixEnd_613468 := by exact prefixLift 613468
  have htrace : WordTrace (prefixWord ++ tailWord_613468) baseStart_613468 baseEnd_613468 := by
    simpa [prefixWord, tailWord_613468, baseEnd_613468] using wordTrace_append hprefix tailTrace_613468
  have hstable : (prefixWord ++ tailWord_613468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613468).length < 2 ^ (prefixWord ++ tailWord_613468).sum := by decide
  have hdescent : baseEnd_613468 < baseStart_613468 := by decide
  rcases family_descends (prefixWord ++ tailWord_613468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613496 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_613496 : Nat := 118140960795 + 613496 * 2 ^ 59
def prefixEnd_613496 : Nat := 4983230072969 + 3 ^ 40 * 613496 * 2
def baseEnd_613496 : Nat := 280016291209632824692079

theorem tailTrace_613496 : CollatzResearch.WordTrace tailWord_613496 prefixEnd_613496 280016291209632824692079 := by
  unfold tailWord_613496
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188018692708121810102171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14917358256944162413469561 11188018692708121810102171)
  ·
    refine ⟨16782028039062182715153257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11188018692708121810102171 16782028039062182715153257)
    ·
      refine ⟨12586521029296637036364943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16782028039062182715153257 12586521029296637036364943)
      ·
        refine ⟨18879781543944955554547415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12586521029296637036364943 18879781543944955554547415)
        ·
          refine ⟨28319672315917433331821123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18879781543944955554547415 28319672315917433331821123)
          ·
            refine ⟨42479508473876149997731685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28319672315917433331821123 42479508473876149997731685)
            ·
              refine ⟨7964907838851778124574691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42479508473876149997731685 7964907838851778124574691)
              ·
                refine ⟨11947361758277667186862037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7964907838851778124574691 11947361758277667186862037)
                ·
                  refine ⟨280016291209632824692079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11947361758277667186862037 280016291209632824692079)
                  ·
                    rfl

theorem cell20_613496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_613496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613496 prefixEnd_613496 := by exact prefixLift 613496
  have htrace : WordTrace (prefixWord ++ tailWord_613496) baseStart_613496 baseEnd_613496 := by
    simpa [prefixWord, tailWord_613496, baseEnd_613496] using wordTrace_append hprefix tailTrace_613496
  have hstable : (prefixWord ++ tailWord_613496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613496).length < 2 ^ (prefixWord ++ tailWord_613496).sum := by decide
  have hdescent : baseEnd_613496 < baseStart_613496 := by decide
  rcases family_descends (prefixWord ++ tailWord_613496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613502 : List Nat := [4, 2, 4, 1, 1, 8]
def baseStart_613502 : Nat := 118140960795 + 613502 * 2 ^ 59
def prefixEnd_613502 : Nat := 4983230072969 + 3 ^ 40 * 613502 * 2
def baseEnd_613502 : Nat := 10371075176782350758965

theorem tailTrace_613502 : CollatzResearch.WordTrace tailWord_613502 prefixEnd_613502 10371075176782350758965 := by
  unfold tailWord_613502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797032027924313330615345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14917504148929671096615173 2797032027924313330615345)
  ·
    refine ⟨2097774020943234997961509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2797032027924313330615345 2097774020943234997961509)
    ·
      refine ⟨393332628926856562117783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2097774020943234997961509 393332628926856562117783)
      ·
        refine ⟨589998943390284843176675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393332628926856562117783 589998943390284843176675)
        ·
          refine ⟨884998415085427264765013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589998943390284843176675 884998415085427264765013)
          ·
            refine ⟨10371075176782350758965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 884998415085427264765013 10371075176782350758965)
            ·
              rfl

theorem cell20_613502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 8].length) (baseStart_613502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613502 prefixEnd_613502 := by exact prefixLift 613502
  have htrace : WordTrace (prefixWord ++ tailWord_613502) baseStart_613502 baseEnd_613502 := by
    simpa [prefixWord, tailWord_613502, baseEnd_613502] using wordTrace_append hprefix tailTrace_613502
  have hstable : (prefixWord ++ tailWord_613502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613502).length < 2 ^ (prefixWord ++ tailWord_613502).sum := by decide
  have hdescent : baseEnd_613502 < baseStart_613502 := by decide
  rcases family_descends (prefixWord ++ tailWord_613502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613512 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_613512 : Nat := 118140960795 + 613512 * 2 ^ 59
def prefixEnd_613512 : Nat := 4983230072969 + 3 ^ 40 * 613512 * 2
def baseEnd_613512 : Nat := 280023594045607880158681

theorem tailTrace_613512 : CollatzResearch.WordTrace tailWord_613512 prefixEnd_613512 280023594045607880158681 := by
  unfold tailWord_613512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188310476679139176393395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14917747302238852235191193 11188310476679139176393395)
  ·
    refine ⟨16782465715018708764590093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11188310476679139176393395 16782465715018708764590093)
    ·
      refine ⟨6293424643132015786721285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16782465715018708764590093 6293424643132015786721285)
      ·
        refine ⟨1180017120587252960010241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6293424643132015786721285 1180017120587252960010241)
        ·
          refine ⟨885012840440439720007681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180017120587252960010241 885012840440439720007681)
          ·
            refine ⟨663759630330329790005761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885012840440439720007681 663759630330329790005761)
            ·
              refine ⟨497819722747747342504321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663759630330329790005761 497819722747747342504321)
              ·
                refine ⟨373364792060810506878241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497819722747747342504321 373364792060810506878241)
                ·
                  refine ⟨280023594045607880158681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373364792060810506878241 280023594045607880158681)
                  ·
                    rfl

theorem cell20_613512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_613512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613512 prefixEnd_613512 := by exact prefixLift 613512
  have htrace : WordTrace (prefixWord ++ tailWord_613512) baseStart_613512 baseEnd_613512 := by
    simpa [prefixWord, tailWord_613512, baseEnd_613512] using wordTrace_append hprefix tailTrace_613512
  have hstable : (prefixWord ++ tailWord_613512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613512).length < 2 ^ (prefixWord ++ tailWord_613512).sum := by decide
  have hdescent : baseEnd_613512 < baseStart_613512 := by decide
  rcases family_descends (prefixWord ++ tailWord_613512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613513 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_613513 : Nat := 118140960795 + 613513 * 2 ^ 59
def prefixEnd_613513 : Nat := 4983230072969 + 3 ^ 40 * 613513 * 2
def baseEnd_613513 : Nat := 280024050472856321125343

theorem tailTrace_613513 : CollatzResearch.WordTrace tailWord_613513 prefixEnd_613513 280024050472856321125343 := by
  unfold tailWord_613513
  simp only [CollatzResearch.WordTrace]
  refine ⟨22376657426354655523573193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14917771617569770349048795 22376657426354655523573193)
  ·
    refine ⟨16782493069765991642679895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22376657426354655523573193 16782493069765991642679895)
    ·
      refine ⟨25173739604648987464019843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16782493069765991642679895 25173739604648987464019843)
      ·
        refine ⟨37760609406973481196029765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25173739604648987464019843 37760609406973481196029765)
        ·
          refine ⟨7080114263807527724255581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37760609406973481196029765 7080114263807527724255581)
          ·
            refine ⟨2655042848927822896595843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7080114263807527724255581 2655042848927822896595843)
            ·
              refine ⟨3982564273391734344893765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2655042848927822896595843 3982564273391734344893765)
              ·
                refine ⟨746730801260950189667581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3982564273391734344893765 746730801260950189667581)
                ·
                  refine ⟨280024050472856321125343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746730801260950189667581 280024050472856321125343)
                  ·
                    rfl

theorem cell20_613513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_613513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613513 prefixEnd_613513 := by exact prefixLift 613513
  have htrace : WordTrace (prefixWord ++ tailWord_613513) baseStart_613513 baseEnd_613513 := by
    simpa [prefixWord, tailWord_613513, baseEnd_613513] using wordTrace_append hprefix tailTrace_613513
  have hstable : (prefixWord ++ tailWord_613513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613513).length < 2 ^ (prefixWord ++ tailWord_613513).sum := by decide
  have hdescent : baseEnd_613513 < baseStart_613513 := by decide
  rcases family_descends (prefixWord ++ tailWord_613513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613530 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_613530 : Nat := 118140960795 + 613530 * 2 ^ 59
def prefixEnd_613530 : Nat := 4983230072969 + 3 ^ 40 * 613530 * 2
def baseEnd_613530 : Nat := 280031809736079817558607

theorem tailTrace_613530 : CollatzResearch.WordTrace tailWord_613530 prefixEnd_613530 280031809736079817558607 := by
  unfold tailWord_613530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594319366823266856735511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14918184978195378284628029 5594319366823266856735511)
  ·
    refine ⟨8391479050234900285103267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5594319366823266856735511 8391479050234900285103267)
    ·
      refine ⟨12587218575352350427654901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8391479050234900285103267 12587218575352350427654901)
      ·
        refine ⟨1180051741439282852592647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12587218575352350427654901 1180051741439282852592647)
        ·
          refine ⟨1770077612158924278888971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180051741439282852592647 1770077612158924278888971)
          ·
            refine ⟨2655116418238386418333457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770077612158924278888971 2655116418238386418333457)
            ·
              refine ⟨1991337313678789813750093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655116418238386418333457 1991337313678789813750093)
              ·
                refine ⟨746751492629546180156285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991337313678789813750093 746751492629546180156285)
                ·
                  refine ⟨280031809736079817558607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746751492629546180156285 280031809736079817558607)
                  ·
                    rfl

theorem cell20_613530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_613530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613530 prefixEnd_613530 := by exact prefixLift 613530
  have htrace : WordTrace (prefixWord ++ tailWord_613530) baseStart_613530 baseEnd_613530 := by
    simpa [prefixWord, tailWord_613530, baseEnd_613530] using wordTrace_append hprefix tailTrace_613530
  have hstable : (prefixWord ++ tailWord_613530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613530).length < 2 ^ (prefixWord ++ tailWord_613530).sum := by decide
  have hdescent : baseEnd_613530 < baseStart_613530 := by decide
  rcases family_descends (prefixWord ++ tailWord_613530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613554 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_613554 : Nat := 118140960795 + 613554 * 2 ^ 59
def prefixEnd_613554 : Nat := 4983230072969 + 3 ^ 40 * 613554 * 2
def baseEnd_613554 : Nat := 280042763990042400758509

theorem tailTrace_613554 : CollatzResearch.WordTrace tailWord_613554 prefixEnd_613554 280042763990042400758509 := by
  unfold tailWord_613554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594538204801529881453929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14918768546137413017210477 5594538204801529881453929)
  ·
    refine ⟨4195903653601147411090447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5594538204801529881453929 4195903653601147411090447)
    ·
      refine ⟨6293855480401721116635671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4195903653601147411090447 6293855480401721116635671)
      ·
        refine ⟨9440783220602581674953507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293855480401721116635671 9440783220602581674953507)
        ·
          refine ⟨14161174830903872512430261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440783220602581674953507 14161174830903872512430261)
          ·
            refine ⟨1327610140397238048040337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14161174830903872512430261 1327610140397238048040337)
            ·
              refine ⟨995707605297928536030253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327610140397238048040337 995707605297928536030253)
              ·
                refine ⟨373390351986723201011345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995707605297928536030253 373390351986723201011345)
                ·
                  refine ⟨280042763990042400758509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373390351986723201011345 280042763990042400758509)
                  ·
                    rfl

theorem cell20_613554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_613554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613554 prefixEnd_613554 := by exact prefixLift 613554
  have htrace : WordTrace (prefixWord ++ tailWord_613554) baseStart_613554 baseEnd_613554 := by
    simpa [prefixWord, tailWord_613554, baseEnd_613554] using wordTrace_append hprefix tailTrace_613554
  have hstable : (prefixWord ++ tailWord_613554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613554).length < 2 ^ (prefixWord ++ tailWord_613554).sum := by decide
  have hdescent : baseEnd_613554 < baseStart_613554 := by decide
  rcases family_descends (prefixWord ++ tailWord_613554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613581 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 3]
def baseStart_613581 : Nat := 118140960795 + 613581 * 2 ^ 59
def prefixEnd_613581 : Nat := 4983230072969 + 3 ^ 40 * 613581 * 2
def baseEnd_613581 : Nat := 280055087525750306858399

theorem tailTrace_613581 : CollatzResearch.WordTrace tailWord_613581 prefixEnd_613581 280055087525750306858399 := by
  unfold tailWord_613581
  simp only [CollatzResearch.WordTrace]
  refine ⟨22379137590108303137048597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14919425060072202091365731 22379137590108303137048597)
  ·
    refine ⟨1049022074536326709549153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22379137590108303137048597 1049022074536326709549153)
    ·
      refine ⟨786766555902245032161865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1049022074536326709549153 786766555902245032161865)
      ·
        refine ⟨590074916926683774121399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786766555902245032161865 590074916926683774121399)
        ·
          refine ⟨885112375390025661182099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590074916926683774121399 885112375390025661182099)
          ·
            refine ⟨1327668563085038491773149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885112375390025661182099 1327668563085038491773149)
            ·
              refine ⟨497875711156889434414931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1327668563085038491773149 497875711156889434414931)
              ·
                refine ⟨746813566735334151622397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497875711156889434414931 746813566735334151622397)
                ·
                  refine ⟨280055087525750306858399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746813566735334151622397 280055087525750306858399)
                  ·
                    rfl

theorem cell20_613581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_613581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613581 prefixEnd_613581 := by exact prefixLift 613581
  have htrace : WordTrace (prefixWord ++ tailWord_613581) baseStart_613581 baseEnd_613581 := by
    simpa [prefixWord, tailWord_613581, baseEnd_613581] using wordTrace_append hprefix tailTrace_613581
  have hstable : (prefixWord ++ tailWord_613581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613581).length < 2 ^ (prefixWord ++ tailWord_613581).sum := by decide
  have hdescent : baseEnd_613581 < baseStart_613581 := by decide
  rcases family_descends (prefixWord ++ tailWord_613581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613630 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_613630 : Nat := 118140960795 + 613630 * 2 ^ 59
def prefixEnd_613630 : Nat := 4983230072969 + 3 ^ 40 * 613630 * 2
def baseEnd_613630 : Nat := 280077452460923914224865

theorem tailTrace_613630 : CollatzResearch.WordTrace tailWord_613630 prefixEnd_613630 280077452460923914224865 := by
  unfold tailWord_613630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797615595866348063197793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14920616511287189670388229 2797615595866348063197793)
  ·
    refine ⟨2098211696899761047398345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2797615595866348063197793 2098211696899761047398345)
    ·
      refine ⟨1573658772674820785548759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2098211696899761047398345 1573658772674820785548759)
      ·
        refine ⟨2360488159012231178323139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573658772674820785548759 2360488159012231178323139)
        ·
          refine ⟨3540732238518346767484709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360488159012231178323139 3540732238518346767484709)
          ·
            refine ⟨663887294722190018903383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3540732238518346767484709 663887294722190018903383)
            ·
              refine ⟨995830942083285028355075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663887294722190018903383 995830942083285028355075)
              ·
                refine ⟨1493746413124927542532613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995830942083285028355075 1493746413124927542532613)
                ·
                  refine ⟨280077452460923914224865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1493746413124927542532613 280077452460923914224865)
                  ·
                    rfl

theorem cell20_613630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_613630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613630 prefixEnd_613630 := by exact prefixLift 613630
  have htrace : WordTrace (prefixWord ++ tailWord_613630) baseStart_613630 baseEnd_613630 := by
    simpa [prefixWord, tailWord_613630, baseEnd_613630] using wordTrace_append hprefix tailTrace_613630
  have hstable : (prefixWord ++ tailWord_613630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613630).length < 2 ^ (prefixWord ++ tailWord_613630).sum := by decide
  have hdescent : baseEnd_613630 < baseStart_613630 := by decide
  rcases family_descends (prefixWord ++ tailWord_613630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613640 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_613640 : Nat := 118140960795 + 613640 * 2 ^ 59
def prefixEnd_613640 : Nat := 4983230072969 + 3 ^ 40 * 613640 * 2
def baseEnd_613640 : Nat := 280082016733408323891491

theorem tailTrace_613640 : CollatzResearch.WordTrace tailWord_613640 prefixEnd_613640 280082016733408323891491 := by
  unfold tailWord_613640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190644748447278106723187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14920859664596370808964249 11190644748447278106723187)
  ·
    refine ⟨16785967122670917160084781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11190644748447278106723187 16785967122670917160084781)
    ·
      refine ⟨6294737671001593935031793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16785967122670917160084781 6294737671001593935031793)
      ·
        refine ⟨4721053253251195451273845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6294737671001593935031793 4721053253251195451273845)
        ·
          refine ⟨442598742492299573556923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4721053253251195451273845 442598742492299573556923)
          ·
            refine ⟨663898113738449360335385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442598742492299573556923 663898113738449360335385)
            ·
              refine ⟨497923585303837020251539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663898113738449360335385 497923585303837020251539)
              ·
                refine ⟨746885377955755530377309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497923585303837020251539 746885377955755530377309)
                ·
                  refine ⟨280082016733408323891491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746885377955755530377309 280082016733408323891491)
                  ·
                    rfl

theorem cell20_613640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_613640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613640 prefixEnd_613640 := by exact prefixLift 613640
  have htrace : WordTrace (prefixWord ++ tailWord_613640) baseStart_613640 baseEnd_613640 := by
    simpa [prefixWord, tailWord_613640, baseEnd_613640] using wordTrace_append hprefix tailTrace_613640
  have hstable : (prefixWord ++ tailWord_613640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613640).length < 2 ^ (prefixWord ++ tailWord_613640).sum := by decide
  have hdescent : baseEnd_613640 < baseStart_613640 := by decide
  rcases family_descends (prefixWord ++ tailWord_613640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613641 : List Nat := [1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_613641 : Nat := 118140960795 + 613641 * 2 ^ 59
def prefixEnd_613641 : Nat := 4983230072969 + 3 ^ 40 * 613641 * 2
def baseEnd_613641 : Nat := 93360824386885588286051

theorem tailTrace_613641 : CollatzResearch.WordTrace tailWord_613641 prefixEnd_613641 93360824386885588286051 := by
  unfold tailWord_613641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22381325969890933384232777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14920883979927288922821851 22381325969890933384232777)
  ·
    refine ⟨16785994477418200038174583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22381325969890933384232777 16785994477418200038174583)
    ·
      refine ⟨25178991716127300057261875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16785994477418200038174583 25178991716127300057261875)
      ·
        refine ⟨37768487574190950085892813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25178991716127300057261875 37768487574190950085892813)
        ·
          refine ⟨14163182840321606282209805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37768487574190950085892813 14163182840321606282209805)
          ·
            refine ⟨5311193565120602355828677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14163182840321606282209805 5311193565120602355828677)
            ·
              refine ⟨995848793460112941717877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5311193565120602355828677 995848793460112941717877)
              ·
                refine ⟨93360824386885588286051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995848793460112941717877 93360824386885588286051)
                ·
                  rfl

theorem cell20_613641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_613641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613641 prefixEnd_613641 := by exact prefixLift 613641
  have htrace : WordTrace (prefixWord ++ tailWord_613641) baseStart_613641 baseEnd_613641 := by
    simpa [prefixWord, tailWord_613641, baseEnd_613641] using wordTrace_append hprefix tailTrace_613641
  have hstable : (prefixWord ++ tailWord_613641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613641).length < 2 ^ (prefixWord ++ tailWord_613641).sum := by decide
  have hdescent : baseEnd_613641 < baseStart_613641 := by decide
  rcases family_descends (prefixWord ++ tailWord_613641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613644 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_613644 : Nat := 118140960795 + 613644 * 2 ^ 59
def prefixEnd_613644 : Nat := 4983230072969 + 3 ^ 40 * 613644 * 2
def baseEnd_613644 : Nat := 280083842442402087758141

theorem tailTrace_613644 : CollatzResearch.WordTrace tailWord_613644 prefixEnd_613644 280083842442402087758141 := by
  unfold tailWord_613644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190717694440032448295993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14920956925920043264394657 11190717694440032448295993)
  ·
    refine ⟨8393038270830024336221995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11190717694440032448295993 8393038270830024336221995)
    ·
      refine ⟨12589557406245036504332993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393038270830024336221995 12589557406245036504332993)
      ·
        refine ⟨9442168054683777378249745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12589557406245036504332993 9442168054683777378249745)
        ·
          refine ⟨7081626041012833033687309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9442168054683777378249745 7081626041012833033687309)
          ·
            refine ⟨2655609765379812387632741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7081626041012833033687309 2655609765379812387632741)
            ·
              refine ⟨497926831008714822681139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2655609765379812387632741 497926831008714822681139)
              ·
                refine ⟨746890246513072234021709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497926831008714822681139 746890246513072234021709)
                ·
                  refine ⟨280083842442402087758141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746890246513072234021709 280083842442402087758141)
                  ·
                    rfl

theorem cell20_613644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_613644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613644 prefixEnd_613644 := by exact prefixLift 613644
  have htrace : WordTrace (prefixWord ++ tailWord_613644) baseStart_613644 baseEnd_613644 := by
    simpa [prefixWord, tailWord_613644, baseEnd_613644] using wordTrace_append hprefix tailTrace_613644
  have hstable : (prefixWord ++ tailWord_613644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613644).length < 2 ^ (prefixWord ++ tailWord_613644).sum := by decide
  have hdescent : baseEnd_613644 < baseStart_613644 := by decide
  rcases family_descends (prefixWord ++ tailWord_613644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613682 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_613682 : Nat := 118140960795 + 613682 * 2 ^ 59
def prefixEnd_613682 : Nat := 4983230072969 + 3 ^ 40 * 613682 * 2
def baseEnd_613682 : Nat := 280101186677842844491319

theorem tailTrace_613682 : CollatzResearch.WordTrace tailWord_613682 prefixEnd_613682 280101186677842844491319 := by
  unfold tailWord_613682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595705340685599346618825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14921880908494931590983533 5595705340685599346618825)
  ·
    refine ⟨4196779005514199509964119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5595705340685599346618825 4196779005514199509964119)
    ·
      refine ⟨6295168508271299264946179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196779005514199509964119 6295168508271299264946179)
      ·
        refine ⟨9442752762406948897419269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6295168508271299264946179 9442752762406948897419269)
        ·
          refine ⟨1770516142951302918266113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9442752762406948897419269 1770516142951302918266113)
          ·
            refine ⟨1327887107213477188699585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770516142951302918266113 1327887107213477188699585)
            ·
              refine ⟨995915330410107891524689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327887107213477188699585 995915330410107891524689)
              ·
                refine ⟨746936497807580918643517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995915330410107891524689 746936497807580918643517)
                ·
                  refine ⟨280101186677842844491319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746936497807580918643517 280101186677842844491319)
                  ·
                    rfl

theorem cell20_613682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_613682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613682 prefixEnd_613682 := by exact prefixLift 613682
  have htrace : WordTrace (prefixWord ++ tailWord_613682) baseStart_613682 baseEnd_613682 := by
    simpa [prefixWord, tailWord_613682, baseEnd_613682] using wordTrace_append hprefix tailTrace_613682
  have hstable : (prefixWord ++ tailWord_613682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613682).length < 2 ^ (prefixWord ++ tailWord_613682).sum := by decide
  have hdescent : baseEnd_613682 < baseStart_613682 := by decide
  rcases family_descends (prefixWord ++ tailWord_613682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613685 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 2]
def baseStart_613685 : Nat := 118140960795 + 613685 * 2 ^ 59
def prefixEnd_613685 : Nat := 4983230072969 + 3 ^ 40 * 613685 * 2
def baseEnd_613685 : Nat := 280102555959588167391307

theorem tailTrace_613685 : CollatzResearch.WordTrace tailWord_613685 prefixEnd_613685 280102555959588167391307 := by
  unfold tailWord_613685
  simp only [CollatzResearch.WordTrace]
  refine ⟨22382930781731528898834509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14921953854487685932556339 22382930781731528898834509)
  ·
    refine ⟨8393599043149323337062941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22382930781731528898834509 8393599043149323337062941)
    ·
      refine ⟨3147599641180996251398603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8393599043149323337062941 3147599641180996251398603)
      ·
        refine ⟨4721399461771494377097905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147599641180996251398603 4721399461771494377097905)
        ·
          refine ⟨3541049596328620782823429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4721399461771494377097905 3541049596328620782823429)
          ·
            refine ⟨663946799311616396779393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3541049596328620782823429 663946799311616396779393)
            ·
              refine ⟨497960099483712297584545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663946799311616396779393 497960099483712297584545)
              ·
                refine ⟨373470074612784223188409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497960099483712297584545 373470074612784223188409)
                ·
                  refine ⟨280102555959588167391307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373470074612784223188409 280102555959588167391307)
                  ·
                    rfl

theorem cell20_613685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_613685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613685 prefixEnd_613685 := by exact prefixLift 613685
  have htrace : WordTrace (prefixWord ++ tailWord_613685) baseStart_613685 baseEnd_613685 := by
    simpa [prefixWord, tailWord_613685, baseEnd_613685] using wordTrace_append hprefix tailTrace_613685
  have hstable : (prefixWord ++ tailWord_613685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613685).length < 2 ^ (prefixWord ++ tailWord_613685).sum := by decide
  have hdescent : baseEnd_613685 < baseStart_613685 := by decide
  rcases family_descends (prefixWord ++ tailWord_613685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613703 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_613703 : Nat := 118140960795 + 613703 * 2 ^ 59
def prefixEnd_613703 : Nat := 4983230072969 + 3 ^ 40 * 613703 * 2
def baseEnd_613703 : Nat := 280110771650060104791233

theorem tailTrace_613703 : CollatzResearch.WordTrace tailWord_613703 prefixEnd_613703 280110771650060104791233 := by
  unfold tailWord_613703
  simp only [CollatzResearch.WordTrace]
  refine ⟨22383587295666317972989763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14922391530444211981993175 22383587295666317972989763)
  ·
    refine ⟨33575380943499476959484645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22383587295666317972989763 33575380943499476959484645)
    ·
      refine ⟨6295383926906151929903371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33575380943499476959484645 6295383926906151929903371)
      ·
        refine ⟨9443075890359227894855057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6295383926906151929903371 9443075890359227894855057)
        ·
          refine ⟨7082306917769420921141293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9443075890359227894855057 7082306917769420921141293)
          ·
            refine ⟨2655865094163532845427985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7082306917769420921141293 2655865094163532845427985)
            ·
              refine ⟨1991898820622649634070989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655865094163532845427985 1991898820622649634070989)
              ·
                refine ⟨746962057733493612776621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991898820622649634070989 746962057733493612776621)
                ·
                  refine ⟨280110771650060104791233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746962057733493612776621 280110771650060104791233)
                  ·
                    rfl

theorem cell20_613703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_613703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613703 prefixEnd_613703 := by exact prefixLift 613703
  have htrace : WordTrace (prefixWord ++ tailWord_613703) baseStart_613703 baseEnd_613703 := by
    simpa [prefixWord, tailWord_613703, baseEnd_613703] using wordTrace_append hprefix tailTrace_613703
  have hstable : (prefixWord ++ tailWord_613703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613703).length < 2 ^ (prefixWord ++ tailWord_613703).sum := by decide
  have hdescent : baseEnd_613703 < baseStart_613703 := by decide
  rcases family_descends (prefixWord ++ tailWord_613703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613710 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_613710 : Nat := 118140960795 + 613710 * 2 ^ 59
def prefixEnd_613710 : Nat := 4983230072969 + 3 ^ 40 * 613710 * 2
def baseEnd_613710 : Nat := 280113966640799191557871

theorem tailTrace_613710 : CollatzResearch.WordTrace tailWord_613710 prefixEnd_613710 280113966640799191557871 := by
  unfold tailWord_613710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797980325830119771061823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14922561737760638778996389 2797980325830119771061823)
  ·
    refine ⟨4196970488745179656592735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2797980325830119771061823 4196970488745179656592735)
    ·
      refine ⟨6295455733117769484889103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196970488745179656592735 6295455733117769484889103)
      ·
        refine ⟨9443183599676654227333655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6295455733117769484889103 9443183599676654227333655)
        ·
          refine ⟨14164775399514981341000483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9443183599676654227333655 14164775399514981341000483)
          ·
            refine ⟨21247163099272472011500725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14164775399514981341000483 21247163099272472011500725)
            ·
              refine ⟨1991921540556794251078193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21247163099272472011500725 1991921540556794251078193)
              ·
                refine ⟨1493941155417595688308645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1991921540556794251078193 1493941155417595688308645)
                ·
                  refine ⟨280113966640799191557871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1493941155417595688308645 280113966640799191557871)
                  ·
                    rfl

theorem cell20_613710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_613710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613710 prefixEnd_613710 := by exact prefixLift 613710
  have htrace : WordTrace (prefixWord ++ tailWord_613710) baseStart_613710 baseEnd_613710 := by
    simpa [prefixWord, tailWord_613710, baseEnd_613710] using wordTrace_append hprefix tailTrace_613710
  have hstable : (prefixWord ++ tailWord_613710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613710).length < 2 ^ (prefixWord ++ tailWord_613710).sum := by decide
  have hdescent : baseEnd_613710 < baseStart_613710 := by decide
  rcases family_descends (prefixWord ++ tailWord_613710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613741 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_613741 : Nat := 118140960795 + 613741 * 2 ^ 59
def prefixEnd_613741 : Nat := 4983230072969 + 3 ^ 40 * 613741 * 2
def baseEnd_613741 : Nat := 280128115885500861524411

theorem tailTrace_613741 : CollatzResearch.WordTrace tailWord_613741 prefixEnd_613741 280128115885500861524411 := by
  unfold tailWord_613741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22384973269528650462873077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14923315513019100308582051 22384973269528650462873077)
  ·
    refine ⟨2098591244018310980894351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22384973269528650462873077 2098591244018310980894351)
    ·
      refine ⟨3147886866027466471341527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098591244018310980894351 3147886866027466471341527)
      ·
        refine ⟨4721830299041199707012291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147886866027466471341527 4721830299041199707012291)
        ·
          refine ⟨7082745448561799560518437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721830299041199707012291 7082745448561799560518437)
          ·
            refine ⟨1328014771605337417597207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7082745448561799560518437 1328014771605337417597207)
            ·
              refine ⟨1992022157408006126395811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328014771605337417597207 1992022157408006126395811)
              ·
                refine ⟨2988033236112009189593717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992022157408006126395811 2988033236112009189593717)
                ·
                  refine ⟨280128115885500861524411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2988033236112009189593717 280128115885500861524411)
                  ·
                    rfl

theorem cell20_613741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_613741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613741 prefixEnd_613741 := by exact prefixLift 613741
  have htrace : WordTrace (prefixWord ++ tailWord_613741) baseStart_613741 baseEnd_613741 := by
    simpa [prefixWord, tailWord_613741, baseEnd_613741] using wordTrace_append hprefix tailTrace_613741
  have hstable : (prefixWord ++ tailWord_613741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613741).length < 2 ^ (prefixWord ++ tailWord_613741).sum := by decide
  have hdescent : baseEnd_613741 < baseStart_613741 := by decide
  rcases family_descends (prefixWord ++ tailWord_613741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613778 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_613778 : Nat := 118140960795 + 613778 * 2 ^ 59
def prefixEnd_613778 : Nat := 4983230072969 + 3 ^ 40 * 613778 * 2
def baseEnd_613778 : Nat := 280145003693693177290927

theorem tailTrace_613778 : CollatzResearch.WordTrace tailWord_613778 prefixEnd_613778 280145003693693177290927 := by
  unfold tailWord_613778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596580692598651445492497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14924215180263070521313325 5596580692598651445492497)
  ·
    refine ⟨4197435519448988584119373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5596580692598651445492497 4197435519448988584119373)
    ·
      refine ⟨1574038319793370719044765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4197435519448988584119373 1574038319793370719044765)
      ·
        refine ⟨590264369922514019641787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1574038319793370719044765 590264369922514019641787)
        ·
          refine ⟨885396554883771029462681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590264369922514019641787 885396554883771029462681)
          ·
            refine ⟨664047416162828272097011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885396554883771029462681 664047416162828272097011)
            ·
              refine ⟨996071124244242408145517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664047416162828272097011 996071124244242408145517)
              ·
                refine ⟨373526671591590903054569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 996071124244242408145517 373526671591590903054569)
                ·
                  refine ⟨280145003693693177290927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373526671591590903054569 280145003693693177290927)
                  ·
                    rfl

theorem cell20_613778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_613778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613778 prefixEnd_613778 := by exact prefixLift 613778
  have htrace : WordTrace (prefixWord ++ tailWord_613778) baseStart_613778 baseEnd_613778 := by
    simpa [prefixWord, tailWord_613778, baseEnd_613778] using wordTrace_append hprefix tailTrace_613778
  have hstable : (prefixWord ++ tailWord_613778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613778).length < 2 ^ (prefixWord ++ tailWord_613778).sum := by decide
  have hdescent : baseEnd_613778 < baseStart_613778 := by decide
  rcases family_descends (prefixWord ++ tailWord_613778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613813 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 3]
def baseStart_613813 : Nat := 118140960795 + 613813 * 2 ^ 59
def prefixEnd_613813 : Nat := 4983230072969 + 3 ^ 40 * 613813 * 2
def baseEnd_613813 : Nat := 280160978647388611124117

theorem tailTrace_613813 : CollatzResearch.WordTrace tailWord_613813 prefixEnd_613813 280160978647388611124117 := by
  unfold tailWord_613813
  simp only [CollatzResearch.WordTrace]
  refine ⟨22387599325267806759494093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14925066216845204506329395 22387599325267806759494093)
  ·
    refine ⟨8395349746975427534810285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22387599325267806759494093 8395349746975427534810285)
    ·
      refine ⟨3148256155115785325553857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8395349746975427534810285 3148256155115785325553857)
      ·
        refine ⟨2361192116336838994165393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3148256155115785325553857 2361192116336838994165393)
        ·
          refine ⟨1770894087252629245624045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361192116336838994165393 1770894087252629245624045)
          ·
            refine ⟨664085282719735967109017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1770894087252629245624045 664085282719735967109017)
            ·
              refine ⟨498063962039801975331763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664085282719735967109017 498063962039801975331763)
              ·
                refine ⟨747095943059702962997645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498063962039801975331763 747095943059702962997645)
                ·
                  refine ⟨280160978647388611124117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747095943059702962997645 280160978647388611124117)
                  ·
                    rfl

theorem cell20_613813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_613813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613813 prefixEnd_613813 := by exact prefixLift 613813
  have htrace : WordTrace (prefixWord ++ tailWord_613813) baseStart_613813 baseEnd_613813 := by
    simpa [prefixWord, tailWord_613813, baseEnd_613813] using wordTrace_append hprefix tailTrace_613813
  have hstable : (prefixWord ++ tailWord_613813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613813).length < 2 ^ (prefixWord ++ tailWord_613813).sum := by decide
  have hdescent : baseEnd_613813 < baseStart_613813 := by decide
  rcases family_descends (prefixWord ++ tailWord_613813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613838 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_613838 : Nat := 118140960795 + 613838 * 2 ^ 59
def prefixEnd_613838 : Nat := 4983230072969 + 3 ^ 40 * 613838 * 2
def baseEnd_613838 : Nat := 280172389328599635290681

theorem tailTrace_613838 : CollatzResearch.WordTrace tailWord_613838 prefixEnd_613838 280172389328599635290681 := by
  unfold tailWord_613838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798563893772154503644271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14925674100118157352769445 2798563893772154503644271)
  ·
    refine ⟨4197845840658231755466407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2798563893772154503644271 4197845840658231755466407)
    ·
      refine ⟨6296768760987347633199611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4197845840658231755466407 6296768760987347633199611)
      ·
        refine ⟨9445153141481021449799417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296768760987347633199611 9445153141481021449799417)
        ·
          refine ⟨7083864856110766087349563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9445153141481021449799417 7083864856110766087349563)
          ·
            refine ⟨10625797284166149131024345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7083864856110766087349563 10625797284166149131024345)
            ·
              refine ⟨7969347963124611848268259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10625797284166149131024345 7969347963124611848268259)
              ·
                refine ⟨11954021944686917772402389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7969347963124611848268259 11954021944686917772402389)
                ·
                  refine ⟨280172389328599635290681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11954021944686917772402389 280172389328599635290681)
                  ·
                    rfl

theorem cell20_613838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_613838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613838 prefixEnd_613838 := by exact prefixLift 613838
  have htrace : WordTrace (prefixWord ++ tailWord_613838) baseStart_613838 baseEnd_613838 := by
    simpa [prefixWord, tailWord_613838, baseEnd_613838] using wordTrace_append hprefix tailTrace_613838
  have hstable : (prefixWord ++ tailWord_613838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613838).length < 2 ^ (prefixWord ++ tailWord_613838).sum := by decide
  have hdescent : baseEnd_613838 < baseStart_613838 := by decide
  rcases family_descends (prefixWord ++ tailWord_613838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613852 : List Nat := [2, 2, 16]
def baseStart_613852 : Nat := 118140960795 + 613852 * 2 ^ 59
def prefixEnd_613852 : Nat := 4983230072969 + 3 ^ 40 * 613852 * 2
def baseEnd_613852 : Nat := 384333030603673263133

theorem tailTrace_613852 : CollatzResearch.WordTrace tailWord_613852 prefixEnd_613852 384333030603673263133 := by
  unfold tailWord_613852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11194510886063258210081905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14926014514751010946775873 11194510886063258210081905)
  ·
    refine ⟨8395883164547443657561429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11194510886063258210081905 8395883164547443657561429)
    ·
      refine ⟨384333030603673263133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 8395883164547443657561429 384333030603673263133)
      ·
        rfl

theorem cell20_613852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 16].length) (baseStart_613852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613852 prefixEnd_613852 := by exact prefixLift 613852
  have htrace : WordTrace (prefixWord ++ tailWord_613852) baseStart_613852 baseEnd_613852 := by
    simpa [prefixWord, tailWord_613852, baseEnd_613852] using wordTrace_append hprefix tailTrace_613852
  have hstable : (prefixWord ++ tailWord_613852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613852).length < 2 ^ (prefixWord ++ tailWord_613852).sum := by decide
  have hdescent : baseEnd_613852 < baseStart_613852 := by decide
  rcases family_descends (prefixWord ++ tailWord_613852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613855 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_613855 : Nat := 118140960795 + 613855 * 2 ^ 59
def prefixEnd_613855 : Nat := 4983230072969 + 3 ^ 40 * 613855 * 2
def baseEnd_613855 : Nat := 280180148591823131723945

theorem tailTrace_613855 : CollatzResearch.WordTrace tailWord_613855 prefixEnd_613855 280180148591823131723945 := by
  unfold tailWord_613855
  simp only [CollatzResearch.WordTrace]
  refine ⟨22389131191115647932523019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14926087460743765288348679 22389131191115647932523019)
  ·
    refine ⟨33583696786673471898784529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22389131191115647932523019 33583696786673471898784529)
    ·
      refine ⟨25187772590005103924088397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33583696786673471898784529 25187772590005103924088397)
      ·
        refine ⟨9445414721251913971533149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25187772590005103924088397 9445414721251913971533149)
        ·
          refine ⟨3542030520469467739324931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9445414721251913971533149 3542030520469467739324931)
          ·
            refine ⟨5313045780704201608987397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542030520469467739324931 5313045780704201608987397)
            ·
              refine ⟨996196083882037801685137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5313045780704201608987397 996196083882037801685137)
              ·
                refine ⟨747147062911528351263853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996196083882037801685137 747147062911528351263853)
                ·
                  refine ⟨280180148591823131723945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747147062911528351263853 280180148591823131723945)
                  ·
                    rfl

theorem cell20_613855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_613855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613855 prefixEnd_613855 := by exact prefixLift 613855
  have htrace : WordTrace (prefixWord ++ tailWord_613855) baseStart_613855 baseEnd_613855 := by
    simpa [prefixWord, tailWord_613855, baseEnd_613855] using wordTrace_append hprefix tailTrace_613855
  have hstable : (prefixWord ++ tailWord_613855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613855).length < 2 ^ (prefixWord ++ tailWord_613855).sum := by decide
  have hdescent : baseEnd_613855 < baseStart_613855 := by decide
  rcases family_descends (prefixWord ++ tailWord_613855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613883 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_613883 : Nat := 118140960795 + 613883 * 2 ^ 59
def prefixEnd_613883 : Nat := 4983230072969 + 3 ^ 40 * 613883 * 2
def baseEnd_613883 : Nat := 280192928554779478790497

theorem tailTrace_613883 : CollatzResearch.WordTrace tailWord_613883 prefixEnd_613883 280192928554779478790497 := by
  unfold tailWord_613883
  simp only [CollatzResearch.WordTrace]
  refine ⟨22390152435014208714542303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14926768290009472476361535 22390152435014208714542303)
  ·
    refine ⟨33585228652521313071813455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22390152435014208714542303 33585228652521313071813455)
    ·
      refine ⟨50377842978781969607720183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33585228652521313071813455 50377842978781969607720183)
      ·
        refine ⟨75566764468172954411580275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50377842978781969607720183 75566764468172954411580275)
        ·
          refine ⟨113350146702259431617370413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75566764468172954411580275 113350146702259431617370413)
          ·
            refine ⟨42506305013347286856513905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113350146702259431617370413 42506305013347286856513905)
            ·
              refine ⟨31879728760010465142385429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42506305013347286856513905 31879728760010465142385429)
              ·
                refine ⟨1494362285625490553549317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31879728760010465142385429 1494362285625490553549317)
                ·
                  refine ⟨280192928554779478790497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494362285625490553549317 280192928554779478790497)
                  ·
                    rfl

theorem cell20_613883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_613883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613883 prefixEnd_613883 := by exact prefixLift 613883
  have htrace : WordTrace (prefixWord ++ tailWord_613883) baseStart_613883 baseEnd_613883 := by
    simpa [prefixWord, tailWord_613883, baseEnd_613883] using wordTrace_append hprefix tailTrace_613883
  have hstable : (prefixWord ++ tailWord_613883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613883).length < 2 ^ (prefixWord ++ tailWord_613883).sum := by decide
  have hdescent : baseEnd_613883 < baseStart_613883 := by decide
  rcases family_descends (prefixWord ++ tailWord_613883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613917 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 2]
def baseStart_613917 : Nat := 118140960795 + 613917 * 2 ^ 59
def prefixEnd_613917 : Nat := 4983230072969 + 3 ^ 40 * 613917 * 2
def baseEnd_613917 : Nat := 280208447081226471657025

theorem tailTrace_613917 : CollatzResearch.WordTrace tailWord_613917 prefixEnd_613917 280208447081226471657025 := by
  unfold tailWord_613917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22391392516891032521280005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14927595011260688347520003 22391392516891032521280005)
  ·
    refine ⟨4198386096917068597740001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22391392516891032521280005 4198386096917068597740001)
    ·
      refine ⟨3148789572687801448305001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4198386096917068597740001 3148789572687801448305001)
      ·
        refine ⟨2361592179515851086228751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3148789572687801448305001 2361592179515851086228751)
        ·
          refine ⟨3542388269273776629343127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361592179515851086228751 3542388269273776629343127)
          ·
            refine ⟨5313582403910664944014691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542388269273776629343127 5313582403910664944014691)
            ·
              refine ⟨7970373605865997416022037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313582403910664944014691 7970373605865997416022037)
              ·
                refine ⟨373611262774968628876033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7970373605865997416022037 373611262774968628876033)
                ·
                  refine ⟨280208447081226471657025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373611262774968628876033 280208447081226471657025)
                  ·
                    rfl

theorem cell20_613917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_613917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613917 prefixEnd_613917 := by exact prefixLift 613917
  have htrace : WordTrace (prefixWord ++ tailWord_613917) baseStart_613917 baseEnd_613917 := by
    simpa [prefixWord, tailWord_613917, baseEnd_613917] using wordTrace_append hprefix tailTrace_613917
  have hstable : (prefixWord ++ tailWord_613917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613917).length < 2 ^ (prefixWord ++ tailWord_613917).sum := by decide
  have hdescent : baseEnd_613917 < baseStart_613917 := by decide
  rcases family_descends (prefixWord ++ tailWord_613917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613945 : List Nat := [1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_613945 : Nat := 118140960795 + 613945 * 2 ^ 59
def prefixEnd_613945 : Nat := 4983230072969 + 3 ^ 40 * 613945 * 2
def baseEnd_613945 : Nat := 93407075681394272907859

theorem tailTrace_613945 : CollatzResearch.WordTrace tailWord_613945 prefixEnd_613945 93407075681394272907859 := by
  unfold tailWord_613945
  simp only [CollatzResearch.WordTrace]
  refine ⟨22392413760789593303299289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14928275840526395535532859 22392413760789593303299289)
  ·
    refine ⟨16794310320592194977474467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22392413760789593303299289 16794310320592194977474467)
    ·
      refine ⟨25191465480888292466211701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16794310320592194977474467 25191465480888292466211701)
      ·
        refine ⟨2361699888833277418707347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25191465480888292466211701 2361699888833277418707347)
        ·
          refine ⟨3542549833249916128061021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361699888833277418707347 3542549833249916128061021)
          ·
            refine ⟨1328456187468718548022883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3542549833249916128061021 1328456187468718548022883)
            ·
              refine ⟨1992684281203077822034325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328456187468718548022883 1992684281203077822034325)
              ·
                refine ⟨93407075681394272907859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1992684281203077822034325 93407075681394272907859)
                ·
                  rfl

theorem cell20_613945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_613945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613945 prefixEnd_613945 := by exact prefixLift 613945
  have htrace : WordTrace (prefixWord ++ tailWord_613945) baseStart_613945 baseEnd_613945 := by
    simpa [prefixWord, tailWord_613945, baseEnd_613945] using wordTrace_append hprefix tailTrace_613945
  have hstable : (prefixWord ++ tailWord_613945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613945).length < 2 ^ (prefixWord ++ tailWord_613945).sum := by decide
  have hdescent : baseEnd_613945 < baseStart_613945 := by decide
  rcases family_descends (prefixWord ++ tailWord_613945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613958 : List Nat := [6, 1, 1, 1, 4, 1, 6]
def baseStart_613958 : Nat := 118140960795 + 613958 * 2 ^ 59
def prefixEnd_613958 : Nat := 4983230072969 + 3 ^ 40 * 613958 * 2
def baseEnd_613958 : Nat := 31136351177601394587799

theorem tailTrace_613958 : CollatzResearch.WordTrace tailWord_613958 prefixEnd_613958 31136351177601394587799 := by
  unfold tailWord_613958
  simp only [CollatzResearch.WordTrace]
  refine ⟨699777747179453016360079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14928591939828331015681685 699777747179453016360079)
  ·
    refine ⟨1049666620769179524540119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699777747179453016360079 1049666620769179524540119)
    ·
      refine ⟨1574499931153769286810179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049666620769179524540119 1574499931153769286810179)
      ·
        refine ⟨2361749896730653930215269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574499931153769286810179 2361749896730653930215269)
        ·
          refine ⟨442828105636997611915363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2361749896730653930215269 442828105636997611915363)
          ·
            refine ⟨664242158455496417873045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442828105636997611915363 664242158455496417873045)
            ·
              refine ⟨31136351177601394587799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 664242158455496417873045 31136351177601394587799)
              ·
                rfl

theorem cell20_613958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 6].length) (baseStart_613958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613958 prefixEnd_613958 := by exact prefixLift 613958
  have htrace : WordTrace (prefixWord ++ tailWord_613958) baseStart_613958 baseEnd_613958 := by
    simpa [prefixWord, tailWord_613958, baseEnd_613958] using wordTrace_append hprefix tailTrace_613958
  have hstable : (prefixWord ++ tailWord_613958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613958).length < 2 ^ (prefixWord ++ tailWord_613958).sum := by decide
  have hdescent : baseEnd_613958 < baseStart_613958 := by decide
  rcases family_descends (prefixWord ++ tailWord_613958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613972 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_613972 : Nat := 118140960795 + 613972 * 2 ^ 59
def prefixEnd_613972 : Nat := 4983230072969 + 3 ^ 40 * 613972 * 2
def baseEnd_613972 : Nat := 280233550579890724823467

theorem tailTrace_613972 : CollatzResearch.WordTrace tailWord_613972 prefixEnd_613972 280233550579890724823467 := by
  unfold tailWord_613972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196699265845888457266085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14928932354461184609688113 11196699265845888457266085)
  ·
    refine ⟨2099381112346104085737391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11196699265845888457266085 2099381112346104085737391)
    ·
      refine ⟨3149071668519156128606087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099381112346104085737391 3149071668519156128606087)
      ·
        refine ⟨4723607502778734192909131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149071668519156128606087 4723607502778734192909131)
        ·
          refine ⟨7085411254168101289363697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723607502778734192909131 7085411254168101289363697)
          ·
            refine ⟨5314058440626075967022773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7085411254168101289363697 5314058440626075967022773)
            ·
              refine ⟨498192978808694621908385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5314058440626075967022773 498192978808694621908385)
              ·
                refine ⟨373644734106520966431289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498192978808694621908385 373644734106520966431289)
                ·
                  refine ⟨280233550579890724823467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373644734106520966431289 280233550579890724823467)
                  ·
                    rfl

theorem cell20_613972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_613972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_613972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_613972 prefixEnd_613972 := by exact prefixLift 613972
  have htrace : WordTrace (prefixWord ++ tailWord_613972) baseStart_613972 baseEnd_613972 := by
    simpa [prefixWord, tailWord_613972, baseEnd_613972] using wordTrace_append hprefix tailTrace_613972
  have hstable : (prefixWord ++ tailWord_613972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613972).length < 2 ^ (prefixWord ++ tailWord_613972).sum := by decide
  have hdescent : baseEnd_613972 < baseStart_613972 := by decide
  rcases family_descends (prefixWord ++ tailWord_613972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614052 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_614052 : Nat := 118140960795 + 614052 * 2 ^ 59
def prefixEnd_614052 : Nat := 4983230072969 + 3 ^ 40 * 614052 * 2
def baseEnd_614052 : Nat := 280270064759766002156473

theorem tailTrace_614052 : CollatzResearch.WordTrace tailWord_614052 prefixEnd_614052 280270064759766002156473 := by
  unfold tailWord_614052
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198158185700975288722205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14930877580934633718296273 11198158185700975288722205)
  ·
    refine ⟨4199309319637865733270827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11198158185700975288722205 4199309319637865733270827)
    ·
      refine ⟨6298963979456798599906241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199309319637865733270827 6298963979456798599906241)
      ·
        refine ⟨4724222984592598949929681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6298963979456798599906241 4724222984592598949929681)
        ·
          refine ⟨3543167238444449212447261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4724222984592598949929681 3543167238444449212447261)
          ·
            refine ⟨1328687714416668454667723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3543167238444449212447261 1328687714416668454667723)
            ·
              refine ⟨1993031571625002682001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328687714416668454667723 1993031571625002682001585)
              ·
                refine ⟨1494773678718752011501189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993031571625002682001585 1494773678718752011501189)
                ·
                  refine ⟨280270064759766002156473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494773678718752011501189 280270064759766002156473)
                  ·
                    rfl

theorem cell20_614052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_614052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614052 prefixEnd_614052 := by exact prefixLift 614052
  have htrace : WordTrace (prefixWord ++ tailWord_614052) baseStart_614052 baseEnd_614052 := by
    simpa [prefixWord, tailWord_614052, baseEnd_614052] using wordTrace_append hprefix tailTrace_614052
  have hstable : (prefixWord ++ tailWord_614052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614052).length < 2 ^ (prefixWord ++ tailWord_614052).sum := by decide
  have hdescent : baseEnd_614052 < baseStart_614052 := by decide
  rcases family_descends (prefixWord ++ tailWord_614052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614080 : List Nat := [2, 1, 1, 2, 4, 1, 9]
def baseStart_614080 : Nat := 118140960795 + 614080 * 2 ^ 59
def prefixEnd_614080 : Nat := 4983230072969 + 3 ^ 40 * 614080 * 2
def baseEnd_614080 : Nat := 31142538302524705469225

theorem tailTrace_614080 : CollatzResearch.WordTrace tailWord_614080 prefixEnd_614080 31142538302524705469225 := by
  unfold tailWord_614080
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198668807650255679731847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14931558410200340906309129 11198668807650255679731847)
  ·
    refine ⟨16798003211475383519597771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11198668807650255679731847 16798003211475383519597771)
    ·
      refine ⟨25197004817213075279396657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16798003211475383519597771 25197004817213075279396657)
      ·
        refine ⟨18897753612909806459547493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25197004817213075279396657 18897753612909806459547493)
        ·
          refine ⟨3543328802420588711165155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18897753612909806459547493 3543328802420588711165155)
          ·
            refine ⟨5314993203630883066747733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543328802420588711165155 5314993203630883066747733)
            ·
              refine ⟨31142538302524705469225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5314993203630883066747733 31142538302524705469225)
              ·
                rfl

theorem cell20_614080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_614080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614080 prefixEnd_614080 := by exact prefixLift 614080
  have htrace : WordTrace (prefixWord ++ tailWord_614080) baseStart_614080 baseEnd_614080 := by
    simpa [prefixWord, tailWord_614080, baseEnd_614080] using wordTrace_append hprefix tailTrace_614080
  have hstable : (prefixWord ++ tailWord_614080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614080).length < 2 ^ (prefixWord ++ tailWord_614080).sum := by decide
  have hdescent : baseEnd_614080 < baseStart_614080 := by decide
  rcases family_descends (prefixWord ++ tailWord_614080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614086 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_614086 : Nat := 118140960795 + 614086 * 2 ^ 59
def prefixEnd_614086 : Nat := 4983230072969 + 3 ^ 40 * 614086 * 2
def baseEnd_614086 : Nat := 280285583286212995023001

theorem tailTrace_614086 : CollatzResearch.WordTrace tailWord_614086 prefixEnd_614086 280285583286212995023001 := by
  unfold tailWord_614086
  simp only [CollatzResearch.WordTrace]
  refine ⟨699923639164961699505691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14931704302185849589454741 699923639164961699505691)
  ·
    refine ⟨1049885458747442549258537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699923639164961699505691 1049885458747442549258537)
    ·
      refine ⟨787414094060581911943903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1049885458747442549258537 787414094060581911943903)
      ·
        refine ⟨1181121141090872867915855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787414094060581911943903 1181121141090872867915855)
        ·
          refine ⟨1771681711636309301873783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181121141090872867915855 1771681711636309301873783)
          ·
            refine ⟨2657522567454463952810675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771681711636309301873783 2657522567454463952810675)
            ·
              refine ⟨3986283851181695929216013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657522567454463952810675 3986283851181695929216013)
              ·
                refine ⟨1494856444193135973456005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3986283851181695929216013 1494856444193135973456005)
                ·
                  refine ⟨280285583286212995023001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494856444193135973456005 280285583286212995023001)
                  ·
                    rfl

theorem cell20_614086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_614086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614086 prefixEnd_614086 := by exact prefixLift 614086
  have htrace : WordTrace (prefixWord ++ tailWord_614086) baseStart_614086 baseEnd_614086 := by
    simpa [prefixWord, tailWord_614086, baseEnd_614086] using wordTrace_append hprefix tailTrace_614086
  have hstable : (prefixWord ++ tailWord_614086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614086).length < 2 ^ (prefixWord ++ tailWord_614086).sum := by decide
  have hdescent : baseEnd_614086 < baseStart_614086 := by decide
  rcases family_descends (prefixWord ++ tailWord_614086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614111 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_614111 : Nat := 118140960795 + 614111 * 2 ^ 59
def prefixEnd_614111 : Nat := 4983230072969 + 3 ^ 40 * 614111 * 2
def baseEnd_614111 : Nat := 280296993967424019189565

theorem tailTrace_614111 : CollatzResearch.WordTrace tailWord_614111 prefixEnd_614111 280296993967424019189565 := by
  unfold tailWord_614111
  simp only [CollatzResearch.WordTrace]
  refine ⟨22398468278188203653842187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14932312185458802435894791 22398468278188203653842187)
  ·
    refine ⟨33597702417282305480763281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22398468278188203653842187 33597702417282305480763281)
    ·
      refine ⟨25198276812961729110572461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33597702417282305480763281 25198276812961729110572461)
      ·
        refine ⟨9449353804860648416464673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25198276812961729110572461 9449353804860648416464673)
        ·
          refine ⟨7087015353645486312348505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9449353804860648416464673 7087015353645486312348505)
          ·
            refine ⟨5315261515234114734261379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7087015353645486312348505 5315261515234114734261379)
            ·
              refine ⟨7972892272851172101392069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315261515234114734261379 7972892272851172101392069)
              ·
                refine ⟨1494917301159594769011013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7972892272851172101392069 1494917301159594769011013)
                ·
                  refine ⟨280296993967424019189565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1494917301159594769011013 280296993967424019189565)
                  ·
                    rfl

theorem cell20_614111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_614111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614111 prefixEnd_614111 := by exact prefixLift 614111
  have htrace : WordTrace (prefixWord ++ tailWord_614111) baseStart_614111 baseEnd_614111 := by
    simpa [prefixWord, tailWord_614111, baseEnd_614111] using wordTrace_append hprefix tailTrace_614111
  have hstable : (prefixWord ++ tailWord_614111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614111).length < 2 ^ (prefixWord ++ tailWord_614111).sum := by decide
  have hdescent : baseEnd_614111 < baseStart_614111 := by decide
  rcases family_descends (prefixWord ++ tailWord_614111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614128 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_614128 : Nat := 118140960795 + 614128 * 2 ^ 59
def prefixEnd_614128 : Nat := 4983230072969 + 3 ^ 40 * 614128 * 2
def baseEnd_614128 : Nat := 280304753230647515622829

theorem tailTrace_614128 : CollatzResearch.WordTrace tailWord_614128 prefixEnd_614128 280304753230647515622829 := by
  unfold tailWord_614128
  simp only [CollatzResearch.WordTrace]
  refine ⟨11199544159563307778605519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14932725546084410371474025 11199544159563307778605519)
  ·
    refine ⟨16799316239344961667908279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11199544159563307778605519 16799316239344961667908279)
    ·
      refine ⟨25198974359017442501862419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16799316239344961667908279 25198974359017442501862419)
      ·
        refine ⟨37798461538526163752793629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25198974359017442501862419 37798461538526163752793629)
        ·
          refine ⟨14174423076947311407297611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37798461538526163752793629 14174423076947311407297611)
          ·
            refine ⟨21261634615420967110946417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14174423076947311407297611 21261634615420967110946417)
            ·
              refine ⟨15946225961565725333209813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21261634615420967110946417 15946225961565725333209813)
              ·
                refine ⟨373739670974196687497105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15946225961565725333209813 373739670974196687497105)
                ·
                  refine ⟨280304753230647515622829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373739670974196687497105 280304753230647515622829)
                  ·
                    rfl

theorem cell20_614128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_614128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614128 prefixEnd_614128 := by exact prefixLift 614128
  have htrace : WordTrace (prefixWord ++ tailWord_614128) baseStart_614128 baseEnd_614128 := by
    simpa [prefixWord, tailWord_614128, baseEnd_614128] using wordTrace_append hprefix tailTrace_614128
  have hstable : (prefixWord ++ tailWord_614128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614128).length < 2 ^ (prefixWord ++ tailWord_614128).sum := by decide
  have hdescent : baseEnd_614128 < baseStart_614128 := by decide
  rcases family_descends (prefixWord ++ tailWord_614128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614156 : List Nat := [2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_614156 : Nat := 118140960795 + 614156 * 2 ^ 59
def prefixEnd_614156 : Nat := 4983230072969 + 3 ^ 40 * 614156 * 2
def baseEnd_614156 : Nat := 93439177731201287563127

theorem tailTrace_614156 : CollatzResearch.WordTrace tailWord_614156 prefixEnd_614156 93439177731201287563127 := by
  unfold tailWord_614156
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200054781512588169615161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14933406375350117559486881 11200054781512588169615161)
  ·
    refine ⟨8400041086134441127211371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11200054781512588169615161 8400041086134441127211371)
    ·
      refine ⟨12600061629201661690817057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400041086134441127211371 12600061629201661690817057)
      ·
        refine ⟨9450046221901246268112793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12600061629201661690817057 9450046221901246268112793)
        ·
          refine ⟨7087534666425934701084595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9450046221901246268112793 7087534666425934701084595)
          ·
            refine ⟨10631301999638902051626893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087534666425934701084595 10631301999638902051626893)
            ·
              refine ⟨3986738249864588269360085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10631301999638902051626893 3986738249864588269360085)
              ·
                refine ⟨93439177731201287563127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3986738249864588269360085 93439177731201287563127)
                ·
                  rfl

theorem cell20_614156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_614156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614156 prefixEnd_614156 := by exact prefixLift 614156
  have htrace : WordTrace (prefixWord ++ tailWord_614156) baseStart_614156 baseEnd_614156 := by
    simpa [prefixWord, tailWord_614156, baseEnd_614156] using wordTrace_append hprefix tailTrace_614156
  have hstable : (prefixWord ++ tailWord_614156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614156).length < 2 ^ (prefixWord ++ tailWord_614156).sum := by decide
  have hdescent : baseEnd_614156 < baseStart_614156 := by decide
  rcases family_descends (prefixWord ++ tailWord_614156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614163 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_614163 : Nat := 118140960795 + 614163 * 2 ^ 59
def prefixEnd_614163 : Nat := 4983230072969 + 3 ^ 40 * 614163 * 2
def baseEnd_614163 : Nat := 280320728184342949456019

theorem tailTrace_614163 : CollatzResearch.WordTrace tailWord_614163 prefixEnd_614163 280320728184342949456019 := by
  unfold tailWord_614163
  simp only [CollatzResearch.WordTrace]
  refine ⟨22400364873999816534735143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14933576582666544356490095 22400364873999816534735143)
  ·
    refine ⟨33600547310999724802102715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22400364873999816534735143 33600547310999724802102715)
    ·
      refine ⟨50400820966499587203154073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33600547310999724802102715 50400820966499587203154073)
      ·
        refine ⟨37800615724874690402365555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50400820966499587203154073 37800615724874690402365555)
        ·
          refine ⟨56700923587312035603548333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37800615724874690402365555 56700923587312035603548333)
          ·
            refine ⟨21262846345242013351330625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56700923587312035603548333 21262846345242013351330625)
            ·
              refine ⟨15947134758931510013497969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21262846345242013351330625 15947134758931510013497969)
              ·
                refine ⟨11960351069198632510123477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15947134758931510013497969 11960351069198632510123477)
                ·
                  refine ⟨280320728184342949456019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11960351069198632510123477 280320728184342949456019)
                  ·
                    rfl

theorem cell20_614163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_614163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614163 prefixEnd_614163 := by exact prefixLift 614163
  have htrace : WordTrace (prefixWord ++ tailWord_614163) baseStart_614163 baseEnd_614163 := by
    simpa [prefixWord, tailWord_614163, baseEnd_614163] using wordTrace_append hprefix tailTrace_614163
  have hstable : (prefixWord ++ tailWord_614163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614163).length < 2 ^ (prefixWord ++ tailWord_614163).sum := by decide
  have hdescent : baseEnd_614163 < baseStart_614163 := by decide
  rcases family_descends (prefixWord ++ tailWord_614163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614190 : List Nat := [4, 1, 3, 2, 3, 7]
def baseStart_614190 : Nat := 118140960795 + 614190 * 2 ^ 59
def prefixEnd_614190 : Nat := 4983230072969 + 3 ^ 40 * 614190 * 2
def baseEnd_614190 : Nat := 10382705619261142798367

theorem tailTrace_614190 : CollatzResearch.WordTrace tailWord_614190 prefixEnd_614190 10382705619261142798367 := by
  unfold tailWord_614190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800168705612750018246003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14934233096601333430645349 2800168705612750018246003)
  ·
    refine ⟨4200253058419125027369005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800168705612750018246003 4200253058419125027369005)
    ·
      refine ⟨1575094896907171885263377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4200253058419125027369005 1575094896907171885263377)
      ·
        refine ⟨1181321172680378913947533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575094896907171885263377 1181321172680378913947533)
        ·
          refine ⟨442995439755142092730325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1181321172680378913947533 442995439755142092730325)
          ·
            refine ⟨10382705619261142798367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 442995439755142092730325 10382705619261142798367)
            ·
              rfl

theorem cell20_614190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 7].length) (baseStart_614190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614190 prefixEnd_614190 := by exact prefixLift 614190
  have htrace : WordTrace (prefixWord ++ tailWord_614190) baseStart_614190 baseEnd_614190 := by
    simpa [prefixWord, tailWord_614190, baseEnd_614190] using wordTrace_append hprefix tailTrace_614190
  have hstable : (prefixWord ++ tailWord_614190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614190).length < 2 ^ (prefixWord ++ tailWord_614190).sum := by decide
  have hdescent : baseEnd_614190 < baseStart_614190 := by decide
  rcases family_descends (prefixWord ++ tailWord_614190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614194 : List Nat := [3, 2, 1, 1, 3, 10]
def baseStart_614194 : Nat := 118140960795 + 614194 * 2 ^ 59
def prefixEnd_614194 : Nat := 4983230072969 + 3 ^ 40 * 614194 * 2
def baseEnd_614194 : Nat := 10382773238112763682317

theorem tailTrace_614194 : CollatzResearch.WordTrace tailWord_614194 prefixEnd_614194 10382773238112763682317 := by
  unfold tailWord_614194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600373884221877207278409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14934330357925005886075757 5600373884221877207278409)
  ·
    refine ⟨4200280413166407905458807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5600373884221877207278409 4200280413166407905458807)
    ·
      refine ⟨6300420619749611858188211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200280413166407905458807 6300420619749611858188211)
      ·
        refine ⟨9450630929624417787282317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300420619749611858188211 9450630929624417787282317)
        ·
          refine ⟨3543986598609156670230869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9450630929624417787282317 3543986598609156670230869)
          ·
            refine ⟨10382773238112763682317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3543986598609156670230869 10382773238112763682317)
            ·
              rfl

theorem cell20_614194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 10].length) (baseStart_614194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614194 prefixEnd_614194 := by exact prefixLift 614194
  have htrace : WordTrace (prefixWord ++ tailWord_614194) baseStart_614194 baseEnd_614194 := by
    simpa [prefixWord, tailWord_614194, baseEnd_614194] using wordTrace_append hprefix tailTrace_614194
  have hstable : (prefixWord ++ tailWord_614194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614194).length < 2 ^ (prefixWord ++ tailWord_614194).sum := by decide
  have hdescent : baseEnd_614194 < baseStart_614194 := by decide
  rcases family_descends (prefixWord ++ tailWord_614194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614200 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_614200 : Nat := 118140960795 + 614200 * 2 ^ 59
def prefixEnd_614200 : Nat := 4983230072969 + 3 ^ 40 * 614200 * 2
def baseEnd_614200 : Nat := 280337615992535265222535

theorem tailTrace_614200 : CollatzResearch.WordTrace tailWord_614200 prefixEnd_614200 280337615992535265222535 := by
  unfold tailWord_614200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200857187432885926916027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14934476249910514569221369 11200857187432885926916027)
  ·
    refine ⟨16801285781149328890374041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11200857187432885926916027 16801285781149328890374041)
    ·
      refine ⟨12600964335861996667780531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16801285781149328890374041 12600964335861996667780531)
      ·
        refine ⟨18901446503792995001670797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12600964335861996667780531 18901446503792995001670797)
        ·
          refine ⟨7088042438922373125626549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18901446503792995001670797 7088042438922373125626549)
          ·
            refine ⟨664503978648972480527489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7088042438922373125626549 664503978648972480527489)
            ·
              refine ⟨498377983986729360395617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664503978648972480527489 498377983986729360395617)
              ·
                refine ⟨373783487990047020296713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498377983986729360395617 373783487990047020296713)
                ·
                  refine ⟨280337615992535265222535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373783487990047020296713 280337615992535265222535)
                  ·
                    rfl

theorem cell20_614200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_614200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614200 prefixEnd_614200 := by exact prefixLift 614200
  have htrace : WordTrace (prefixWord ++ tailWord_614200) baseStart_614200 baseEnd_614200 := by
    simpa [prefixWord, tailWord_614200, baseEnd_614200] using wordTrace_append hprefix tailTrace_614200
  have hstable : (prefixWord ++ tailWord_614200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614200).length < 2 ^ (prefixWord ++ tailWord_614200).sum := by decide
  have hdescent : baseEnd_614200 < baseStart_614200 := by decide
  rcases family_descends (prefixWord ++ tailWord_614200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614211 : List Nat := [1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_614211 : Nat := 118140960795 + 614211 * 2 ^ 59
def prefixEnd_614211 : Nat := 4983230072969 + 3 ^ 40 * 614211 * 2
def baseEnd_614211 : Nat := 93447545564089371951941

theorem tailTrace_614211 : CollatzResearch.WordTrace tailWord_614211 prefixEnd_614211 93447545564089371951941 := by
  unfold tailWord_614211
  simp only [CollatzResearch.WordTrace]
  refine ⟨22402115577825920732482487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14934743718550613821654991 22402115577825920732482487)
  ·
    refine ⟨33603173366738881098723731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22402115577825920732482487 33603173366738881098723731)
    ·
      refine ⟨50404760050108321648085597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33603173366738881098723731 50404760050108321648085597)
      ·
        refine ⟨18901785018790620618032099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50404760050108321648085597 18901785018790620618032099)
        ·
          refine ⟨28352677528185930927048149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18901785018790620618032099 28352677528185930927048149)
          ·
            refine ⟨664515879566857756102691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28352677528185930927048149 664515879566857756102691)
            ·
              refine ⟨996773819350286634154037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664515879566857756102691 996773819350286634154037)
              ·
                refine ⟨93447545564089371951941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 996773819350286634154037 93447545564089371951941)
                ·
                  rfl

theorem cell20_614211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_614211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614211 prefixEnd_614211 := by exact prefixLift 614211
  have htrace : WordTrace (prefixWord ++ tailWord_614211) baseStart_614211 baseEnd_614211 := by
    simpa [prefixWord, tailWord_614211, baseEnd_614211] using wordTrace_append hprefix tailTrace_614211
  have hstable : (prefixWord ++ tailWord_614211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614211).length < 2 ^ (prefixWord ++ tailWord_614211).sum := by decide
  have hdescent : baseEnd_614211 < baseStart_614211 := by decide
  rcases family_descends (prefixWord ++ tailWord_614211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614218 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_614218 : Nat := 118140960795 + 614218 * 2 ^ 59
def prefixEnd_614218 : Nat := 4983230072969 + 3 ^ 40 * 614218 * 2
def baseEnd_614218 : Nat := 280345831683007202622461

theorem tailTrace_614218 : CollatzResearch.WordTrace tailWord_614218 prefixEnd_614218 280345831683007202622461 := by
  unfold tailWord_614218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600592722200140231996827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14934913925867040618658205 5600592722200140231996827)
  ·
    refine ⟨8400889083300210347995241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600592722200140231996827 8400889083300210347995241)
    ·
      refine ⟨6300666812475157760996431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8400889083300210347995241 6300666812475157760996431)
      ·
        refine ⟨9451000218712736641494647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300666812475157760996431 9451000218712736641494647)
        ·
          refine ⟨14176500328069104962241971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9451000218712736641494647 14176500328069104962241971)
          ·
            refine ⟨21264750492103657443362957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14176500328069104962241971 21264750492103657443362957)
            ·
              refine ⟨7974281434538871541261109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21264750492103657443362957 7974281434538871541261109)
              ·
                refine ⟨747588884488019206993229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7974281434538871541261109 747588884488019206993229)
                ·
                  refine ⟨280345831683007202622461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747588884488019206993229 280345831683007202622461)
                  ·
                    rfl

theorem cell20_614218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_614218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614218 prefixEnd_614218 := by exact prefixLift 614218
  have htrace : WordTrace (prefixWord ++ tailWord_614218) baseStart_614218 baseEnd_614218 := by
    simpa [prefixWord, tailWord_614218, baseEnd_614218] using wordTrace_append hprefix tailTrace_614218
  have hstable : (prefixWord ++ tailWord_614218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614218).length < 2 ^ (prefixWord ++ tailWord_614218).sum := by decide
  have hdescent : baseEnd_614218 < baseStart_614218 := by decide
  rcases family_descends (prefixWord ++ tailWord_614218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614221 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_614221 : Nat := 118140960795 + 614221 * 2 ^ 59
def prefixEnd_614221 : Nat := 4983230072969 + 3 ^ 40 * 614221 * 2
def baseEnd_614221 : Nat := 280347200964752525522449

theorem tailTrace_614221 : CollatzResearch.WordTrace tailWord_614221 prefixEnd_614221 280347200964752525522449 := by
  unfold tailWord_614221
  simp only [CollatzResearch.WordTrace]
  refine ⟨22402480307789692440346517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14934986871859794960231011 22402480307789692440346517)
  ·
    refine ⟨1050116264427641833141243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22402480307789692440346517 1050116264427641833141243)
    ·
      refine ⟨1575174396641462749711865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050116264427641833141243 1575174396641462749711865)
      ·
        refine ⟨1181380797481097062283899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575174396641462749711865 1181380797481097062283899)
        ·
          refine ⟨1772071196221645593425849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181380797481097062283899 1772071196221645593425849)
          ·
            refine ⟨1329053397166234195069387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772071196221645593425849 1329053397166234195069387)
            ·
              refine ⟨1993580095749351292604081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329053397166234195069387 1993580095749351292604081)
              ·
                refine ⟨1495185071812013469453061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993580095749351292604081 1495185071812013469453061)
                ·
                  refine ⟨280347200964752525522449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495185071812013469453061 280347200964752525522449)
                  ·
                    rfl

theorem cell20_614221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_614221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614221 prefixEnd_614221 := by exact prefixLift 614221
  have htrace : WordTrace (prefixWord ++ tailWord_614221) baseStart_614221 baseEnd_614221 := by
    simpa [prefixWord, tailWord_614221, baseEnd_614221] using wordTrace_append hprefix tailTrace_614221
  have hstable : (prefixWord ++ tailWord_614221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614221).length < 2 ^ (prefixWord ++ tailWord_614221).sum := by decide
  have hdescent : baseEnd_614221 < baseStart_614221 := by decide
  rcases family_descends (prefixWord ++ tailWord_614221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614225 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_614225 : Nat := 118140960795 + 614225 * 2 ^ 59
def prefixEnd_614225 : Nat := 4983230072969 + 3 ^ 40 * 614225 * 2
def baseEnd_614225 : Nat := 280349026673746289389099

theorem tailTrace_614225 : CollatzResearch.WordTrace tailWord_614225 prefixEnd_614225 280349026673746289389099 := by
  unfold tailWord_614225
  simp only [CollatzResearch.WordTrace]
  refine ⟨22402626199775201123492129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14935084133183467415661419 22402626199775201123492129)
  ·
    refine ⟨16801969649831400842619097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22402626199775201123492129 16801969649831400842619097)
    ·
      refine ⟨12601477237373550631964323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16801969649831400842619097 12601477237373550631964323)
      ·
        refine ⟨18902215856060325947946485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12601477237373550631964323 18902215856060325947946485)
        ·
          refine ⟨1772082736505655557619983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18902215856060325947946485 1772082736505655557619983)
          ·
            refine ⟨2658124104758483336429975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772082736505655557619983 2658124104758483336429975)
            ·
              refine ⟨3987186157137725004644963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658124104758483336429975 3987186157137725004644963)
              ·
                refine ⟨5980779235706587506967445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3987186157137725004644963 5980779235706587506967445)
                ·
                  refine ⟨280349026673746289389099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5980779235706587506967445 280349026673746289389099)
                  ·
                    rfl

theorem cell20_614225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_614225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614225 prefixEnd_614225 := by exact prefixLift 614225
  have htrace : WordTrace (prefixWord ++ tailWord_614225) baseStart_614225 baseEnd_614225 := by
    simpa [prefixWord, tailWord_614225, baseEnd_614225] using wordTrace_append hprefix tailTrace_614225
  have hstable : (prefixWord ++ tailWord_614225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614225).length < 2 ^ (prefixWord ++ tailWord_614225).sum := by decide
  have hdescent : baseEnd_614225 < baseStart_614225 := by decide
  rcases family_descends (prefixWord ++ tailWord_614225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614228 : List Nat := [2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_614228 : Nat := 118140960795 + 614228 * 2 ^ 59
def prefixEnd_614228 : Nat := 4983230072969 + 3 ^ 40 * 614228 * 2
def baseEnd_614228 : Nat := 93450131985163870763029

theorem tailTrace_614228 : CollatzResearch.WordTrace tailWord_614228 prefixEnd_614228 93450131985163870763029 := by
  unfold tailWord_614228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11201367809382166317925669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14935157079176221757234225 11201367809382166317925669)
  ·
    refine ⟨2100256464259156184611063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11201367809382166317925669 2100256464259156184611063)
    ·
      refine ⟨3150384696388734276916595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2100256464259156184611063 3150384696388734276916595)
      ·
        refine ⟨4725577044583101415374893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150384696388734276916595 4725577044583101415374893)
        ·
          refine ⟨1772091391718663030765585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4725577044583101415374893 1772091391718663030765585)
          ·
            refine ⟨1329068543788997273074189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772091391718663030765585 1329068543788997273074189)
            ·
              refine ⟨498400703920873977402821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329068543788997273074189 498400703920873977402821)
              ·
                refine ⟨93450131985163870763029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498400703920873977402821 93450131985163870763029)
                ·
                  rfl

theorem cell20_614228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_614228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614228 prefixEnd_614228 := by exact prefixLift 614228
  have htrace : WordTrace (prefixWord ++ tailWord_614228) baseStart_614228 baseEnd_614228 := by
    simpa [prefixWord, tailWord_614228, baseEnd_614228] using wordTrace_append hprefix tailTrace_614228
  have hstable : (prefixWord ++ tailWord_614228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614228).length < 2 ^ (prefixWord ++ tailWord_614228).sum := by decide
  have hdescent : baseEnd_614228 < baseStart_614228 := by decide
  rcases family_descends (prefixWord ++ tailWord_614228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614308 : List Nat := [2, 3, 1, 2, 1, 3, 8]
def baseStart_614308 : Nat := 118140960795 + 614308 * 2 ^ 59
def prefixEnd_614308 : Nat := 4983230072969 + 3 ^ 40 * 614308 * 2
def baseEnd_614308 : Nat := 31154101126151876624677

theorem tailTrace_614308 : CollatzResearch.WordTrace tailWord_614308 prefixEnd_614308 31154101126151876624677 := by
  unfold tailWord_614308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202826729237253149381789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14937102305649670865842385 11202826729237253149381789)
  ·
    refine ⟨4201060023463969931018171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11202826729237253149381789 4201060023463969931018171)
    ·
      refine ⟨6301590035195954896527257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201060023463969931018171 6301590035195954896527257)
      ·
        refine ⟨4726192526396966172395443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6301590035195954896527257 4726192526396966172395443)
        ·
          refine ⟨7089288789595449258593165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726192526396966172395443 7089288789595449258593165)
          ·
            refine ⟨2658483296098293471972437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7089288789595449258593165 2658483296098293471972437)
            ·
              refine ⟨31154101126151876624677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2658483296098293471972437 31154101126151876624677)
              ·
                rfl

theorem cell20_614308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_614308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614308 prefixEnd_614308 := by exact prefixLift 614308
  have htrace : WordTrace (prefixWord ++ tailWord_614308) baseStart_614308 baseEnd_614308 := by
    simpa [prefixWord, tailWord_614308, baseEnd_614308] using wordTrace_append hprefix tailTrace_614308
  have hstable : (prefixWord ++ tailWord_614308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614308).length < 2 ^ (prefixWord ++ tailWord_614308).sum := by decide
  have hdescent : baseEnd_614308 < baseStart_614308 := by decide
  rcases family_descends (prefixWord ++ tailWord_614308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614324 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_614324 : Nat := 118140960795 + 614324 * 2 ^ 59
def prefixEnd_614324 : Nat := 4983230072969 + 3 ^ 40 * 614324 * 2
def baseEnd_614324 : Nat := 280394212971341945088695

theorem tailTrace_614324 : CollatzResearch.WordTrace tailWord_614324 prefixEnd_614324 280394212971341945088695 := by
  unfold tailWord_614324
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203118513208270515673013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14937491350944360687564017 11203118513208270515673013)
  ·
    refine ⟨1050292360613275360844345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11203118513208270515673013 1050292360613275360844345)
    ·
      refine ⟨787719270459956520633259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050292360613275360844345 787719270459956520633259)
      ·
        refine ⟨1181578905689934780949889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787719270459956520633259 1181578905689934780949889)
        ·
          refine ⟨886184179267451085712417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181578905689934780949889 886184179267451085712417)
          ·
            refine ⟨664638134450588314284313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886184179267451085712417 664638134450588314284313)
            ·
              refine ⟨498478600837941235713235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664638134450588314284313 498478600837941235713235)
              ·
                refine ⟨747717901256911853569853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498478600837941235713235 747717901256911853569853)
                ·
                  refine ⟨280394212971341945088695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747717901256911853569853 280394212971341945088695)
                  ·
                    rfl

theorem cell20_614324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_614324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614324 prefixEnd_614324 := by exact prefixLift 614324
  have htrace : WordTrace (prefixWord ++ tailWord_614324) baseStart_614324 baseEnd_614324 := by
    simpa [prefixWord, tailWord_614324, baseEnd_614324] using wordTrace_append hprefix tailTrace_614324
  have hstable : (prefixWord ++ tailWord_614324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614324).length < 2 ^ (prefixWord ++ tailWord_614324).sum := by decide
  have hdescent : baseEnd_614324 < baseStart_614324 := by decide
  rcases family_descends (prefixWord ++ tailWord_614324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614325 : List Nat := [1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_614325 : Nat := 118140960795 + 614325 * 2 ^ 59
def prefixEnd_614325 : Nat := 4983230072969 + 3 ^ 40 * 614325 * 2
def baseEnd_614325 : Nat := 93464889799530128685119

theorem tailTrace_614325 : CollatzResearch.WordTrace tailWord_614325 prefixEnd_614325 93464889799530128685119 := by
  unfold tailWord_614325
  simp only [CollatzResearch.WordTrace]
  refine ⟨22406273499412918202132429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14937515666275278801421619 22406273499412918202132429)
  ·
    refine ⟨8402352562279844325799661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22406273499412918202132429 8402352562279844325799661)
    ·
      refine ⟨3150882210854941622174873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8402352562279844325799661 3150882210854941622174873)
      ·
        refine ⟨2363161658141206216631155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3150882210854941622174873 2363161658141206216631155)
        ·
          refine ⟨3544742487211809324946733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363161658141206216631155 3544742487211809324946733)
          ·
            refine ⟨1329278432704428496855025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3544742487211809324946733 1329278432704428496855025)
            ·
              refine ⟨996958824528321372641269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329278432704428496855025 996958824528321372641269)
              ·
                refine ⟨93464889799530128685119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 996958824528321372641269 93464889799530128685119)
                ·
                  rfl

theorem cell20_614325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_614325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614325 prefixEnd_614325 := by exact prefixLift 614325
  have htrace : WordTrace (prefixWord ++ tailWord_614325) baseStart_614325 baseEnd_614325 := by
    simpa [prefixWord, tailWord_614325, baseEnd_614325] using wordTrace_append hprefix tailTrace_614325
  have hstable : (prefixWord ++ tailWord_614325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614325).length < 2 ^ (prefixWord ++ tailWord_614325).sum := by decide
  have hdescent : baseEnd_614325 < baseStart_614325 := by decide
  rcases family_descends (prefixWord ++ tailWord_614325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614346 : List Nat := [3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_614346 : Nat := 118140960795 + 614346 * 2 ^ 59
def prefixEnd_614346 : Nat := 4983230072969 + 3 ^ 40 * 614346 * 2
def baseEnd_614346 : Nat := 93468084790269215451757

theorem tailTrace_614346 : CollatzResearch.WordTrace tailWord_614346 prefixEnd_614346 93468084790269215451757 := by
  unfold tailWord_614346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5601759858084209697161723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14938026288224559192431261 5601759858084209697161723)
  ·
    refine ⟨8402639787126314545742585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5601759858084209697161723 8402639787126314545742585)
    ·
      refine ⟨6301979840344735909306939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8402639787126314545742585 6301979840344735909306939)
      ·
        refine ⟨9452969760517103863960409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6301979840344735909306939 9452969760517103863960409)
        ·
          refine ⟨7089727320387827897970307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9452969760517103863960409 7089727320387827897970307)
          ·
            refine ⟨10634590980581741846955461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7089727320387827897970307 10634590980581741846955461)
            ·
              refine ⟨1993985808859076596304149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10634590980581741846955461 1993985808859076596304149)
              ·
                refine ⟨93468084790269215451757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1993985808859076596304149 93468084790269215451757)
                ·
                  rfl

theorem cell20_614346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_614346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614346 prefixEnd_614346 := by exact prefixLift 614346
  have htrace : WordTrace (prefixWord ++ tailWord_614346) baseStart_614346 baseEnd_614346 := by
    simpa [prefixWord, tailWord_614346, baseEnd_614346] using wordTrace_append hprefix tailTrace_614346
  have hstable : (prefixWord ++ tailWord_614346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614346).length < 2 ^ (prefixWord ++ tailWord_614346).sum := by decide
  have hdescent : baseEnd_614346 < baseStart_614346 := by decide
  rcases family_descends (prefixWord ++ tailWord_614346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614353 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_614353 : Nat := 118140960795 + 614353 * 2 ^ 59
def prefixEnd_614353 : Nat := 4983230072969 + 3 ^ 40 * 614353 * 2
def baseEnd_614353 : Nat := 280407449361546733121909

theorem tailTrace_614353 : CollatzResearch.WordTrace tailWord_614353 prefixEnd_614353 280407449361546733121909 := by
  unfold tailWord_614353
  simp only [CollatzResearch.WordTrace]
  refine ⟨22407294743311478984151713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14938196495540985989434475 22407294743311478984151713)
  ·
    refine ⟨16805471057483609238113785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22407294743311478984151713 16805471057483609238113785)
    ·
      refine ⟨12604103293112706928585339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16805471057483609238113785 12604103293112706928585339)
      ·
        refine ⟨18906154939669060392878009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12604103293112706928585339 18906154939669060392878009)
        ·
          refine ⟨14179616204751795294658507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18906154939669060392878009 14179616204751795294658507)
          ·
            refine ⟨21269424307127692941987761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14179616204751795294658507 21269424307127692941987761)
            ·
              refine ⟨15952068230345769706490821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21269424307127692941987761 15952068230345769706490821)
              ·
                refine ⟨2991012793189831819967029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15952068230345769706490821 2991012793189831819967029)
                ·
                  refine ⟨280407449361546733121909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2991012793189831819967029 280407449361546733121909)
                  ·
                    rfl

theorem cell20_614353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_614353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_614353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_614353 prefixEnd_614353 := by exact prefixLift 614353
  have htrace : WordTrace (prefixWord ++ tailWord_614353) baseStart_614353 baseEnd_614353 := by
    simpa [prefixWord, tailWord_614353, baseEnd_614353] using wordTrace_append hprefix tailTrace_614353
  have hstable : (prefixWord ++ tailWord_614353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614353).length < 2 ^ (prefixWord ++ tailWord_614353).sum := by decide
  have hdescent : baseEnd_614353 < baseStart_614353 := by decide
  rcases family_descends (prefixWord ++ tailWord_614353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
