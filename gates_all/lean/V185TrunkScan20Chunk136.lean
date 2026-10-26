import V185TrunkScan20Chunk135

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_825777 : List Nat := [1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_825777 : Nat := 118140960795 + 825777 * 2 ^ 59
def prefixEnd_825777 : Nat := 4983230072969 + 3 ^ 40 * 825777 * 2
def baseEnd_825777 : Nat := 125635707978643222930319

theorem tailTrace_825777 : CollatzResearch.WordTrace tailWord_825777 prefixEnd_825777 125635707978643222930319 := by
  unfold tailWord_825777
  simp only [CollatzResearch.WordTrace]
  refine ⟨30118561529358435328619585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20079041019572290219079723 30118561529358435328619585)
  ·
    refine ⟨22588921147018826496464689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30118561529358435328619585 22588921147018826496464689)
    ·
      refine ⟨16941690860264119872348517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22588921147018826496464689 16941690860264119872348517)
      ·
        refine ⟨3176567036299522476065347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16941690860264119872348517 3176567036299522476065347)
        ·
          refine ⟨4764850554449283714098021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176567036299522476065347 4764850554449283714098021)
          ·
            refine ⟨893409478959240696393379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4764850554449283714098021 893409478959240696393379)
            ·
              refine ⟨1340114218438861044590069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893409478959240696393379 1340114218438861044590069)
              ·
                refine ⟨125635707978643222930319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1340114218438861044590069 125635707978643222930319)
                ·
                  rfl

theorem cell20_825777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_825777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825777 prefixEnd_825777 := by exact prefixLift 825777
  have htrace : WordTrace (prefixWord ++ tailWord_825777) baseStart_825777 baseEnd_825777 := by
    simpa [prefixWord, tailWord_825777, baseEnd_825777] using wordTrace_append hprefix tailTrace_825777
  have hstable : (prefixWord ++ tailWord_825777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825777).length < 2 ^ (prefixWord ++ tailWord_825777).sum := by decide
  have hdescent : baseEnd_825777 < baseStart_825777 := by decide
  rcases family_descends (prefixWord ++ tailWord_825777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825850 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_825850 : Nat := 118140960795 + 825850 * 2 ^ 59
def prefixEnd_825850 : Nat := 4983230072969 + 3 ^ 40 * 825850 * 2
def baseEnd_825850 : Nat := 376940443125065859357325

theorem tailTrace_825850 : CollatzResearch.WordTrace tailWord_825850 prefixEnd_825850 376940443125065859357325 := by
  unfold tailWord_825850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7530306014523492199006751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20080816038729312530684669 7530306014523492199006751)
  ·
    refine ⟨11295459021785238298510127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7530306014523492199006751 11295459021785238298510127)
    ·
      refine ⟨16943188532677857447765191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11295459021785238298510127 16943188532677857447765191)
      ·
        refine ⟨25414782799016786171647787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943188532677857447765191 25414782799016786171647787)
        ·
          refine ⟨38122174198525179257471681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25414782799016786171647787 38122174198525179257471681)
          ·
            refine ⟨28591630648893884443103761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38122174198525179257471681 28591630648893884443103761)
            ·
              refine ⟨21443722986670413332327821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28591630648893884443103761 21443722986670413332327821)
              ·
                refine ⟨8041396120001404999622933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21443722986670413332327821 8041396120001404999622933)
                ·
                  refine ⟨376940443125065859357325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8041396120001404999622933 376940443125065859357325)
                  ·
                    rfl

theorem cell20_825850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_825850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825850 prefixEnd_825850 := by exact prefixLift 825850
  have htrace : WordTrace (prefixWord ++ tailWord_825850) baseStart_825850 baseEnd_825850 := by
    simpa [prefixWord, tailWord_825850, baseEnd_825850] using wordTrace_append hprefix tailTrace_825850
  have hstable : (prefixWord ++ tailWord_825850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825850).length < 2 ^ (prefixWord ++ tailWord_825850).sum := by decide
  have hdescent : baseEnd_825850 < baseStart_825850 := by decide
  rcases family_descends (prefixWord ++ tailWord_825850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825860 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_825860 : Nat := 118140960795 + 825860 * 2 ^ 59
def prefixEnd_825860 : Nat := 4983230072969 + 3 ^ 40 * 825860 * 2
def baseEnd_825860 : Nat := 376945007397550269023951

theorem tailTrace_825860 : CollatzResearch.WordTrace tailWord_825860 prefixEnd_825860 376945007397550269023951 := by
  unfold tailWord_825860
  simp only [CollatzResearch.WordTrace]
  refine ⟨15060794394028870251945517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20081059192038493669260689 15060794394028870251945517)
  ·
    refine ⟨5647797897760826344479569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15060794394028870251945517 5647797897760826344479569)
    ·
      refine ⟨4235848423320619758359677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5647797897760826344479569 4235848423320619758359677)
      ·
        refine ⟨1588443158745232409384879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4235848423320619758359677 1588443158745232409384879)
        ·
          refine ⟨2382664738117848614077319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588443158745232409384879 2382664738117848614077319)
          ·
            refine ⟨3573997107176772921115979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382664738117848614077319 3573997107176772921115979)
            ·
              refine ⟨5360995660765159381673969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573997107176772921115979 5360995660765159381673969)
              ·
                refine ⟨4020746745573869536255477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5360995660765159381673969 4020746745573869536255477)
                ·
                  refine ⟨376945007397550269023951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4020746745573869536255477 376945007397550269023951)
                  ·
                    rfl

theorem cell20_825860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_825860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825860 prefixEnd_825860 := by exact prefixLift 825860
  have htrace : WordTrace (prefixWord ++ tailWord_825860) baseStart_825860 baseEnd_825860 := by
    simpa [prefixWord, tailWord_825860, baseEnd_825860] using wordTrace_append hprefix tailTrace_825860
  have hstable : (prefixWord ++ tailWord_825860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825860).length < 2 ^ (prefixWord ++ tailWord_825860).sum := by decide
  have hdescent : baseEnd_825860 < baseStart_825860 := by decide
  rcases family_descends (prefixWord ++ tailWord_825860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825884 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_825884 : Nat := 118140960795 + 825884 * 2 ^ 59
def prefixEnd_825884 : Nat := 4983230072969 + 3 ^ 40 * 825884 * 2
def baseEnd_825884 : Nat := 376955961651512852223853

theorem tailTrace_825884 : CollatzResearch.WordTrace tailWord_825884 prefixEnd_825884 376955961651512852223853 := by
  unfold tailWord_825884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061232069985396301382353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20081642759980528401843137 15061232069985396301382353)
  ·
    refine ⟨11295924052489047226036765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15061232069985396301382353 11295924052489047226036765)
    ·
      refine ⟨4235971519683392709763787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11295924052489047226036765 4235971519683392709763787)
      ·
        refine ⟨6353957279525089064645681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235971519683392709763787 6353957279525089064645681)
        ·
          refine ⟨4765467959643816798484261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353957279525089064645681 4765467959643816798484261)
          ·
            refine ⟨893525242433215649715799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4765467959643816798484261 893525242433215649715799)
            ·
              refine ⟨1340287863649823474573699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893525242433215649715799 1340287863649823474573699)
              ·
                refine ⟨2010431795474735211860549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340287863649823474573699 2010431795474735211860549)
                ·
                  refine ⟨376955961651512852223853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010431795474735211860549 376955961651512852223853)
                  ·
                    rfl

theorem cell20_825884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_825884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825884 prefixEnd_825884 := by exact prefixLift 825884
  have htrace : WordTrace (prefixWord ++ tailWord_825884) baseStart_825884 baseEnd_825884 := by
    simpa [prefixWord, tailWord_825884, baseEnd_825884] using wordTrace_append hprefix tailTrace_825884
  have hstable : (prefixWord ++ tailWord_825884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825884).length < 2 ^ (prefixWord ++ tailWord_825884).sum := by decide
  have hdescent : baseEnd_825884 < baseStart_825884 := by decide
  rcases family_descends (prefixWord ++ tailWord_825884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825960 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_825960 : Nat := 118140960795 + 825960 * 2 ^ 59
def prefixEnd_825960 : Nat := 4983230072969 + 3 ^ 40 * 825960 * 2
def baseEnd_825960 : Nat := 376990650122394365690209

theorem tailTrace_825960 : CollatzResearch.WordTrace tailWord_825960 prefixEnd_825960 376990650122394365690209 := by
  unfold tailWord_825960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062618043847728791265667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20083490725130305055020889 15062618043847728791265667)
  ·
    refine ⟨22593927065771593186898501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15062618043847728791265667 22593927065771593186898501)
    ·
      refine ⟨4236361324832173722543469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22593927065771593186898501 4236361324832173722543469)
      ·
        refine ⟨1588635496812065145953801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4236361324832173722543469 1588635496812065145953801)
        ·
          refine ⟨1191476622609048859465351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1588635496812065145953801 1191476622609048859465351)
          ·
            refine ⟨1787214933913573289198027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191476622609048859465351 1787214933913573289198027)
            ·
              refine ⟨2680822400870359933797041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787214933913573289198027 2680822400870359933797041)
              ·
                refine ⟨2010616800652769950347781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680822400870359933797041 2010616800652769950347781)
                ·
                  refine ⟨376990650122394365690209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010616800652769950347781 376990650122394365690209)
                  ·
                    rfl

theorem cell20_825960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_825960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825960 prefixEnd_825960 := by exact prefixLift 825960
  have htrace : WordTrace (prefixWord ++ tailWord_825960) baseStart_825960 baseEnd_825960 := by
    simpa [prefixWord, tailWord_825960, baseEnd_825960] using wordTrace_append hprefix tailTrace_825960
  have hstable : (prefixWord ++ tailWord_825960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825960).length < 2 ^ (prefixWord ++ tailWord_825960).sum := by decide
  have hdescent : baseEnd_825960 < baseStart_825960 := by decide
  rcases family_descends (prefixWord ++ tailWord_825960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825964 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_825964 : Nat := 118140960795 + 825964 * 2 ^ 59
def prefixEnd_825964 : Nat := 4983230072969 + 3 ^ 40 * 825964 * 2
def baseEnd_825964 : Nat := 376992475831388129556859

theorem tailTrace_825964 : CollatzResearch.WordTrace tailWord_825964 prefixEnd_825964 376992475831388129556859 := by
  unfold tailWord_825964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062690989840483132838473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20083587986453977510451297 15062690989840483132838473)
  ·
    refine ⟨11297018242380362349628855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15062690989840483132838473 11297018242380362349628855)
    ·
      refine ⟨16945527363570543524443283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11297018242380362349628855 16945527363570543524443283)
      ·
        refine ⟨25418291045355815286664925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16945527363570543524443283 25418291045355815286664925)
        ·
          refine ⟨9531859142008430732499347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25418291045355815286664925 9531859142008430732499347)
          ·
            refine ⟨14297788713012646098749021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531859142008430732499347 14297788713012646098749021)
            ·
              refine ⟨5361670767379742287030883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14297788713012646098749021 5361670767379742287030883)
              ·
                refine ⟨8042506151069613430546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361670767379742287030883 8042506151069613430546325)
                ·
                  refine ⟨376992475831388129556859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8042506151069613430546325 376992475831388129556859)
                  ·
                    rfl

theorem cell20_825964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_825964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825964 prefixEnd_825964 := by exact prefixLift 825964
  have htrace : WordTrace (prefixWord ++ tailWord_825964) baseStart_825964 baseEnd_825964 := by
    simpa [prefixWord, tailWord_825964, baseEnd_825964] using wordTrace_append hprefix tailTrace_825964
  have hstable : (prefixWord ++ tailWord_825964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825964).length < 2 ^ (prefixWord ++ tailWord_825964).sum := by decide
  have hdescent : baseEnd_825964 < baseStart_825964 := by decide
  rcases family_descends (prefixWord ++ tailWord_825964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825988 : List Nat := [2, 3, 2, 1, 3, 2, 7]
def baseStart_825988 : Nat := 118140960795 + 825988 * 2 ^ 59
def prefixEnd_825988 : Nat := 4983230072969 + 3 ^ 40 * 825988 * 2
def baseEnd_825988 : Nat := 41889270009483412528529

theorem tailTrace_825988 : CollatzResearch.WordTrace tailWord_825988 prefixEnd_825988 41889270009483412528529 := by
  unfold tailWord_825988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063128665797009182275309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20084171554396012243033745 15063128665797009182275309)
  ·
    refine ⟨5648673249673878443353241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15063128665797009182275309 5648673249673878443353241)
    ·
      refine ⟨4236504937255408832514931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5648673249673878443353241 4236504937255408832514931)
      ·
        refine ⟨6354757405883113248772397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236504937255408832514931 6354757405883113248772397)
        ·
          refine ⟨2383034027206167468289649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6354757405883113248772397 2383034027206167468289649)
          ·
            refine ⟨1787275520404625601217237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383034027206167468289649 1787275520404625601217237)
            ·
              refine ⟨41889270009483412528529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1787275520404625601217237 41889270009483412528529)
              ·
                rfl

theorem cell20_825988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_825988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825988 prefixEnd_825988 := by exact prefixLift 825988
  have htrace : WordTrace (prefixWord ++ tailWord_825988) baseStart_825988 baseEnd_825988 := by
    simpa [prefixWord, tailWord_825988, baseEnd_825988] using wordTrace_append hprefix tailTrace_825988
  have hstable : (prefixWord ++ tailWord_825988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825988).length < 2 ^ (prefixWord ++ tailWord_825988).sum := by decide
  have hdescent : baseEnd_825988 < baseStart_825988 := by decide
  rcases family_descends (prefixWord ++ tailWord_825988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825995 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_825995 : Nat := 118140960795 + 825995 * 2 ^ 59
def prefixEnd_825995 : Nat := 4983230072969 + 3 ^ 40 * 825995 * 2
def baseEnd_825995 : Nat := 377006625076089799523399

theorem tailTrace_825995 : CollatzResearch.WordTrace tailWord_825995 prefixEnd_825995 377006625076089799523399 := by
  unfold tailWord_825995
  simp only [CollatzResearch.WordTrace]
  refine ⟨30126512642568658560055439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20084341761712439040036959 30126512642568658560055439)
  ·
    refine ⟨45189768963852987840083159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30126512642568658560055439 45189768963852987840083159)
    ·
      refine ⟨67784653445779481760124739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45189768963852987840083159 67784653445779481760124739)
      ·
        refine ⟨101676980168669222640187109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67784653445779481760124739 101676980168669222640187109)
        ·
          refine ⟨19064433781625479245035083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101676980168669222640187109 19064433781625479245035083)
          ·
            refine ⟨28596650672438218867552625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064433781625479245035083 28596650672438218867552625)
            ·
              refine ⟨21447488004328664150664469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28596650672438218867552625 21447488004328664150664469)
              ·
                refine ⟨1005351000202906132062397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21447488004328664150664469 1005351000202906132062397)
                ·
                  refine ⟨377006625076089799523399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005351000202906132062397 377006625076089799523399)
                  ·
                    rfl

theorem cell20_825995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_825995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825995 prefixEnd_825995 := by exact prefixLift 825995
  have htrace : WordTrace (prefixWord ++ tailWord_825995) baseStart_825995 baseEnd_825995 := by
    simpa [prefixWord, tailWord_825995, baseEnd_825995] using wordTrace_append hprefix tailTrace_825995
  have hstable : (prefixWord ++ tailWord_825995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825995).length < 2 ^ (prefixWord ++ tailWord_825995).sum := by decide
  have hdescent : baseEnd_825995 < baseStart_825995 := by decide
  rcases family_descends (prefixWord ++ tailWord_825995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825998 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_825998 : Nat := 118140960795 + 825998 * 2 ^ 59
def prefixEnd_825998 : Nat := 4983230072969 + 3 ^ 40 * 825998 * 2
def baseEnd_825998 : Nat := 377007994357835122423387

theorem tailTrace_825998 : CollatzResearch.WordTrace tailWord_825998 prefixEnd_825998 377007994357835122423387 := by
  unfold tailWord_825998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765827757694723759051831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20084414707705193381609765 3765827757694723759051831)
  ·
    refine ⟨5648741636542085638577747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765827757694723759051831 5648741636542085638577747)
    ·
      refine ⟨8473112454813128457866621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648741636542085638577747 8473112454813128457866621)
      ·
        refine ⟨3177417170554923171699983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8473112454813128457866621 3177417170554923171699983)
        ·
          refine ⟨4766125755832384757549975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177417170554923171699983 4766125755832384757549975)
          ·
            refine ⟨7149188633748577136324963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766125755832384757549975 7149188633748577136324963)
            ·
              refine ⟨10723782950622865704487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149188633748577136324963 10723782950622865704487445)
              ·
                refine ⟨502677325810446829897849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10723782950622865704487445 502677325810446829897849)
                ·
                  refine ⟨377007994357835122423387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502677325810446829897849 377007994357835122423387)
                  ·
                    rfl

theorem cell20_825998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_825998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825998 prefixEnd_825998 := by exact prefixLift 825998
  have htrace : WordTrace (prefixWord ++ tailWord_825998) baseStart_825998 baseEnd_825998 := by
    simpa [prefixWord, tailWord_825998, baseEnd_825998] using wordTrace_append hprefix tailTrace_825998
  have hstable : (prefixWord ++ tailWord_825998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825998).length < 2 ^ (prefixWord ++ tailWord_825998).sum := by decide
  have hdescent : baseEnd_825998 < baseStart_825998 := by decide
  rcases family_descends (prefixWord ++ tailWord_825998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826009 : List Nat := [1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_826009 : Nat := 118140960795 + 826009 * 2 ^ 59
def prefixEnd_826009 : Nat := 4983230072969 + 3 ^ 40 * 826009 * 2
def baseEnd_826009 : Nat := 125671005019189324352225

theorem tailTrace_826009 : CollatzResearch.WordTrace tailWord_826009 prefixEnd_826009 125671005019189324352225 := by
  unfold tailWord_826009
  simp only [CollatzResearch.WordTrace]
  refine ⟨30127023264517938951065081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20084682176345292634043387 30127023264517938951065081)
  ·
    refine ⟨22595267448388454213298811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30127023264517938951065081 22595267448388454213298811)
    ·
      refine ⟨33892901172582681319948217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22595267448388454213298811 33892901172582681319948217)
      ·
        refine ⟨25419675879437010989961163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33892901172582681319948217 25419675879437010989961163)
        ·
          refine ⟨38129513819155516484941745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25419675879437010989961163 38129513819155516484941745)
          ·
            refine ⟨28597135364366637363706309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38129513819155516484941745 28597135364366637363706309)
            ·
              refine ⟨5361962880818744505694933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28597135364366637363706309 5361962880818744505694933)
              ·
                refine ⟨125671005019189324352225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5361962880818744505694933 125671005019189324352225)
                ·
                  rfl

theorem cell20_826009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_826009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826009 prefixEnd_826009 := by exact prefixLift 826009
  have htrace : WordTrace (prefixWord ++ tailWord_826009) baseStart_826009 baseEnd_826009 := by
    simpa [prefixWord, tailWord_826009, baseEnd_826009] using wordTrace_append hprefix tailTrace_826009
  have hstable : (prefixWord ++ tailWord_826009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826009).length < 2 ^ (prefixWord ++ tailWord_826009).sum := by decide
  have hdescent : baseEnd_826009 < baseStart_826009 := by decide
  rcases family_descends (prefixWord ++ tailWord_826009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826047 : List Nat := [1, 1, 2, 2, 2, 4, 8]
def baseStart_826047 : Nat := 118140960795 + 826047 * 2 ^ 59
def prefixEnd_826047 : Nat := 4983230072969 + 3 ^ 40 * 826047 * 2
def baseEnd_826047 : Nat := 41892262143667636643317

theorem tailTrace_826047 : CollatzResearch.WordTrace tailWord_826047 prefixEnd_826047 41892262143667636643317 := by
  unfold tailWord_826047
  simp only [CollatzResearch.WordTrace]
  refine ⟨30128409238380271440948395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20085606158920180960632263 30128409238380271440948395)
  ·
    refine ⟨45192613857570407161422593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30128409238380271440948395 45192613857570407161422593)
    ·
      refine ⟨33894460393177805371066945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45192613857570407161422593 33894460393177805371066945)
      ·
        refine ⟨25420845294883354028300209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33894460393177805371066945 25420845294883354028300209)
        ·
          refine ⟨19065633971162515521225157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25420845294883354028300209 19065633971162515521225157)
          ·
            refine ⟨3574806369592971660229717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19065633971162515521225157 3574806369592971660229717)
            ·
              refine ⟨41892262143667636643317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3574806369592971660229717 41892262143667636643317)
              ·
                rfl

theorem cell20_826047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_826047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826047 prefixEnd_826047 := by exact prefixLift 826047
  have htrace : WordTrace (prefixWord ++ tailWord_826047) baseStart_826047 baseEnd_826047 := by
    simpa [prefixWord, tailWord_826047, baseEnd_826047] using wordTrace_append hprefix tailTrace_826047
  have hstable : (prefixWord ++ tailWord_826047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826047).length < 2 ^ (prefixWord ++ tailWord_826047).sum := by decide
  have hdescent : baseEnd_826047 < baseStart_826047 := by decide
  rcases family_descends (prefixWord ++ tailWord_826047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826049 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 2]
def baseStart_826049 : Nat := 118140960795 + 826049 * 2 ^ 59
def prefixEnd_826049 : Nat := 4983230072969 + 3 ^ 40 * 826049 * 2
def baseEnd_826049 : Nat := 377031272147505611723179

theorem tailTrace_826049 : CollatzResearch.WordTrace tailWord_826049 prefixEnd_826049 377031272147505611723179 := by
  unfold tailWord_826049
  simp only [CollatzResearch.WordTrace]
  refine ⟨30128482184373025782521201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20085654789582017188347467 30128482184373025782521201)
  ·
    refine ⟨22596361638279769336890901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30128482184373025782521201 22596361638279769336890901)
    ·
      refine ⟨1059204451794364187666761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22596361638279769336890901 1059204451794364187666761)
      ·
        refine ⟨794403338845773140750071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059204451794364187666761 794403338845773140750071)
        ·
          refine ⟨1191605008268659711125107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794403338845773140750071 1191605008268659711125107)
          ·
            refine ⟨1787407512402989566687661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191605008268659711125107 1787407512402989566687661)
            ·
              refine ⟨670277817151121087507873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787407512402989566687661 670277817151121087507873)
              ·
                refine ⟨502708362863340815630905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670277817151121087507873 502708362863340815630905)
                ·
                  refine ⟨377031272147505611723179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502708362863340815630905 377031272147505611723179)
                  ·
                    rfl

theorem cell20_826049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_826049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826049 prefixEnd_826049 := by exact prefixLift 826049
  have htrace : WordTrace (prefixWord ++ tailWord_826049) baseStart_826049 baseEnd_826049 := by
    simpa [prefixWord, tailWord_826049, baseEnd_826049] using wordTrace_append hprefix tailTrace_826049
  have hstable : (prefixWord ++ tailWord_826049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826049).length < 2 ^ (prefixWord ++ tailWord_826049).sum := by decide
  have hdescent : baseEnd_826049 < baseStart_826049 := by decide
  rcases family_descends (prefixWord ++ tailWord_826049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826101 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 3]
def baseStart_826101 : Nat := 118140960795 + 826101 * 2 ^ 59
def prefixEnd_826101 : Nat := 4983230072969 + 3 ^ 40 * 826101 * 2
def baseEnd_826101 : Nat := 377055006364424541989633

theorem tailTrace_826101 : CollatzResearch.WordTrace tailWord_826101 prefixEnd_826101 377055006364424541989633 := by
  unfold tailWord_826101
  simp only [CollatzResearch.WordTrace]
  refine ⟨30130378780184638663414157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20086919186789759108942771 30130378780184638663414157)
  ·
    refine ⟨11298892042569239498780309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30130378780184638663414157 11298892042569239498780309)
    ·
      refine ⟨529635564495433101505327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11298892042569239498780309 529635564495433101505327)
      ·
        refine ⟨794453346743149652257991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529635564495433101505327 794453346743149652257991)
        ·
          refine ⟨1191680020114724478386987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794453346743149652257991 1191680020114724478386987)
          ·
            refine ⟨1787520030172086717580481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191680020114724478386987 1787520030172086717580481)
            ·
              refine ⟨1340640022629065038185361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787520030172086717580481 1340640022629065038185361)
              ·
                refine ⟨1005480016971798778639021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340640022629065038185361 1005480016971798778639021)
                ·
                  refine ⟨377055006364424541989633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005480016971798778639021 377055006364424541989633)
                  ·
                    rfl

theorem cell20_826101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_826101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826101 prefixEnd_826101 := by exact prefixLift 826101
  have htrace : WordTrace (prefixWord ++ tailWord_826101) baseStart_826101 baseEnd_826101 := by
    simpa [prefixWord, tailWord_826101, baseEnd_826101] using wordTrace_append hprefix tailTrace_826101
  have hstable : (prefixWord ++ tailWord_826101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826101).length < 2 ^ (prefixWord ++ tailWord_826101).sum := by decide
  have hdescent : baseEnd_826101 < baseStart_826101 := by decide
  rcases family_descends (prefixWord ++ tailWord_826101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826119 : List Nat := [1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_826119 : Nat := 118140960795 + 826119 * 2 ^ 59
def prefixEnd_826119 : Nat := 4983230072969 + 3 ^ 40 * 826119 * 2
def baseEnd_826119 : Nat := 125687740684965493129853

theorem tailTrace_826119 : CollatzResearch.WordTrace tailWord_826119 prefixEnd_826119 125687740684965493129853 := by
  unfold tailWord_826119
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131035294119427737569411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20087356862746285158379607 30131035294119427737569411)
  ·
    refine ⟨45196552941179141606354117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30131035294119427737569411 45196552941179141606354117)
    ·
      refine ⟨8474353676471089051191397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45196552941179141606354117 8474353676471089051191397)
      ·
        refine ⟨1588941314338329197098387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8474353676471089051191397 1588941314338329197098387)
        ·
          refine ⟨2383411971507493795647581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588941314338329197098387 2383411971507493795647581)
          ·
            refine ⟨893779489315310173367843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2383411971507493795647581 893779489315310173367843)
            ·
              refine ⟨1340669233972965260051765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893779489315310173367843 1340669233972965260051765)
              ·
                refine ⟨125687740684965493129853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1340669233972965260051765 125687740684965493129853)
                ·
                  rfl

theorem cell20_826119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_826119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826119 prefixEnd_826119 := by exact prefixLift 826119
  have htrace : WordTrace (prefixWord ++ tailWord_826119) baseStart_826119 baseEnd_826119 := by
    simpa [prefixWord, tailWord_826119, baseEnd_826119] using wordTrace_append hprefix tailTrace_826119
  have hstable : (prefixWord ++ tailWord_826119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826119).length < 2 ^ (prefixWord ++ tailWord_826119).sum := by decide
  have hdescent : baseEnd_826119 < baseStart_826119 := by decide
  rcases family_descends (prefixWord ++ tailWord_826119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826161 : List Nat := [1, 2, 2, 3, 2, 1, 9]
def baseStart_826161 : Nat := 118140960795 + 826161 * 2 ^ 59
def prefixEnd_826161 : Nat := 4983230072969 + 3 ^ 40 * 826161 * 2
def baseEnd_826161 : Nat := 41898043555481222221043

theorem tailTrace_826161 : CollatzResearch.WordTrace tailWord_826161 prefixEnd_826161 41898043555481222221043 := by
  unfold tailWord_826161
  simp only [CollatzResearch.WordTrace]
  refine ⟨30132567159967268910598337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20088378106644845940398891 30132567159967268910598337)
  ·
    refine ⟨22599425369975451682948753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30132567159967268910598337 22599425369975451682948753)
    ·
      refine ⟨16949569027481588762211565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22599425369975451682948753 16949569027481588762211565)
      ·
        refine ⟨6356088385305595785829337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16949569027481588762211565 6356088385305595785829337)
        ·
          refine ⟨4767066288979196839372003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6356088385305595785829337 4767066288979196839372003)
          ·
            refine ⟨7150599433468795259058005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767066288979196839372003 7150599433468795259058005)
            ·
              refine ⟨41898043555481222221043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7150599433468795259058005 41898043555481222221043)
              ·
                rfl

theorem cell20_826161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_826161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826161 prefixEnd_826161 := by exact prefixLift 826161
  have htrace : WordTrace (prefixWord ++ tailWord_826161) baseStart_826161 baseEnd_826161 := by
    simpa [prefixWord, tailWord_826161, baseEnd_826161] using wordTrace_append hprefix tailTrace_826161
  have hstable : (prefixWord ++ tailWord_826161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826161).length < 2 ^ (prefixWord ++ tailWord_826161).sum := by decide
  have hdescent : baseEnd_826161 < baseStart_826161 := by decide
  rcases family_descends (prefixWord ++ tailWord_826161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826192 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_826192 : Nat := 118140960795 + 826192 * 2 ^ 59
def prefixEnd_826192 : Nat := 4983230072969 + 3 ^ 40 * 826192 * 2
def baseEnd_826192 : Nat := 377096541244032669955927

theorem tailTrace_826192 : CollatzResearch.WordTrace tailWord_826192 prefixEnd_826192 377096541244032669955927 := by
  unfold tailWord_826192
  simp only [CollatzResearch.WordTrace]
  refine ⟨15066848911427480602488415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20089131881903307469984553 15066848911427480602488415)
  ·
    refine ⟨22600273367141220903732623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15066848911427480602488415 22600273367141220903732623)
    ·
      refine ⟨33900410050711831355598935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22600273367141220903732623 33900410050711831355598935)
      ·
        refine ⟨50850615076067747033398403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33900410050711831355598935 50850615076067747033398403)
        ·
          refine ⟨76275922614101620550097605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50850615076067747033398403 76275922614101620550097605)
          ·
            refine ⟨14301735490144053853143301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76275922614101620550097605 14301735490144053853143301)
            ·
              refine ⟨2681575404402010097464369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14301735490144053853143301 2681575404402010097464369)
              ·
                refine ⟨2011181553301507573098277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681575404402010097464369 2011181553301507573098277)
                ·
                  refine ⟨377096541244032669955927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011181553301507573098277 377096541244032669955927)
                  ·
                    rfl

theorem cell20_826192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_826192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826192 prefixEnd_826192 := by exact prefixLift 826192
  have htrace : WordTrace (prefixWord ++ tailWord_826192) baseStart_826192 baseEnd_826192 := by
    simpa [prefixWord, tailWord_826192, baseEnd_826192] using wordTrace_append hprefix tailTrace_826192
  have hstable : (prefixWord ++ tailWord_826192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826192).length < 2 ^ (prefixWord ++ tailWord_826192).sum := by decide
  have hdescent : baseEnd_826192 < baseStart_826192 := by decide
  rcases family_descends (prefixWord ++ tailWord_826192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826209 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 2]
def baseStart_826209 : Nat := 118140960795 + 826209 * 2 ^ 59
def prefixEnd_826209 : Nat := 4983230072969 + 3 ^ 40 * 826209 * 2
def baseEnd_826209 : Nat := 377104300507256166389191

theorem tailTrace_826209 : CollatzResearch.WordTrace tailWord_826209 prefixEnd_826209 377104300507256166389191 := by
  unfold tailWord_826209
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134317863793373108345681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20089545242528915405563787 30134317863793373108345681)
  ·
    refine ⟨22600738397845029831259261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30134317863793373108345681 22600738397845029831259261)
    ·
      refine ⟨8475276899191886186722223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22600738397845029831259261 8475276899191886186722223)
      ·
        refine ⟨12712915348787829280083335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475276899191886186722223 12712915348787829280083335)
        ·
          refine ⟨19069373023181743920125003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12712915348787829280083335 19069373023181743920125003)
          ·
            refine ⟨28604059534772615880187505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19069373023181743920125003 28604059534772615880187505)
            ·
              refine ⟨21453044651079461910140629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28604059534772615880187505 21453044651079461910140629)
              ·
                refine ⟨502805734009674888518921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21453044651079461910140629 502805734009674888518921)
                ·
                  refine ⟨377104300507256166389191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502805734009674888518921 377104300507256166389191)
                  ·
                    rfl

theorem cell20_826209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_826209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826209 prefixEnd_826209 := by exact prefixLift 826209
  have htrace : WordTrace (prefixWord ++ tailWord_826209) baseStart_826209 baseEnd_826209 := by
    simpa [prefixWord, tailWord_826209, baseEnd_826209] using wordTrace_append hprefix tailTrace_826209
  have hstable : (prefixWord ++ tailWord_826209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826209).length < 2 ^ (prefixWord ++ tailWord_826209).sum := by decide
  have hdescent : baseEnd_826209 < baseStart_826209 := by decide
  rcases family_descends (prefixWord ++ tailWord_826209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826216 : List Nat := [2, 1, 4, 2, 1, 4, 6]
def baseStart_826216 : Nat := 118140960795 + 826216 * 2 ^ 59
def prefixEnd_826216 : Nat := 4983230072969 + 3 ^ 40 * 826216 * 2
def baseEnd_826216 : Nat := 41900832833110583683981

theorem tailTrace_826216 : CollatzResearch.WordTrace tailWord_826216 prefixEnd_826216 41900832833110583683981 := by
  unfold tailWord_826216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067286587384006651925251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20089715449845342202567001 15067286587384006651925251)
  ·
    refine ⟨22600929881076009977887877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067286587384006651925251 22600929881076009977887877)
    ·
      refine ⟨4237674352701751870853977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22600929881076009977887877 4237674352701751870853977)
      ·
        refine ⟨3178255764526313903140483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4237674352701751870853977 3178255764526313903140483)
        ·
          refine ⟨4767383646789470854710725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178255764526313903140483 4767383646789470854710725)
          ·
            refine ⟨893884433773025785258261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4767383646789470854710725 893884433773025785258261)
            ·
              refine ⟨41900832833110583683981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 893884433773025785258261 41900832833110583683981)
              ·
                rfl

theorem cell20_826216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_826216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826216 prefixEnd_826216 := by exact prefixLift 826216
  have htrace : WordTrace (prefixWord ++ tailWord_826216) baseStart_826216 baseEnd_826216 := by
    simpa [prefixWord, tailWord_826216, baseEnd_826216] using wordTrace_append hprefix tailTrace_826216
  have hstable : (prefixWord ++ tailWord_826216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826216).length < 2 ^ (prefixWord ++ tailWord_826216).sum := by decide
  have hdescent : baseEnd_826216 < baseStart_826216 := by decide
  rcases family_descends (prefixWord ++ tailWord_826216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826222 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_826222 : Nat := 118140960795 + 826222 * 2 ^ 59
def prefixEnd_826222 : Nat := 4983230072969 + 3 ^ 40 * 826222 * 2
def baseEnd_826222 : Nat := 377110234061485898955805

theorem tailTrace_826222 : CollatzResearch.WordTrace tailWord_826222 prefixEnd_826222 377110234061485898955805 := by
  unfold tailWord_826222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766849001593284541071115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20089861341830850885712613 3766849001593284541071115)
  ·
    refine ⟨5650273502389926811606673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766849001593284541071115 5650273502389926811606673)
    ·
      refine ⟨4237705126792445108705005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5650273502389926811606673 4237705126792445108705005)
      ·
        refine ⟨1589139422547166915764377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4237705126792445108705005 1589139422547166915764377)
        ·
          refine ⟨1191854566910375186823283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589139422547166915764377 1191854566910375186823283)
          ·
            refine ⟨1787781850365562780234925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191854566910375186823283 1787781850365562780234925)
            ·
              refine ⟨670418193887086042588097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787781850365562780234925 670418193887086042588097)
              ·
                refine ⟨502813645415314531941073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670418193887086042588097 502813645415314531941073)
                ·
                  refine ⟨377110234061485898955805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502813645415314531941073 377110234061485898955805)
                  ·
                    rfl

theorem cell20_826222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_826222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826222 prefixEnd_826222 := by exact prefixLift 826222
  have htrace : WordTrace (prefixWord ++ tailWord_826222) baseStart_826222 baseEnd_826222 := by
    simpa [prefixWord, tailWord_826222, baseEnd_826222] using wordTrace_append hprefix tailTrace_826222
  have hstable : (prefixWord ++ tailWord_826222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826222).length < 2 ^ (prefixWord ++ tailWord_826222).sum := by decide
  have hdescent : baseEnd_826222 < baseStart_826222 := by decide
  rcases family_descends (prefixWord ++ tailWord_826222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826237 : List Nat := [1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_826237 : Nat := 118140960795 + 826237 * 2 ^ 59
def prefixEnd_826237 : Nat := 4983230072969 + 3 ^ 40 * 826237 * 2
def baseEnd_826237 : Nat := 125705693490070837818581

theorem tailTrace_826237 : CollatzResearch.WordTrace tailWord_826237 prefixEnd_826237 125705693490070837818581 := by
  unfold tailWord_826237
  simp only [CollatzResearch.WordTrace]
  refine ⟨30135339107691933890364965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20090226071794622593576643 30135339107691933890364965)
  ·
    refine ⟨5650376082692237604443431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30135339107691933890364965 5650376082692237604443431)
    ·
      refine ⟨8475564124038356406665147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650376082692237604443431 8475564124038356406665147)
      ·
        refine ⟨12713346186057534609997721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475564124038356406665147 12713346186057534609997721)
        ·
          refine ⟨9535009639543150957498291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12713346186057534609997721 9535009639543150957498291)
          ·
            refine ⟨14302514459314726436247437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535009639543150957498291 14302514459314726436247437)
            ·
              refine ⟨5363442922243022413592789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14302514459314726436247437 5363442922243022413592789)
              ·
                refine ⟨125705693490070837818581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5363442922243022413592789 125705693490070837818581)
                ·
                  rfl

theorem cell20_826237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_826237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826237 prefixEnd_826237 := by exact prefixLift 826237
  have htrace : WordTrace (prefixWord ++ tailWord_826237) baseStart_826237 baseEnd_826237 := by
    simpa [prefixWord, tailWord_826237, baseEnd_826237] using wordTrace_append hprefix tailTrace_826237
  have hstable : (prefixWord ++ tailWord_826237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826237).length < 2 ^ (prefixWord ++ tailWord_826237).sum := by decide
  have hdescent : baseEnd_826237 < baseStart_826237 := by decide
  rcases family_descends (prefixWord ++ tailWord_826237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826320 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_826320 : Nat := 118140960795 + 826320 * 2 ^ 59
def prefixEnd_826320 : Nat := 4983230072969 + 3 ^ 40 * 826320 * 2
def baseEnd_826320 : Nat := 377154963931833113688737

theorem tailTrace_826320 : CollatzResearch.WordTrace tailWord_826320 prefixEnd_826320 377154963931833113688737 := by
  unfold tailWord_826320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15069183183195619532818207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20092244244260826043757609 15069183183195619532818207)
  ·
    refine ⟨22603774774793429299227311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15069183183195619532818207 22603774774793429299227311)
    ·
      refine ⟨33905662162190143948840967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22603774774793429299227311 33905662162190143948840967)
      ·
        refine ⟨50858493243285215923261451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33905662162190143948840967 50858493243285215923261451)
        ·
          refine ⟨76287739864927823884892177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50858493243285215923261451 76287739864927823884892177)
          ·
            refine ⟨57215804898695867913669133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76287739864927823884892177 57215804898695867913669133)
            ·
              refine ⟨21455926837010950467625925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57215804898695867913669133 21455926837010950467625925)
              ·
                refine ⟨4022986281939553212679861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21455926837010950467625925 4022986281939553212679861)
                ·
                  refine ⟨377154963931833113688737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4022986281939553212679861 377154963931833113688737)
                  ·
                    rfl

theorem cell20_826320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_826320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826320 prefixEnd_826320 := by exact prefixLift 826320
  have htrace : WordTrace (prefixWord ++ tailWord_826320) baseStart_826320 baseEnd_826320 := by
    simpa [prefixWord, tailWord_826320, baseEnd_826320] using wordTrace_append hprefix tailTrace_826320
  have hstable : (prefixWord ++ tailWord_826320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826320).length < 2 ^ (prefixWord ++ tailWord_826320).sum := by decide
  have hdescent : baseEnd_826320 < baseStart_826320 := by decide
  rcases family_descends (prefixWord ++ tailWord_826320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826333 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_826333 : Nat := 118140960795 + 826333 * 2 ^ 59
def prefixEnd_826333 : Nat := 4983230072969 + 3 ^ 40 * 826333 * 2
def baseEnd_826333 : Nat := 377160897486062846255351

theorem tailTrace_826333 : CollatzResearch.WordTrace tailWord_826333 prefixEnd_826333 377160897486062846255351 := by
  unfold tailWord_826333
  simp only [CollatzResearch.WordTrace]
  refine ⟨30138840515344142285859653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20092560343562761523906435 30138840515344142285859653)
  ·
    refine ⟨5651032596627026678598685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30138840515344142285859653 5651032596627026678598685)
    ·
      refine ⟨2119137223735135004474507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5651032596627026678598685 2119137223735135004474507)
      ·
        refine ⟨3178705835602702506711761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119137223735135004474507 3178705835602702506711761)
        ·
          refine ⟨2384029376702026880033821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3178705835602702506711761 2384029376702026880033821)
          ·
            refine ⟨894011016263260080012683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2384029376702026880033821 894011016263260080012683)
            ·
              refine ⟨1341016524394890120019025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894011016263260080012683 1341016524394890120019025)
              ·
                refine ⟨1005762393296167590014269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341016524394890120019025 1005762393296167590014269)
                ·
                  refine ⟨377160897486062846255351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005762393296167590014269 377160897486062846255351)
                  ·
                    rfl

theorem cell20_826333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_826333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826333 prefixEnd_826333 := by exact prefixLift 826333
  have htrace : WordTrace (prefixWord ++ tailWord_826333) baseStart_826333 baseEnd_826333 := by
    simpa [prefixWord, tailWord_826333, baseEnd_826333] using wordTrace_append hprefix tailTrace_826333
  have hstable : (prefixWord ++ tailWord_826333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826333).length < 2 ^ (prefixWord ++ tailWord_826333).sum := by decide
  have hdescent : baseEnd_826333 < baseStart_826333 := by decide
  rcases family_descends (prefixWord ++ tailWord_826333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826344 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_826344 : Nat := 118140960795 + 826344 * 2 ^ 59
def prefixEnd_826344 : Nat := 4983230072969 + 3 ^ 40 * 826344 * 2
def baseEnd_826344 : Nat := 377165918185795696888639

theorem tailTrace_826344 : CollatzResearch.WordTrace tailWord_826344 prefixEnd_826344 377165918185795696888639 := by
  unfold tailWord_826344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15069620859152145582255043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20092827812202860776340057 15069620859152145582255043)
  ·
    refine ⟨22604431288728218373382565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15069620859152145582255043 22604431288728218373382565)
    ·
      refine ⟨4238330866636540945009231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22604431288728218373382565 4238330866636540945009231)
      ·
        refine ⟨6357496299954811417513847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238330866636540945009231 6357496299954811417513847)
        ·
          refine ⟨9536244449932217126270771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357496299954811417513847 9536244449932217126270771)
          ·
            refine ⟨14304366674898325689406157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9536244449932217126270771 14304366674898325689406157)
            ·
              refine ⟨5364137503086872133527309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14304366674898325689406157 5364137503086872133527309)
              ·
                refine ⟨2011551563657577050072741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5364137503086872133527309 2011551563657577050072741)
                ·
                  refine ⟨377165918185795696888639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011551563657577050072741 377165918185795696888639)
                  ·
                    rfl

theorem cell20_826344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_826344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826344 prefixEnd_826344 := by exact prefixLift 826344
  have htrace : WordTrace (prefixWord ++ tailWord_826344) baseStart_826344 baseEnd_826344 := by
    simpa [prefixWord, tailWord_826344, baseEnd_826344] using wordTrace_append hprefix tailTrace_826344
  have hstable : (prefixWord ++ tailWord_826344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826344).length < 2 ^ (prefixWord ++ tailWord_826344).sum := by decide
  have hdescent : baseEnd_826344 < baseStart_826344 := by decide
  rcases family_descends (prefixWord ++ tailWord_826344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826378 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_826378 : Nat := 118140960795 + 826378 * 2 ^ 59
def prefixEnd_826378 : Nat := 4983230072969 + 3 ^ 40 * 826378 * 2
def baseEnd_826378 : Nat := 377181436712242689755167

theorem tailTrace_826378 : CollatzResearch.WordTrace tailWord_826378 prefixEnd_826378 377181436712242689755167 := by
  unfold tailWord_826378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535120450045278742811947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20093654533454076647498525 7535120450045278742811947)
  ·
    refine ⟨11302680675067918114217921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535120450045278742811947 11302680675067918114217921)
    ·
      refine ⟨8477010506300938585663441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11302680675067918114217921 8477010506300938585663441)
      ·
        refine ⟨6357757879725703939247581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8477010506300938585663441 6357757879725703939247581)
        ·
          refine ⟨2384159204897138977217843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6357757879725703939247581 2384159204897138977217843)
          ·
            refine ⟨3576238807345708465826765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384159204897138977217843 3576238807345708465826765)
            ·
              refine ⟨1341089552754640674685037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3576238807345708465826765 1341089552754640674685037)
              ·
                refine ⟨502908582282990253006889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341089552754640674685037 502908582282990253006889)
                ·
                  refine ⟨377181436712242689755167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502908582282990253006889 377181436712242689755167)
                  ·
                    rfl

theorem cell20_826378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_826378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826378 prefixEnd_826378 := by exact prefixLift 826378
  have htrace : WordTrace (prefixWord ++ tailWord_826378) baseStart_826378 baseEnd_826378 := by
    simpa [prefixWord, tailWord_826378, baseEnd_826378] using wordTrace_append hprefix tailTrace_826378
  have hstable : (prefixWord ++ tailWord_826378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826378).length < 2 ^ (prefixWord ++ tailWord_826378).sum := by decide
  have hdescent : baseEnd_826378 < baseStart_826378 := by decide
  rcases family_descends (prefixWord ++ tailWord_826378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826389 : List Nat := [1, 3, 2, 1, 4, 1, 8]
def baseStart_826389 : Nat := 118140960795 + 826389 * 2 ^ 59
def prefixEnd_826389 : Nat := 4983230072969 + 3 ^ 40 * 826389 * 2
def baseEnd_826389 : Nat := 41909606379108393376495

theorem tailTrace_826389 : CollatzResearch.WordTrace tailWord_826389 prefixEnd_826389 41909606379108393376495 := by
  unfold tailWord_826389
  simp only [CollatzResearch.WordTrace]
  refine ⟨30140883003141263849898221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20093922002094175899932147 30140883003141263849898221)
  ·
    refine ⟨11302831126177973943711833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30140883003141263849898221 11302831126177973943711833)
    ·
      refine ⟨8477123344633480457783875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11302831126177973943711833 8477123344633480457783875)
      ·
        refine ⟨12715685016950220686675813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477123344633480457783875 12715685016950220686675813)
        ·
          refine ⟨2384190940678166378751715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12715685016950220686675813 2384190940678166378751715)
          ·
            refine ⟨3576286411017249568127573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384190940678166378751715 3576286411017249568127573)
            ·
              refine ⟨41909606379108393376495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3576286411017249568127573 41909606379108393376495)
              ·
                rfl

theorem cell20_826389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_826389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826389 prefixEnd_826389 := by exact prefixLift 826389
  have htrace : WordTrace (prefixWord ++ tailWord_826389) baseStart_826389 baseEnd_826389 := by
    simpa [prefixWord, tailWord_826389, baseEnd_826389] using wordTrace_append hprefix tailTrace_826389
  have hstable : (prefixWord ++ tailWord_826389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826389).length < 2 ^ (prefixWord ++ tailWord_826389).sum := by decide
  have hdescent : baseEnd_826389 < baseStart_826389 := by decide
  rcases family_descends (prefixWord ++ tailWord_826389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826399 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_826399 : Nat := 118140960795 + 826399 * 2 ^ 59
def prefixEnd_826399 : Nat := 4983230072969 + 3 ^ 40 * 826399 * 2
def baseEnd_826399 : Nat := 377191021684459950055081

theorem tailTrace_826399 : CollatzResearch.WordTrace tailWord_826399 prefixEnd_826399 377191021684459950055081 := by
  unfold tailWord_826399
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141247733105035557762251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20094165155403357038508167 30141247733105035557762251)
  ·
    refine ⟨45211871599657553336643377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30141247733105035557762251 45211871599657553336643377)
    ·
      refine ⟨33908903699743165002482533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45211871599657553336643377 33908903699743165002482533)
      ·
        refine ⟨6357919443701843437965475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33908903699743165002482533 6357919443701843437965475)
        ·
          refine ⟨9536879165552765156948213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357919443701843437965475 9536879165552765156948213)
          ·
            refine ⟨894082421770571733463895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9536879165552765156948213 894082421770571733463895)
            ·
              refine ⟨1341123632655857600195843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894082421770571733463895 1341123632655857600195843)
              ·
                refine ⟨2011685448983786400293765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341123632655857600195843 2011685448983786400293765)
                ·
                  refine ⟨377191021684459950055081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2011685448983786400293765 377191021684459950055081)
                  ·
                    rfl

theorem cell20_826399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_826399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826399 prefixEnd_826399 := by exact prefixLift 826399
  have htrace : WordTrace (prefixWord ++ tailWord_826399) baseStart_826399 baseEnd_826399 := by
    simpa [prefixWord, tailWord_826399, baseEnd_826399] using wordTrace_append hprefix tailTrace_826399
  have hstable : (prefixWord ++ tailWord_826399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826399).length < 2 ^ (prefixWord ++ tailWord_826399).sum := by decide
  have hdescent : baseEnd_826399 < baseStart_826399 := by decide
  rcases family_descends (prefixWord ++ tailWord_826399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826441 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_826441 : Nat := 118140960795 + 826441 * 2 ^ 59
def prefixEnd_826441 : Nat := 4983230072969 + 3 ^ 40 * 826441 * 2
def baseEnd_826441 : Nat := 377210191628894470654909

theorem tailTrace_826441 : CollatzResearch.WordTrace tailWord_826441 prefixEnd_826441 377210191628894470654909 := by
  unfold tailWord_826441
  simp only [CollatzResearch.WordTrace]
  refine ⟨30142779598952876730791177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20095186399301917820527451 30142779598952876730791177)
  ·
    refine ⟨22607084699214657548093383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30142779598952876730791177 22607084699214657548093383)
    ·
      refine ⟨33910627048821986322140075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22607084699214657548093383 33910627048821986322140075)
      ·
        refine ⟨50865940573232979483210113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33910627048821986322140075 50865940573232979483210113)
        ·
          refine ⟨38149455429924734612407585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50865940573232979483210113 38149455429924734612407585)
          ·
            refine ⟨28612091572443550959305689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38149455429924734612407585 28612091572443550959305689)
            ·
              refine ⟨21459068679332663219479267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28612091572443550959305689 21459068679332663219479267)
              ·
                refine ⟨32188603018998994829218901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21459068679332663219479267 32188603018998994829218901)
                ·
                  refine ⟨377210191628894470654909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32188603018998994829218901 377210191628894470654909)
                  ·
                    rfl

theorem cell20_826441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_826441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826441 prefixEnd_826441 := by exact prefixLift 826441
  have htrace : WordTrace (prefixWord ++ tailWord_826441) baseStart_826441 baseEnd_826441 := by
    simpa [prefixWord, tailWord_826441, baseEnd_826441] using wordTrace_append hprefix tailTrace_826441
  have hstable : (prefixWord ++ tailWord_826441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826441).length < 2 ^ (prefixWord ++ tailWord_826441).sum := by decide
  have hdescent : baseEnd_826441 < baseStart_826441 := by decide
  rcases family_descends (prefixWord ++ tailWord_826441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826465 : List Nat := [1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_826465 : Nat := 118140960795 + 826465 * 2 ^ 59
def prefixEnd_826465 : Nat := 4983230072969 + 3 ^ 40 * 826465 * 2
def baseEnd_826465 : Nat := 125740381960952351284937

theorem tailTrace_826465 : CollatzResearch.WordTrace tailWord_826465 prefixEnd_826465 125740381960952351284937 := by
  unfold tailWord_826465
  simp only [CollatzResearch.WordTrace]
  refine ⟨30143654950865928829664849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20095769967243952553109899 30143654950865928829664849)
  ·
    refine ⟨22607741213149446622248637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30143654950865928829664849 22607741213149446622248637)
    ·
      refine ⟨8477902954931042483343239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22607741213149446622248637 8477902954931042483343239)
      ·
        refine ⟨12716854432396563725014859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477902954931042483343239 12716854432396563725014859)
        ·
          refine ⟨19075281648594845587522289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12716854432396563725014859 19075281648594845587522289)
          ·
            refine ⟨14306461236446134190641717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19075281648594845587522289 14306461236446134190641717)
            ·
              refine ⟨1341230740916825080372661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14306461236446134190641717 1341230740916825080372661)
              ·
                refine ⟨125740381960952351284937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1341230740916825080372661 125740381960952351284937)
                ·
                  rfl

theorem cell20_826465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_826465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826465 prefixEnd_826465 := by exact prefixLift 826465
  have htrace : WordTrace (prefixWord ++ tailWord_826465) baseStart_826465 baseEnd_826465 := by
    simpa [prefixWord, tailWord_826465, baseEnd_826465] using wordTrace_append hprefix tailTrace_826465
  have hstable : (prefixWord ++ tailWord_826465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826465).length < 2 ^ (prefixWord ++ tailWord_826465).sum := by decide
  have hdescent : baseEnd_826465 < baseStart_826465 := by decide
  rcases family_descends (prefixWord ++ tailWord_826465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826482 : List Nat := [3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_826482 : Nat := 118140960795 + 826482 * 2 ^ 59
def prefixEnd_826482 : Nat := 4983230072969 + 3 ^ 40 * 826482 * 2
def baseEnd_826482 : Nat := 125742968382026850096025

theorem tailTrace_826482 : CollatzResearch.WordTrace tailWord_826482 prefixEnd_826482 125742968382026850096025 := by
  unfold tailWord_826482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536068747951085183258425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20096183327869560488689133 7536068747951085183258425)
  ·
    refine ⟨5652051560963313887443819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7536068747951085183258425 5652051560963313887443819)
    ·
      refine ⟨8478077341444970831165729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5652051560963313887443819 8478077341444970831165729)
      ·
        refine ⟨6358558006083728123374297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8478077341444970831165729 6358558006083728123374297)
        ·
          refine ⟨4768918504562796092530723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6358558006083728123374297 4768918504562796092530723)
          ·
            refine ⟨7153377756844194138796085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768918504562796092530723 7153377756844194138796085)
            ·
              refine ⟨670629164704143200512133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7153377756844194138796085 670629164704143200512133)
              ·
                refine ⟨125742968382026850096025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 670629164704143200512133 125742968382026850096025)
                ·
                  rfl

theorem cell20_826482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_826482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826482 prefixEnd_826482 := by exact prefixLift 826482
  have htrace : WordTrace (prefixWord ++ tailWord_826482) baseStart_826482 baseEnd_826482 := by
    simpa [prefixWord, tailWord_826482, baseEnd_826482] using wordTrace_append hprefix tailTrace_826482
  have hstable : (prefixWord ++ tailWord_826482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826482).length < 2 ^ (prefixWord ++ tailWord_826482).sum := by decide
  have hdescent : baseEnd_826482 < baseStart_826482 := by decide
  rcases family_descends (prefixWord ++ tailWord_826482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826558 : List Nat := [4, 2, 1, 1, 3, 3, 6]
def baseStart_826558 : Nat := 118140960795 + 826558 * 2 ^ 59
def prefixEnd_826558 : Nat := 4983230072969 + 3 ^ 40 * 826558 * 2
def baseEnd_826558 : Nat := 41918177068551340417159

theorem tailTrace_826558 : CollatzResearch.WordTrace tailWord_826558 prefixEnd_826558 41918177068551340417159 := by
  unfold tailWord_826558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3768380867441125714100041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20098031293019337141866885 3768380867441125714100041)
  ·
    refine ⟨2826285650580844285575031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3768380867441125714100041 2826285650580844285575031)
    ·
      refine ⟨4239428475871266428362547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826285650580844285575031 4239428475871266428362547)
      ·
        refine ⟨6359142713806899642543821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239428475871266428362547 6359142713806899642543821)
        ·
          refine ⟨2384678517677587365953933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6359142713806899642543821 2384678517677587365953933)
          ·
            refine ⟨894254444129095262232725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2384678517677587365953933 894254444129095262232725)
            ·
              refine ⟨41918177068551340417159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 894254444129095262232725 41918177068551340417159)
              ·
                rfl

theorem cell20_826558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_826558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826558 prefixEnd_826558 := by exact prefixLift 826558
  have htrace : WordTrace (prefixWord ++ tailWord_826558) baseStart_826558 baseEnd_826558 := by
    simpa [prefixWord, tailWord_826558, baseEnd_826558] using wordTrace_append hprefix tailTrace_826558
  have hstable : (prefixWord ++ tailWord_826558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826558).length < 2 ^ (prefixWord ++ tailWord_826558).sum := by decide
  have hdescent : baseEnd_826558 < baseStart_826558 := by decide
  rcases family_descends (prefixWord ++ tailWord_826558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826620 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_826620 : Nat := 118140960795 + 826620 * 2 ^ 59
def prefixEnd_826620 : Nat := 4983230072969 + 3 ^ 40 * 826620 * 2
def baseEnd_826620 : Nat := 377291892106365403687511

theorem tailTrace_826620 : CollatzResearch.WordTrace tailWord_826620 prefixEnd_826620 377291892106365403687511 := by
  unfold tailWord_826620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074654132652195150778657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20099538843536260201038209 15074654132652195150778657)
  ·
    refine ⟨11305990599489146363083993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15074654132652195150778657 11305990599489146363083993)
    ·
      refine ⟨8479492949616859772312995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11305990599489146363083993 8479492949616859772312995)
      ·
        refine ⟨12719239424425289658469493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479492949616859772312995 12719239424425289658469493)
        ·
          refine ⟨1192428696039870905481515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12719239424425289658469493 1192428696039870905481515)
          ·
            refine ⟨1788643044059806358222273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192428696039870905481515 1788643044059806358222273)
            ·
              refine ⟨1341482283044854768666705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788643044059806358222273 1341482283044854768666705)
              ·
                refine ⟨1006111712283641076500029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341482283044854768666705 1006111712283641076500029)
                ·
                  refine ⟨377291892106365403687511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006111712283641076500029 377291892106365403687511)
                  ·
                    rfl

theorem cell20_826620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_826620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826620 prefixEnd_826620 := by exact prefixLift 826620
  have htrace : WordTrace (prefixWord ++ tailWord_826620) baseStart_826620 baseEnd_826620 := by
    simpa [prefixWord, tailWord_826620, baseEnd_826620] using wordTrace_append hprefix tailTrace_826620
  have hstable : (prefixWord ++ tailWord_826620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826620).length < 2 ^ (prefixWord ++ tailWord_826620).sum := by decide
  have hdescent : baseEnd_826620 < baseStart_826620 := by decide
  rcases family_descends (prefixWord ++ tailWord_826620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826627 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 2]
def baseStart_826627 : Nat := 118140960795 + 826627 * 2 ^ 59
def prefixEnd_826627 : Nat := 4983230072969 + 3 ^ 40 * 826627 * 2
def baseEnd_826627 : Nat := 377295087097104490454149

theorem tailTrace_826627 : CollatzResearch.WordTrace tailWord_826627 prefixEnd_826627 377295087097104490454149 := by
  unfold tailWord_826627
  simp only [CollatzResearch.WordTrace]
  refine ⟨30149563576279030497062135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20099709050852686998041423 30149563576279030497062135)
  ·
    refine ⟨45224345364418545745593203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30149563576279030497062135 45224345364418545745593203)
    ·
      refine ⟨67836518046627818618389805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45224345364418545745593203 67836518046627818618389805)
      ·
        refine ⟨25438694267485431981896177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67836518046627818618389805 25438694267485431981896177)
        ·
          refine ⟨19079020700614073986422133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25438694267485431981896177 19079020700614073986422133)
          ·
            refine ⟨1788658190682569436227075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19079020700614073986422133 1788658190682569436227075)
            ·
              refine ⟨2682987286023854154340613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788658190682569436227075 2682987286023854154340613)
              ·
                refine ⟨503060116129472653938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2682987286023854154340613 503060116129472653938865)
                ·
                  refine ⟨377295087097104490454149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503060116129472653938865 377295087097104490454149)
                  ·
                    rfl

theorem cell20_826627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 2].length) (baseStart_826627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826627 prefixEnd_826627 := by exact prefixLift 826627
  have htrace : WordTrace (prefixWord ++ tailWord_826627) baseStart_826627 baseEnd_826627 := by
    simpa [prefixWord, tailWord_826627, baseEnd_826627] using wordTrace_append hprefix tailTrace_826627
  have hstable : (prefixWord ++ tailWord_826627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826627).length < 2 ^ (prefixWord ++ tailWord_826627).sum := by decide
  have hdescent : baseEnd_826627 < baseStart_826627 := by decide
  rcases family_descends (prefixWord ++ tailWord_826627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826648 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_826648 : Nat := 118140960795 + 826648 * 2 ^ 59
def prefixEnd_826648 : Nat := 4983230072969 + 3 ^ 40 * 826648 * 2
def baseEnd_826648 : Nat := 377304672069321750754063

theorem tailTrace_826648 : CollatzResearch.WordTrace tailWord_826648 prefixEnd_826648 377304672069321750754063 := by
  unfold tailWord_826648
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075164754601475541788299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20100219672801967389051065 15075164754601475541788299)
  ·
    refine ⟨22612747131902213312682449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15075164754601475541788299 22612747131902213312682449)
    ·
      refine ⟨16959560348926659984511837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22612747131902213312682449 16959560348926659984511837)
      ·
        refine ⟨6359835130847497494191939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16959560348926659984511837 6359835130847497494191939)
        ·
          refine ⟨9539752696271246241287909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359835130847497494191939 9539752696271246241287909)
          ·
            refine ⟨1788703630550858670241483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9539752696271246241287909 1788703630550858670241483)
            ·
              refine ⟨2683055445826288005362225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788703630550858670241483 2683055445826288005362225)
              ·
                refine ⟨2012291584369716004021669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2683055445826288005362225 2012291584369716004021669)
                ·
                  refine ⟨377304672069321750754063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012291584369716004021669 377304672069321750754063)
                  ·
                    rfl

theorem cell20_826648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_826648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826648 prefixEnd_826648 := by exact prefixLift 826648
  have htrace : WordTrace (prefixWord ++ tailWord_826648) baseStart_826648 baseEnd_826648 := by
    simpa [prefixWord, tailWord_826648, baseEnd_826648] using wordTrace_append hprefix tailTrace_826648
  have hstable : (prefixWord ++ tailWord_826648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826648).length < 2 ^ (prefixWord ++ tailWord_826648).sum := by decide
  have hdescent : baseEnd_826648 < baseStart_826648 := by decide
  rcases family_descends (prefixWord ++ tailWord_826648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826707 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_826707 : Nat := 118140960795 + 826707 * 2 ^ 59
def prefixEnd_826707 : Nat := 4983230072969 + 3 ^ 40 * 826707 * 2
def baseEnd_826707 : Nat := 377331601276979767787155

theorem tailTrace_826707 : CollatzResearch.WordTrace tailWord_826707 prefixEnd_826707 377331601276979767787155 := by
  unfold tailWord_826707
  simp only [CollatzResearch.WordTrace]
  refine ⟨30152481415989204159974375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20101654277326136106649583 30152481415989204159974375)
  ·
    refine ⟨45228722123983806239961563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30152481415989204159974375 45228722123983806239961563)
    ·
      refine ⟨67843083185975709359942345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45228722123983806239961563 67843083185975709359942345)
      ·
        refine ⟨50882312389481782019956759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67843083185975709359942345 50882312389481782019956759)
        ·
          refine ⟨76323468584222673029935139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50882312389481782019956759 76323468584222673029935139)
          ·
            refine ⟨114485202876334009544902709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76323468584222673029935139 114485202876334009544902709)
            ·
              refine ⟨10732987769656313394834629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114485202876334009544902709 10732987769656313394834629)
              ·
                refine ⟨2012435206810558761531493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10732987769656313394834629 2012435206810558761531493)
                ·
                  refine ⟨377331601276979767787155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012435206810558761531493 377331601276979767787155)
                  ·
                    rfl

theorem cell20_826707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_826707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826707 prefixEnd_826707 := by exact prefixLift 826707
  have htrace : WordTrace (prefixWord ++ tailWord_826707) baseStart_826707 baseEnd_826707 := by
    simpa [prefixWord, tailWord_826707, baseEnd_826707] using wordTrace_append hprefix tailTrace_826707
  have hstable : (prefixWord ++ tailWord_826707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826707).length < 2 ^ (prefixWord ++ tailWord_826707).sum := by decide
  have hdescent : baseEnd_826707 < baseStart_826707 := by decide
  rcases family_descends (prefixWord ++ tailWord_826707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826720 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_826720 : Nat := 118140960795 + 826720 * 2 ^ 59
def prefixEnd_826720 : Nat := 4983230072969 + 3 ^ 40 * 826720 * 2
def baseEnd_826720 : Nat := 377337534831209500353769

theorem tailTrace_826720 : CollatzResearch.WordTrace tailWord_826720 prefixEnd_826720 377337534831209500353769 := by
  unfold tailWord_826720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15076477782471053690098807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20101970376628071586798409 15076477782471053690098807)
  ·
    refine ⟨22614716673706580535148211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15076477782471053690098807 22614716673706580535148211)
    ·
      refine ⟨33922075010559870802722317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22614716673706580535148211 33922075010559870802722317)
      ·
        refine ⟨12720778128959951551020869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33922075010559870802722317 12720778128959951551020869)
        ·
          refine ⟨2385145899179990915816413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12720778128959951551020869 2385145899179990915816413)
          ·
            refine ⟨894429712192496593431155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2385145899179990915816413 894429712192496593431155)
            ·
              refine ⟨1341644568288744890146733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894429712192496593431155 1341644568288744890146733)
              ·
                refine ⟨503116713108279333805025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341644568288744890146733 503116713108279333805025)
                ·
                  refine ⟨377337534831209500353769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503116713108279333805025 377337534831209500353769)
                  ·
                    rfl

theorem cell20_826720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_826720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826720 prefixEnd_826720 := by exact prefixLift 826720
  have htrace : WordTrace (prefixWord ++ tailWord_826720) baseStart_826720 baseEnd_826720 := by
    simpa [prefixWord, tailWord_826720, baseEnd_826720] using wordTrace_append hprefix tailTrace_826720
  have hstable : (prefixWord ++ tailWord_826720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826720).length < 2 ^ (prefixWord ++ tailWord_826720).sum := by decide
  have hdescent : baseEnd_826720 < baseStart_826720 := by decide
  rcases family_descends (prefixWord ++ tailWord_826720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826738 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_826738 : Nat := 118140960795 + 826738 * 2 ^ 59
def prefixEnd_826738 : Nat := 4983230072969 + 3 ^ 40 * 826738 * 2
def baseEnd_826738 : Nat := 377345750521681437753695

theorem tailTrace_826738 : CollatzResearch.WordTrace tailWord_826738 prefixEnd_826738 377345750521681437753695 := by
  unfold tailWord_826738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538403019719224113588217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20102408052584597636235245 7538403019719224113588217)
  ·
    refine ⟨5653802264789418085191163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7538403019719224113588217 5653802264789418085191163)
    ·
      refine ⟨8480703397184127127786745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653802264789418085191163 8480703397184127127786745)
      ·
        refine ⟨6360527547888095345840059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8480703397184127127786745 6360527547888095345840059)
        ·
          refine ⟨9540791321832143018760089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360527547888095345840059 9540791321832143018760089)
          ·
            refine ⟨7155593491374107264070067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9540791321832143018760089 7155593491374107264070067)
            ·
              refine ⟨10733390237061160896105101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155593491374107264070067 10733390237061160896105101)
              ·
                refine ⟨4025021338897935336039413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10733390237061160896105101 4025021338897935336039413)
                ·
                  refine ⟨377345750521681437753695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4025021338897935336039413 377345750521681437753695)
                  ·
                    rfl

theorem cell20_826738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_826738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826738 prefixEnd_826738 := by exact prefixLift 826738
  have htrace : WordTrace (prefixWord ++ tailWord_826738) baseStart_826738 baseEnd_826738 := by
    simpa [prefixWord, tailWord_826738, baseEnd_826738] using wordTrace_append hprefix tailTrace_826738
  have hstable : (prefixWord ++ tailWord_826738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826738).length < 2 ^ (prefixWord ++ tailWord_826738).sum := by decide
  have hdescent : baseEnd_826738 < baseStart_826738 := by decide
  rcases family_descends (prefixWord ++ tailWord_826738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826755 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_826755 : Nat := 118140960795 + 826755 * 2 ^ 59
def prefixEnd_826755 : Nat := 4983230072969 + 3 ^ 40 * 826755 * 2
def baseEnd_826755 : Nat := 377353509784904934186959

theorem tailTrace_826755 : CollatzResearch.WordTrace tailWord_826755 prefixEnd_826755 377353509784904934186959 := by
  unfold tailWord_826755
  simp only [CollatzResearch.WordTrace]
  refine ⟨30154232119815308357721719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20102821413210205571814479 30154232119815308357721719)
  ·
    refine ⟨45231348179722962536582579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30154232119815308357721719 45231348179722962536582579)
    ·
      refine ⟨67847022269584443804873869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45231348179722962536582579 67847022269584443804873869)
      ·
        refine ⟨25442633351094166426827701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67847022269584443804873869 25442633351094166426827701)
        ·
          refine ⟨2385246876665078102515097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25442633351094166426827701 2385246876665078102515097)
          ·
            refine ⟨1788935157498808576886323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385246876665078102515097 1788935157498808576886323)
            ·
              refine ⟨2683402736248212865329485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788935157498808576886323 2683402736248212865329485)
              ·
                refine ⟨1006276026093079824498557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683402736248212865329485 1006276026093079824498557)
                ·
                  refine ⟨377353509784904934186959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006276026093079824498557 377353509784904934186959)
                  ·
                    rfl

theorem cell20_826755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_826755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826755 prefixEnd_826755 := by exact prefixLift 826755
  have htrace : WordTrace (prefixWord ++ tailWord_826755) baseStart_826755 baseEnd_826755 := by
    simpa [prefixWord, tailWord_826755, baseEnd_826755] using wordTrace_append hprefix tailTrace_826755
  have hstable : (prefixWord ++ tailWord_826755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826755).length < 2 ^ (prefixWord ++ tailWord_826755).sum := by decide
  have hdescent : baseEnd_826755 < baseStart_826755 := by decide
  rcases family_descends (prefixWord ++ tailWord_826755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826792 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_826792 : Nat := 118140960795 + 826792 * 2 ^ 59
def prefixEnd_826792 : Nat := 4983230072969 + 3 ^ 40 * 826792 * 2
def baseEnd_826792 : Nat := 377370397593097249953475

theorem tailTrace_826792 : CollatzResearch.WordTrace tailWord_826792 prefixEnd_826792 377370397593097249953475 := by
  unfold tailWord_826792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077790810340631838409315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20103721080454175784545753 15077790810340631838409315)
  ·
    refine ⟨22616686215510947757613973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077790810340631838409315 22616686215510947757613973)
    ·
      refine ⟨1060157166352075676138155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22616686215510947757613973 1060157166352075676138155)
      ·
        refine ⟨1590235749528113514207233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060157166352075676138155 1590235749528113514207233)
        ·
          refine ⟨1192676812146085135655425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590235749528113514207233 1192676812146085135655425)
          ·
            refine ⟨894507609109563851741569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192676812146085135655425 894507609109563851741569)
            ·
              refine ⟨670880706832172888806177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894507609109563851741569 670880706832172888806177)
              ·
                refine ⟨503160530124129666604633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670880706832172888806177 503160530124129666604633)
                ·
                  refine ⟨377370397593097249953475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503160530124129666604633 377370397593097249953475)
                  ·
                    rfl

theorem cell20_826792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_826792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826792 prefixEnd_826792 := by exact prefixLift 826792
  have htrace : WordTrace (prefixWord ++ tailWord_826792) baseStart_826792 baseEnd_826792 := by
    simpa [prefixWord, tailWord_826792, baseEnd_826792] using wordTrace_append hprefix tailTrace_826792
  have hstable : (prefixWord ++ tailWord_826792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826792).length < 2 ^ (prefixWord ++ tailWord_826792).sum := by decide
  have hdescent : baseEnd_826792 < baseStart_826792 := by decide
  rcases family_descends (prefixWord ++ tailWord_826792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826814 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_826814 : Nat := 118140960795 + 826814 * 2 ^ 59
def prefixEnd_826814 : Nat := 4983230072969 + 3 ^ 40 * 826814 * 2
def baseEnd_826814 : Nat := 377380438992562951220051

theorem tailTrace_826814 : CollatzResearch.WordTrace tailWord_826814 prefixEnd_826814 377380438992562951220051 := by
  unfold tailWord_826814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769548003325195179264937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20104256017734374289412997 3769548003325195179264937)
  ·
    refine ⟨2827161002493896384448703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3769548003325195179264937 2827161002493896384448703)
    ·
      refine ⟨4240741503740844576673055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827161002493896384448703 4240741503740844576673055)
      ·
        refine ⟨6361112255611266865009583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240741503740844576673055 6361112255611266865009583)
        ·
          refine ⟨9541668383416900297514375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361112255611266865009583 9541668383416900297514375)
          ·
            refine ⟨14312502575125350446271563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541668383416900297514375 14312502575125350446271563)
            ·
              refine ⟨21468753862688025669407345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312502575125350446271563 21468753862688025669407345)
              ·
                refine ⟨16101565397016019252055509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21468753862688025669407345 16101565397016019252055509)
                ·
                  refine ⟨377380438992562951220051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16101565397016019252055509 377380438992562951220051)
                  ·
                    rfl

theorem cell20_826814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_826814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826814 prefixEnd_826814 := by exact prefixLift 826814
  have htrace : WordTrace (prefixWord ++ tailWord_826814) baseStart_826814 baseEnd_826814 := by
    simpa [prefixWord, tailWord_826814, baseEnd_826814] using wordTrace_append hprefix tailTrace_826814
  have hstable : (prefixWord ++ tailWord_826814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826814).length < 2 ^ (prefixWord ++ tailWord_826814).sum := by decide
  have hdescent : baseEnd_826814 < baseStart_826814 := by decide
  rcases family_descends (prefixWord ++ tailWord_826814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826845 : List Nat := [1, 4, 3, 1, 1, 3, 7]
def baseStart_826845 : Nat := 118140960795 + 826845 * 2 ^ 59
def prefixEnd_826845 : Nat := 4983230072969 + 3 ^ 40 * 826845 * 2
def baseEnd_826845 : Nat := 41932732026362735687399

theorem tailTrace_826845 : CollatzResearch.WordTrace tailWord_826845 prefixEnd_826845 41932732026362735687399 := by
  unfold tailWord_826845
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157514689489253728497989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20105009792992835818998659 30157514689489253728497989)
  ·
    refine ⟨5654534004279235074093373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30157514689489253728497989 5654534004279235074093373)
    ·
      refine ⟨2120450251604713152785015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5654534004279235074093373 2120450251604713152785015)
      ·
        refine ⟨3180675377407069729177523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120450251604713152785015 3180675377407069729177523)
        ·
          refine ⟨4771013066110604593766285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180675377407069729177523 4771013066110604593766285)
          ·
            refine ⟨1789129899791476722662357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4771013066110604593766285 1789129899791476722662357)
            ·
              refine ⟨41932732026362735687399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1789129899791476722662357 41932732026362735687399)
              ·
                rfl

theorem cell20_826845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_826845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826845 prefixEnd_826845 := by exact prefixLift 826845
  have htrace : WordTrace (prefixWord ++ tailWord_826845) baseStart_826845 baseEnd_826845 := by
    simpa [prefixWord, tailWord_826845, baseEnd_826845] using wordTrace_append hprefix tailTrace_826845
  have hstable : (prefixWord ++ tailWord_826845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826845).length < 2 ^ (prefixWord ++ tailWord_826845).sum := by decide
  have hdescent : baseEnd_826845 < baseStart_826845 := by decide
  rcases family_descends (prefixWord ++ tailWord_826845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826855 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 2]
def baseStart_826855 : Nat := 118140960795 + 826855 * 2 ^ 59
def prefixEnd_826855 : Nat := 4983230072969 + 3 ^ 40 * 826855 * 2
def baseEnd_826855 : Nat := 377399152509749030853217

theorem tailTrace_826855 : CollatzResearch.WordTrace tailWord_826855 prefixEnd_826855 377399152509749030853217 := by
  unfold tailWord_826855
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157879419453025436362019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20105252946302016957574679 30157879419453025436362019)
  ·
    refine ⟨45236819129179538154543029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30157879419453025436362019 45236819129179538154543029)
    ·
      refine ⟨4240951793360581701988409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45236819129179538154543029 4240951793360581701988409)
      ·
        refine ⟨3180713845020436276491307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4240951793360581701988409 3180713845020436276491307)
        ·
          refine ⟨4771070767530654414736961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180713845020436276491307 4771070767530654414736961)
          ·
            refine ⟨3578303075647990811052721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771070767530654414736961 3578303075647990811052721)
            ·
              refine ⟨2683727306735993108289541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3578303075647990811052721 2683727306735993108289541)
              ·
                refine ⟨503198870012998707804289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2683727306735993108289541 503198870012998707804289)
                ·
                  refine ⟨377399152509749030853217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503198870012998707804289 377399152509749030853217)
                  ·
                    rfl

theorem cell20_826855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2].length) (baseStart_826855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826855 prefixEnd_826855 := by exact prefixLift 826855
  have htrace : WordTrace (prefixWord ++ tailWord_826855) baseStart_826855 baseEnd_826855 := by
    simpa [prefixWord, tailWord_826855, baseEnd_826855] using wordTrace_append hprefix tailTrace_826855
  have hstable : (prefixWord ++ tailWord_826855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826855).length < 2 ^ (prefixWord ++ tailWord_826855).sum := by decide
  have hdescent : baseEnd_826855 < baseStart_826855 := by decide
  rcases family_descends (prefixWord ++ tailWord_826855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826890 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_826890 : Nat := 118140960795 + 826890 * 2 ^ 59
def prefixEnd_826890 : Nat := 4983230072969 + 3 ^ 40 * 826890 * 2
def baseEnd_826890 : Nat := 377415127463444464686407

theorem tailTrace_826890 : CollatzResearch.WordTrace tailWord_826890 prefixEnd_826890 377415127463444464686407 := by
  unfold tailWord_826890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539788993581556603471531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20106103982884150942590749 7539788993581556603471531)
  ·
    refine ⟨11309683490372334905207297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7539788993581556603471531 11309683490372334905207297)
    ·
      refine ⟨8482262617779251178905473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11309683490372334905207297 8482262617779251178905473)
      ·
        refine ⟨6361696963334438384179105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8482262617779251178905473 6361696963334438384179105)
        ·
          refine ⟨4771272722500828788134329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361696963334438384179105 4771272722500828788134329)
          ·
            refine ⟨3578454541875621591100747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771272722500828788134329 3578454541875621591100747)
            ·
              refine ⟨5367681812813432386651121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578454541875621591100747 5367681812813432386651121)
              ·
                refine ⟨4025761359610074289988341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367681812813432386651121 4025761359610074289988341)
                ·
                  refine ⟨377415127463444464686407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4025761359610074289988341 377415127463444464686407)
                  ·
                    rfl

theorem cell20_826890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_826890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826890 prefixEnd_826890 := by exact prefixLift 826890
  have htrace : WordTrace (prefixWord ++ tailWord_826890) baseStart_826890 baseEnd_826890 := by
    simpa [prefixWord, tailWord_826890, baseEnd_826890] using wordTrace_append hprefix tailTrace_826890
  have hstable : (prefixWord ++ tailWord_826890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826890).length < 2 ^ (prefixWord ++ tailWord_826890).sum := by decide
  have hdescent : baseEnd_826890 < baseStart_826890 := by decide
  rcases family_descends (prefixWord ++ tailWord_826890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826914 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_826914 : Nat := 118140960795 + 826914 * 2 ^ 59
def prefixEnd_826914 : Nat := 4983230072969 + 3 ^ 40 * 826914 * 2
def baseEnd_826914 : Nat := 377426081717407047886309

theorem tailTrace_826914 : CollatzResearch.WordTrace tailWord_826914 prefixEnd_826914 377426081717407047886309 := by
  unfold tailWord_826914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540007831559819628189949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20106687550826185675173197 7540007831559819628189949)
  ·
    refine ⟨2827502936834932360571231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7540007831559819628189949 2827502936834932360571231)
    ·
      refine ⟨4241254405252398540856847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827502936834932360571231 4241254405252398540856847)
      ·
        refine ⟨6361881607878597811285271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241254405252398540856847 6361881607878597811285271)
        ·
          refine ⟨9542822411817896716927907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361881607878597811285271 9542822411817896716927907)
          ·
            refine ⟨14314233617726845075391861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542822411817896716927907 14314233617726845075391861)
            ·
              refine ⟨1341959401661891725817987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14314233617726845075391861 1341959401661891725817987)
              ·
                refine ⟨2012939102492837588726981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341959401661891725817987 2012939102492837588726981)
                ·
                  refine ⟨377426081717407047886309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012939102492837588726981 377426081717407047886309)
                  ·
                    rfl

theorem cell20_826914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_826914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826914 prefixEnd_826914 := by exact prefixLift 826914
  have htrace : WordTrace (prefixWord ++ tailWord_826914) baseStart_826914 baseEnd_826914 := by
    simpa [prefixWord, tailWord_826914, baseEnd_826914] using wordTrace_append hprefix tailTrace_826914
  have hstable : (prefixWord ++ tailWord_826914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826914).length < 2 ^ (prefixWord ++ tailWord_826914).sum := by decide
  have hdescent : baseEnd_826914 < baseStart_826914 := by decide
  rcases family_descends (prefixWord ++ tailWord_826914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826920 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_826920 : Nat := 118140960795 + 826920 * 2 ^ 59
def prefixEnd_826920 : Nat := 4983230072969 + 3 ^ 40 * 826920 * 2
def baseEnd_826920 : Nat := 377428820280897693686285

theorem tailTrace_826920 : CollatzResearch.WordTrace tailWord_826920 prefixEnd_826920 377428820280897693686285 := by
  unfold tailWord_826920
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080125082108770768739107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20106833442811694358318809 15080125082108770768739107)
  ·
    refine ⟨22620187623163156153108661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15080125082108770768739107 22620187623163156153108661)
    ·
      refine ⟨2120642589671545889353937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22620187623163156153108661 2120642589671545889353937)
      ·
        refine ⟨1590481942253659417015453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2120642589671545889353937 1590481942253659417015453)
        ·
          refine ⟨596430728345122281380795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1590481942253659417015453 596430728345122281380795)
          ·
            refine ⟨894646092517683422071193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596430728345122281380795 894646092517683422071193)
            ·
              refine ⟨670984569388262566553395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894646092517683422071193 670984569388262566553395)
              ·
                refine ⟨1006476854082393849830093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670984569388262566553395 1006476854082393849830093)
                ·
                  refine ⟨377428820280897693686285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006476854082393849830093 377428820280897693686285)
                  ·
                    rfl

theorem cell20_826920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_826920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_826920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_826920 prefixEnd_826920 := by exact prefixLift 826920
  have htrace : WordTrace (prefixWord ++ tailWord_826920) baseStart_826920 baseEnd_826920 := by
    simpa [prefixWord, tailWord_826920, baseEnd_826920] using wordTrace_append hprefix tailTrace_826920
  have hstable : (prefixWord ++ tailWord_826920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826920).length < 2 ^ (prefixWord ++ tailWord_826920).sum := by decide
  have hdescent : baseEnd_826920 < baseStart_826920 := by decide
  rcases family_descends (prefixWord ++ tailWord_826920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827080 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_827080 : Nat := 118140960795 + 827080 * 2 ^ 59
def prefixEnd_827080 : Nat := 4983230072969 + 3 ^ 40 * 827080 * 2
def baseEnd_827080 : Nat := 377501848640648248352297

theorem tailTrace_827080 : CollatzResearch.WordTrace tailWord_827080 prefixEnd_827080 377501848640648248352297 := by
  unfold tailWord_827080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15083042921818944431651347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20110723895758592575535129 15083042921818944431651347)
  ·
    refine ⟨22624564382728416647477021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15083042921818944431651347 22624564382728416647477021)
    ·
      refine ⟨8484211643523156242803883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22624564382728416647477021 8484211643523156242803883)
      ·
        refine ⟨12726317465284734364205825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484211643523156242803883 12726317465284734364205825)
        ·
          refine ⟨9544738098963550773154369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12726317465284734364205825 9544738098963550773154369)
          ·
            refine ⟨7158553574222663079865777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9544738098963550773154369 7158553574222663079865777)
            ·
              refine ⟨5368915180666997309899333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7158553574222663079865777 5368915180666997309899333)
              ·
                refine ⟨1006671596375061995606125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5368915180666997309899333 1006671596375061995606125)
                ·
                  refine ⟨377501848640648248352297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006671596375061995606125 377501848640648248352297)
                  ·
                    rfl

theorem cell20_827080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_827080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827080 prefixEnd_827080 := by exact prefixLift 827080
  have htrace : WordTrace (prefixWord ++ tailWord_827080) baseStart_827080 baseEnd_827080 := by
    simpa [prefixWord, tailWord_827080, baseEnd_827080] using wordTrace_append hprefix tailTrace_827080
  have hstable : (prefixWord ++ tailWord_827080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827080).length < 2 ^ (prefixWord ++ tailWord_827080).sum := by decide
  have hdescent : baseEnd_827080 < baseStart_827080 := by decide
  rcases family_descends (prefixWord ++ tailWord_827080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827097 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 3]
def baseStart_827097 : Nat := 118140960795 + 827097 * 2 ^ 59
def prefixEnd_827097 : Nat := 4983230072969 + 3 ^ 40 * 827097 * 2
def baseEnd_827097 : Nat := 377509607903871744785561

theorem tailTrace_827097 : CollatzResearch.WordTrace tailWord_827097 prefixEnd_827097 377509607903871744785561 := by
  unfold tailWord_827097
  simp only [CollatzResearch.WordTrace]
  refine ⟨30166705884576300766671545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20111137256384200511114363 30166705884576300766671545)
  ·
    refine ⟨22625029413432225575003659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30166705884576300766671545 22625029413432225575003659)
    ·
      refine ⟨33937544120148338362505489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22625029413432225575003659 33937544120148338362505489)
      ·
        refine ⟨25453158090111253771879117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33937544120148338362505489 25453158090111253771879117)
        ·
          refine ⟨9544934283791720164454669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25453158090111253771879117 9544934283791720164454669)
          ·
            refine ⟨3579350356421895061670501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9544934283791720164454669 3579350356421895061670501)
            ·
              refine ⟨671128191829105324063219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3579350356421895061670501 671128191829105324063219)
              ·
                refine ⟨1006692287743657986094829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671128191829105324063219 1006692287743657986094829)
                ·
                  refine ⟨377509607903871744785561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006692287743657986094829 377509607903871744785561)
                  ·
                    rfl

theorem cell20_827097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_827097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827097 prefixEnd_827097 := by exact prefixLift 827097
  have htrace : WordTrace (prefixWord ++ tailWord_827097) baseStart_827097 baseEnd_827097 := by
    simpa [prefixWord, tailWord_827097, baseEnd_827097] using wordTrace_append hprefix tailTrace_827097
  have hstable : (prefixWord ++ tailWord_827097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827097).length < 2 ^ (prefixWord ++ tailWord_827097).sum := by decide
  have hdescent : baseEnd_827097 < baseStart_827097 := by decide
  rcases family_descends (prefixWord ++ tailWord_827097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827134 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_827134 : Nat := 118140960795 + 827134 * 2 ^ 59
def prefixEnd_827134 : Nat := 4983230072969 + 3 ^ 40 * 827134 * 2
def baseEnd_827134 : Nat := 377526495712064060552077

theorem tailTrace_827134 : CollatzResearch.WordTrace tailWord_827134 prefixEnd_827134 377526495712064060552077 := by
  unfold tailWord_827134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771006923180282010721057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20112036923628170723845637 3771006923180282010721057)
  ·
    refine ⟨2828255192385211508040793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3771006923180282010721057 2828255192385211508040793)
    ·
      refine ⟨2121191394288908631030595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828255192385211508040793 2121191394288908631030595)
      ·
        refine ⟨3181787091433362946545893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121191394288908631030595 3181787091433362946545893)
        ·
          refine ⟨596585079643755552477355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3181787091433362946545893 596585079643755552477355)
          ·
            refine ⟨894877619465633328716033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596585079643755552477355 894877619465633328716033)
            ·
              refine ⟨671158214599224996537025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894877619465633328716033 671158214599224996537025)
              ·
                refine ⟨503368660949418747402769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671158214599224996537025 503368660949418747402769)
                ·
                  refine ⟨377526495712064060552077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503368660949418747402769 377526495712064060552077)
                  ·
                    rfl

theorem cell20_827134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_827134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827134 prefixEnd_827134 := by exact prefixLift 827134
  have htrace : WordTrace (prefixWord ++ tailWord_827134) baseStart_827134 baseEnd_827134 := by
    simpa [prefixWord, tailWord_827134, baseEnd_827134] using wordTrace_append hprefix tailTrace_827134
  have hstable : (prefixWord ++ tailWord_827134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827134).length < 2 ^ (prefixWord ++ tailWord_827134).sum := by decide
  have hdescent : baseEnd_827134 < baseStart_827134 := by decide
  rcases family_descends (prefixWord ++ tailWord_827134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827139 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_827139 : Nat := 118140960795 + 827139 * 2 ^ 59
def prefixEnd_827139 : Nat := 4983230072969 + 3 ^ 40 * 827139 * 2
def baseEnd_827139 : Nat := 377528777848306265385389

theorem tailTrace_827139 : CollatzResearch.WordTrace tailWord_827139 prefixEnd_827139 377528777848306265385389 := by
  unfold tailWord_827139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30168237750424141939700471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20112158500282761293133647 30168237750424141939700471)
  ·
    refine ⟨45252356625636212909550707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30168237750424141939700471 45252356625636212909550707)
    ·
      refine ⟨67878534938454319364326061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45252356625636212909550707 67878534938454319364326061)
      ·
        refine ⟨25454450601920369761622273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67878534938454319364326061 25454450601920369761622273)
        ·
          refine ⟨19090837951440277321216705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25454450601920369761622273 19090837951440277321216705)
          ·
            refine ⟨14318128463580207990912529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19090837951440277321216705 14318128463580207990912529)
            ·
              refine ⟨10738596347685155993184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14318128463580207990912529 10738596347685155993184397)
              ·
                refine ⟨4026973630381933497444149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10738596347685155993184397 4026973630381933497444149)
                ·
                  refine ⟨377528777848306265385389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4026973630381933497444149 377528777848306265385389)
                  ·
                    rfl

theorem cell20_827139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_827139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827139 prefixEnd_827139 := by exact prefixLift 827139
  have htrace : WordTrace (prefixWord ++ tailWord_827139) baseStart_827139 baseEnd_827139 := by
    simpa [prefixWord, tailWord_827139, baseEnd_827139] using wordTrace_append hprefix tailTrace_827139
  have hstable : (prefixWord ++ tailWord_827139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827139).length < 2 ^ (prefixWord ++ tailWord_827139).sum := by decide
  have hdescent : baseEnd_827139 < baseStart_827139 := by decide
  rcases family_descends (prefixWord ++ tailWord_827139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827180 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_827180 : Nat := 118140960795 + 827180 * 2 ^ 59
def prefixEnd_827180 : Nat := 4983230072969 + 3 ^ 40 * 827180 * 2
def baseEnd_827180 : Nat := 377547491365492345018555

theorem tailTrace_827180 : CollatzResearch.WordTrace tailWord_827180 prefixEnd_827180 377547491365492345018555 := by
  unfold tailWord_827180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084866571637802970971497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20113155428850403961295329 15084866571637802970971497)
  ·
    refine ⟨11313649928728352228228623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15084866571637802970971497 11313649928728352228228623)
    ·
      refine ⟨16970474893092528342342935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11313649928728352228228623 16970474893092528342342935)
      ·
        refine ⟨25455712339638792513514403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16970474893092528342342935 25455712339638792513514403)
        ·
          refine ⟨38183568509458188770271605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25455712339638792513514403 38183568509458188770271605)
          ·
            refine ⟨3579709547761705197212963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38183568509458188770271605 3579709547761705197212963)
            ·
              refine ⟨5369564321642557795819445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579709547761705197212963 5369564321642557795819445)
              ·
                refine ⟨503396655153989793358073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5369564321642557795819445 503396655153989793358073)
                ·
                  refine ⟨377547491365492345018555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503396655153989793358073 377547491365492345018555)
                  ·
                    rfl

theorem cell20_827180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_827180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827180 prefixEnd_827180 := by exact prefixLift 827180
  have htrace : WordTrace (prefixWord ++ tailWord_827180) baseStart_827180 baseEnd_827180 := by
    simpa [prefixWord, tailWord_827180, baseEnd_827180] using wordTrace_append hprefix tailTrace_827180
  have hstable : (prefixWord ++ tailWord_827180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827180).length < 2 ^ (prefixWord ++ tailWord_827180).sum := by decide
  have hdescent : baseEnd_827180 < baseStart_827180 := by decide
  rcases family_descends (prefixWord ++ tailWord_827180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827190 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_827190 : Nat := 118140960795 + 827190 * 2 ^ 59
def prefixEnd_827190 : Nat := 4983230072969 + 3 ^ 40 * 827190 * 2
def baseEnd_827190 : Nat := 377552055637976754685181

theorem tailTrace_827190 : CollatzResearch.WordTrace tailWord_827190 prefixEnd_827190 377552055637976754685181 := by
  unfold tailWord_827190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885631117077461103112939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20113398582159585099871349 1885631117077461103112939)
  ·
    refine ⟨2828446675616191654669409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1885631117077461103112939 2828446675616191654669409)
    ·
      refine ⟨2121335006712143741002057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828446675616191654669409 2121335006712143741002057)
      ·
        refine ⟨1591001255034107805751543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121335006712143741002057 1591001255034107805751543)
        ·
          refine ⟨2386501882551161708627315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591001255034107805751543 2386501882551161708627315)
          ·
            refine ⟨3579752823826742562940973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386501882551161708627315 3579752823826742562940973)
            ·
              refine ⟨1342407308935028461102865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3579752823826742562940973 1342407308935028461102865)
              ·
                refine ⟨1006805481701271345827149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342407308935028461102865 1006805481701271345827149)
                ·
                  refine ⟨377552055637976754685181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006805481701271345827149 377552055637976754685181)
                  ·
                    rfl

theorem cell20_827190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_827190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827190 prefixEnd_827190 := by exact prefixLift 827190
  have htrace : WordTrace (prefixWord ++ tailWord_827190) baseStart_827190 baseEnd_827190 := by
    simpa [prefixWord, tailWord_827190, baseEnd_827190] using wordTrace_append hprefix tailTrace_827190
  have hstable : (prefixWord ++ tailWord_827190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827190).length < 2 ^ (prefixWord ++ tailWord_827190).sum := by decide
  have hdescent : baseEnd_827190 < baseStart_827190 := by decide
  rcases family_descends (prefixWord ++ tailWord_827190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827194 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_827194 : Nat := 118140960795 + 827194 * 2 ^ 59
def prefixEnd_827194 : Nat := 4983230072969 + 3 ^ 40 * 827194 * 2
def baseEnd_827194 : Nat := 377553881346970518551831

theorem tailTrace_827194 : CollatzResearch.WordTrace tailWord_827194 prefixEnd_827194 377553881346970518551831 := by
  unfold tailWord_827194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542560941306221583238159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20113495843483257555301757 7542560941306221583238159)
  ·
    refine ⟨11313841411959332374857239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7542560941306221583238159 11313841411959332374857239)
    ·
      refine ⟨16970762117938998562285859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11313841411959332374857239 16970762117938998562285859)
      ·
        refine ⟨25456143176908497843428789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16970762117938998562285859 25456143176908497843428789)
        ·
          refine ⟨2386513422835171672821449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25456143176908497843428789 2386513422835171672821449)
          ·
            refine ⟨1789885067126378754616087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386513422835171672821449 1789885067126378754616087)
            ·
              refine ⟨2684827600689568131924131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789885067126378754616087 2684827600689568131924131)
              ·
                refine ⟨4027241401034352197886197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684827600689568131924131 4027241401034352197886197)
                ·
                  refine ⟨377553881346970518551831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4027241401034352197886197 377553881346970518551831)
                  ·
                    rfl

theorem cell20_827194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_827194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827194 prefixEnd_827194 := by exact prefixLift 827194
  have htrace : WordTrace (prefixWord ++ tailWord_827194) baseStart_827194 baseEnd_827194 := by
    simpa [prefixWord, tailWord_827194, baseEnd_827194] using wordTrace_append hprefix tailTrace_827194
  have hstable : (prefixWord ++ tailWord_827194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827194).length < 2 ^ (prefixWord ++ tailWord_827194).sum := by decide
  have hdescent : baseEnd_827194 < baseStart_827194 := by decide
  rcases family_descends (prefixWord ++ tailWord_827194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827197 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 2]
def baseStart_827197 : Nat := 118140960795 + 827197 * 2 ^ 59
def prefixEnd_827197 : Nat := 4983230072969 + 3 ^ 40 * 827197 * 2
def baseEnd_827197 : Nat := 377555250628715841451819

theorem tailTrace_827197 : CollatzResearch.WordTrace tailWord_827197 prefixEnd_827197 377555250628715841451819 := by
  unfold tailWord_827197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30170353184214017845311845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20113568789476011896874563 30170353184214017845311845)
  ·
    refine ⟨5656941222040128345995971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30170353184214017845311845 5656941222040128345995971)
    ·
      refine ⟨8485411833060192518993957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656941222040128345995971 8485411833060192518993957)
      ·
        refine ⟨1591014718698786097311367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8485411833060192518993957 1591014718698786097311367)
        ·
          refine ⟨2386522078048179145967051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591014718698786097311367 2386522078048179145967051)
          ·
            refine ⟨3579783117072268718950577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386522078048179145967051 3579783117072268718950577)
            ·
              refine ⟨2684837337804201539212933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579783117072268718950577 2684837337804201539212933)
              ·
                refine ⟨503407000838287788602425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2684837337804201539212933 503407000838287788602425)
                ·
                  refine ⟨377555250628715841451819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503407000838287788602425 377555250628715841451819)
                  ·
                    rfl

theorem cell20_827197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_827197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827197 prefixEnd_827197 := by exact prefixLift 827197
  have htrace : WordTrace (prefixWord ++ tailWord_827197) baseStart_827197 baseEnd_827197 := by
    simpa [prefixWord, tailWord_827197, baseEnd_827197] using wordTrace_append hprefix tailTrace_827197
  have hstable : (prefixWord ++ tailWord_827197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827197).length < 2 ^ (prefixWord ++ tailWord_827197).sum := by decide
  have hdescent : baseEnd_827197 < baseStart_827197 := by decide
  rcases family_descends (prefixWord ++ tailWord_827197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827242 : List Nat := [3, 1, 3, 4, 1, 2, 6]
def baseStart_827242 : Nat := 118140960795 + 827242 * 2 ^ 59
def prefixEnd_827242 : Nat := 4983230072969 + 3 ^ 40 * 827242 * 2
def baseEnd_827242 : Nat := 41952865539432853883515

theorem tailTrace_827242 : CollatzResearch.WordTrace tailWord_827242 prefixEnd_827242 41952865539432853883515 := by
  unfold tailWord_827242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542998617262747632674995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20114662979367327020466653 7542998617262747632674995)
  ·
    refine ⟨11314497925894121449012493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7542998617262747632674995 11314497925894121449012493)
    ·
      refine ⟨4242936722210295543379685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11314497925894121449012493 4242936722210295543379685)
      ·
        refine ⟨795550635414430414383691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4242936722210295543379685 795550635414430414383691)
        ·
          refine ⟨1193325953121645621575537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795550635414430414383691 1193325953121645621575537)
          ·
            refine ⟨894994464841234216181653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193325953121645621575537 894994464841234216181653)
            ·
              refine ⟨41952865539432853883515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 894994464841234216181653 41952865539432853883515)
              ·
                rfl

theorem cell20_827242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_827242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827242 prefixEnd_827242 := by exact prefixLift 827242
  have htrace : WordTrace (prefixWord ++ tailWord_827242) baseStart_827242 baseEnd_827242 := by
    simpa [prefixWord, tailWord_827242, baseEnd_827242] using wordTrace_append hprefix tailTrace_827242
  have hstable : (prefixWord ++ tailWord_827242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827242).length < 2 ^ (prefixWord ++ tailWord_827242).sum := by decide
  have hdescent : baseEnd_827242 < baseStart_827242 := by decide
  rcases family_descends (prefixWord ++ tailWord_827242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827349 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 2]
def baseStart_827349 : Nat := 118140960795 + 827349 * 2 ^ 59
def prefixEnd_827349 : Nat := 4983230072969 + 3 ^ 40 * 827349 * 2
def baseEnd_827349 : Nat := 377624627570478868384531

theorem tailTrace_827349 : CollatzResearch.WordTrace tailWord_827349 prefixEnd_827349 377624627570478868384531 := by
  unfold tailWord_827349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175897079663347804845101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20117264719775565203230067 30175897079663347804845101)
  ·
    refine ⟨11315961404873755426816913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30175897079663347804845101 11315961404873755426816913)
    ·
      refine ⟨8486971053655316570112685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11315961404873755426816913 8486971053655316570112685)
      ·
        refine ⟨3182614145120743713792257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8486971053655316570112685 3182614145120743713792257)
        ·
          refine ⟨2386960608840557785344193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182614145120743713792257 2386960608840557785344193)
          ·
            refine ⟨1790220456630418339008145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386960608840557785344193 1790220456630418339008145)
            ·
              refine ⟨1342665342472813754256109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790220456630418339008145 1342665342472813754256109)
              ·
                refine ⟨503499503427305157846041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1342665342472813754256109 503499503427305157846041)
                ·
                  refine ⟨377624627570478868384531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503499503427305157846041 377624627570478868384531)
                  ·
                    rfl

theorem cell20_827349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_827349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827349 prefixEnd_827349 := by exact prefixLift 827349
  have htrace : WordTrace (prefixWord ++ tailWord_827349) baseStart_827349 baseEnd_827349 := by
    simpa [prefixWord, tailWord_827349, baseEnd_827349] using wordTrace_append hprefix tailTrace_827349
  have hstable : (prefixWord ++ tailWord_827349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827349).length < 2 ^ (prefixWord ++ tailWord_827349).sum := by decide
  have hdescent : baseEnd_827349 < baseStart_827349 := by decide
  rcases family_descends (prefixWord ++ tailWord_827349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827363 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_827363 : Nat := 118140960795 + 827363 * 2 ^ 59
def prefixEnd_827363 : Nat := 4983230072969 + 3 ^ 40 * 827363 * 2
def baseEnd_827363 : Nat := 377631017551957041917807

theorem tailTrace_827363 : CollatzResearch.WordTrace tailWord_827363 prefixEnd_827363 377631017551957041917807 := by
  unfold tailWord_827363
  simp only [CollatzResearch.WordTrace]
  refine ⟨30176407701612628195854743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20117605134408418797236495 30176407701612628195854743)
  ·
    refine ⟨45264611552418942293782115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30176407701612628195854743 45264611552418942293782115)
    ·
      refine ⟨67896917328628413440673173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45264611552418942293782115 67896917328628413440673173)
      ·
        refine ⟨3182667999779456880031555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67896917328628413440673173 3182667999779456880031555)
        ·
          refine ⟨4774001999669185320047333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182667999779456880031555 4774001999669185320047333)
          ·
            refine ⟨895125374937972247508875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4774001999669185320047333 895125374937972247508875)
            ·
              refine ⟨1342688062406958371263313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895125374937972247508875 1342688062406958371263313)
              ·
                refine ⟨1007016046805218778447485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342688062406958371263313 1007016046805218778447485)
                ·
                  refine ⟨377631017551957041917807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007016046805218778447485 377631017551957041917807)
                  ·
                    rfl

theorem cell20_827363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_827363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827363 prefixEnd_827363 := by exact prefixLift 827363
  have htrace : WordTrace (prefixWord ++ tailWord_827363) baseStart_827363 baseEnd_827363 := by
    simpa [prefixWord, tailWord_827363, baseEnd_827363] using wordTrace_append hprefix tailTrace_827363
  have hstable : (prefixWord ++ tailWord_827363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827363).length < 2 ^ (prefixWord ++ tailWord_827363).sum := by decide
  have hdescent : baseEnd_827363 < baseStart_827363 := by decide
  rcases family_descends (prefixWord ++ tailWord_827363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827370 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_827370 : Nat := 118140960795 + 827370 * 2 ^ 59
def prefixEnd_827370 : Nat := 4983230072969 + 3 ^ 40 * 827370 * 2
def baseEnd_827370 : Nat := 377634212542696128684445

theorem tailTrace_827370 : CollatzResearch.WordTrace tailWord_827370 prefixEnd_827370 377634212542696128684445 := by
  unfold tailWord_827370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544165753146817097839891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20117775341724845594239709 7544165753146817097839891)
  ·
    refine ⟨11316248629720225646759837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7544165753146817097839891 11316248629720225646759837)
    ·
      refine ⟨4243593236145084617534939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11316248629720225646759837 4243593236145084617534939)
      ·
        refine ⟨6365389854217626926302409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243593236145084617534939 6365389854217626926302409)
        ·
          refine ⟨4774042390663220194726807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365389854217626926302409 4774042390663220194726807)
          ·
            refine ⟨7161063585994830292090211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774042390663220194726807 7161063585994830292090211)
            ·
              refine ⟨10741595378992245438135317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161063585994830292090211 10741595378992245438135317)
              ·
                refine ⟨503512283390261504912593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10741595378992245438135317 503512283390261504912593)
                ·
                  refine ⟨377634212542696128684445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503512283390261504912593 377634212542696128684445)
                  ·
                    rfl

theorem cell20_827370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_827370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827370 prefixEnd_827370 := by exact prefixLift 827370
  have htrace : WordTrace (prefixWord ++ tailWord_827370) baseStart_827370 baseEnd_827370 := by
    simpa [prefixWord, tailWord_827370, baseEnd_827370] using wordTrace_append hprefix tailTrace_827370
  have hstable : (prefixWord ++ tailWord_827370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827370).length < 2 ^ (prefixWord ++ tailWord_827370).sum := by decide
  have hdescent : baseEnd_827370 < baseStart_827370 := by decide
  rcases family_descends (prefixWord ++ tailWord_827370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827415 : List Nat := [1, 1, 3, 5, 2, 2, 6]
def baseStart_827415 : Nat := 118140960795 + 827415 * 2 ^ 59
def prefixEnd_827415 : Nat := 4983230072969 + 3 ^ 40 * 827415 * 2
def baseEnd_827415 : Nat := 41961639085430663576029

theorem tailTrace_827415 : CollatzResearch.WordTrace tailWord_827415 prefixEnd_827415 41961639085430663576029 := by
  unfold tailWord_827415
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178304297424241076747699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20118869531616160717831799 30178304297424241076747699)
  ·
    refine ⟨45267456446136361615121549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30178304297424241076747699 45267456446136361615121549)
    ·
      refine ⟨16975296167301135605670581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45267456446136361615121549 16975296167301135605670581)
      ·
        refine ⟨1591434015684481463031617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16975296167301135605670581 1591434015684481463031617)
        ·
          refine ⟨1193575511763361097273713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591434015684481463031617 1193575511763361097273713)
          ·
            refine ⟨895181633822520822955285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193575511763361097273713 895181633822520822955285)
            ·
              refine ⟨41961639085430663576029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 895181633822520822955285 41961639085430663576029)
              ·
                rfl

theorem cell20_827415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_827415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827415 prefixEnd_827415 := by exact prefixLift 827415
  have htrace : WordTrace (prefixWord ++ tailWord_827415) baseStart_827415 baseEnd_827415 := by
    simpa [prefixWord, tailWord_827415, baseEnd_827415] using wordTrace_append hprefix tailTrace_827415
  have hstable : (prefixWord ++ tailWord_827415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827415).length < 2 ^ (prefixWord ++ tailWord_827415).sum := by decide
  have hdescent : baseEnd_827415 < baseStart_827415 := by decide
  rcases family_descends (prefixWord ++ tailWord_827415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827425 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 4]
def baseStart_827425 : Nat := 118140960795 + 827425 * 2 ^ 59
def prefixEnd_827425 : Nat := 4983230072969 + 3 ^ 40 * 827425 * 2
def baseEnd_827425 : Nat := 377659316041360381850887

theorem tailTrace_827425 : CollatzResearch.WordTrace tailWord_827425 prefixEnd_827425 377659316041360381850887 := by
  unfold tailWord_827425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178669027388012784611729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20119112684925341856407819 30178669027388012784611729)
  ·
    refine ⟨22634001770541009588458797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30178669027388012784611729 22634001770541009588458797)
    ·
      refine ⟨8487750663952878595672049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22634001770541009588458797 8487750663952878595672049)
      ·
        refine ⟨6365812997964658946754037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8487750663952878595672049 6365812997964658946754037)
        ·
          refine ⟨596794968559186776258191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6365812997964658946754037 596794968559186776258191)
          ·
            refine ⟨895192452838780164387287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596794968559186776258191 895192452838780164387287)
            ·
              refine ⟨1342788679258170246580931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895192452838780164387287 1342788679258170246580931)
              ·
                refine ⟨2014183018887255369871397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342788679258170246580931 2014183018887255369871397)
                ·
                  refine ⟨377659316041360381850887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014183018887255369871397 377659316041360381850887)
                  ·
                    rfl

theorem cell20_827425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_827425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827425 prefixEnd_827425 := by exact prefixLift 827425
  have htrace : WordTrace (prefixWord ++ tailWord_827425) baseStart_827425 baseEnd_827425 := by
    simpa [prefixWord, tailWord_827425, baseEnd_827425] using wordTrace_append hprefix tailTrace_827425
  have hstable : (prefixWord ++ tailWord_827425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827425).length < 2 ^ (prefixWord ++ tailWord_827425).sum := by decide
  have hdescent : baseEnd_827425 < baseStart_827425 := by decide
  rcases family_descends (prefixWord ++ tailWord_827425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827429 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_827429 : Nat := 118140960795 + 827429 * 2 ^ 59
def prefixEnd_827429 : Nat := 4983230072969 + 3 ^ 40 * 827429 * 2
def baseEnd_827429 : Nat := 377661141750354145717537

theorem tailTrace_827429 : CollatzResearch.WordTrace tailWord_827429 prefixEnd_827429 377661141750354145717537 := by
  unfold tailWord_827429
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178814919373521467757341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20119209946249014311838227 30178814919373521467757341)
  ·
    refine ⟨11317055594765070550409003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30178814919373521467757341 11317055594765070550409003)
    ·
      refine ⟨16975583392147605825613505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317055594765070550409003 16975583392147605825613505)
      ·
        refine ⟨12731687544110704369210129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16975583392147605825613505 12731687544110704369210129)
        ·
          refine ⟨9548765658083028276907597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12731687544110704369210129 9548765658083028276907597)
          ·
            refine ⟨3580787121781135603840349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9548765658083028276907597 3580787121781135603840349)
            ·
              refine ⟨1342795170667925851440131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3580787121781135603840349 1342795170667925851440131)
              ·
                refine ⟨2014192756001888777160197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342795170667925851440131 2014192756001888777160197)
                ·
                  refine ⟨377661141750354145717537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014192756001888777160197 377661141750354145717537)
                  ·
                    rfl

theorem cell20_827429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_827429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827429 prefixEnd_827429 := by exact prefixLift 827429
  have htrace : WordTrace (prefixWord ++ tailWord_827429) baseStart_827429 baseEnd_827429 := by
    simpa [prefixWord, tailWord_827429, baseEnd_827429] using wordTrace_append hprefix tailTrace_827429
  have hstable : (prefixWord ++ tailWord_827429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827429).length < 2 ^ (prefixWord ++ tailWord_827429).sum := by decide
  have hdescent : baseEnd_827429 < baseStart_827429 := by decide
  rcases family_descends (prefixWord ++ tailWord_827429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827432 : List Nat := [2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_827432 : Nat := 118140960795 + 827432 * 2 ^ 59
def prefixEnd_827432 : Nat := 4983230072969 + 3 ^ 40 * 827432 * 2
def baseEnd_827432 : Nat := 125887503677366489539175

theorem tailTrace_827432 : CollatzResearch.WordTrace tailWord_827432 prefixEnd_827432 125887503677366489539175 := by
  unfold tailWord_827432
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089462169181326490058275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20119282892241768653411033 15089462169181326490058275)
  ·
    refine ⟨22634193253771989735087413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15089462169181326490058275 22634193253771989735087413)
    ·
      refine ⟨2121955617541124037664445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22634193253771989735087413 2121955617541124037664445)
      ·
        refine ⟨795733356577921514124167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2121955617541124037664445 795733356577921514124167)
        ·
          refine ⟨1193600034866882271186251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795733356577921514124167 1193600034866882271186251)
          ·
            refine ⟨1790400052300323406779377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193600034866882271186251 1790400052300323406779377)
            ·
              refine ⟨1342800039225242555084533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790400052300323406779377 1342800039225242555084533)
              ·
                refine ⟨125887503677366489539175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1342800039225242555084533 125887503677366489539175)
                ·
                  rfl

theorem cell20_827432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_827432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827432 prefixEnd_827432 := by exact prefixLift 827432
  have htrace : WordTrace (prefixWord ++ tailWord_827432) baseStart_827432 baseEnd_827432 := by
    simpa [prefixWord, tailWord_827432, baseEnd_827432] using wordTrace_append hprefix tailTrace_827432
  have hstable : (prefixWord ++ tailWord_827432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827432).length < 2 ^ (prefixWord ++ tailWord_827432).sum := by decide
  have hdescent : baseEnd_827432 < baseStart_827432 := by decide
  rcases family_descends (prefixWord ++ tailWord_827432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827450 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_827450 : Nat := 118140960795 + 827450 * 2 ^ 59
def prefixEnd_827450 : Nat := 4983230072969 + 3 ^ 40 * 827450 * 2
def baseEnd_827450 : Nat := 377670726722571406017451

theorem tailTrace_827450 : CollatzResearch.WordTrace tailWord_827450 prefixEnd_827450 377670726722571406017451 := by
  unfold tailWord_827450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544895213074360513567951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20119720568198294702847869 7544895213074360513567951)
  ·
    refine ⟨11317342819611540770351927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7544895213074360513567951 11317342819611540770351927)
    ·
      refine ⟨16976014229417311155527891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317342819611540770351927 16976014229417311155527891)
      ·
        refine ⟨25464021344125966733291837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16976014229417311155527891 25464021344125966733291837)
        ·
          refine ⟨9549008004047237524984439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25464021344125966733291837 9549008004047237524984439)
          ·
            refine ⟨14323512006070856287476659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549008004047237524984439 14323512006070856287476659)
            ·
              refine ⟨21485268009106284431214989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14323512006070856287476659 21485268009106284431214989)
              ·
                refine ⟨8056975503414856661705621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21485268009106284431214989 8056975503414856661705621)
                ·
                  refine ⟨377670726722571406017451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8056975503414856661705621 377670726722571406017451)
                  ·
                    rfl

theorem cell20_827450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_827450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827450 prefixEnd_827450 := by exact prefixLift 827450
  have htrace : WordTrace (prefixWord ++ tailWord_827450) baseStart_827450 baseEnd_827450 := by
    simpa [prefixWord, tailWord_827450, baseEnd_827450] using wordTrace_append hprefix tailTrace_827450
  have hstable : (prefixWord ++ tailWord_827450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827450).length < 2 ^ (prefixWord ++ tailWord_827450).sum := by decide
  have hdescent : baseEnd_827450 < baseStart_827450 := by decide
  rcases family_descends (prefixWord ++ tailWord_827450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827474 : List Nat := [3, 2, 2, 1, 4, 8]
def baseStart_827474 : Nat := 118140960795 + 827474 * 2 ^ 59
def prefixEnd_827474 : Nat := 4983230072969 + 3 ^ 40 * 827474 * 2
def baseEnd_827474 : Nat := 13988210406538295896939

theorem tailTrace_827474 : CollatzResearch.WordTrace tailWord_827474 prefixEnd_827474 13988210406538295896939 := by
  unfold tailWord_827474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7545114051052623538286369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20120304136140329435430317 7545114051052623538286369)
  ·
    refine ⟨5658835538289467653714777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7545114051052623538286369 5658835538289467653714777)
    ·
      refine ⟨4244126653717100740286083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5658835538289467653714777 4244126653717100740286083)
      ·
        refine ⟨6366189980575651110429125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244126653717100740286083 6366189980575651110429125)
        ·
          refine ⟨1193660621357934583205461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6366189980575651110429125 1193660621357934583205461)
          ·
            refine ⟨13988210406538295896939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1193660621357934583205461 13988210406538295896939)
            ·
              rfl

theorem cell20_827474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 8].length) (baseStart_827474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827474 prefixEnd_827474 := by exact prefixLift 827474
  have htrace : WordTrace (prefixWord ++ tailWord_827474) baseStart_827474 baseEnd_827474 := by
    simpa [prefixWord, tailWord_827474, baseEnd_827474] using wordTrace_append hprefix tailTrace_827474
  have hstable : (prefixWord ++ tailWord_827474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827474).length < 2 ^ (prefixWord ++ tailWord_827474).sum := by decide
  have hdescent : baseEnd_827474 < baseStart_827474 := by decide
  rcases family_descends (prefixWord ++ tailWord_827474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827553 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 3]
def baseStart_827553 : Nat := 118140960795 + 827553 * 2 ^ 59
def prefixEnd_827553 : Nat := 4983230072969 + 3 ^ 40 * 827553 * 2
def baseEnd_827553 : Nat := 377717738729160825583697

theorem tailTrace_827553 : CollatzResearch.WordTrace tailWord_827553 prefixEnd_827553 377717738729160825583697 := by
  unfold tailWord_827553
  simp only [CollatzResearch.WordTrace]
  refine ⟨30183337570924290645271313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20122225047282860430180875 30183337570924290645271313)
  ·
    refine ⟨22637503178193217983953485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30183337570924290645271313 22637503178193217983953485)
    ·
      refine ⟨8489063691822456743982557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22637503178193217983953485 8489063691822456743982557)
      ·
        refine ⟨3183398884433421278993459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8489063691822456743982557 3183398884433421278993459)
        ·
          refine ⟨4775098326650131918490189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183398884433421278993459 4775098326650131918490189)
          ·
            refine ⟨1790661872493799469433821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4775098326650131918490189 1790661872493799469433821)
            ·
              refine ⟨671498202185174801037683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1790661872493799469433821 671498202185174801037683)
              ·
                refine ⟨1007247303277762201556525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671498202185174801037683 1007247303277762201556525)
                ·
                  refine ⟨377717738729160825583697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007247303277762201556525 377717738729160825583697)
                  ·
                    rfl

theorem cell20_827553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_827553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827553 prefixEnd_827553 := by exact prefixLift 827553
  have htrace : WordTrace (prefixWord ++ tailWord_827553) baseStart_827553 baseEnd_827553 := by
    simpa [prefixWord, tailWord_827553, baseEnd_827553] using wordTrace_append hprefix tailTrace_827553
  have hstable : (prefixWord ++ tailWord_827553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827553).length < 2 ^ (prefixWord ++ tailWord_827553).sum := by decide
  have hdescent : baseEnd_827553 < baseStart_827553 := by decide
  rcases family_descends (prefixWord ++ tailWord_827553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827573 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 2]
def baseStart_827573 : Nat := 118140960795 + 827573 * 2 ^ 59
def prefixEnd_827573 : Nat := 4983230072969 + 3 ^ 40 * 827573 * 2
def baseEnd_827573 : Nat := 377726867274129644916949

theorem tailTrace_827573 : CollatzResearch.WordTrace tailWord_827573 prefixEnd_827573 377726867274129644916949 := by
  unfold tailWord_827573
  simp only [CollatzResearch.WordTrace]
  refine ⟨30184067030851834060999373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20122711353901222707332915 30184067030851834060999373)
  ·
    refine ⟨11319025136569437772874765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30184067030851834060999373 11319025136569437772874765)
    ·
      refine ⟨4244634426213539164828037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11319025136569437772874765 4244634426213539164828037)
      ·
        refine ⟨795868954915038593405257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4244634426213539164828037 795868954915038593405257)
        ·
          refine ⟨596901716186278945053943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795868954915038593405257 596901716186278945053943)
          ·
            refine ⟨895352574279418417580915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596901716186278945053943 895352574279418417580915)
            ·
              refine ⟨1343028861419127626371373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895352574279418417580915 1343028861419127626371373)
              ·
                refine ⟨503635823032172859889265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343028861419127626371373 503635823032172859889265)
                ·
                  refine ⟨377726867274129644916949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503635823032172859889265 377726867274129644916949)
                  ·
                    rfl

theorem cell20_827573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_827573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827573 prefixEnd_827573 := by exact prefixLift 827573
  have htrace : WordTrace (prefixWord ++ tailWord_827573) baseStart_827573 baseEnd_827573 := by
    simpa [prefixWord, tailWord_827573, baseEnd_827573] using wordTrace_append hprefix tailTrace_827573
  have hstable : (prefixWord ++ tailWord_827573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827573).length < 2 ^ (prefixWord ++ tailWord_827573).sum := by decide
  have hdescent : baseEnd_827573 < baseStart_827573 := by decide
  rcases family_descends (prefixWord ++ tailWord_827573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827588 : List Nat := [2, 3, 3, 1, 2, 1, 8]
def baseStart_827588 : Nat := 118140960795 + 827588 * 2 ^ 59
def prefixEnd_827588 : Nat := 4983230072969 + 3 ^ 40 * 827588 * 2
def baseEnd_827588 : Nat := 41970412631428473268543

theorem tailTrace_827588 : CollatzResearch.WordTrace tailWord_827588 prefixEnd_827588 41970412631428473268543 := by
  unfold tailWord_827588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092307062898745811397709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20123076083864994415196945 15092307062898745811397709)
  ·
    refine ⟨5659615148587029679274141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15092307062898745811397709 5659615148587029679274141)
    ·
      refine ⟨2122355680720136129727803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5659615148587029679274141 2122355680720136129727803)
      ·
        refine ⟨3183533521080204194591705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122355680720136129727803 3183533521080204194591705)
        ·
          refine ⟨2387650140810153145943779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3183533521080204194591705 2387650140810153145943779)
          ·
            refine ⟨3581475211215229718915669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387650140810153145943779 3581475211215229718915669)
            ·
              refine ⟨41970412631428473268543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3581475211215229718915669 41970412631428473268543)
              ·
                rfl

theorem cell20_827588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_827588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827588 prefixEnd_827588 := by exact prefixLift 827588
  have htrace : WordTrace (prefixWord ++ tailWord_827588) baseStart_827588 baseEnd_827588 := by
    simpa [prefixWord, tailWord_827588, baseEnd_827588] using wordTrace_append hprefix tailTrace_827588
  have hstable : (prefixWord ++ tailWord_827588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827588).length < 2 ^ (prefixWord ++ tailWord_827588).sum := by decide
  have hdescent : baseEnd_827588 < baseStart_827588 := by decide
  rcases family_descends (prefixWord ++ tailWord_827588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827595 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_827595 : Nat := 118140960795 + 827595 * 2 ^ 59
def prefixEnd_827595 : Nat := 4983230072969 + 3 ^ 40 * 827595 * 2
def baseEnd_827595 : Nat := 377736908673595346183525

theorem tailTrace_827595 : CollatzResearch.WordTrace tailWord_827595 prefixEnd_827595 377736908673595346183525 := by
  unfold tailWord_827595
  simp only [CollatzResearch.WordTrace]
  refine ⟨30184869436772131818300239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20123246291181421212200159 30184869436772131818300239)
  ·
    refine ⟨45277304155158197727450359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30184869436772131818300239 45277304155158197727450359)
    ·
      refine ⟨67915956232737296591175539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45277304155158197727450359 67915956232737296591175539)
      ·
        refine ⟨101873934349105944886763309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67915956232737296591175539 101873934349105944886763309)
        ·
          refine ⟨38202725380914729332536241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101873934349105944886763309 38202725380914729332536241)
          ·
            refine ⟨28652044035686046999402181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38202725380914729332536241 28652044035686046999402181)
            ·
              refine ⟨5372258256691133812387909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28652044035686046999402181 5372258256691133812387909)
              ·
                refine ⟨1007298423129587589822733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5372258256691133812387909 1007298423129587589822733)
                ·
                  refine ⟨377736908673595346183525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007298423129587589822733 377736908673595346183525)
                  ·
                    rfl

theorem cell20_827595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_827595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827595 prefixEnd_827595 := by exact prefixLift 827595
  have htrace : WordTrace (prefixWord ++ tailWord_827595) baseStart_827595 baseEnd_827595 := by
    simpa [prefixWord, tailWord_827595, baseEnd_827595] using wordTrace_append hprefix tailTrace_827595
  have hstable : (prefixWord ++ tailWord_827595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827595).length < 2 ^ (prefixWord ++ tailWord_827595).sum := by decide
  have hdescent : baseEnd_827595 < baseStart_827595 := by decide
  rcases family_descends (prefixWord ++ tailWord_827595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827598 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_827598 : Nat := 118140960795 + 827598 * 2 ^ 59
def prefixEnd_827598 : Nat := 4983230072969 + 3 ^ 40 * 827598 * 2
def baseEnd_827598 : Nat := 377738277955340669083513

theorem tailTrace_827598 : CollatzResearch.WordTrace tailWord_827598 prefixEnd_827598 377738277955340669083513 := by
  unfold tailWord_827598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773122356970157916332431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20123319237174175553772965 3773122356970157916332431)
  ·
    refine ⟨5659683535455236874498647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773122356970157916332431 5659683535455236874498647)
    ·
      refine ⟨8489525303182855311747971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5659683535455236874498647 8489525303182855311747971)
      ·
        refine ⟨12734287954774282967621957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489525303182855311747971 12734287954774282967621957)
        ·
          refine ⟨2387678991520178056429117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12734287954774282967621957 2387678991520178056429117)
          ·
            refine ⟨895379621820066771160919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2387678991520178056429117 895379621820066771160919)
            ·
              refine ⟨1343069432730100156741379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895379621820066771160919 1343069432730100156741379)
              ·
                refine ⟨2014604149095150235112069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343069432730100156741379 2014604149095150235112069)
                ·
                  refine ⟨377738277955340669083513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014604149095150235112069 377738277955340669083513)
                  ·
                    rfl

theorem cell20_827598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_827598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827598 prefixEnd_827598 := by exact prefixLift 827598
  have htrace : WordTrace (prefixWord ++ tailWord_827598) baseStart_827598 baseEnd_827598 := by
    simpa [prefixWord, tailWord_827598, baseEnd_827598] using wordTrace_append hprefix tailTrace_827598
  have hstable : (prefixWord ++ tailWord_827598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827598).length < 2 ^ (prefixWord ++ tailWord_827598).sum := by decide
  have hdescent : baseEnd_827598 < baseStart_827598 := by decide
  rcases family_descends (prefixWord ++ tailWord_827598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827605 : List Nat := [1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_827605 : Nat := 118140960795 + 827605 * 2 ^ 59
def prefixEnd_827605 : Nat := 4983230072969 + 3 ^ 40 * 827605 * 2
def baseEnd_827605 : Nat := 125913824315359918616717

theorem tailTrace_827605 : CollatzResearch.WordTrace tailWord_827605 prefixEnd_827605 125913824315359918616717 := by
  unfold tailWord_827605
  simp only [CollatzResearch.WordTrace]
  refine ⟨30185234166735903526164269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20123489444490602350776179 30185234166735903526164269)
  ·
    refine ⟨11319462812525963822311601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30185234166735903526164269 11319462812525963822311601)
    ·
      refine ⟨8489597109394472866733701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11319462812525963822311601 8489597109394472866733701)
      ·
        refine ⟨1591799458011463662512569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8489597109394472866733701 1591799458011463662512569)
        ·
          refine ⟨1193849593508597746884427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591799458011463662512569 1193849593508597746884427)
          ·
            refine ⟨1790774390262896620326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193849593508597746884427 1790774390262896620326641)
            ·
              refine ⟨1343080792697172465244981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790774390262896620326641 1343080792697172465244981)
              ·
                refine ⟨125913824315359918616717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343080792697172465244981 125913824315359918616717)
                ·
                  rfl

theorem cell20_827605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_827605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827605 prefixEnd_827605 := by exact prefixLift 827605
  have htrace : WordTrace (prefixWord ++ tailWord_827605) baseStart_827605 baseEnd_827605 := by
    simpa [prefixWord, tailWord_827605, baseEnd_827605] using wordTrace_append hprefix tailTrace_827605
  have hstable : (prefixWord ++ tailWord_827605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827605).length < 2 ^ (prefixWord ++ tailWord_827605).sum := by decide
  have hdescent : baseEnd_827605 < baseStart_827605 := by decide
  rcases family_descends (prefixWord ++ tailWord_827605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827609 : List Nat := [1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_827609 : Nat := 118140960795 + 827609 * 2 ^ 59
def prefixEnd_827609 : Nat := 4983230072969 + 3 ^ 40 * 827609 * 2
def baseEnd_827609 : Nat := 125914432885024506572267

theorem tailTrace_827609 : CollatzResearch.WordTrace tailWord_827609 prefixEnd_827609 125914432885024506572267 := by
  unfold tailWord_827609
  simp only [CollatzResearch.WordTrace]
  refine ⟨30185380058721412209309881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20123586705814274806206587 30185380058721412209309881)
  ·
    refine ⟨22639035044041059156982411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30185380058721412209309881 22639035044041059156982411)
    ·
      refine ⟨33958552566061588735473617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22639035044041059156982411 33958552566061588735473617)
      ·
        refine ⟨25468914424546191551605213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33958552566061588735473617 25468914424546191551605213)
        ·
          refine ⟨9550842909204821831851955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25468914424546191551605213 9550842909204821831851955)
          ·
            refine ⟨14326264363807232747777933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550842909204821831851955 14326264363807232747777933)
            ·
              refine ⟨5372349136427712280416725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14326264363807232747777933 5372349136427712280416725)
              ·
                refine ⟨125914432885024506572267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5372349136427712280416725 125914432885024506572267)
                ·
                  rfl

theorem cell20_827609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_827609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827609 prefixEnd_827609 := by exact prefixLift 827609
  have htrace : WordTrace (prefixWord ++ tailWord_827609) baseStart_827609 baseEnd_827609 := by
    simpa [prefixWord, tailWord_827609, baseEnd_827609] using wordTrace_append hprefix tailTrace_827609
  have hstable : (prefixWord ++ tailWord_827609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827609).length < 2 ^ (prefixWord ++ tailWord_827609).sum := by decide
  have hdescent : baseEnd_827609 < baseStart_827609 := by decide
  rcases family_descends (prefixWord ++ tailWord_827609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827687 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 2]
def baseStart_827687 : Nat := 118140960795 + 827687 * 2 ^ 59
def prefixEnd_827687 : Nat := 4983230072969 + 3 ^ 40 * 827687 * 2
def baseEnd_827687 : Nat := 377778899980451915116483

theorem tailTrace_827687 : CollatzResearch.WordTrace tailWord_827687 prefixEnd_827687 377778899980451915116483 := by
  unfold tailWord_827687
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188224952438831530649315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20125483301625887687099543 30188224952438831530649315)
  ·
    refine ⟨45282337428658247295973973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188224952438831530649315 45282337428658247295973973)
    ·
      refine ⟨530652391742088835499695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 45282337428658247295973973 530652391742088835499695)
      ·
        refine ⟨795978587613133253249543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530652391742088835499695 795978587613133253249543)
        ·
          refine ⟨1193967881419699879874315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795978587613133253249543 1193967881419699879874315)
          ·
            refine ⟨1790951822129549819811473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193967881419699879874315 1790951822129549819811473)
            ·
              refine ⟨1343213866597162364858605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790951822129549819811473 1343213866597162364858605)
              ·
                refine ⟨503705199973935886821977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343213866597162364858605 503705199973935886821977)
                ·
                  refine ⟨377778899980451915116483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503705199973935886821977 377778899980451915116483)
                  ·
                    rfl

theorem cell20_827687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2].length) (baseStart_827687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827687 prefixEnd_827687 := by exact prefixLift 827687
  have htrace : WordTrace (prefixWord ++ tailWord_827687) baseStart_827687 baseEnd_827687 := by
    simpa [prefixWord, tailWord_827687, baseEnd_827687] using wordTrace_append hprefix tailTrace_827687
  have hstable : (prefixWord ++ tailWord_827687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827687).length < 2 ^ (prefixWord ++ tailWord_827687).sum := by decide
  have hdescent : baseEnd_827687 < baseStart_827687 := by decide
  rcases family_descends (prefixWord ++ tailWord_827687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827695 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 2]
def baseStart_827695 : Nat := 118140960795 + 827695 * 2 ^ 59
def prefixEnd_827695 : Nat := 4983230072969 + 3 ^ 40 * 827695 * 2
def baseEnd_827695 : Nat := 377782551398439442849783

theorem tailTrace_827695 : CollatzResearch.WordTrace tailWord_827695 prefixEnd_827695 377782551398439442849783 := by
  unfold tailWord_827695
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188516736409848896940539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20125677824273232597960359 30188516736409848896940539)
  ·
    refine ⟨45282775104614773345410809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188516736409848896940539 45282775104614773345410809)
    ·
      refine ⟨33962081328461080009058107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45282775104614773345410809 33962081328461080009058107)
      ·
        refine ⟨50943121992691620013587161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33962081328461080009058107 50943121992691620013587161)
        ·
          refine ⟨38207341494518715010190371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50943121992691620013587161 38207341494518715010190371)
          ·
            refine ⟨57311012241778072515285557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38207341494518715010190371 57311012241778072515285557)
            ·
              refine ⟨5372907397666694298308021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57311012241778072515285557 5372907397666694298308021)
              ·
                refine ⟨503710068531252590466377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5372907397666694298308021 503710068531252590466377)
                ·
                  refine ⟨377782551398439442849783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503710068531252590466377 377782551398439442849783)
                  ·
                    rfl

theorem cell20_827695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2].length) (baseStart_827695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827695 prefixEnd_827695 := by exact prefixLift 827695
  have htrace : WordTrace (prefixWord ++ tailWord_827695) baseStart_827695 baseEnd_827695 := by
    simpa [prefixWord, tailWord_827695, baseEnd_827695] using wordTrace_append hprefix tailTrace_827695
  have hstable : (prefixWord ++ tailWord_827695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827695).length < 2 ^ (prefixWord ++ tailWord_827695).sum := by decide
  have hdescent : baseEnd_827695 < baseStart_827695 := by decide
  rcases family_descends (prefixWord ++ tailWord_827695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827705 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_827705 : Nat := 118140960795 + 827705 * 2 ^ 59
def prefixEnd_827705 : Nat := 4983230072969 + 3 ^ 40 * 827705 * 2
def baseEnd_827705 : Nat := 377787115670923852516409

theorem tailTrace_827705 : CollatzResearch.WordTrace tailWord_827705 prefixEnd_827705 377787115670923852516409 := by
  unfold tailWord_827705
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188881466373620604804569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20125920977582413736536379 30188881466373620604804569)
  ·
    refine ⟨22641661099780215453603427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30188881466373620604804569 22641661099780215453603427)
    ·
      refine ⟨33962491649670323180405141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22641661099780215453603427 33962491649670323180405141)
      ·
        refine ⟨1591991796078296399081491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33962491649670323180405141 1591991796078296399081491)
        ·
          refine ⟨2387987694117444598622237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591991796078296399081491 2387987694117444598622237)
          ·
            refine ⟨895495385294041724483339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2387987694117444598622237 895495385294041724483339)
            ·
              refine ⟨1343243077941062586725009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895495385294041724483339 1343243077941062586725009)
              ·
                refine ⟨1007432308455796940043757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343243077941062586725009 1007432308455796940043757)
                ·
                  refine ⟨377787115670923852516409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007432308455796940043757 377787115670923852516409)
                  ·
                    rfl

theorem cell20_827705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_827705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827705 prefixEnd_827705 := by exact prefixLift 827705
  have htrace : WordTrace (prefixWord ++ tailWord_827705) baseStart_827705 baseEnd_827705 := by
    simpa [prefixWord, tailWord_827705, baseEnd_827705] using wordTrace_append hprefix tailTrace_827705
  have hstable : (prefixWord ++ tailWord_827705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827705).length < 2 ^ (prefixWord ++ tailWord_827705).sum := by decide
  have hdescent : baseEnd_827705 < baseStart_827705 := by decide
  rcases family_descends (prefixWord ++ tailWord_827705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827771 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_827771 : Nat := 118140960795 + 827771 * 2 ^ 59
def prefixEnd_827771 : Nat := 4983230072969 + 3 ^ 40 * 827771 * 2
def baseEnd_827771 : Nat := 377817239869320956316139

theorem tailTrace_827771 : CollatzResearch.WordTrace tailWord_827771 prefixEnd_827771 377817239869320956316139 := by
  unfold tailWord_827771
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191288684134513876707167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20127525789423009251138111 30191288684134513876707167)
  ·
    refine ⟨45286933026201770815060751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30191288684134513876707167 45286933026201770815060751)
    ·
      refine ⟨67930399539302656222591127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45286933026201770815060751 67930399539302656222591127)
      ·
        refine ⟨101895599308953984333886691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67930399539302656222591127 101895599308953984333886691)
        ·
          refine ⟨152843398963430976500830037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101895599308953984333886691 152843398963430976500830037)
          ·
            refine ⟨895566790801353377934551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 152843398963430976500830037 895566790801353377934551)
            ·
              refine ⟨1343350186202030066901827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895566790801353377934551 1343350186202030066901827)
              ·
                refine ⟨2015025279303045100352741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343350186202030066901827 2015025279303045100352741)
                ·
                  refine ⟨377817239869320956316139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015025279303045100352741 377817239869320956316139)
                  ·
                    rfl

theorem cell20_827771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_827771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827771 prefixEnd_827771 := by exact prefixLift 827771
  have htrace : WordTrace (prefixWord ++ tailWord_827771) baseStart_827771 baseEnd_827771 := by
    simpa [prefixWord, tailWord_827771, baseEnd_827771] using wordTrace_append hprefix tailTrace_827771
  have hstable : (prefixWord ++ tailWord_827771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827771).length < 2 ^ (prefixWord ++ tailWord_827771).sum := by decide
  have hdescent : baseEnd_827771 < baseStart_827771 := by decide
  rcases family_descends (prefixWord ++ tailWord_827771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827799 : List Nat := [1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_827799 : Nat := 118140960795 + 827799 * 2 ^ 59
def prefixEnd_827799 : Nat := 4983230072969 + 3 ^ 40 * 827799 * 2
def baseEnd_827799 : Nat := 125943339944092434460897

theorem tailTrace_827799 : CollatzResearch.WordTrace tailWord_827799 prefixEnd_827799 125943339944092434460897 := by
  unfold tailWord_827799
  simp only [CollatzResearch.WordTrace]
  refine ⟨30192309928033074658726451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20128206618688716439150967 30192309928033074658726451)
  ·
    refine ⟨45288464892049611988089677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30192309928033074658726451 45288464892049611988089677)
    ·
      refine ⟨16983174334518604495533629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45288464892049611988089677 16983174334518604495533629)
      ·
        refine ⟨6368690375444476685825111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16983174334518604495533629 6368690375444476685825111)
        ·
          refine ⟨9553035563166715028737667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368690375444476685825111 9553035563166715028737667)
          ·
            refine ⟨14329553344750072543106501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553035563166715028737667 14329553344750072543106501)
            ·
              refine ⟨2686791252140638601832469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14329553344750072543106501 2686791252140638601832469)
              ·
                refine ⟨125943339944092434460897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2686791252140638601832469 125943339944092434460897)
                ·
                  rfl

theorem cell20_827799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_827799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827799 prefixEnd_827799 := by exact prefixLift 827799
  have htrace : WordTrace (prefixWord ++ tailWord_827799) baseStart_827799 baseEnd_827799 := by
    simpa [prefixWord, tailWord_827799, baseEnd_827799] using wordTrace_append hprefix tailTrace_827799
  have hstable : (prefixWord ++ tailWord_827799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827799).length < 2 ^ (prefixWord ++ tailWord_827799).sum := by decide
  have hdescent : baseEnd_827799 < baseStart_827799 := by decide
  rcases family_descends (prefixWord ++ tailWord_827799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827816 : List Nat := [2, 1, 6, 1, 1, 9]
def baseStart_827816 : Nat := 118140960795 + 827816 * 2 ^ 59
def prefixEnd_827816 : Nat := 4983230072969 + 3 ^ 40 * 827816 * 2
def baseEnd_827816 : Nat := 13993991818351881474665

theorem tailTrace_827816 : CollatzResearch.WordTrace tailWord_827816 prefixEnd_827816 13993991818351881474665 := by
  unfold tailWord_827816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15096464984485743281047651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20128619979314324374730201 15096464984485743281047651)
  ·
    refine ⟨22644697476728614921571477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15096464984485743281047651 22644697476728614921571477)
    ·
      refine ⟨1061470194221653824448663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22644697476728614921571477 1061470194221653824448663)
      ·
        refine ⟨1592205291332480736672995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061470194221653824448663 1592205291332480736672995)
        ·
          refine ⟨2388307936998721105009493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592205291332480736672995 2388307936998721105009493)
          ·
            refine ⟨13993991818351881474665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2388307936998721105009493 13993991818351881474665)
            ·
              rfl

theorem cell20_827816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 9].length) (baseStart_827816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827816 prefixEnd_827816 := by exact prefixLift 827816
  have htrace : WordTrace (prefixWord ++ tailWord_827816) baseStart_827816 baseEnd_827816 := by
    simpa [prefixWord, tailWord_827816, baseEnd_827816] using wordTrace_append hprefix tailTrace_827816
  have hstable : (prefixWord ++ tailWord_827816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827816).length < 2 ^ (prefixWord ++ tailWord_827816).sum := by decide
  have hdescent : baseEnd_827816 < baseStart_827816 := by decide
  rcases family_descends (prefixWord ++ tailWord_827816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827818 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_827818 : Nat := 118140960795 + 827818 * 2 ^ 59
def prefixEnd_827818 : Nat := 4983230072969 + 3 ^ 40 * 827818 * 2
def baseEnd_827818 : Nat := 377838691949997681749281

theorem tailTrace_827818 : CollatzResearch.WordTrace tailWord_827818 prefixEnd_827818 377838691949997681749281 := by
  unfold tailWord_827818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548250728741060225917027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20128668609976160602445405 7548250728741060225917027)
  ·
    refine ⟨11322376093111590338875541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7548250728741060225917027 11322376093111590338875541)
    ·
      refine ⟨530736379364605797134791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11322376093111590338875541 530736379364605797134791)
      ·
        refine ⟨796104569046908695702187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530736379364605797134791 796104569046908695702187)
        ·
          refine ⟨1194156853570363043553281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796104569046908695702187 1194156853570363043553281)
          ·
            refine ⟨895617640177772282664961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194156853570363043553281 895617640177772282664961)
            ·
              refine ⟨671713230133329211998721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895617640177772282664961 671713230133329211998721)
              ·
                refine ⟨503784922599996908999041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671713230133329211998721 503784922599996908999041)
                ·
                  refine ⟨377838691949997681749281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503784922599996908999041 377838691949997681749281)
                  ·
                    rfl

theorem cell20_827818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_827818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827818 prefixEnd_827818 := by exact prefixLift 827818
  have htrace : WordTrace (prefixWord ++ tailWord_827818) baseStart_827818 baseEnd_827818 := by
    simpa [prefixWord, tailWord_827818, baseEnd_827818] using wordTrace_append hprefix tailTrace_827818
  have hstable : (prefixWord ++ tailWord_827818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827818).length < 2 ^ (prefixWord ++ tailWord_827818).sum := by decide
  have hdescent : baseEnd_827818 < baseStart_827818 := by decide
  rcases family_descends (prefixWord ++ tailWord_827818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827885 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_827885 : Nat := 118140960795 + 827885 * 2 ^ 59
def prefixEnd_827885 : Nat := 4983230072969 + 3 ^ 40 * 827885 * 2
def baseEnd_827885 : Nat := 377869272575643226515673

theorem tailTrace_827885 : CollatzResearch.WordTrace tailWord_827885 prefixEnd_827885 377869272575643226515673 := by
  unfold tailWord_827885
  simp only [CollatzResearch.WordTrace]
  refine ⟨30195446605721511346357109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20130297737147674230904739 30195446605721511346357109)
  ·
    refine ⟨2830823119286391688720979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30195446605721511346357109 2830823119286391688720979)
    ·
      refine ⟨4246234678929587533081469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830823119286391688720979 4246234678929587533081469)
      ·
        refine ⟨1592338004598595324905551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4246234678929587533081469 1592338004598595324905551)
        ·
          refine ⟨2388507006897892987358327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592338004598595324905551 2388507006897892987358327)
          ·
            refine ⟨3582760510346839481037491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388507006897892987358327 3582760510346839481037491)
            ·
              refine ⟨5374140765520259221556237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582760510346839481037491 5374140765520259221556237)
              ·
                refine ⟨2015302787070097208083589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374140765520259221556237 2015302787070097208083589)
                ·
                  refine ⟨377869272575643226515673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015302787070097208083589 377869272575643226515673)
                  ·
                    rfl

theorem cell20_827885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_827885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827885 prefixEnd_827885 := by exact prefixLift 827885
  have htrace : WordTrace (prefixWord ++ tailWord_827885) baseStart_827885 baseEnd_827885 := by
    simpa [prefixWord, tailWord_827885, baseEnd_827885] using wordTrace_append hprefix tailTrace_827885
  have hstable : (prefixWord ++ tailWord_827885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827885).length < 2 ^ (prefixWord ++ tailWord_827885).sum := by decide
  have hdescent : baseEnd_827885 < baseStart_827885 := by decide
  rcases family_descends (prefixWord ++ tailWord_827885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827937 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_827937 : Nat := 118140960795 + 827937 * 2 ^ 59
def prefixEnd_827937 : Nat := 4983230072969 + 3 ^ 40 * 827937 * 2
def baseEnd_827937 : Nat := 377893006792562156782127

theorem tailTrace_827937 : CollatzResearch.WordTrace tailWord_827937 prefixEnd_827937 377893006792562156782127 := by
  unfold tailWord_827937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30197343201533124227250065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20131562134355416151500043 30197343201533124227250065)
  ·
    refine ⟨22648007401149843170437549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30197343201533124227250065 22648007401149843170437549)
    ·
      refine ⟨8493002775431191188914081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22648007401149843170437549 8493002775431191188914081)
      ·
        refine ⟨6369752081573393391685561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8493002775431191188914081 6369752081573393391685561)
        ·
          refine ⟨4777314061180045043764171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6369752081573393391685561 4777314061180045043764171)
          ·
            refine ⟨7165971091770067565646257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777314061180045043764171 7165971091770067565646257)
            ·
              refine ⟨5374478318827550674234693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7165971091770067565646257 5374478318827550674234693)
              ·
                refine ⟨1007714684780165751419005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5374478318827550674234693 1007714684780165751419005)
                ·
                  refine ⟨377893006792562156782127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007714684780165751419005 377893006792562156782127)
                  ·
                    rfl

theorem cell20_827937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_827937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827937 prefixEnd_827937 := by exact prefixLift 827937
  have htrace : WordTrace (prefixWord ++ tailWord_827937) baseStart_827937 baseEnd_827937 := by
    simpa [prefixWord, tailWord_827937, baseEnd_827937] using wordTrace_append hprefix tailTrace_827937
  have hstable : (prefixWord ++ tailWord_827937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827937).length < 2 ^ (prefixWord ++ tailWord_827937).sum := by decide
  have hdescent : baseEnd_827937 < baseStart_827937 := by decide
  rcases family_descends (prefixWord ++ tailWord_827937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827950 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_827950 : Nat := 118140960795 + 827950 * 2 ^ 59
def prefixEnd_827950 : Nat := 4983230072969 + 3 ^ 40 * 827950 * 2
def baseEnd_827950 : Nat := 377898940346791889348741

theorem tailTrace_827950 : CollatzResearch.WordTrace tailWord_827950 prefixEnd_827950 377898940346791889348741 := by
  unfold tailWord_827950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774727168810753430934163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20131878233657351631648869 3774727168810753430934163)
  ·
    refine ⟨5662090753216130146401245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774727168810753430934163 5662090753216130146401245)
    ·
      refine ⟨2123284032456048804900467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5662090753216130146401245 2123284032456048804900467)
      ·
        refine ⟨3184926048684073207350701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123284032456048804900467 3184926048684073207350701)
        ·
          refine ⟨1194347268256527452756513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3184926048684073207350701 1194347268256527452756513)
          ·
            refine ⟨895760451192395589567385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194347268256527452756513 895760451192395589567385)
            ·
              refine ⟨671820338394296692175539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895760451192395589567385 671820338394296692175539)
              ·
                refine ⟨1007730507591445038263309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671820338394296692175539 1007730507591445038263309)
                ·
                  refine ⟨377898940346791889348741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007730507591445038263309 377898940346791889348741)
                  ·
                    rfl

theorem cell20_827950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_827950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827950 prefixEnd_827950 := by exact prefixLift 827950
  have htrace : WordTrace (prefixWord ++ tailWord_827950) baseStart_827950 baseEnd_827950 := by
    simpa [prefixWord, tailWord_827950, baseEnd_827950] using wordTrace_append hprefix tailTrace_827950
  have hstable : (prefixWord ++ tailWord_827950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827950).length < 2 ^ (prefixWord ++ tailWord_827950).sum := by decide
  have hdescent : baseEnd_827950 < baseStart_827950 := by decide
  rcases family_descends (prefixWord ++ tailWord_827950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827954 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_827954 : Nat := 118140960795 + 827954 * 2 ^ 59
def prefixEnd_827954 : Nat := 4983230072969 + 3 ^ 40 * 827954 * 2
def baseEnd_827954 : Nat := 377900766055785653215391

theorem tailTrace_827954 : CollatzResearch.WordTrace tailWord_827954 prefixEnd_827954 377900766055785653215391 := by
  unfold tailWord_827954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549490810617884032654729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20131975494981024087079277 7549490810617884032654729)
  ·
    refine ⟨5662118107963413024491047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7549490810617884032654729 5662118107963413024491047)
    ·
      refine ⟨8493177161945119536736571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662118107963413024491047 8493177161945119536736571)
      ·
        refine ⟨12739765742917679305104857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8493177161945119536736571 12739765742917679305104857)
        ·
          refine ⟨9554824307188259478828643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739765742917679305104857 9554824307188259478828643)
          ·
            refine ⟨14332236460782389218242965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554824307188259478828643 14332236460782389218242965)
            ·
              refine ⟨671823584099174494605139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14332236460782389218242965 671823584099174494605139)
              ·
                refine ⟨1007735376148761741907709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671823584099174494605139 1007735376148761741907709)
                ·
                  refine ⟨377900766055785653215391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007735376148761741907709 377900766055785653215391)
                  ·
                    rfl

theorem cell20_827954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_827954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827954 prefixEnd_827954 := by exact prefixLift 827954
  have htrace : WordTrace (prefixWord ++ tailWord_827954) baseStart_827954 baseEnd_827954 := by
    simpa [prefixWord, tailWord_827954, baseEnd_827954] using wordTrace_append hprefix tailTrace_827954
  have hstable : (prefixWord ++ tailWord_827954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827954).length < 2 ^ (prefixWord ++ tailWord_827954).sum := by decide
  have hdescent : baseEnd_827954 < baseStart_827954 := by decide
  rcases family_descends (prefixWord ++ tailWord_827954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827998 : List Nat := [4, 4, 1, 2, 2, 1, 1, 5]
def baseStart_827998 : Nat := 118140960795 + 827998 * 2 ^ 59
def prefixEnd_827998 : Nat := 4983230072969 + 3 ^ 40 * 827998 * 2
def baseEnd_827998 : Nat := 125973616284905685249515

theorem tailTrace_827998 : CollatzResearch.WordTrace tailWord_827998 prefixEnd_827998 125973616284905685249515 := by
  unfold tailWord_827998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774946006789016455652581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20133045369541421096813765 3774946006789016455652581)
  ·
    refine ⟨707802376272940585434859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3774946006789016455652581 707802376272940585434859)
    ·
      refine ⟨1061703564409410878152289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707802376272940585434859 1061703564409410878152289)
      ·
        refine ⟨796277673307058158614217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061703564409410878152289 796277673307058158614217)
        ·
          refine ⟨597208254980293618960663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796277673307058158614217 597208254980293618960663)
          ·
            refine ⟨895812382470440428440995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597208254980293618960663 895812382470440428440995)
            ·
              refine ⟨1343718573705660642661493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895812382470440428440995 1343718573705660642661493)
              ·
                refine ⟨125973616284905685249515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343718573705660642661493 125973616284905685249515)
                ·
                  rfl

theorem cell20_827998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_827998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_827998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_827998 prefixEnd_827998 := by exact prefixLift 827998
  have htrace : WordTrace (prefixWord ++ tailWord_827998) baseStart_827998 baseEnd_827998 := by
    simpa [prefixWord, tailWord_827998, baseEnd_827998] using wordTrace_append hprefix tailTrace_827998
  have hstable : (prefixWord ++ tailWord_827998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827998).length < 2 ^ (prefixWord ++ tailWord_827998).sum := by decide
  have hdescent : baseEnd_827998 < baseStart_827998 := by decide
  rcases family_descends (prefixWord ++ tailWord_827998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828002 : List Nat := [3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_828002 : Nat := 118140960795 + 828002 * 2 ^ 59
def prefixEnd_828002 : Nat := 4983230072969 + 3 ^ 40 * 828002 * 2
def baseEnd_828002 : Nat := 125974224854570273205065

theorem tailTrace_828002 : CollatzResearch.WordTrace tailWord_828002 prefixEnd_828002 125974224854570273205065 := by
  unfold tailWord_828002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549928486574410082091565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20133142630865093552244173 7549928486574410082091565)
  ·
    refine ⟨2831223182465403780784337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7549928486574410082091565 2831223182465403780784337)
    ·
      refine ⟨2123417386849052835588253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2831223182465403780784337 2123417386849052835588253)
      ·
        refine ⟨796281520068394813345595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2123417386849052835588253 796281520068394813345595)
        ·
          refine ⟨1194422280102592220018393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796281520068394813345595 1194422280102592220018393)
          ·
            refine ⟨895816710076944165013795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194422280102592220018393 895816710076944165013795)
            ·
              refine ⟨1343725065115416247520693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895816710076944165013795 1343725065115416247520693)
              ·
                refine ⟨125974224854570273205065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1343725065115416247520693 125974224854570273205065)
                ·
                  rfl

theorem cell20_828002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_828002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828002 prefixEnd_828002 := by exact prefixLift 828002
  have htrace : WordTrace (prefixWord ++ tailWord_828002) baseStart_828002 baseEnd_828002 := by
    simpa [prefixWord, tailWord_828002, baseEnd_828002] using wordTrace_append hprefix tailTrace_828002
  have hstable : (prefixWord ++ tailWord_828002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828002).length < 2 ^ (prefixWord ++ tailWord_828002).sum := by decide
  have hdescent : baseEnd_828002 < baseStart_828002 := by decide
  rcases family_descends (prefixWord ++ tailWord_828002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828037 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 2]
def baseStart_828037 : Nat := 118140960795 + 828037 * 2 ^ 59
def prefixEnd_828037 : Nat := 4983230072969 + 3 ^ 40 * 828037 * 2
def baseEnd_828037 : Nat := 377938649517406253448385

theorem tailTrace_828037 : CollatzResearch.WordTrace tailWord_828037 prefixEnd_828037 377938649517406253448385 := by
  unfold tailWord_828037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30200990501170841305890365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20133993667447227537260243 30200990501170841305890365)
  ·
    refine ⟨11325371437939065489708887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30200990501170841305890365 11325371437939065489708887)
    ·
      refine ⟨16988057156908598234563331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11325371437939065489708887 16988057156908598234563331)
      ·
        refine ⟨25482085735362897351844997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16988057156908598234563331 25482085735362897351844997)
        ·
          refine ⟨4777891075380543253470937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25482085735362897351844997 4777891075380543253470937)
          ·
            refine ⟨3583418306535407440103203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777891075380543253470937 3583418306535407440103203)
            ·
              refine ⟨5375127459803111160154805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583418306535407440103203 5375127459803111160154805)
              ·
                refine ⟨503918199356541671264513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5375127459803111160154805 503918199356541671264513)
                ·
                  refine ⟨377938649517406253448385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503918199356541671264513 377938649517406253448385)
                  ·
                    rfl

theorem cell20_828037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_828037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828037 prefixEnd_828037 := by exact prefixLift 828037
  have htrace : WordTrace (prefixWord ++ tailWord_828037) baseStart_828037 baseEnd_828037 := by
    simpa [prefixWord, tailWord_828037, baseEnd_828037] using wordTrace_append hprefix tailTrace_828037
  have hstable : (prefixWord ++ tailWord_828037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828037).length < 2 ^ (prefixWord ++ tailWord_828037).sum := by decide
  have hdescent : baseEnd_828037 < baseStart_828037 := by decide
  rcases family_descends (prefixWord ++ tailWord_828037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828041 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_828041 : Nat := 118140960795 + 828041 * 2 ^ 59
def prefixEnd_828041 : Nat := 4983230072969 + 3 ^ 40 * 828041 * 2
def baseEnd_828041 : Nat := 377940475226400017315035

theorem tailTrace_828041 : CollatzResearch.WordTrace tailWord_828041 prefixEnd_828041 377940475226400017315035 := by
  unfold tailWord_828041
  simp only [CollatzResearch.WordTrace]
  refine ⟨30201136393156349989035977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20134090928770899992690651 30201136393156349989035977)
  ·
    refine ⟨22650852294867262491776983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30201136393156349989035977 22650852294867262491776983)
    ·
      refine ⟨33976278442300893737665475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22650852294867262491776983 33976278442300893737665475)
      ·
        refine ⟨50964417663451340606498213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33976278442300893737665475 50964417663451340606498213)
        ·
          refine ⟨9555828311897126363718415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50964417663451340606498213 9555828311897126363718415)
          ·
            refine ⟨14333742467845689545577623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9555828311897126363718415 14333742467845689545577623)
            ·
              refine ⟨21500613701768534318366435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14333742467845689545577623 21500613701768534318366435)
              ·
                refine ⟨32250920552652801477549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21500613701768534318366435 32250920552652801477549653)
                ·
                  refine ⟨377940475226400017315035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32250920552652801477549653 377940475226400017315035)
                  ·
                    rfl

theorem cell20_828041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_828041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828041 prefixEnd_828041 := by exact prefixLift 828041
  have htrace : WordTrace (prefixWord ++ tailWord_828041) baseStart_828041 baseEnd_828041 := by
    simpa [prefixWord, tailWord_828041, baseEnd_828041] using wordTrace_append hprefix tailTrace_828041
  have hstable : (prefixWord ++ tailWord_828041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828041).length < 2 ^ (prefixWord ++ tailWord_828041).sum := by decide
  have hdescent : baseEnd_828041 < baseStart_828041 := by decide
  rcases family_descends (prefixWord ++ tailWord_828041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828068 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_828068 : Nat := 118140960795 + 828068 * 2 ^ 59
def prefixEnd_828068 : Nat := 4983230072969 + 3 ^ 40 * 828068 * 2
def baseEnd_828068 : Nat := 377952798762107923414925

theorem tailTrace_828068 : CollatzResearch.WordTrace tailWord_828068 prefixEnd_828068 377952798762107923414925 := by
  unfold tailWord_828068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101060582029266800134429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20134747442705689066845905 15101060582029266800134429)
  ·
    refine ⟨5662897718260975050050411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15101060582029266800134429 5662897718260975050050411)
    ·
      refine ⟨8494346577391462575075617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662897718260975050050411 8494346577391462575075617)
      ·
        refine ⟨6370759933043596931306713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8494346577391462575075617 6370759933043596931306713)
        ·
          refine ⟨4778069949782697698480035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6370759933043596931306713 4778069949782697698480035)
          ·
            refine ⟨7167104924674046547720053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778069949782697698480035 7167104924674046547720053)
            ·
              refine ⟨671916086688191863848755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7167104924674046547720053 671916086688191863848755)
              ·
                refine ⟨1007874130032287795773133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671916086688191863848755 1007874130032287795773133)
                ·
                  refine ⟨377952798762107923414925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007874130032287795773133 377952798762107923414925)
                  ·
                    rfl

theorem cell20_828068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_828068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828068 prefixEnd_828068 := by exact prefixLift 828068
  have htrace : WordTrace (prefixWord ++ tailWord_828068) baseStart_828068 baseEnd_828068 := by
    simpa [prefixWord, tailWord_828068, baseEnd_828068] using wordTrace_append hprefix tailTrace_828068
  have hstable : (prefixWord ++ tailWord_828068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828068).length < 2 ^ (prefixWord ++ tailWord_828068).sum := by decide
  have hdescent : baseEnd_828068 < baseStart_828068 := by decide
  rcases family_descends (prefixWord ++ tailWord_828068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828078 : List Nat := [4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_828078 : Nat := 118140960795 + 828078 * 2 ^ 59
def prefixEnd_828078 : Nat := 4983230072969 + 3 ^ 40 * 828078 * 2
def baseEnd_828078 : Nat := 125985787678197444360517

theorem tailTrace_828078 : CollatzResearch.WordTrace tailWord_828078 prefixEnd_828078 125985787678197444360517 := by
  unfold tailWord_828078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775310736752788163516611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20134990596014870205421925 3775310736752788163516611)
  ·
    refine ⟨5662966105129182245274917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775310736752788163516611 5662966105129182245274917)
    ·
      refine ⟨1061806144711721670989047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5662966105129182245274917 1061806144711721670989047)
      ·
        refine ⟨1592709217067582506483571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061806144711721670989047 1592709217067582506483571)
        ·
          refine ⟨2389063825601373759725357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592709217067582506483571 2389063825601373759725357)
          ·
            refine ⟨895898934600515159897009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2389063825601373759725357 895898934600515159897009)
            ·
              refine ⟨671924200950386369922757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895898934600515159897009 671924200950386369922757)
              ·
                refine ⟨125985787678197444360517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 671924200950386369922757 125985787678197444360517)
                ·
                  rfl

theorem cell20_828078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_828078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828078 prefixEnd_828078 := by exact prefixLift 828078
  have htrace : WordTrace (prefixWord ++ tailWord_828078) baseStart_828078 baseEnd_828078 := by
    simpa [prefixWord, tailWord_828078, baseEnd_828078] using wordTrace_append hprefix tailTrace_828078
  have hstable : (prefixWord ++ tailWord_828078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828078).length < 2 ^ (prefixWord ++ tailWord_828078).sum := by decide
  have hdescent : baseEnd_828078 < baseStart_828078 := by decide
  rcases family_descends (prefixWord ++ tailWord_828078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828109 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_828109 : Nat := 118140960795 + 828109 * 2 ^ 59
def prefixEnd_828109 : Nat := 4983230072969 + 3 ^ 40 * 828109 * 2
def baseEnd_828109 : Nat := 377971512279294003048091

theorem tailTrace_828109 : CollatzResearch.WordTrace tailWord_828109 prefixEnd_828109 377971512279294003048091 := by
  unfold tailWord_828109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30203616556909997602511381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20135744371273331735007587 30203616556909997602511381)
  ·
    refine ⟨1415794526105156137617721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30203616556909997602511381 1415794526105156137617721)
    ·
      refine ⟨1061845894578867103213291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1415794526105156137617721 1061845894578867103213291)
      ·
        refine ⟨1592768841868300654819937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061845894578867103213291 1592768841868300654819937)
        ·
          refine ⟨1194576631401225491114953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1592768841868300654819937 1194576631401225491114953)
          ·
            refine ⟨895932473550919118336215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194576631401225491114953 895932473550919118336215)
            ·
              refine ⟨1343898710326378677504323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895932473550919118336215 1343898710326378677504323)
              ·
                refine ⟨2015848065489568016256485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343898710326378677504323 2015848065489568016256485)
                ·
                  refine ⟨377971512279294003048091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015848065489568016256485 377971512279294003048091)
                  ·
                    rfl

theorem cell20_828109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_828109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828109 prefixEnd_828109 := by exact prefixLift 828109
  have htrace : WordTrace (prefixWord ++ tailWord_828109) baseStart_828109 baseEnd_828109 := by
    simpa [prefixWord, tailWord_828109, baseEnd_828109] using wordTrace_append hprefix tailTrace_828109
  have hstable : (prefixWord ++ tailWord_828109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828109).length < 2 ^ (prefixWord ++ tailWord_828109).sum := by decide
  have hdescent : baseEnd_828109 < baseStart_828109 := by decide
  rcases family_descends (prefixWord ++ tailWord_828109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828127 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_828127 : Nat := 118140960795 + 828127 * 2 ^ 59
def prefixEnd_828127 : Nat := 4983230072969 + 3 ^ 40 * 828127 * 2
def baseEnd_828127 : Nat := 377979727969765940448017

theorem tailTrace_828127 : CollatzResearch.WordTrace tailWord_828127 prefixEnd_828127 377979727969765940448017 := by
  unfold tailWord_828127
  simp only [CollatzResearch.WordTrace]
  refine ⟨30204273070844786676666635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20136182047229857784444423 30204273070844786676666635)
  ·
    refine ⟨45306409606267180014999953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30204273070844786676666635 45306409606267180014999953)
    ·
      refine ⟨33979807204700385011249965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45306409606267180014999953 33979807204700385011249965)
      ·
        refine ⟨12742427701762644379218737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33979807204700385011249965 12742427701762644379218737)
        ·
          refine ⟨9556820776321983284414053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12742427701762644379218737 9556820776321983284414053)
          ·
            refine ⟨1791903895560371865827635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9556820776321983284414053 1791903895560371865827635)
            ·
              refine ⟨2687855843340557798741453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791903895560371865827635 2687855843340557798741453)
              ·
                refine ⟨1007945941252709174528045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2687855843340557798741453 1007945941252709174528045)
                ·
                  refine ⟨377979727969765940448017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007945941252709174528045 377979727969765940448017)
                  ·
                    rfl

theorem cell20_828127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_828127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828127 prefixEnd_828127 := by exact prefixLift 828127
  have htrace : WordTrace (prefixWord ++ tailWord_828127) baseStart_828127 baseEnd_828127 := by
    simpa [prefixWord, tailWord_828127, baseEnd_828127] using wordTrace_append hprefix tailTrace_828127
  have hstable : (prefixWord ++ tailWord_828127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828127).length < 2 ^ (prefixWord ++ tailWord_828127).sum := by decide
  have hdescent : baseEnd_828127 < baseStart_828127 := by decide
  rcases family_descends (prefixWord ++ tailWord_828127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828141 : List Nat := [1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_828141 : Nat := 118140960795 + 828141 * 2 ^ 59
def prefixEnd_828141 : Nat := 4983230072969 + 3 ^ 40 * 828141 * 2
def baseEnd_828141 : Nat := 125995372650414704660431

theorem tailTrace_828141 : CollatzResearch.WordTrace tailWord_828141 prefixEnd_828141 125995372650414704660431 := by
  unfold tailWord_828141
  simp only [CollatzResearch.WordTrace]
  refine ⟨30204783692794067067676277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20136522461862711378450851 30204783692794067067676277)
  ·
    refine ⟨2831698471199443787594651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30204783692794067067676277 2831698471199443787594651)
    ·
      refine ⟨4247547706799165681391977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831698471199443787594651 4247547706799165681391977)
      ·
        refine ⟨3185660780099374261043983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247547706799165681391977 3185660780099374261043983)
        ·
          refine ⟨4778491170149061391565975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185660780099374261043983 4778491170149061391565975)
          ·
            refine ⟨7167736755223592087348963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778491170149061391565975 7167736755223592087348963)
            ·
              refine ⟨10751605132835388131023445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167736755223592087348963 10751605132835388131023445)
              ·
                refine ⟨125995372650414704660431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10751605132835388131023445 125995372650414704660431)
                ·
                  rfl

theorem cell20_828141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_828141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828141 prefixEnd_828141 := by exact prefixLift 828141
  have htrace : WordTrace (prefixWord ++ tailWord_828141) baseStart_828141 baseEnd_828141 := by
    simpa [prefixWord, tailWord_828141, baseEnd_828141] using wordTrace_append hprefix tailTrace_828141
  have hstable : (prefixWord ++ tailWord_828141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828141).length < 2 ^ (prefixWord ++ tailWord_828141).sum := by decide
  have hdescent : baseEnd_828141 < baseStart_828141 := by decide
  rcases family_descends (prefixWord ++ tailWord_828141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828168 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_828168 : Nat := 118140960795 + 828168 * 2 ^ 59
def prefixEnd_828168 : Nat := 4983230072969 + 3 ^ 40 * 828168 * 2
def baseEnd_828168 : Nat := 377998441486952020081183

theorem tailTrace_828168 : CollatzResearch.WordTrace tailWord_828168 prefixEnd_828168 377998441486952020081183 := by
  unfold tailWord_828168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15102884231848125339454579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20137178975797500452606105 15102884231848125339454579)
  ·
    refine ⟨22654326347772188009181869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15102884231848125339454579 22654326347772188009181869)
    ·
      refine ⟨8495372380414570503443201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22654326347772188009181869 8495372380414570503443201)
      ·
        refine ⟨6371529285310927877582401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8495372380414570503443201 6371529285310927877582401)
        ·
          refine ⟨4778646963983195908186801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6371529285310927877582401 4778646963983195908186801)
          ·
            refine ⟨3583985222987396931140101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4778646963983195908186801 3583985222987396931140101)
            ·
              refine ⟨671997229310136924588769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3583985222987396931140101 671997229310136924588769)
              ·
                refine ⟨503997921982602693441577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671997229310136924588769 503997921982602693441577)
                ·
                  refine ⟨377998441486952020081183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503997921982602693441577 377998441486952020081183)
                  ·
                    rfl

theorem cell20_828168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_828168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828168 prefixEnd_828168 := by exact prefixLift 828168
  have htrace : WordTrace (prefixWord ++ tailWord_828168) baseStart_828168 baseEnd_828168 := by
    simpa [prefixWord, tailWord_828168, baseEnd_828168] using wordTrace_append hprefix tailTrace_828168
  have hstable : (prefixWord ++ tailWord_828168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828168).length < 2 ^ (prefixWord ++ tailWord_828168).sum := by decide
  have hdescent : baseEnd_828168 < baseStart_828168 := by decide
  rcases family_descends (prefixWord ++ tailWord_828168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828206 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_828206 : Nat := 118140960795 + 828206 * 2 ^ 59
def prefixEnd_828206 : Nat := 4983230072969 + 3 ^ 40 * 828206 * 2
def baseEnd_828206 : Nat := 378015785722392776814361

theorem tailTrace_828206 : CollatzResearch.WordTrace tailWord_828206 prefixEnd_828206 378015785722392776814361 := by
  unfold tailWord_828206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775894304694822896099059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20138102958372388779194981 3775894304694822896099059)
  ·
    refine ⟨5663841457042234344148589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775894304694822896099059 5663841457042234344148589)
    ·
      refine ⟨2123940546390837879055721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5663841457042234344148589 2123940546390837879055721)
      ·
        refine ⟨1592955409793128409291791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2123940546390837879055721 1592955409793128409291791)
        ·
          refine ⟨2389433114689692613937687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592955409793128409291791 2389433114689692613937687)
          ·
            refine ⟨3584149672034538920906531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389433114689692613937687 3584149672034538920906531)
            ·
              refine ⟨5376224508051808381359797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584149672034538920906531 5376224508051808381359797)
              ·
                refine ⟨504021047629857035752481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5376224508051808381359797 504021047629857035752481)
                ·
                  refine ⟨378015785722392776814361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504021047629857035752481 378015785722392776814361)
                  ·
                    rfl

theorem cell20_828206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_828206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828206 prefixEnd_828206 := by exact prefixLift 828206
  have htrace : WordTrace (prefixWord ++ tailWord_828206) baseStart_828206 baseEnd_828206 := by
    simpa [prefixWord, tailWord_828206, baseEnd_828206] using wordTrace_append hprefix tailTrace_828206
  have hstable : (prefixWord ++ tailWord_828206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828206).length < 2 ^ (prefixWord ++ tailWord_828206).sum := by decide
  have hdescent : baseEnd_828206 < baseStart_828206 := by decide
  rcases family_descends (prefixWord ++ tailWord_828206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828293 : List Nat := [1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_828293 : Nat := 118140960795 + 828293 * 2 ^ 59
def prefixEnd_828293 : Nat := 4983230072969 + 3 ^ 40 * 828293 * 2
def baseEnd_828293 : Nat := 126018498297669046971335

theorem tailTrace_828293 : CollatzResearch.WordTrace tailWord_828293 prefixEnd_828293 126018498297669046971335 := by
  unfold tailWord_828293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30210327588243397027209533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20140218392162264684806355 30210327588243397027209533)
  ·
    refine ⟨11328872845591273885203575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30210327588243397027209533 11328872845591273885203575)
    ·
      refine ⟨16993309268386910827805363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11328872845591273885203575 16993309268386910827805363)
      ·
        refine ⟨25489963902580366241708045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993309268386910827805363 25489963902580366241708045)
        ·
          refine ⟨9558736463467637340640517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25489963902580366241708045 9558736463467637340640517)
          ·
            refine ⟨1792263086900182001370097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9558736463467637340640517 1792263086900182001370097)
            ·
              refine ⟨1344197315175136501027573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792263086900182001370097 1344197315175136501027573)
              ·
                refine ⟨126018498297669046971335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1344197315175136501027573 126018498297669046971335)
                ·
                  rfl

theorem cell20_828293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_828293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828293 prefixEnd_828293 := by exact prefixLift 828293
  have htrace : WordTrace (prefixWord ++ tailWord_828293) baseStart_828293 baseEnd_828293 := by
    simpa [prefixWord, tailWord_828293, baseEnd_828293] using wordTrace_append hprefix tailTrace_828293
  have hstable : (prefixWord ++ tailWord_828293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828293).length < 2 ^ (prefixWord ++ tailWord_828293).sum := by decide
  have hdescent : baseEnd_828293 < baseStart_828293 := by decide
  rcases family_descends (prefixWord ++ tailWord_828293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828296 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_828296 : Nat := 118140960795 + 828296 * 2 ^ 59
def prefixEnd_828296 : Nat := 4983230072969 + 3 ^ 40 * 828296 * 2
def baseEnd_828296 : Nat := 378056864174752463813993

theorem tailTrace_828296 : CollatzResearch.WordTrace tailWord_828296 prefixEnd_828296 378056864174752463813993 := by
  unfold tailWord_828296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15105218503616264269784371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20140291338155019026379161 15105218503616264269784371)
  ·
    refine ⟨22657827755424396404676557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15105218503616264269784371 22657827755424396404676557)
    ·
      refine ⟨8496685408284148651753709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22657827755424396404676557 8496685408284148651753709)
      ·
        refine ⟨3186257028106555744407641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8496685408284148651753709 3186257028106555744407641)
        ·
          refine ⟨2389692771079916808305731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186257028106555744407641 2389692771079916808305731)
          ·
            refine ⟨3584539156619875212458597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389692771079916808305731 3584539156619875212458597)
            ·
              refine ⟨672101091866226602335987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3584539156619875212458597 672101091866226602335987)
              ·
                refine ⟨1008151637799339903503981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672101091866226602335987 1008151637799339903503981)
                ·
                  refine ⟨378056864174752463813993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008151637799339903503981 378056864174752463813993)
                  ·
                    rfl

theorem cell20_828296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_828296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828296 prefixEnd_828296 := by exact prefixLift 828296
  have htrace : WordTrace (prefixWord ++ tailWord_828296) baseStart_828296 baseEnd_828296 := by
    simpa [prefixWord, tailWord_828296, baseEnd_828296] using wordTrace_append hprefix tailTrace_828296
  have hstable : (prefixWord ++ tailWord_828296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828296).length < 2 ^ (prefixWord ++ tailWord_828296).sum := by decide
  have hdescent : baseEnd_828296 < baseStart_828296 := by decide
  rcases family_descends (prefixWord ++ tailWord_828296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828333 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 2]
def baseStart_828333 : Nat := 118140960795 + 828333 * 2 ^ 59
def prefixEnd_828333 : Nat := 4983230072969 + 3 ^ 40 * 828333 * 2
def baseEnd_828333 : Nat := 378073751982944779580509

theorem tailTrace_828333 : CollatzResearch.WordTrace tailWord_828333 prefixEnd_828333 378073751982944779580509 := by
  unfold tailWord_828333
  simp only [CollatzResearch.WordTrace]
  refine ⟨30211786508098483858665653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20141191005398989239110435 30211786508098483858665653)
  ·
    refine ⟨2832354985134232861749905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30211786508098483858665653 2832354985134232861749905)
    ·
      refine ⟨2124266238850674646312429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832354985134232861749905 2124266238850674646312429)
      ·
        refine ⟨796599839569002992367161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2124266238850674646312429 796599839569002992367161)
        ·
          refine ⟨597449879676752244275371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796599839569002992367161 597449879676752244275371)
          ·
            refine ⟨896174819515128366413057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597449879676752244275371 896174819515128366413057)
            ·
              refine ⟨672131114636346274809793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896174819515128366413057 672131114636346274809793)
              ·
                refine ⟨504098335977259706107345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672131114636346274809793 504098335977259706107345)
                ·
                  refine ⟨378073751982944779580509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504098335977259706107345 378073751982944779580509)
                  ·
                    rfl

theorem cell20_828333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_828333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828333 prefixEnd_828333 := by exact prefixLift 828333
  have htrace : WordTrace (prefixWord ++ tailWord_828333) baseStart_828333 baseEnd_828333 := by
    simpa [prefixWord, tailWord_828333, baseEnd_828333] using wordTrace_append hprefix tailTrace_828333
  have hstable : (prefixWord ++ tailWord_828333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828333).length < 2 ^ (prefixWord ++ tailWord_828333).sum := by decide
  have hdescent : baseEnd_828333 < baseStart_828333 := by decide
  rcases family_descends (prefixWord ++ tailWord_828333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828337 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 2]
def baseStart_828337 : Nat := 118140960795 + 828337 * 2 ^ 59
def prefixEnd_828337 : Nat := 4983230072969 + 3 ^ 40 * 828337 * 2
def baseEnd_828337 : Nat := 378075577691938543447159

theorem tailTrace_828337 : CollatzResearch.WordTrace tailWord_828337 prefixEnd_828337 378075577691938543447159 := by
  unfold tailWord_828337
  simp only [CollatzResearch.WordTrace]
  refine ⟨30211932400083992541811265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20141288266722661694540843 30211932400083992541811265)
  ·
    refine ⟨22658949300062994406358449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30211932400083992541811265 22658949300062994406358449)
    ·
      refine ⟨16994211975047245804768837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22658949300062994406358449 16994211975047245804768837)
      ·
        refine ⟨3186414745321358588394157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16994211975047245804768837 3186414745321358588394157)
        ·
          refine ⟨1194905529495509470647809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3186414745321358588394157 1194905529495509470647809)
          ·
            refine ⟨896179147121632102985857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194905529495509470647809 896179147121632102985857)
            ·
              refine ⟨672134360341224077239393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896179147121632102985857 672134360341224077239393)
              ·
                refine ⟨504100770255918057929545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672134360341224077239393 504100770255918057929545)
                ·
                  refine ⟨378075577691938543447159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504100770255918057929545 378075577691938543447159)
                  ·
                    rfl

theorem cell20_828337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_828337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828337 prefixEnd_828337 := by exact prefixLift 828337
  have htrace : WordTrace (prefixWord ++ tailWord_828337) baseStart_828337 baseEnd_828337 := by
    simpa [prefixWord, tailWord_828337, baseEnd_828337] using wordTrace_append hprefix tailTrace_828337
  have hstable : (prefixWord ++ tailWord_828337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828337).length < 2 ^ (prefixWord ++ tailWord_828337).sum := by decide
  have hdescent : baseEnd_828337 < baseStart_828337 := by decide
  rcases family_descends (prefixWord ++ tailWord_828337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828341 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 2]
def baseStart_828341 : Nat := 118140960795 + 828341 * 2 ^ 59
def prefixEnd_828341 : Nat := 4983230072969 + 3 ^ 40 * 828341 * 2
def baseEnd_828341 : Nat := 378077403400932307313809

theorem tailTrace_828341 : CollatzResearch.WordTrace tailWord_828341 prefixEnd_828341 378077403400932307313809 := by
  unfold tailWord_828341
  simp only [CollatzResearch.WordTrace]
  refine ⟨30212078292069501224956877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20141385528046334149971251 30212078292069501224956877)
  ·
    refine ⟨11329529359526062959358829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30212078292069501224956877 11329529359526062959358829)
    ·
      refine ⟨4248573509822273609759561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11329529359526062959358829 4248573509822273609759561)
      ·
        refine ⟨3186430132366705207319671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248573509822273609759561 3186430132366705207319671)
        ·
          refine ⟨4779645198550057810979507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186430132366705207319671 4779645198550057810979507)
          ·
            refine ⟨7169467797825086716469261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779645198550057810979507 7169467797825086716469261)
            ·
              refine ⟨2688550424184407518675973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7169467797825086716469261 2688550424184407518675973)
              ·
                refine ⟨504103204534576409751745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2688550424184407518675973 504103204534576409751745)
                ·
                  refine ⟨378077403400932307313809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504103204534576409751745 378077403400932307313809)
                  ·
                    rfl

theorem cell20_828341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_828341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828341 prefixEnd_828341 := by exact prefixLift 828341
  have htrace : WordTrace (prefixWord ++ tailWord_828341) baseStart_828341 baseEnd_828341 := by
    simpa [prefixWord, tailWord_828341, baseEnd_828341] using wordTrace_append hprefix tailTrace_828341
  have hstable : (prefixWord ++ tailWord_828341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828341).length < 2 ^ (prefixWord ++ tailWord_828341).sum := by decide
  have hdescent : baseEnd_828341 < baseStart_828341 := by decide
  rcases family_descends (prefixWord ++ tailWord_828341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828369 : List Nat := [1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_828369 : Nat := 118140960795 + 828369 * 2 ^ 59
def prefixEnd_828369 : Nat := 4983230072969 + 3 ^ 40 * 828369 * 2
def baseEnd_828369 : Nat := 126030061121296218126787

theorem tailTrace_828369 : CollatzResearch.WordTrace tailWord_828369 prefixEnd_828369 126030061121296218126787 := by
  unfold tailWord_828369
  simp only [CollatzResearch.WordTrace]
  refine ⟨30213099535968062006976161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20142066357312041337984107 30213099535968062006976161)
  ·
    refine ⟨22659824651976046505232121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30213099535968062006976161 22659824651976046505232121)
    ·
      refine ⟨16994868488982034878924091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22659824651976046505232121 16994868488982034878924091)
      ·
        refine ⟨25492302733473052318386137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994868488982034878924091 25492302733473052318386137)
        ·
          refine ⟨19119227050104789238789603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25492302733473052318386137 19119227050104789238789603)
          ·
            refine ⟨28678840575157183858184405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19119227050104789238789603 28678840575157183858184405)
            ·
              refine ⟨672160325980246496676197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28678840575157183858184405 672160325980246496676197)
              ·
                refine ⟨126030061121296218126787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672160325980246496676197 126030061121296218126787)
                ·
                  rfl

theorem cell20_828369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_828369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828369 prefixEnd_828369 := by exact prefixLift 828369
  have htrace : WordTrace (prefixWord ++ tailWord_828369) baseStart_828369 baseEnd_828369 := by
    simpa [prefixWord, tailWord_828369, baseEnd_828369] using wordTrace_append hprefix tailTrace_828369
  have hstable : (prefixWord ++ tailWord_828369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828369).length < 2 ^ (prefixWord ++ tailWord_828369).sum := by decide
  have hdescent : baseEnd_828369 < baseStart_828369 := by decide
  rcases family_descends (prefixWord ++ tailWord_828369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828386 : List Nat := [3, 3, 3, 1, 1, 2, 7]
def baseStart_828386 : Nat := 118140960795 + 828386 * 2 ^ 59
def prefixEnd_828386 : Nat := 4983230072969 + 3 ^ 40 * 828386 * 2
def baseEnd_828386 : Nat := 42010882514123572312625

theorem tailTrace_828386 : CollatzResearch.WordTrace tailWord_828386 prefixEnd_828386 42010882514123572312625 := by
  unfold tailWord_828386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7553429894226618477586253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20142479717937649273563341 7553429894226618477586253)
  ·
    refine ⟨2832536210334981929094845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7553429894226618477586253 2832536210334981929094845)
    ·
      refine ⟨1062201078875618223410567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2832536210334981929094845 1062201078875618223410567)
      ·
        refine ⟨1593301618313427335115851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062201078875618223410567 1593301618313427335115851)
        ·
          refine ⟨2389952427470141002673777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593301618313427335115851 2389952427470141002673777)
          ·
            refine ⟨1792464320602605752005333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389952427470141002673777 1792464320602605752005333)
            ·
              refine ⟨42010882514123572312625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1792464320602605752005333 42010882514123572312625)
              ·
                rfl

theorem cell20_828386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_828386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828386 prefixEnd_828386 := by exact prefixLift 828386
  have htrace : WordTrace (prefixWord ++ tailWord_828386) baseStart_828386 baseEnd_828386 := by
    simpa [prefixWord, tailWord_828386, baseEnd_828386] using wordTrace_append hprefix tailTrace_828386
  have hstable : (prefixWord ++ tailWord_828386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828386).length < 2 ^ (prefixWord ++ tailWord_828386).sum := by decide
  have hdescent : baseEnd_828386 < baseStart_828386 := by decide
  rcases family_descends (prefixWord ++ tailWord_828386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828389 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_828389 : Nat := 118140960795 + 828389 * 2 ^ 59
def prefixEnd_828389 : Nat := 4983230072969 + 3 ^ 40 * 828389 * 2
def baseEnd_828389 : Nat := 378099311908857473713613

theorem tailTrace_828389 : CollatzResearch.WordTrace tailWord_828389 prefixEnd_828389 378099311908857473713613 := by
  unfold tailWord_828389
  simp only [CollatzResearch.WordTrace]
  refine ⟨30213828995895605422704221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20142552663930403615136147 30213828995895605422704221)
  ·
    refine ⟨11330185873460852033514083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30213828995895605422704221 11330185873460852033514083)
    ·
      refine ⟨16995278810191278050271125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330185873460852033514083 16995278810191278050271125)
      ·
        refine ⟨796653694227716158606459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16995278810191278050271125 796653694227716158606459)
        ·
          refine ⟨1194980541341574237909689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796653694227716158606459 1194980541341574237909689)
          ·
            refine ⟨896235406006180678432267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194980541341574237909689 896235406006180678432267)
            ·
              refine ⟨1344353109009271017648401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896235406006180678432267 1344353109009271017648401)
              ·
                refine ⟨1008264831756953263236301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344353109009271017648401 1008264831756953263236301)
                ·
                  refine ⟨378099311908857473713613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008264831756953263236301 378099311908857473713613)
                  ·
                    rfl

theorem cell20_828389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_828389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828389 prefixEnd_828389 := by exact prefixLift 828389
  have htrace : WordTrace (prefixWord ++ tailWord_828389) baseStart_828389 baseEnd_828389 := by
    simpa [prefixWord, tailWord_828389, baseEnd_828389] using wordTrace_append hprefix tailTrace_828389
  have hstable : (prefixWord ++ tailWord_828389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828389).length < 2 ^ (prefixWord ++ tailWord_828389).sum := by decide
  have hdescent : baseEnd_828389 < baseStart_828389 := by decide
  rcases family_descends (prefixWord ++ tailWord_828389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828421 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_828421 : Nat := 118140960795 + 828421 * 2 ^ 59
def prefixEnd_828421 : Nat := 4983230072969 + 3 ^ 40 * 828421 * 2
def baseEnd_828421 : Nat := 378113917580807584646815

theorem tailTrace_828421 : CollatzResearch.WordTrace tailWord_828421 prefixEnd_828421 378113917580807584646815 := by
  unfold tailWord_828421
  simp only [CollatzResearch.WordTrace]
  refine ⟨30214996131779674887869117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20143330754519783258579411 30214996131779674887869117)
  ·
    refine ⟨11330623549417378082950919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30214996131779674887869117 11330623549417378082950919)
    ·
      refine ⟨16995935324126067124426379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330623549417378082950919 16995935324126067124426379)
      ·
        refine ⟨25493902986189100686639569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16995935324126067124426379 25493902986189100686639569)
        ·
          refine ⟨19120427239641825514979677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25493902986189100686639569 19120427239641825514979677)
          ·
            refine ⟨7170160214865684568117379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19120427239641825514979677 7170160214865684568117379)
            ·
              refine ⟨10755240322298526852176069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7170160214865684568117379 10755240322298526852176069)
              ·
                refine ⟨2016607560430973784783013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10755240322298526852176069 2016607560430973784783013)
                ·
                  refine ⟨378113917580807584646815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2016607560430973784783013 378113917580807584646815)
                  ·
                    rfl

theorem cell20_828421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_828421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828421 prefixEnd_828421 := by exact prefixLift 828421
  have htrace : WordTrace (prefixWord ++ tailWord_828421) baseStart_828421 baseEnd_828421 := by
    simpa [prefixWord, tailWord_828421, baseEnd_828421] using wordTrace_append hprefix tailTrace_828421
  have hstable : (prefixWord ++ tailWord_828421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828421).length < 2 ^ (prefixWord ++ tailWord_828421).sum := by decide
  have hdescent : baseEnd_828421 < baseStart_828421 := by decide
  rcases family_descends (prefixWord ++ tailWord_828421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828424 : List Nat := [2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_828424 : Nat := 118140960795 + 828424 * 2 ^ 59
def prefixEnd_828424 : Nat := 4983230072969 + 3 ^ 40 * 828424 * 2
def baseEnd_828424 : Nat := 126038428954184302515601

theorem tailTrace_828424 : CollatzResearch.WordTrace tailWord_828424 prefixEnd_828424 126038428954184302515601 := by
  unfold tailWord_828424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15107552775384403200114163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20143403700512537600152217 15107552775384403200114163)
  ·
    refine ⟨22661329163076604800171245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15107552775384403200114163 22661329163076604800171245)
    ·
      refine ⟨8497998436153726800064217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22661329163076604800171245 8497998436153726800064217)
      ·
        refine ⟨6373498827115295100048163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8497998436153726800064217 6373498827115295100048163)
        ·
          refine ⟨9560248240672942650072245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373498827115295100048163 9560248240672942650072245)
          ·
            refine ⟨896273272563088373444273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9560248240672942650072245 896273272563088373444273)
            ·
              refine ⟨672204954422316280083205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896273272563088373444273 672204954422316280083205)
              ·
                refine ⟨126038428954184302515601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672204954422316280083205 126038428954184302515601)
                ·
                  rfl

theorem cell20_828424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_828424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828424 prefixEnd_828424 := by exact prefixLift 828424
  have htrace : WordTrace (prefixWord ++ tailWord_828424) baseStart_828424 baseEnd_828424 := by
    simpa [prefixWord, tailWord_828424, baseEnd_828424] using wordTrace_append hprefix tailTrace_828424
  have hstable : (prefixWord ++ tailWord_828424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828424).length < 2 ^ (prefixWord ++ tailWord_828424).sum := by decide
  have hdescent : baseEnd_828424 < baseStart_828424 := by decide
  rcases family_descends (prefixWord ++ tailWord_828424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828455 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_828455 : Nat := 118140960795 + 828455 * 2 ^ 59
def prefixEnd_828455 : Nat := 4983230072969 + 3 ^ 40 * 828455 * 2
def baseEnd_828455 : Nat := 378129436107254577513343

theorem tailTrace_828455 : CollatzResearch.WordTrace tailWord_828455 prefixEnd_828455 378129436107254577513343 := by
  unfold tailWord_828455
  simp only [CollatzResearch.WordTrace]
  refine ⟨30216236213656498694606819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20144157475770999129737879 30216236213656498694606819)
  ·
    refine ⟨45324354320484748041910229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30216236213656498694606819 45324354320484748041910229)
    ·
      refine ⟨1062289554386361282232271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45324354320484748041910229 1062289554386361282232271)
      ·
        refine ⟨1593434331579541923348407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062289554386361282232271 1593434331579541923348407)
        ·
          refine ⟨2390151497369312885022611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593434331579541923348407 2390151497369312885022611)
          ·
            refine ⟨3585227246053969327533917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390151497369312885022611 3585227246053969327533917)
            ·
              refine ⟨1344460217270238497825219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585227246053969327533917 1344460217270238497825219)
              ·
                refine ⟨2016690325905357746737829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344460217270238497825219 2016690325905357746737829)
                ·
                  refine ⟨378129436107254577513343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2016690325905357746737829 378129436107254577513343)
                  ·
                    rfl

theorem cell20_828455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_828455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828455 prefixEnd_828455 := by exact prefixLift 828455
  have htrace : WordTrace (prefixWord ++ tailWord_828455) baseStart_828455 baseEnd_828455 := by
    simpa [prefixWord, tailWord_828455, baseEnd_828455] using wordTrace_append hprefix tailTrace_828455
  have hstable : (prefixWord ++ tailWord_828455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828455).length < 2 ^ (prefixWord ++ tailWord_828455).sum := by decide
  have hdescent : baseEnd_828455 < baseStart_828455 := by decide
  rcases family_descends (prefixWord ++ tailWord_828455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828521 : List Nat := [1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_828521 : Nat := 118140960795 + 828521 * 2 ^ 59
def prefixEnd_828521 : Nat := 4983230072969 + 3 ^ 40 * 828521 * 2
def baseEnd_828521 : Nat := 126053186768550560437691

theorem tailTrace_828521 : CollatzResearch.WordTrace tailWord_828521 prefixEnd_828521 126053186768550560437691 := by
  unfold tailWord_828521
  simp only [CollatzResearch.WordTrace]
  refine ⟨30218643431417391966509417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20145762287611594644339611 30218643431417391966509417)
  ·
    refine ⟨22663982573563043974882063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30218643431417391966509417 22663982573563043974882063)
    ·
      refine ⟨33995973860344565962323095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22663982573563043974882063 33995973860344565962323095)
      ·
        refine ⟨50993960790516848943484643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33995973860344565962323095 50993960790516848943484643)
        ·
          refine ⟨76490941185775273415226965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50993960790516848943484643 76490941185775273415226965)
          ·
            refine ⟨896378217020803985334691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 76490941185775273415226965 896378217020803985334691)
            ·
              refine ⟨1344567325531205978002037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896378217020803985334691 1344567325531205978002037)
              ·
                refine ⟨126053186768550560437691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1344567325531205978002037 126053186768550560437691)
                ·
                  rfl

theorem cell20_828521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_828521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828521 prefixEnd_828521 := by exact prefixLift 828521
  have htrace : WordTrace (prefixWord ++ tailWord_828521) baseStart_828521 baseEnd_828521 := by
    simpa [prefixWord, tailWord_828521, baseEnd_828521] using wordTrace_append hprefix tailTrace_828521
  have hstable : (prefixWord ++ tailWord_828521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828521).length < 2 ^ (prefixWord ++ tailWord_828521).sum := by decide
  have hdescent : baseEnd_828521 < baseStart_828521 := by decide
  rcases family_descends (prefixWord ++ tailWord_828521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828528 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_828528 : Nat := 118140960795 + 828528 * 2 ^ 59
def prefixEnd_828528 : Nat := 4983230072969 + 3 ^ 40 * 828528 * 2
def baseEnd_828528 : Nat := 378162755296390768079711

theorem tailTrace_828528 : CollatzResearch.WordTrace tailWord_828528 prefixEnd_828528 378162755296390768079711 := by
  unfold tailWord_828528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109449371196016081007119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20145932494928021441342825 15109449371196016081007119)
  ·
    refine ⟨22664174056794024121510679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109449371196016081007119 22664174056794024121510679)
    ·
      refine ⟨33996261085191036182266019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22664174056794024121510679 33996261085191036182266019)
      ·
        refine ⟨50994391627786554273399029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33996261085191036182266019 50994391627786554273399029)
        ·
          refine ⟨4780724215104989463131159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50994391627786554273399029 4780724215104989463131159)
          ·
            refine ⟨7171086322657484194696739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780724215104989463131159 7171086322657484194696739)
            ·
              refine ⟨10756629483986226292045109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171086322657484194696739 10756629483986226292045109)
              ·
                refine ⟨1008434014123708714879229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10756629483986226292045109 1008434014123708714879229)
                ·
                  refine ⟨378162755296390768079711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008434014123708714879229 378162755296390768079711)
                  ·
                    rfl

theorem cell20_828528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_828528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828528 prefixEnd_828528 := by exact prefixLift 828528
  have htrace : WordTrace (prefixWord ++ tailWord_828528) baseStart_828528 baseEnd_828528 := by
    simpa [prefixWord, tailWord_828528, baseEnd_828528] using wordTrace_append hprefix tailTrace_828528
  have hstable : (prefixWord ++ tailWord_828528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828528).length < 2 ^ (prefixWord ++ tailWord_828528).sum := by decide
  have hdescent : baseEnd_828528 < baseStart_828528 := by decide
  rcases family_descends (prefixWord ++ tailWord_828528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828535 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_828535 : Nat := 118140960795 + 828535 * 2 ^ 59
def prefixEnd_828535 : Nat := 4983230072969 + 3 ^ 40 * 828535 * 2
def baseEnd_828535 : Nat := 378165950287129854846349

theorem tailTrace_828535 : CollatzResearch.WordTrace tailWord_828535 prefixEnd_828535 378165950287129854846349 := by
  unfold tailWord_828535
  simp only [CollatzResearch.WordTrace]
  refine ⟨30219154053366672357519059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20146102702244448238346039 30219154053366672357519059)
  ·
    refine ⟨45328731080050008536278589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30219154053366672357519059 45328731080050008536278589)
    ·
      refine ⟨16998274155018753201104471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45328731080050008536278589 16998274155018753201104471)
      ·
        refine ⟨25497411232528129801656707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16998274155018753201104471 25497411232528129801656707)
        ·
          refine ⟨38246116848792194702485061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25497411232528129801656707 38246116848792194702485061)
          ·
            refine ⟨7171146909148536506715949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38246116848792194702485061 7171146909148536506715949)
            ·
              refine ⟨2689180090930701190018481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7171146909148536506715949 2689180090930701190018481)
              ·
                refine ⟨2016885068198025892513861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689180090930701190018481 2016885068198025892513861)
                ·
                  refine ⟨378165950287129854846349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2016885068198025892513861 378165950287129854846349)
                  ·
                    rfl

theorem cell20_828535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_828535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828535 prefixEnd_828535 := by exact prefixLift 828535
  have htrace : WordTrace (prefixWord ++ tailWord_828535) baseStart_828535 baseEnd_828535 := by
    simpa [prefixWord, tailWord_828535, baseEnd_828535] using wordTrace_append hprefix tailTrace_828535
  have hstable : (prefixWord ++ tailWord_828535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828535).length < 2 ^ (prefixWord ++ tailWord_828535).sum := by decide
  have hdescent : baseEnd_828535 < baseStart_828535 := by decide
  rcases family_descends (prefixWord ++ tailWord_828535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828562 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_828562 : Nat := 118140960795 + 828562 * 2 ^ 59
def prefixEnd_828562 : Nat := 4983230072969 + 3 ^ 40 * 828562 * 2
def baseEnd_828562 : Nat := 378178273822837760946239

theorem tailTrace_828562 : CollatzResearch.WordTrace tailWord_828562 prefixEnd_828562 378178273822837760946239 := by
  unfold tailWord_828562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555034706067213992187985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20146759216179237312501293 7555034706067213992187985)
  ·
    refine ⟨5666276029550410494140989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7555034706067213992187985 5666276029550410494140989)
    ·
      refine ⟨2124853511081403935302871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5666276029550410494140989 2124853511081403935302871)
      ·
        refine ⟨3187280266622105902954307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124853511081403935302871 3187280266622105902954307)
        ·
          refine ⟨4780920399933158854431461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187280266622105902954307 4780920399933158854431461)
          ·
            refine ⟨896422574987467285205899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4780920399933158854431461 896422574987467285205899)
            ·
              refine ⟨1344633862481200927808849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896422574987467285205899 1344633862481200927808849)
              ·
                refine ⟨1008475396860900695856637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344633862481200927808849 1008475396860900695856637)
                ·
                  refine ⟨378178273822837760946239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008475396860900695856637 378178273822837760946239)
                  ·
                    rfl

theorem cell20_828562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_828562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828562 prefixEnd_828562 := by exact prefixLift 828562
  have htrace : WordTrace (prefixWord ++ tailWord_828562) baseStart_828562 baseEnd_828562 := by
    simpa [prefixWord, tailWord_828562, baseEnd_828562] using wordTrace_append hprefix tailTrace_828562
  have hstable : (prefixWord ++ tailWord_828562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828562).length < 2 ^ (prefixWord ++ tailWord_828562).sum := by decide
  have hdescent : baseEnd_828562 < baseStart_828562 := by decide
  rcases family_descends (prefixWord ++ tailWord_828562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828604 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_828604 : Nat := 118140960795 + 828604 * 2 ^ 59
def prefixEnd_828604 : Nat := 4983230072969 + 3 ^ 40 * 828604 * 2
def baseEnd_828604 : Nat := 378197443767272281546067

theorem tailTrace_828604 : CollatzResearch.WordTrace tailWord_828604 prefixEnd_828604 378197443767272281546067 := by
  unfold tailWord_828604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110835345058348570890433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20147780460077798094520577 15110835345058348570890433)
  ·
    refine ⟨11333126508793761428167825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15110835345058348570890433 11333126508793761428167825)
    ·
      refine ⟨8499844881595321071125869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11333126508793761428167825 8499844881595321071125869)
      ·
        refine ⟨3187441830598245401672201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8499844881595321071125869 3187441830598245401672201)
        ·
          refine ⟨2390581372948684051254151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3187441830598245401672201 2390581372948684051254151)
          ·
            refine ⟨3585872059423026076881227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390581372948684051254151 3585872059423026076881227)
            ·
              refine ⟨5378808089134539115321841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585872059423026076881227 5378808089134539115321841)
              ·
                refine ⟨4034106066850904336491381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5378808089134539115321841 4034106066850904336491381)
                ·
                  refine ⟨378197443767272281546067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4034106066850904336491381 378197443767272281546067)
                  ·
                    rfl

theorem cell20_828604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_828604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828604 prefixEnd_828604 := by exact prefixLift 828604
  have htrace : WordTrace (prefixWord ++ tailWord_828604) baseStart_828604 baseEnd_828604 := by
    simpa [prefixWord, tailWord_828604, baseEnd_828604] using wordTrace_append hprefix tailTrace_828604
  have hstable : (prefixWord ++ tailWord_828604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828604).length < 2 ^ (prefixWord ++ tailWord_828604).sum := by decide
  have hdescent : baseEnd_828604 < baseStart_828604 := by decide
  rcases family_descends (prefixWord ++ tailWord_828604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828610 : List Nat := [3, 5, 1, 1, 3, 1, 6]
def baseStart_828610 : Nat := 118140960795 + 828610 * 2 ^ 59
def prefixEnd_828610 : Nat := 4983230072969 + 3 ^ 40 * 828610 * 2
def baseEnd_828610 : Nat := 42022242481195880816227

theorem tailTrace_828610 : CollatzResearch.WordTrace tailWord_828610 prefixEnd_828610 42022242481195880816227 := by
  unfold tailWord_828610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555472382023740041624821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20147926352063306777666189 7555472382023740041624821)
  ·
    refine ⟨708325535814725628902327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7555472382023740041624821 708325535814725628902327)
    ·
      refine ⟨1062488303722088443353491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 708325535814725628902327 1062488303722088443353491)
      ·
        refine ⟨1593732455583132665030237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062488303722088443353491 1593732455583132665030237)
        ·
          refine ⟨597649670843674749386339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1593732455583132665030237 597649670843674749386339)
          ·
            refine ⟨896474506265512124079509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597649670843674749386339 896474506265512124079509)
            ·
              refine ⟨42022242481195880816227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 896474506265512124079509 42022242481195880816227)
              ·
                rfl

theorem cell20_828610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 6].length) (baseStart_828610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828610 prefixEnd_828610 := by exact prefixLift 828610
  have htrace : WordTrace (prefixWord ++ tailWord_828610) baseStart_828610 baseEnd_828610 := by
    simpa [prefixWord, tailWord_828610, baseEnd_828610] using wordTrace_append hprefix tailTrace_828610
  have hstable : (prefixWord ++ tailWord_828610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828610).length < 2 ^ (prefixWord ++ tailWord_828610).sum := by decide
  have hdescent : baseEnd_828610 < baseStart_828610 := by decide
  rcases family_descends (prefixWord ++ tailWord_828610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828618 : List Nat := [3, 1, 2, 1, 3, 2, 8]
def baseStart_828618 : Nat := 118140960795 + 828618 * 2 ^ 59
def prefixEnd_828618 : Nat := 4983230072969 + 3 ^ 40 * 828618 * 2
def baseEnd_828618 : Nat := 42022648194305606119927

theorem tailTrace_828618 : CollatzResearch.WordTrace tailWord_828618 prefixEnd_828618 42022648194305606119927 := by
  unfold tailWord_828618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555545328016494383197627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20148120874710651688527005 7555545328016494383197627)
  ·
    refine ⟨11333317992024741574796441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7555545328016494383197627 11333317992024741574796441)
    ·
      refine ⟨8499988494018556181097331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11333317992024741574796441 8499988494018556181097331)
      ·
        refine ⟨12749982741027834271645997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499988494018556181097331 12749982741027834271645997)
        ·
          refine ⟨4781243527885437851867249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12749982741027834271645997 4781243527885437851867249)
          ·
            refine ⟨3585932645914078388900437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781243527885437851867249 3585932645914078388900437)
            ·
              refine ⟨42022648194305606119927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3585932645914078388900437 42022648194305606119927)
              ·
                rfl

theorem cell20_828618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_828618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828618 prefixEnd_828618 := by exact prefixLift 828618
  have htrace : WordTrace (prefixWord ++ tailWord_828618) baseStart_828618 baseEnd_828618 := by
    simpa [prefixWord, tailWord_828618, baseEnd_828618] using wordTrace_append hprefix tailTrace_828618
  have hstable : (prefixWord ++ tailWord_828618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828618).length < 2 ^ (prefixWord ++ tailWord_828618).sum := by decide
  have hdescent : baseEnd_828618 < baseStart_828618 := by decide
  rcases family_descends (prefixWord ++ tailWord_828618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828666 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_828666 : Nat := 118140960795 + 828666 * 2 ^ 59
def prefixEnd_828666 : Nat := 4983230072969 + 3 ^ 40 * 828666 * 2
def baseEnd_828666 : Nat := 378225742256675621479147

theorem tailTrace_828666 : CollatzResearch.WordTrace tailWord_828666 prefixEnd_828666 378225742256675621479147 := by
  unfold tailWord_828666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555983003973020432634463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20149288010594721153691901 7555983003973020432634463)
  ·
    refine ⟨11333974505959530648951695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7555983003973020432634463 11333974505959530648951695)
    ·
      refine ⟨17000961758939295973427543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11333974505959530648951695 17000961758939295973427543)
      ·
        refine ⟨25501442638408943960141315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17000961758939295973427543 25501442638408943960141315)
        ·
          refine ⟨38252163957613415940211973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25501442638408943960141315 38252163957613415940211973)
          ·
            refine ⟨7172280742052515488789745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38252163957613415940211973 7172280742052515488789745)
            ·
              refine ⟨5379210556539386616592309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7172280742052515488789745 5379210556539386616592309)
              ·
                refine ⟨504300989675567495305529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5379210556539386616592309 504300989675567495305529)
                ·
                  refine ⟨378225742256675621479147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504300989675567495305529 378225742256675621479147)
                  ·
                    rfl

theorem cell20_828666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_828666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828666 prefixEnd_828666 := by exact prefixLift 828666
  have htrace : WordTrace (prefixWord ++ tailWord_828666) baseStart_828666 baseEnd_828666 := by
    simpa [prefixWord, tailWord_828666, baseEnd_828666] using wordTrace_append hprefix tailTrace_828666
  have hstable : (prefixWord ++ tailWord_828666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828666).length < 2 ^ (prefixWord ++ tailWord_828666).sum := by decide
  have hdescent : baseEnd_828666 < baseStart_828666 := by decide
  rcases family_descends (prefixWord ++ tailWord_828666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828683 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 2]
def baseStart_828683 : Nat := 118140960795 + 828683 * 2 ^ 59
def prefixEnd_828683 : Nat := 4983230072969 + 3 ^ 40 * 828683 * 2
def baseEnd_828683 : Nat := 378233501519899117912411

theorem tailTrace_828683 : CollatzResearch.WordTrace tailWord_828683 prefixEnd_828683 378233501519899117912411 := by
  unfold tailWord_828683
  simp only [CollatzResearch.WordTrace]
  refine ⟨30224552056830493633906703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20149701371220329089271135 30224552056830493633906703)
  ·
    refine ⟨45336828085245740450860055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30224552056830493633906703 45336828085245740450860055)
    ·
      refine ⟨68005242127868610676290083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45336828085245740450860055 68005242127868610676290083)
      ·
        refine ⟨102007863191802916014435125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68005242127868610676290083 102007863191802916014435125)
        ·
          refine ⟨9563237174231523376353293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102007863191802916014435125 9563237174231523376353293)
          ·
            refine ⟨3586213940336821266132485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9563237174231523376353293 3586213940336821266132485)
            ·
              refine ⟨672415113813153987399841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3586213940336821266132485 672415113813153987399841)
              ·
                refine ⟨504311335359865490549881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672415113813153987399841 504311335359865490549881)
                ·
                  refine ⟨378233501519899117912411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504311335359865490549881 378233501519899117912411)
                  ·
                    rfl

theorem cell20_828683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2].length) (baseStart_828683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828683 prefixEnd_828683 := by exact prefixLift 828683
  have htrace : WordTrace (prefixWord ++ tailWord_828683) baseStart_828683 baseEnd_828683 := by
    simpa [prefixWord, tailWord_828683, baseEnd_828683] using wordTrace_append hprefix tailTrace_828683
  have hstable : (prefixWord ++ tailWord_828683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828683).length < 2 ^ (prefixWord ++ tailWord_828683).sum := by decide
  have hdescent : baseEnd_828683 < baseStart_828683 := by decide
  rcases family_descends (prefixWord ++ tailWord_828683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828704 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_828704 : Nat := 118140960795 + 828704 * 2 ^ 59
def prefixEnd_828704 : Nat := 4983230072969 + 3 ^ 40 * 828704 * 2
def baseEnd_828704 : Nat := 378243086492116378212325

theorem tailTrace_828704 : CollatzResearch.WordTrace tailWord_828704 prefixEnd_828704 378243086492116378212325 := by
  unfold tailWord_828704
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112658994877207110210583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20150211993169609480280777 15112658994877207110210583)
  ·
    refine ⟨22668988492315810665315875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15112658994877207110210583 22668988492315810665315875)
    ·
      refine ⟨34003482738473715997973813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22668988492315810665315875 34003482738473715997973813)
      ·
        refine ⟨3187826506731910874810045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34003482738473715997973813 3187826506731910874810045)
        ·
          refine ⟨1195434940024466578053767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3187826506731910874810045 1195434940024466578053767)
          ·
            refine ⟨1793152410036699867080651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195434940024466578053767 1793152410036699867080651)
            ·
              refine ⟨2689728615055049800620977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793152410036699867080651 2689728615055049800620977)
              ·
                refine ⟨2017296461291287350465733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689728615055049800620977 2017296461291287350465733)
                ·
                  refine ⟨378243086492116378212325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017296461291287350465733 378243086492116378212325)
                  ·
                    rfl

theorem cell20_828704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_828704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828704 prefixEnd_828704 := by exact prefixLift 828704
  have htrace : WordTrace (prefixWord ++ tailWord_828704) baseStart_828704 baseEnd_828704 := by
    simpa [prefixWord, tailWord_828704, baseEnd_828704] using wordTrace_append hprefix tailTrace_828704
  have hstable : (prefixWord ++ tailWord_828704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828704).length < 2 ^ (prefixWord ++ tailWord_828704).sum := by decide
  have hdescent : baseEnd_828704 < baseStart_828704 := by decide
  rcases family_descends (prefixWord ++ tailWord_828704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828721 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 2]
def baseStart_828721 : Nat := 118140960795 + 828721 * 2 ^ 59
def prefixEnd_828721 : Nat := 4983230072969 + 3 ^ 40 * 828721 * 2
def baseEnd_828721 : Nat := 378250845755339874645589

theorem tailTrace_828721 : CollatzResearch.WordTrace tailWord_828721 prefixEnd_828721 378250845755339874645589 := by
  unfold tailWord_828721
  simp only [CollatzResearch.WordTrace]
  refine ⟨30225938030692826123790017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20150625353795217415860011 30225938030692826123790017)
  ·
    refine ⟨22669453523019619592842513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30225938030692826123790017 22669453523019619592842513)
    ·
      refine ⟨17002090142264714694631885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22669453523019619592842513 17002090142264714694631885)
      ·
        refine ⟨6375783803349268010486957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17002090142264714694631885 6375783803349268010486957)
        ·
          refine ⟨2390918926255975503932609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6375783803349268010486957 2390918926255975503932609)
          ·
            refine ⟨1793189194691981627949457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2390918926255975503932609 1793189194691981627949457)
            ·
              refine ⟨1344891896018986220962093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793189194691981627949457 1344891896018986220962093)
              ·
                refine ⟨504334461007119832860785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344891896018986220962093 504334461007119832860785)
                ·
                  refine ⟨378250845755339874645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504334461007119832860785 378250845755339874645589)
                  ·
                    rfl

theorem cell20_828721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_828721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828721 prefixEnd_828721 := by exact prefixLift 828721
  have htrace : WordTrace (prefixWord ++ tailWord_828721) baseStart_828721 baseEnd_828721 := by
    simpa [prefixWord, tailWord_828721, baseEnd_828721] using wordTrace_append hprefix tailTrace_828721
  have hstable : (prefixWord ++ tailWord_828721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828721).length < 2 ^ (prefixWord ++ tailWord_828721).sum := by decide
  have hdescent : baseEnd_828721 < baseStart_828721 := by decide
  rcases family_descends (prefixWord ++ tailWord_828721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828732 : List Nat := [2, 2, 2, 2, 1, 4, 7]
def baseStart_828732 : Nat := 118140960795 + 828732 * 2 ^ 59
def prefixEnd_828732 : Nat := 4983230072969 + 3 ^ 40 * 828732 * 2
def baseEnd_828732 : Nat := 42028429606119191697653

theorem tailTrace_828732 : CollatzResearch.WordTrace tailWord_828732 prefixEnd_828732 42028429606119191697653 := by
  unfold tailWord_828732
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113169616826487501220225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20150892822435316668293633 15113169616826487501220225)
  ·
    refine ⟨11334877212619865625915169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15113169616826487501220225 11334877212619865625915169)
    ·
      refine ⟨8501157909464899219436377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11334877212619865625915169 8501157909464899219436377)
      ·
        refine ⟨6375868432098674414577283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8501157909464899219436377 6375868432098674414577283)
        ·
          refine ⟨9563802648148011621865925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375868432098674414577283 9563802648148011621865925)
          ·
            refine ⟨1793212996527752179099861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9563802648148011621865925 1793212996527752179099861)
            ·
              refine ⟨42028429606119191697653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1793212996527752179099861 42028429606119191697653)
              ·
                rfl

theorem cell20_828732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_828732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828732 prefixEnd_828732 := by exact prefixLift 828732
  have htrace : WordTrace (prefixWord ++ tailWord_828732) baseStart_828732 baseEnd_828732 := by
    simpa [prefixWord, tailWord_828732, baseEnd_828732] using wordTrace_append hprefix tailTrace_828732
  have hstable : (prefixWord ++ tailWord_828732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828732).length < 2 ^ (prefixWord ++ tailWord_828732).sum := by decide
  have hdescent : baseEnd_828732 < baseStart_828732 := by decide
  rcases family_descends (prefixWord ++ tailWord_828732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828735 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_828735 : Nat := 118140960795 + 828735 * 2 ^ 59
def prefixEnd_828735 : Nat := 4983230072969 + 3 ^ 40 * 828735 * 2
def baseEnd_828735 : Nat := 378257235736818048178865

theorem tailTrace_828735 : CollatzResearch.WordTrace tailWord_828735 prefixEnd_828735 378257235736818048178865 := by
  unfold tailWord_828735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30226448652642106514799659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20150965768428071009866439 30226448652642106514799659)
  ·
    refine ⟨45339672978963159772199489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30226448652642106514799659 45339672978963159772199489)
    ·
      refine ⟨34004754734222369829149617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45339672978963159772199489 34004754734222369829149617)
      ·
        refine ⟨25503566050666777371862213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34004754734222369829149617 25503566050666777371862213)
        ·
          refine ⟨4781918634500020757224165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25503566050666777371862213 4781918634500020757224165)
          ·
            refine ⟨896609743968753891979531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4781918634500020757224165 896609743968753891979531)
            ·
              refine ⟨1344914615953130837969297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896609743968753891979531 1344914615953130837969297)
              ·
                refine ⟨1008685961964848128476973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344914615953130837969297 1008685961964848128476973)
                ·
                  refine ⟨378257235736818048178865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008685961964848128476973 378257235736818048178865)
                  ·
                    rfl

theorem cell20_828735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_828735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828735 prefixEnd_828735 := by exact prefixLift 828735
  have htrace : WordTrace (prefixWord ++ tailWord_828735) baseStart_828735 baseEnd_828735 := by
    simpa [prefixWord, tailWord_828735, baseEnd_828735] using wordTrace_append hprefix tailTrace_828735
  have hstable : (prefixWord ++ tailWord_828735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828735).length < 2 ^ (prefixWord ++ tailWord_828735).sum := by decide
  have hdescent : baseEnd_828735 < baseStart_828735 := by decide
  rcases family_descends (prefixWord ++ tailWord_828735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828758 : List Nat := [5, 2, 3, 1, 2, 1, 2, 4]
def baseStart_828758 : Nat := 118140960795 + 828758 * 2 ^ 59
def prefixEnd_828758 : Nat := 4983230072969 + 3 ^ 40 * 828758 * 2
def baseEnd_828758 : Nat := 126089244521177396804035

theorem tailTrace_828758 : CollatzResearch.WordTrace tailWord_828758 prefixEnd_828758 126089244521177396804035 := by
  unfold tailWord_828758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889205470722423840180433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20151525021039187628591285 1889205470722423840180433)
  ·
    refine ⟨1416904103041817880135325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1889205470722423840180433 1416904103041817880135325)
    ·
      refine ⟨531339038640681705050747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1416904103041817880135325 531339038640681705050747)
      ·
        refine ⟨797008557961022557576121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531339038640681705050747 797008557961022557576121)
        ·
          refine ⟨597756418470766918182091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797008557961022557576121 597756418470766918182091)
          ·
            refine ⟨896634627706150377273137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597756418470766918182091 896634627706150377273137)
            ·
              refine ⟨672475970779612782954853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896634627706150377273137 672475970779612782954853)
              ·
                refine ⟨126089244521177396804035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672475970779612782954853 126089244521177396804035)
                ·
                  rfl

theorem cell20_828758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_828758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828758 prefixEnd_828758 := by exact prefixLift 828758
  have htrace : WordTrace (prefixWord ++ tailWord_828758) baseStart_828758 baseEnd_828758 := by
    simpa [prefixWord, tailWord_828758, baseEnd_828758] using wordTrace_append hprefix tailTrace_828758
  have hstable : (prefixWord ++ tailWord_828758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828758).length < 2 ^ (prefixWord ++ tailWord_828758).sum := by decide
  have hdescent : baseEnd_828758 < baseStart_828758 := by decide
  rcases family_descends (prefixWord ++ tailWord_828758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828776 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_828776 : Nat := 118140960795 + 828776 * 2 ^ 59
def prefixEnd_828776 : Nat := 4983230072969 + 3 ^ 40 * 828776 * 2
def baseEnd_828776 : Nat := 378275949254004127812031

theorem tailTrace_828776 : CollatzResearch.WordTrace tailWord_828776 prefixEnd_828776 378275949254004127812031 := by
  unfold tailWord_828776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113972022746785258521091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20151962696995713678028121 15113972022746785258521091)
  ·
    refine ⟨22670958034120177887781637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15113972022746785258521091 22670958034120177887781637)
    ·
      refine ⟨4250804631397533353959057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22670958034120177887781637 4250804631397533353959057)
      ·
        refine ⟨3188103473548150015469293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4250804631397533353959057 3188103473548150015469293)
        ·
          refine ⟨1195538802580556255800985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3188103473548150015469293 1195538802580556255800985)
          ·
            refine ⟨896654101935417191850739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1195538802580556255800985 896654101935417191850739)
            ·
              refine ⟨1344981152903125787776109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896654101935417191850739 1344981152903125787776109)
              ·
                refine ⟨504367932338672170416041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344981152903125787776109 504367932338672170416041)
                ·
                  refine ⟨378275949254004127812031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504367932338672170416041 378275949254004127812031)
                  ·
                    rfl

theorem cell20_828776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_828776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828776 prefixEnd_828776 := by exact prefixLift 828776
  have htrace : WordTrace (prefixWord ++ tailWord_828776) baseStart_828776 baseEnd_828776 := by
    simpa [prefixWord, tailWord_828776, baseEnd_828776] using wordTrace_append hprefix tailTrace_828776
  have hstable : (prefixWord ++ tailWord_828776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828776).length < 2 ^ (prefixWord ++ tailWord_828776).sum := by decide
  have hdescent : baseEnd_828776 < baseStart_828776 := by decide
  rcases family_descends (prefixWord ++ tailWord_828776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828797 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 2]
def baseStart_828797 : Nat := 118140960795 + 828797 * 2 ^ 59
def prefixEnd_828797 : Nat := 4983230072969 + 3 ^ 40 * 828797 * 2
def baseEnd_828797 : Nat := 378285534226221388111945

theorem tailTrace_828797 : CollatzResearch.WordTrace tailWord_828797 prefixEnd_828797 378285534226221388111945 := by
  unfold tailWord_828797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30228709978417491103556645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20152473318944994069037763 30228709978417491103556645)
  ·
    refine ⟨5667883120953279581916871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30228709978417491103556645 5667883120953279581916871)
    ·
      refine ⟨8501824681429919372875307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5667883120953279581916871 8501824681429919372875307)
      ·
        refine ⟨12752737022144879059312961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501824681429919372875307 12752737022144879059312961)
        ·
          refine ⟨9564552766608659294484721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12752737022144879059312961 9564552766608659294484721)
          ·
            refine ⟨7173414574956494470863541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9564552766608659294484721 7173414574956494470863541)
            ·
              refine ⟨672507616402171356643457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7173414574956494470863541 672507616402171356643457)
              ·
                refine ⟨504380712301628517482593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672507616402171356643457 504380712301628517482593)
                ·
                  refine ⟨378285534226221388111945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504380712301628517482593 378285534226221388111945)
                  ·
                    rfl

theorem cell20_828797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_828797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828797 prefixEnd_828797 := by exact prefixLift 828797
  have htrace : WordTrace (prefixWord ++ tailWord_828797) baseStart_828797 baseEnd_828797 := by
    simpa [prefixWord, tailWord_828797, baseEnd_828797] using wordTrace_append hprefix tailTrace_828797
  have hstable : (prefixWord ++ tailWord_828797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828797).length < 2 ^ (prefixWord ++ tailWord_828797).sum := by decide
  have hdescent : baseEnd_828797 < baseStart_828797 := by decide
  rcases family_descends (prefixWord ++ tailWord_828797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828808 : List Nat := [2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_828808 : Nat := 118140960795 + 828808 * 2 ^ 59
def prefixEnd_828808 : Nat := 4983230072969 + 3 ^ 40 * 828808 * 2
def baseEnd_828808 : Nat := 126096851641984746248411

theorem tailTrace_828808 : CollatzResearch.WordTrace tailWord_828808 prefixEnd_828808 126096851641984746248411 := by
  unfold tailWord_828808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114555590688819991103539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20152740787585093321471385 15114555590688819991103539)
  ·
    refine ⟨22671833386033229986655309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15114555590688819991103539 22671833386033229986655309)
    ·
      refine ⟨8501937519762461244995741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22671833386033229986655309 8501937519762461244995741)
      ·
        refine ⟨3188226569910922966873403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8501937519762461244995741 3188226569910922966873403)
        ·
          refine ⟨4782339854866384450310105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188226569910922966873403 4782339854866384450310105)
          ·
            refine ⟨3586754891149788337732579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782339854866384450310105 3586754891149788337732579)
            ·
              refine ⟨5380132336724682506598869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586754891149788337732579 5380132336724682506598869)
              ·
                refine ⟨126096851641984746248411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5380132336724682506598869 126096851641984746248411)
                ·
                  rfl

theorem cell20_828808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_828808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828808 prefixEnd_828808 := by exact prefixLift 828808
  have htrace : WordTrace (prefixWord ++ tailWord_828808) baseStart_828808 baseEnd_828808 := by
    simpa [prefixWord, tailWord_828808, baseEnd_828808] using wordTrace_append hprefix tailTrace_828808
  have hstable : (prefixWord ++ tailWord_828808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828808).length < 2 ^ (prefixWord ++ tailWord_828808).sum := by decide
  have hdescent : baseEnd_828808 < baseStart_828808 := by decide
  rcases family_descends (prefixWord ++ tailWord_828808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828925 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 3]
def baseStart_828925 : Nat := 118140960795 + 828925 * 2 ^ 59
def prefixEnd_828925 : Nat := 4983230072969 + 3 ^ 40 * 828925 * 2
def baseEnd_828925 : Nat := 378343956914021831844755

theorem tailTrace_828925 : CollatzResearch.WordTrace tailWord_828925 prefixEnd_828925 378343956914021831844755 := by
  unfold tailWord_828925
  simp only [CollatzResearch.WordTrace]
  refine ⟨30233378521953768964216229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20155585681302512642810819 30233378521953768964216229)
  ·
    refine ⟨5668758472866331680790543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30233378521953768964216229 5668758472866331680790543)
    ·
      refine ⟨8503137709299497521185815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668758472866331680790543 8503137709299497521185815)
      ·
        refine ⟨12754706563949246281778723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503137709299497521185815 12754706563949246281778723)
        ·
          refine ⟨19132059845923869422668085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754706563949246281778723 19132059845923869422668085)
          ·
            refine ⟨1793630610555362758375133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19132059845923869422668085 1793630610555362758375133)
            ·
              refine ⟨672611478958261034390675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1793630610555362758375133 672611478958261034390675)
              ·
                refine ⟨1008917218437391551586013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672611478958261034390675 1008917218437391551586013)
                ·
                  refine ⟨378343956914021831844755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008917218437391551586013 378343956914021831844755)
                  ·
                    rfl

theorem cell20_828925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_828925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828925 prefixEnd_828925 := by exact prefixLift 828925
  have htrace : WordTrace (prefixWord ++ tailWord_828925) baseStart_828925 baseEnd_828925 := by
    simpa [prefixWord, tailWord_828925, baseEnd_828925] using wordTrace_append hprefix tailTrace_828925
  have hstable : (prefixWord ++ tailWord_828925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828925).length < 2 ^ (prefixWord ++ tailWord_828925).sum := by decide
  have hdescent : baseEnd_828925 < baseStart_828925 := by decide
  rcases family_descends (prefixWord ++ tailWord_828925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828949 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 2]
def baseStart_828949 : Nat := 118140960795 + 828949 * 2 ^ 59
def prefixEnd_828949 : Nat := 4983230072969 + 3 ^ 40 * 828949 * 2
def baseEnd_828949 : Nat := 378354911167984415044657

theorem tailTrace_828949 : CollatzResearch.WordTrace tailWord_828949 prefixEnd_828949 378354911167984415044657 := by
  unfold tailWord_828949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30234253873866821063089901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20156169249244547375393267 30234253873866821063089901)
  ·
    refine ⟨11337845202700057898658713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30234253873866821063089901 11337845202700057898658713)
    ·
      refine ⟨8503383902025043423994035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11337845202700057898658713 8503383902025043423994035)
      ·
        refine ⟨12755075853037565135991053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503383902025043423994035 12755075853037565135991053)
        ·
          refine ⟨4783153444889086925996645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12755075853037565135991053 4783153444889086925996645)
          ·
            refine ⟨896841270916703798624371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4783153444889086925996645 896841270916703798624371)
            ·
              refine ⟨1345261906375055697936557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896841270916703798624371 1345261906375055697936557)
              ·
                refine ⟨504473214890645886726209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1345261906375055697936557 504473214890645886726209)
                ·
                  refine ⟨378354911167984415044657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504473214890645886726209 378354911167984415044657)
                  ·
                    rfl

theorem cell20_828949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_828949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828949 prefixEnd_828949 := by exact prefixLift 828949
  have htrace : WordTrace (prefixWord ++ tailWord_828949) baseStart_828949 baseEnd_828949 := by
    simpa [prefixWord, tailWord_828949, baseEnd_828949] using wordTrace_append hprefix tailTrace_828949
  have hstable : (prefixWord ++ tailWord_828949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828949).length < 2 ^ (prefixWord ++ tailWord_828949).sum := by decide
  have hdescent : baseEnd_828949 < baseStart_828949 := by decide
  rcases family_descends (prefixWord ++ tailWord_828949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828960 : List Nat := [2, 1, 1, 6, 1, 1, 8]
def baseStart_828960 : Nat := 118140960795 + 828960 * 2 ^ 59
def prefixEnd_828960 : Nat := 4983230072969 + 3 ^ 40 * 828960 * 2
def baseEnd_828960 : Nat := 42039992429746362853105

theorem tailTrace_828960 : CollatzResearch.WordTrace tailWord_828960 prefixEnd_828960 42039992429746362853105 := by
  unfold tailWord_828960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15117327538413484970870167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20156436717884646627826889 15117327538413484970870167)
  ·
    refine ⟨22675991307620227456305251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15117327538413484970870167 22675991307620227456305251)
    ·
      refine ⟨34013986961430341184457877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22675991307620227456305251 34013986961430341184457877)
      ·
        refine ⟨1594405638817047243021463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34013986961430341184457877 1594405638817047243021463)
        ·
          refine ⟨2391608458225570864532195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594405638817047243021463 2391608458225570864532195)
          ·
            refine ⟨3587412687338356296798293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391608458225570864532195 3587412687338356296798293)
            ·
              refine ⟨42039992429746362853105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3587412687338356296798293 42039992429746362853105)
              ·
                rfl

theorem cell20_828960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_828960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828960 prefixEnd_828960 := by exact prefixLift 828960
  have htrace : WordTrace (prefixWord ++ tailWord_828960) baseStart_828960 baseEnd_828960 := by
    simpa [prefixWord, tailWord_828960, baseEnd_828960] using wordTrace_append hprefix tailTrace_828960
  have hstable : (prefixWord ++ tailWord_828960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828960).length < 2 ^ (prefixWord ++ tailWord_828960).sum := by decide
  have hdescent : baseEnd_828960 < baseStart_828960 := by decide
  rcases family_descends (prefixWord ++ tailWord_828960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828984 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_828984 : Nat := 118140960795 + 828984 * 2 ^ 59
def prefixEnd_828984 : Nat := 4983230072969 + 3 ^ 40 * 828984 * 2
def baseEnd_828984 : Nat := 378370886121679848877847

theorem tailTrace_828984 : CollatzResearch.WordTrace tailWord_828984 prefixEnd_828984 378370886121679848877847 := by
  unfold tailWord_828984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15117765214370011020307003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20157020285826681360409337 15117765214370011020307003)
  ·
    refine ⟨22676647821555016530460505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15117765214370011020307003 22676647821555016530460505)
    ·
      refine ⟨17007485866166262397845379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22676647821555016530460505 17007485866166262397845379)
      ·
        refine ⟨25511228799249393596768069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17007485866166262397845379 25511228799249393596768069)
        ·
          refine ⟨4783355399859261299394013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25511228799249393596768069 4783355399859261299394013)
          ·
            refine ⟨1793758274947222987272755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4783355399859261299394013 1793758274947222987272755)
            ·
              refine ⟨2690637412420834480909133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793758274947222987272755 2690637412420834480909133)
              ·
                refine ⟨1008989029657812930340925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2690637412420834480909133 1008989029657812930340925)
                ·
                  refine ⟨378370886121679848877847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008989029657812930340925 378370886121679848877847)
                  ·
                    rfl

theorem cell20_828984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_828984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_828984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_828984 prefixEnd_828984 := by exact prefixLift 828984
  have htrace : WordTrace (prefixWord ++ tailWord_828984) baseStart_828984 baseEnd_828984 := by
    simpa [prefixWord, tailWord_828984, baseEnd_828984] using wordTrace_append hprefix tailTrace_828984
  have hstable : (prefixWord ++ tailWord_828984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828984).length < 2 ^ (prefixWord ++ tailWord_828984).sum := by decide
  have hdescent : baseEnd_828984 < baseStart_828984 := by decide
  rcases family_descends (prefixWord ++ tailWord_828984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829046 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_829046 : Nat := 118140960795 + 829046 * 2 ^ 59
def prefixEnd_829046 : Nat := 4983230072969 + 3 ^ 40 * 829046 * 2
def baseEnd_829046 : Nat := 378399184611083188810927

theorem tailTrace_829046 : CollatzResearch.WordTrace tailWord_829046 prefixEnd_829046 378399184611083188810927 := by
  unfold tailWord_829046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889861984657212914335687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20158527836343604419580661 1889861984657212914335687)
  ·
    refine ⟨2834792976985819371503531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1889861984657212914335687 2834792976985819371503531)
    ·
      refine ⟨4252189465478729057255297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834792976985819371503531 4252189465478729057255297)
      ·
        refine ⟨3189142099109046792941473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4252189465478729057255297 3189142099109046792941473)
        ·
          refine ⟨2391856574331785094706105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189142099109046792941473 2391856574331785094706105)
          ·
            refine ⟨1793892430748838821029579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391856574331785094706105 1793892430748838821029579)
            ·
              refine ⟨2690838646123258231544369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793892430748838821029579 2690838646123258231544369)
              ·
                refine ⟨2018128984592443673658277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690838646123258231544369 2018128984592443673658277)
                ·
                  refine ⟨378399184611083188810927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018128984592443673658277 378399184611083188810927)
                  ·
                    rfl

theorem cell20_829046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_829046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829046 prefixEnd_829046 := by exact prefixLift 829046
  have htrace : WordTrace (prefixWord ++ tailWord_829046) baseStart_829046 baseEnd_829046 := by
    simpa [prefixWord, tailWord_829046, baseEnd_829046] using wordTrace_append hprefix tailTrace_829046
  have hstable : (prefixWord ++ tailWord_829046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829046).length < 2 ^ (prefixWord ++ tailWord_829046).sum := by decide
  have hdescent : baseEnd_829046 < baseStart_829046 := by decide
  rcases family_descends (prefixWord ++ tailWord_829046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829053 : List Nat := [1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_829053 : Nat := 118140960795 + 829053 * 2 ^ 59
def prefixEnd_829053 : Nat := 4983230072969 + 3 ^ 40 * 829053 * 2
def baseEnd_829053 : Nat := 126134126533940758525855

theorem tailTrace_829053 : CollatzResearch.WordTrace tailWord_829053 prefixEnd_829053 126134126533940758525855 := by
  unfold tailWord_829053
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238047065490046824875813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20158698043660031216583875 30238047065490046824875813)
  ·
    refine ⟨5669633824779383779664215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30238047065490046824875813 5669633824779383779664215)
    ·
      refine ⟨8504450737169075669496323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669633824779383779664215 8504450737169075669496323)
      ·
        refine ⟨12756676105753613504244485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8504450737169075669496323 12756676105753613504244485)
        ·
          refine ⟨2391876769828802532045841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12756676105753613504244485 2391876769828802532045841)
          ·
            refine ⟨1793907577371601899034381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391876769828802532045841 1793907577371601899034381)
            ·
              refine ⟨672715341514350712137893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1793907577371601899034381 672715341514350712137893)
              ·
                refine ⟨126134126533940758525855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672715341514350712137893 126134126533940758525855)
                ·
                  rfl

theorem cell20_829053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_829053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829053 prefixEnd_829053 := by exact prefixLift 829053
  have htrace : WordTrace (prefixWord ++ tailWord_829053) baseStart_829053 baseEnd_829053 := by
    simpa [prefixWord, tailWord_829053, baseEnd_829053] using wordTrace_append hprefix tailTrace_829053
  have hstable : (prefixWord ++ tailWord_829053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829053).length < 2 ^ (prefixWord ++ tailWord_829053).sum := by decide
  have hdescent : baseEnd_829053 < baseStart_829053 := by decide
  rcases family_descends (prefixWord ++ tailWord_829053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829081 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_829081 : Nat := 118140960795 + 829081 * 2 ^ 59
def prefixEnd_829081 : Nat := 4983230072969 + 3 ^ 40 * 829081 * 2
def baseEnd_829081 : Nat := 378415159564778622644117

theorem tailTrace_829081 : CollatzResearch.WordTrace tailWord_829081 prefixEnd_829081 378415159564778622644117 := by
  unfold tailWord_829081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30239068309388607606895097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20159378872925738404596731 30239068309388607606895097)
  ·
    refine ⟨22679301232041455705171323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30239068309388607606895097 22679301232041455705171323)
    ·
      refine ⟨34018951848062183557756985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22679301232041455705171323 34018951848062183557756985)
      ·
        refine ⟨25514213886046637668317739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34018951848062183557756985 25514213886046637668317739)
        ·
          refine ⟨38271320829069956502476609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25514213886046637668317739 38271320829069956502476609)
          ·
            refine ⟨28703490621802467376857457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38271320829069956502476609 28703490621802467376857457)
            ·
              refine ⟨21527617966351850532643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28703490621802467376857457 21527617966351850532643093)
              ·
                refine ⟨1009107092172742993717645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21527617966351850532643093 1009107092172742993717645)
                ·
                  refine ⟨378415159564778622644117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009107092172742993717645 378415159564778622644117)
                  ·
                    rfl

theorem cell20_829081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_829081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829081 prefixEnd_829081 := by exact prefixLift 829081
  have htrace : WordTrace (prefixWord ++ tailWord_829081) baseStart_829081 baseEnd_829081 := by
    simpa [prefixWord, tailWord_829081, baseEnd_829081] using wordTrace_append hprefix tailTrace_829081
  have hstable : (prefixWord ++ tailWord_829081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829081).length < 2 ^ (prefixWord ++ tailWord_829081).sum := by decide
  have hdescent : baseEnd_829081 < baseStart_829081 := by decide
  rcases family_descends (prefixWord ++ tailWord_829081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829084 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_829084 : Nat := 118140960795 + 829084 * 2 ^ 59
def prefixEnd_829084 : Nat := 4983230072969 + 3 ^ 40 * 829084 * 2
def baseEnd_829084 : Nat := 378416528846523945544105

theorem tailTrace_829084 : CollatzResearch.WordTrace tailWord_829084 prefixEnd_829084 378416528846523945544105 := by
  unfold tailWord_829084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15119588864188869559627153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20159451818918492746169537 15119588864188869559627153)
  ·
    refine ⟨11339691648141652169720365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15119588864188869559627153 11339691648141652169720365)
    ·
      refine ⟨4252384368053119563645137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11339691648141652169720365 4252384368053119563645137)
      ·
        refine ⟨3189288276039839672733853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4252384368053119563645137 3189288276039839672733853)
        ·
          refine ⟨1195983103514939877275195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3189288276039839672733853 1195983103514939877275195)
          ·
            refine ⟨1793974655272409815912793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195983103514939877275195 1793974655272409815912793)
            ·
              refine ⟨1345480991454307361934595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793974655272409815912793 1345480991454307361934595)
              ·
                refine ⟨2018221487181461042901893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345480991454307361934595 2018221487181461042901893)
                ·
                  refine ⟨378416528846523945544105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018221487181461042901893 378416528846523945544105)
                  ·
                    rfl

theorem cell20_829084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_829084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829084 prefixEnd_829084 := by exact prefixLift 829084
  have htrace : WordTrace (prefixWord ++ tailWord_829084) baseStart_829084 baseEnd_829084 := by
    simpa [prefixWord, tailWord_829084, baseEnd_829084] using wordTrace_append hprefix tailTrace_829084
  have hstable : (prefixWord ++ tailWord_829084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829084).length < 2 ^ (prefixWord ++ tailWord_829084).sum := by decide
  have hdescent : baseEnd_829084 < baseStart_829084 := by decide
  rcases family_descends (prefixWord ++ tailWord_829084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829149 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 3]
def baseStart_829149 : Nat := 118140960795 + 829149 * 2 ^ 59
def prefixEnd_829149 : Nat := 4983230072969 + 3 ^ 40 * 829149 * 2
def baseEnd_829149 : Nat := 378446196617672608377173

theorem tailTrace_829149 : CollatzResearch.WordTrace tailWord_829149 prefixEnd_829149 378446196617672608377173 := by
  unfold tailWord_829149
  simp only [CollatzResearch.WordTrace]
  refine ⟨30241548473142255220370501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20161032315428170146913667 30241548473142255220370501)
  ·
    refine ⟨5670290338714172853819469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30241548473142255220370501 5670290338714172853819469)
    ·
      refine ⟨2126358877017814820182301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5670290338714172853819469 2126358877017814820182301)
      ·
        refine ⟨797384578881680557568363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2126358877017814820182301 797384578881680557568363)
        ·
          refine ⟨1196076868322520836352545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797384578881680557568363 1196076868322520836352545)
          ·
            refine ⟨897057651241890627264409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196076868322520836352545 897057651241890627264409)
            ·
              refine ⟨672793238431417970448307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897057651241890627264409 672793238431417970448307)
              ·
                refine ⟨1009189857647126955672461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672793238431417970448307 1009189857647126955672461)
                ·
                  refine ⟨378446196617672608377173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009189857647126955672461 378446196617672608377173)
                  ·
                    rfl

theorem cell20_829149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_829149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829149 prefixEnd_829149 := by exact prefixLift 829149
  have htrace : WordTrace (prefixWord ++ tailWord_829149) baseStart_829149 baseEnd_829149 := by
    simpa [prefixWord, tailWord_829149, baseEnd_829149] using wordTrace_append hprefix tailTrace_829149
  have hstable : (prefixWord ++ tailWord_829149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829149).length < 2 ^ (prefixWord ++ tailWord_829149).sum := by decide
  have hdescent : baseEnd_829149 < baseStart_829149 := by decide
  rcases family_descends (prefixWord ++ tailWord_829149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829164 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_829164 : Nat := 118140960795 + 829164 * 2 ^ 59
def prefixEnd_829164 : Nat := 4983230072969 + 3 ^ 40 * 829164 * 2
def baseEnd_829164 : Nat := 378453043026399222877111

theorem tailTrace_829164 : CollatzResearch.WordTrace tailWord_829164 prefixEnd_829164 378453043026399222877111 := by
  unfold tailWord_829164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121047784043956391083273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20161397045391941854777697 15121047784043956391083273)
  ·
    refine ⟨11340785838032967293312455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15121047784043956391083273 11340785838032967293312455)
    ·
      refine ⟨17011178757049450939968683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11340785838032967293312455 17011178757049450939968683)
      ·
        refine ⟨25516768135574176409953025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17011178757049450939968683 25516768135574176409953025)
        ·
          refine ⟨19137576101680632307464769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25516768135574176409953025 19137576101680632307464769)
          ·
            refine ⟨14353182076260474230598577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19137576101680632307464769 14353182076260474230598577)
            ·
              refine ⟨10764886557195355672948933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14353182076260474230598577 10764886557195355672948933)
              ·
                refine ⟨2018416229474129188677925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10764886557195355672948933 2018416229474129188677925)
                ·
                  refine ⟨378453043026399222877111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018416229474129188677925 378453043026399222877111)
                  ·
                    rfl

theorem cell20_829164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_829164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829164 prefixEnd_829164 := by exact prefixLift 829164
  have htrace : WordTrace (prefixWord ++ tailWord_829164) baseStart_829164 baseEnd_829164 := by
    simpa [prefixWord, tailWord_829164, baseEnd_829164] using wordTrace_append hprefix tailTrace_829164
  have hstable : (prefixWord ++ tailWord_829164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829164).length < 2 ^ (prefixWord ++ tailWord_829164).sum := by decide
  have hdescent : baseEnd_829164 < baseStart_829164 := by decide
  rcases family_descends (prefixWord ++ tailWord_829164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829171 : List Nat := [1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_829171 : Nat := 118140960795 + 829171 * 2 ^ 59
def prefixEnd_829171 : Nat := 4983230072969 + 3 ^ 40 * 829171 * 2
def baseEnd_829171 : Nat := 126152079339046103214583

theorem tailTrace_829171 : CollatzResearch.WordTrace tailWord_829171 prefixEnd_829171 126152079339046103214583 := by
  unfold tailWord_829171
  simp only [CollatzResearch.WordTrace]
  refine ⟨30242350879062552977671367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20161567252708368651780911 30242350879062552977671367)
  ·
    refine ⟨45363526318593829466507051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30242350879062552977671367 45363526318593829466507051)
    ·
      refine ⟨68045289477890744199760577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45363526318593829466507051 68045289477890744199760577)
      ·
        refine ⟨51033967108418058149820433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68045289477890744199760577 51033967108418058149820433)
        ·
          refine ⟨38275475331313543612365325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51033967108418058149820433 38275475331313543612365325)
          ·
            refine ⟨14353303249242578854636997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38275475331313543612365325 14353303249242578854636997)
            ·
              refine ⟨2691244359232983535244437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14353303249242578854636997 2691244359232983535244437)
              ·
                refine ⟨126152079339046103214583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2691244359232983535244437 126152079339046103214583)
                ·
                  rfl

theorem cell20_829171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_829171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829171 prefixEnd_829171 := by exact prefixLift 829171
  have htrace : WordTrace (prefixWord ++ tailWord_829171) baseStart_829171 baseEnd_829171 := by
    simpa [prefixWord, tailWord_829171, baseEnd_829171] using wordTrace_append hprefix tailTrace_829171
  have hstable : (prefixWord ++ tailWord_829171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829171).length < 2 ^ (prefixWord ++ tailWord_829171).sum := by decide
  have hdescent : baseEnd_829171 < baseStart_829171 := by decide
  rcases family_descends (prefixWord ++ tailWord_829171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829191 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_829191 : Nat := 118140960795 + 829191 * 2 ^ 59
def prefixEnd_829191 : Nat := 4983230072969 + 3 ^ 40 * 829191 * 2
def baseEnd_829191 : Nat := 378465366562107128977001

theorem tailTrace_829191 : CollatzResearch.WordTrace tailWord_829191 prefixEnd_829191 378465366562107128977001 := by
  unfold tailWord_829191
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243080338990096393399427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20162053559326730928932951 30243080338990096393399427)
  ·
    refine ⟨45364620508485144590099141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30243080338990096393399427 45364620508485144590099141)
    ·
      refine ⟨8505866345340964610643589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45364620508485144590099141 8505866345340964610643589)
      ·
        refine ⟨1594849939751430864495673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8505866345340964610643589 1594849939751430864495673)
        ·
          refine ⟨1196137454813573148371755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1594849939751430864495673 1196137454813573148371755)
          ·
            refine ⟨1794206182220359722557633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196137454813573148371755 1794206182220359722557633)
            ·
              refine ⟨1345654636665269791918225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794206182220359722557633 1345654636665269791918225)
              ·
                refine ⟨1009240977498952343938669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345654636665269791918225 1009240977498952343938669)
                ·
                  refine ⟨378465366562107128977001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009240977498952343938669 378465366562107128977001)
                  ·
                    rfl

theorem cell20_829191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_829191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829191 prefixEnd_829191 := by exact prefixLift 829191
  have htrace : WordTrace (prefixWord ++ tailWord_829191) baseStart_829191 baseEnd_829191 := by
    simpa [prefixWord, tailWord_829191, baseEnd_829191] using wordTrace_append hprefix tailTrace_829191
  have hstable : (prefixWord ++ tailWord_829191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829191).length < 2 ^ (prefixWord ++ tailWord_829191).sum := by decide
  have hdescent : baseEnd_829191 < baseStart_829191 := by decide
  rcases family_descends (prefixWord ++ tailWord_829191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829195 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_829195 : Nat := 118140960795 + 829195 * 2 ^ 59
def prefixEnd_829195 : Nat := 4983230072969 + 3 ^ 40 * 829195 * 2
def baseEnd_829195 : Nat := 378467192271100892843651

theorem tailTrace_829195 : CollatzResearch.WordTrace tailWord_829195 prefixEnd_829195 378467192271100892843651 := by
  unfold tailWord_829195
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243226230975605076545039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20162150820650403384363359 30243226230975605076545039)
  ·
    refine ⟨45364839346463407614817559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30243226230975605076545039 45364839346463407614817559)
    ·
      refine ⟨68047259019695111422226339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45364839346463407614817559 68047259019695111422226339)
      ·
        refine ⟨102070888529542667133339509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68047259019695111422226339 102070888529542667133339509)
        ·
          refine ⟨9569145799644625043750579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102070888529542667133339509 9569145799644625043750579)
          ·
            refine ⟨14353718699466937565625869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569145799644625043750579 14353718699466937565625869)
            ·
              refine ⟨5382644512300101587109701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14353718699466937565625869 5382644512300101587109701)
              ·
                refine ⟨1009245846056269047583069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5382644512300101587109701 1009245846056269047583069)
                ·
                  refine ⟨378467192271100892843651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009245846056269047583069 378467192271100892843651)
                  ·
                    rfl

theorem cell20_829195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_829195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829195 prefixEnd_829195 := by exact prefixLift 829195
  have htrace : WordTrace (prefixWord ++ tailWord_829195) baseStart_829195 baseEnd_829195 := by
    simpa [prefixWord, tailWord_829195, baseEnd_829195] using wordTrace_append hprefix tailTrace_829195
  have hstable : (prefixWord ++ tailWord_829195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829195).length < 2 ^ (prefixWord ++ tailWord_829195).sum := by decide
  have hdescent : baseEnd_829195 < baseStart_829195 := by decide
  rcases family_descends (prefixWord ++ tailWord_829195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829197 : List Nat := [1, 7, 2, 1, 2, 1, 1, 5]
def baseStart_829197 : Nat := 118140960795 + 829197 * 2 ^ 59
def prefixEnd_829197 : Nat := 4983230072969 + 3 ^ 40 * 829197 * 2
def baseEnd_829197 : Nat := 126156035041865924925659

theorem tailTrace_829197 : CollatzResearch.WordTrace tailWord_829197 prefixEnd_829197 126156035041865924925659 := by
  unfold tailWord_829197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243299176968359418117845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20162199451312239612078563 30243299176968359418117845)
  ·
    refine ⟨708827324460195923862137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30243299176968359418117845 708827324460195923862137)
    ·
      refine ⟨531620493345146942896603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 708827324460195923862137 531620493345146942896603)
      ·
        refine ⟨797430740017720414344905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531620493345146942896603 797430740017720414344905)
        ·
          refine ⟨598073055013290310758679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797430740017720414344905 598073055013290310758679)
          ·
            refine ⟨897109582519935466138019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598073055013290310758679 897109582519935466138019)
            ·
              refine ⟨1345664373779903199207029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897109582519935466138019 1345664373779903199207029)
              ·
                refine ⟨126156035041865924925659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1345664373779903199207029 126156035041865924925659)
                ·
                  rfl

theorem cell20_829197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_829197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829197 prefixEnd_829197 := by exact prefixLift 829197
  have htrace : WordTrace (prefixWord ++ tailWord_829197) baseStart_829197 baseEnd_829197 := by
    simpa [prefixWord, tailWord_829197, baseEnd_829197] using wordTrace_append hprefix tailTrace_829197
  have hstable : (prefixWord ++ tailWord_829197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829197).length < 2 ^ (prefixWord ++ tailWord_829197).sum := by decide
  have hdescent : baseEnd_829197 < baseStart_829197 := by decide
  rcases family_descends (prefixWord ++ tailWord_829197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829257 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 2]
def baseStart_829257 : Nat := 118140960795 + 829257 * 2 ^ 59
def prefixEnd_829257 : Nat := 4983230072969 + 3 ^ 40 * 829257 * 2
def baseEnd_829257 : Nat := 378495490760504232776731

theorem tailTrace_829257 : CollatzResearch.WordTrace tailWord_829257 prefixEnd_829257 378495490760504232776731 := by
  unfold tailWord_829257
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245487556750989665302025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20163658371167326443534683 30245487556750989665302025)
  ·
    refine ⟨22684115667563242248976519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30245487556750989665302025 22684115667563242248976519)
    ·
      refine ⟨34026173501344863373464779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22684115667563242248976519 34026173501344863373464779)
      ·
        refine ⟨51039260252017295060197169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34026173501344863373464779 51039260252017295060197169)
        ·
          refine ⟨38279445189012971295147877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51039260252017295060197169 38279445189012971295147877)
          ·
            refine ⟨7177395972939932117840227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38279445189012971295147877 7177395972939932117840227)
            ·
              refine ⟨10766093959409898176760341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177395972939932117840227 10766093959409898176760341)
              ·
                refine ⟨504660654347338977035641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10766093959409898176760341 504660654347338977035641)
                ·
                  refine ⟨378495490760504232776731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504660654347338977035641 378495490760504232776731)
                  ·
                    rfl

theorem cell20_829257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_829257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829257 prefixEnd_829257 := by exact prefixLift 829257
  have htrace : WordTrace (prefixWord ++ tailWord_829257) baseStart_829257 baseEnd_829257 := by
    simpa [prefixWord, tailWord_829257, baseEnd_829257] using wordTrace_append hprefix tailTrace_829257
  have hstable : (prefixWord ++ tailWord_829257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829257).length < 2 ^ (prefixWord ++ tailWord_829257).sum := by decide
  have hdescent : baseEnd_829257 < baseStart_829257 := by decide
  rcases family_descends (prefixWord ++ tailWord_829257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829309 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_829309 : Nat := 118140960795 + 829309 * 2 ^ 59
def prefixEnd_829309 : Nat := 4983230072969 + 3 ^ 40 * 829309 * 2
def baseEnd_829309 : Nat := 378519224977423163043185

theorem tailTrace_829309 : CollatzResearch.WordTrace tailWord_829309 prefixEnd_829309 378519224977423163043185 := by
  unfold tailWord_829309
  simp only [CollatzResearch.WordTrace]
  refine ⟨30247384152562602546194981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20164922768375068364129987 30247384152562602546194981)
  ·
    refine ⟨5671384528605487977411559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30247384152562602546194981 5671384528605487977411559)
    ·
      refine ⟨8507076792908231966117339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671384528605487977411559 8507076792908231966117339)
      ·
        refine ⟨12760615189362347949176009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507076792908231966117339 12760615189362347949176009)
        ·
          refine ⟨9570461392021760961882007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12760615189362347949176009 9570461392021760961882007)
          ·
            refine ⟨14355692088032641442823011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570461392021760961882007 14355692088032641442823011)
            ·
              refine ⟨21533538132048962164234517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14355692088032641442823011 21533538132048962164234517)
              ·
                refine ⟨1009384599939795101448493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21533538132048962164234517 1009384599939795101448493)
                ·
                  refine ⟨378519224977423163043185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009384599939795101448493 378519224977423163043185)
                  ·
                    rfl

theorem cell20_829309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_829309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829309 prefixEnd_829309 := by exact prefixLift 829309
  have htrace : WordTrace (prefixWord ++ tailWord_829309) baseStart_829309 baseEnd_829309 := by
    simpa [prefixWord, tailWord_829309, baseEnd_829309] using wordTrace_append hprefix tailTrace_829309
  have hstable : (prefixWord ++ tailWord_829309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829309).length < 2 ^ (prefixWord ++ tailWord_829309).sum := by decide
  have hdescent : baseEnd_829309 < baseStart_829309 := by decide
  rcases family_descends (prefixWord ++ tailWord_829309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829312 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_829312 : Nat := 118140960795 + 829312 * 2 ^ 59
def prefixEnd_829312 : Nat := 4983230072969 + 3 ^ 40 * 829312 * 2
def baseEnd_829312 : Nat := 378520594259168485943173

theorem tailTrace_829312 : CollatzResearch.WordTrace tailWord_829312 prefixEnd_829312 378520594259168485943173 := by
  unfold tailWord_829312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15123746785775867029277095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20164995714367822705702793 15123746785775867029277095)
  ·
    refine ⟨22685620178663800543915643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15123746785775867029277095 22685620178663800543915643)
    ·
      refine ⟨34028430267995700815873465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22685620178663800543915643 34028430267995700815873465)
      ·
        refine ⟨25521322700996775611905099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34028430267995700815873465 25521322700996775611905099)
        ·
          refine ⟨38281984051495163417857649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25521322700996775611905099 38281984051495163417857649)
          ·
            refine ⟨28711488038621372563393237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38281984051495163417857649 28711488038621372563393237)
            ·
              refine ⟨672925500905188419454529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28711488038621372563393237 672925500905188419454529)
              ·
                refine ⟨504694125678891314590897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672925500905188419454529 504694125678891314590897)
                ·
                  refine ⟨378520594259168485943173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504694125678891314590897 378520594259168485943173)
                  ·
                    rfl

theorem cell20_829312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_829312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829312 prefixEnd_829312 := by exact prefixLift 829312
  have htrace : WordTrace (prefixWord ++ tailWord_829312) baseStart_829312 baseEnd_829312 := by
    simpa [prefixWord, tailWord_829312, baseEnd_829312] using wordTrace_append hprefix tailTrace_829312
  have hstable : (prefixWord ++ tailWord_829312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829312).length < 2 ^ (prefixWord ++ tailWord_829312).sum := by decide
  have hdescent : baseEnd_829312 < baseStart_829312 := by decide
  rcases family_descends (prefixWord ++ tailWord_829312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829322 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_829322 : Nat := 118140960795 + 829322 * 2 ^ 59
def prefixEnd_829322 : Nat := 4983230072969 + 3 ^ 40 * 829322 * 2
def baseEnd_829322 : Nat := 378525158531652895609799

theorem tailTrace_829322 : CollatzResearch.WordTrace tailWord_829322 prefixEnd_829322 378525158531652895609799 := by
  unfold tailWord_829322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7561964575378876441604555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20165238867677003844278813 7561964575378876441604555)
  ·
    refine ⟨11342946863068314662406833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7561964575378876441604555 11342946863068314662406833)
    ·
      refine ⟨8507210147301235996805125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11342946863068314662406833 8507210147301235996805125)
      ·
        refine ⟨1595101902618981749400961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8507210147301235996805125 1595101902618981749400961)
        ·
          refine ⟨1196326426964236312050721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595101902618981749400961 1196326426964236312050721)
          ·
            refine ⟨897244820223177234038041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196326426964236312050721 897244820223177234038041)
            ·
              refine ⟨672933615167382925528531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897244820223177234038041 672933615167382925528531)
              ·
                refine ⟨1009400422751074388292797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672933615167382925528531 1009400422751074388292797)
                ·
                  refine ⟨378525158531652895609799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009400422751074388292797 378525158531652895609799)
                  ·
                    rfl

theorem cell20_829322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_829322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829322 prefixEnd_829322 := by exact prefixLift 829322
  have htrace : WordTrace (prefixWord ++ tailWord_829322) baseStart_829322 baseEnd_829322 := by
    simpa [prefixWord, tailWord_829322, baseEnd_829322] using wordTrace_append hprefix tailTrace_829322
  have hstable : (prefixWord ++ tailWord_829322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829322).length < 2 ^ (prefixWord ++ tailWord_829322).sum := by decide
  have hdescent : baseEnd_829322 < baseStart_829322 := by decide
  rcases family_descends (prefixWord ++ tailWord_829322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829340 : List Nat := [2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_829340 : Nat := 118140960795 + 829340 * 2 ^ 59
def prefixEnd_829340 : Nat := 4983230072969 + 3 ^ 40 * 829340 * 2
def baseEnd_829340 : Nat := 126177791407374944336575

theorem tailTrace_829340 : CollatzResearch.WordTrace tailWord_829340 prefixEnd_829340 126177791407374944336575 := by
  unfold tailWord_829340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124257407725147420286737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20165676543633529893715649 15124257407725147420286737)
  ·
    refine ⟨11343193055793860565215053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15124257407725147420286737 11343193055793860565215053)
    ·
      refine ⟨4253697395922697711955645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11343193055793860565215053 4253697395922697711955645)
      ·
        refine ⟨1595136523471011641983367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4253697395922697711955645 1595136523471011641983367)
        ·
          refine ⟨2392704785206517462975051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595136523471011641983367 2392704785206517462975051)
          ·
            refine ⟨3589057177809776194462577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392704785206517462975051 3589057177809776194462577)
            ·
              refine ⟨2691792883357332145846933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589057177809776194462577 2691792883357332145846933)
              ·
                refine ⟨126177791407374944336575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2691792883357332145846933 126177791407374944336575)
                ·
                  rfl

theorem cell20_829340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_829340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829340 prefixEnd_829340 := by exact prefixLift 829340
  have htrace : WordTrace (prefixWord ++ tailWord_829340) baseStart_829340 baseEnd_829340 := by
    simpa [prefixWord, tailWord_829340, baseEnd_829340] using wordTrace_append hprefix tailTrace_829340
  have hstable : (prefixWord ++ tailWord_829340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829340).length < 2 ^ (prefixWord ++ tailWord_829340).sum := by decide
  have hdescent : baseEnd_829340 < baseStart_829340 := by decide
  rcases family_descends (prefixWord ++ tailWord_829340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829361 : List Nat := [1, 2, 2, 4, 2, 9]
def baseStart_829361 : Nat := 118140960795 + 829361 * 2 ^ 59
def prefixEnd_829361 : Nat := 4983230072969 + 3 ^ 40 * 829361 * 2
def baseEnd_829361 : Nat := 14020109599790447900357

theorem tailTrace_829361 : CollatzResearch.WordTrace tailWord_829361 prefixEnd_829361 14020109599790447900357 := by
  unfold tailWord_829361
  simp only [CollatzResearch.WordTrace]
  refine ⟨30249280748374215427087937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20166187165582810284725291 30249280748374215427087937)
  ·
    refine ⟨22686960561280661570315953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30249280748374215427087937 22686960561280661570315953)
    ·
      refine ⟨17015220420960496177736965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22686960561280661570315953 17015220420960496177736965)
      ·
        refine ⟨3190353828930093033325681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17015220420960496177736965 3190353828930093033325681)
        ·
          refine ⟨2392765371697569774994261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3190353828930093033325681 2392765371697569774994261)
          ·
            refine ⟨14020109599790447900357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2392765371697569774994261 14020109599790447900357)
            ·
              rfl

theorem cell20_829361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 9].length) (baseStart_829361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829361 prefixEnd_829361 := by exact prefixLift 829361
  have htrace : WordTrace (prefixWord ++ tailWord_829361) baseStart_829361 baseEnd_829361 := by
    simpa [prefixWord, tailWord_829361, baseEnd_829361] using wordTrace_append hprefix tailTrace_829361
  have hstable : (prefixWord ++ tailWord_829361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829361).length < 2 ^ (prefixWord ++ tailWord_829361).sum := by decide
  have hdescent : baseEnd_829361 < baseStart_829361 := by decide
  rcases family_descends (prefixWord ++ tailWord_829361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829405 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 2]
def baseStart_829405 : Nat := 118140960795 + 829405 * 2 ^ 59
def prefixEnd_829405 : Nat := 4983230072969 + 3 ^ 40 * 829405 * 2
def baseEnd_829405 : Nat := 378563041993273495842793

theorem tailTrace_829405 : CollatzResearch.WordTrace tailWord_829405 prefixEnd_829405 378563041993273495842793 := by
  unfold tailWord_829405
  simp only [CollatzResearch.WordTrace]
  refine ⟨30250885560214810941689669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20167257040143207294459779 30250885560214810941689669)
  ·
    refine ⟨5672041042540277051566813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30250885560214810941689669 5672041042540277051566813)
    ·
      refine ⟨2127015390952603894337555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5672041042540277051566813 2127015390952603894337555)
      ·
        refine ⟨3190523086428905841506333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127015390952603894337555 3190523086428905841506333)
        ·
          refine ⟨1196446157410839690564875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3190523086428905841506333 1196446157410839690564875)
          ·
            refine ⟨1794669236116259535847313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196446157410839690564875 1794669236116259535847313)
            ·
              refine ⟨1346001927087194651885485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794669236116259535847313 1346001927087194651885485)
              ·
                refine ⟨504750722657697994457057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346001927087194651885485 504750722657697994457057)
                ·
                  refine ⟨378563041993273495842793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504750722657697994457057 378563041993273495842793)
                  ·
                    rfl

theorem cell20_829405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_829405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829405 prefixEnd_829405 := by exact prefixLift 829405
  have htrace : WordTrace (prefixWord ++ tailWord_829405) baseStart_829405 baseEnd_829405 := by
    simpa [prefixWord, tailWord_829405, baseEnd_829405] using wordTrace_append hprefix tailTrace_829405
  have hstable : (prefixWord ++ tailWord_829405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829405).length < 2 ^ (prefixWord ++ tailWord_829405).sum := by decide
  have hdescent : baseEnd_829405 < baseStart_829405 := by decide
  rcases family_descends (prefixWord ++ tailWord_829405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829409 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 2]
def baseStart_829409 : Nat := 118140960795 + 829409 * 2 ^ 59
def prefixEnd_829409 : Nat := 4983230072969 + 3 ^ 40 * 829409 * 2
def baseEnd_829409 : Nat := 378564867702267259709443

theorem tailTrace_829409 : CollatzResearch.WordTrace tailWord_829409 prefixEnd_829409 378564867702267259709443 := by
  unfold tailWord_829409
  simp only [CollatzResearch.WordTrace]
  refine ⟨30251031452200319624835281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20167354301466879749890187 30251031452200319624835281)
  ·
    refine ⟨22688273589150239718626461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30251031452200319624835281 22688273589150239718626461)
    ·
      refine ⟨8508102595931339894484923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22688273589150239718626461 8508102595931339894484923)
      ·
        refine ⟨12762153893897009841727385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508102595931339894484923 12762153893897009841727385)
        ·
          refine ⟨9571615420422757381295539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12762153893897009841727385 9571615420422757381295539)
          ·
            refine ⟨14357423130634136071943309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9571615420422757381295539 14357423130634136071943309)
            ·
              refine ⟨5384033673987801026978741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14357423130634136071943309 5384033673987801026978741)
              ·
                refine ⟨504753156936356346279257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5384033673987801026978741 504753156936356346279257)
                ·
                  refine ⟨378564867702267259709443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504753156936356346279257 378564867702267259709443)
                  ·
                    rfl

theorem cell20_829409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_829409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829409 prefixEnd_829409 := by exact prefixLift 829409
  have htrace : WordTrace (prefixWord ++ tailWord_829409) baseStart_829409 baseEnd_829409 := by
    simpa [prefixWord, tailWord_829409, baseEnd_829409] using wordTrace_append hprefix tailTrace_829409
  have hstable : (prefixWord ++ tailWord_829409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829409).length < 2 ^ (prefixWord ++ tailWord_829409).sum := by decide
  have hdescent : baseEnd_829409 < baseStart_829409 := by decide
  rcases family_descends (prefixWord ++ tailWord_829409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829450 : List Nat := [3, 1, 2, 2, 5, 1, 2, 4]
def baseStart_829450 : Nat := 118140960795 + 829450 * 2 ^ 59
def prefixEnd_829450 : Nat := 4983230072969 + 3 ^ 40 * 829450 * 2
def baseEnd_829450 : Nat := 126194527073151113114203

theorem tailTrace_829450 : CollatzResearch.WordTrace tailWord_829450 prefixEnd_829450 126194527073151113114203 := by
  unfold tailWord_829450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563131711262945906769451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20168351230034522418051869 7563131711262945906769451)
  ·
    refine ⟨11344697566894418860154177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7563131711262945906769451 11344697566894418860154177)
    ·
      refine ⟨8508523175170814145115633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11344697566894418860154177 8508523175170814145115633)
      ·
        refine ⟨6381392381378110608836725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8508523175170814145115633 6381392381378110608836725)
        ·
          refine ⟨598255535754197869578443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6381392381378110608836725 598255535754197869578443)
          ·
            refine ⟨897383303631296804367665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598255535754197869578443 897383303631296804367665)
            ·
              refine ⟨673037477723472603275749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897383303631296804367665 673037477723472603275749)
              ·
                refine ⟨126194527073151113114203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673037477723472603275749 126194527073151113114203)
                ·
                  rfl

theorem cell20_829450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_829450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829450 prefixEnd_829450 := by exact prefixLift 829450
  have htrace : WordTrace (prefixWord ++ tailWord_829450) baseStart_829450 baseEnd_829450 := by
    simpa [prefixWord, tailWord_829450, baseEnd_829450] using wordTrace_append hprefix tailTrace_829450
  have hstable : (prefixWord ++ tailWord_829450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829450).length < 2 ^ (prefixWord ++ tailWord_829450).sum := by decide
  have hdescent : baseEnd_829450 < baseStart_829450 := by decide
  rcases family_descends (prefixWord ++ tailWord_829450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829533 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_829533 : Nat := 118140960795 + 829533 * 2 ^ 59
def prefixEnd_829533 : Nat := 4983230072969 + 3 ^ 40 * 829533 * 2
def baseEnd_829533 : Nat := 378621464681073939575603

theorem tailTrace_829533 : CollatzResearch.WordTrace tailWord_829533 prefixEnd_829533 378621464681073939575603 := by
  unfold tailWord_829533
  simp only [CollatzResearch.WordTrace]
  refine ⟨30255554103751088802349253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20170369402500725868232835 30255554103751088802349253)
  ·
    refine ⟨5672916394453329150440485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30255554103751088802349253 5672916394453329150440485)
    ·
      refine ⟨1063671823959999215707591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5672916394453329150440485 1063671823959999215707591)
      ·
        refine ⟨1595507735939998823561387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063671823959999215707591 1595507735939998823561387)
        ·
          refine ⟨2393261603909998235342081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595507735939998823561387 2393261603909998235342081)
          ·
            refine ⟨1794946202932498676506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393261603909998235342081 1794946202932498676506561)
            ·
              refine ⟨1346209652199374007379921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794946202932498676506561 1346209652199374007379921)
              ·
                refine ⟨1009657239149530505534941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346209652199374007379921 1009657239149530505534941)
                ·
                  refine ⟨378621464681073939575603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009657239149530505534941 378621464681073939575603)
                  ·
                    rfl

theorem cell20_829533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_829533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829533 prefixEnd_829533 := by exact prefixLift 829533
  have htrace : WordTrace (prefixWord ++ tailWord_829533) baseStart_829533 baseEnd_829533 := by
    simpa [prefixWord, tailWord_829533, baseEnd_829533] using wordTrace_append hprefix tailTrace_829533
  have hstable : (prefixWord ++ tailWord_829533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829533).length < 2 ^ (prefixWord ++ tailWord_829533).sum := by decide
  have hdescent : baseEnd_829533 < baseStart_829533 := by decide
  rcases family_descends (prefixWord ++ tailWord_829533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829540 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_829540 : Nat := 118140960795 + 829540 * 2 ^ 59
def prefixEnd_829540 : Nat := 4983230072969 + 3 ^ 40 * 829540 * 2
def baseEnd_829540 : Nat := 378624659671813026342241

theorem tailTrace_829540 : CollatzResearch.WordTrace tailWord_829540 prefixEnd_829540 378624659671813026342241 := by
  unfold tailWord_829540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127904707362864498927037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20170539609817152665236049 15127904707362864498927037)
  ·
    refine ⟨5672964265261074187097639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15127904707362864498927037 5672964265261074187097639)
    ·
      refine ⟨8509446397891611280646459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672964265261074187097639 8509446397891611280646459)
      ·
        refine ⟨12764169596837416920969689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509446397891611280646459 12764169596837416920969689)
        ·
          refine ⟨9573127197628062690727267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12764169596837416920969689 9573127197628062690727267)
          ·
            refine ⟨14359690796442094036090901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573127197628062690727267 14359690796442094036090901)
            ·
              refine ⟨673110506083223157941761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14359690796442094036090901 673110506083223157941761)
              ·
                refine ⟨504832879562417368456321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673110506083223157941761 504832879562417368456321)
                ·
                  refine ⟨378624659671813026342241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504832879562417368456321 378624659671813026342241)
                  ·
                    rfl

theorem cell20_829540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_829540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829540 prefixEnd_829540 := by exact prefixLift 829540
  have htrace : WordTrace (prefixWord ++ tailWord_829540) baseStart_829540 baseEnd_829540 := by
    simpa [prefixWord, tailWord_829540, baseEnd_829540] using wordTrace_append hprefix tailTrace_829540
  have hstable : (prefixWord ++ tailWord_829540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829540).length < 2 ^ (prefixWord ++ tailWord_829540).sum := by decide
  have hdescent : baseEnd_829540 < baseStart_829540 := by decide
  rcases family_descends (prefixWord ++ tailWord_829540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829551 : List Nat := [1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_829551 : Nat := 118140960795 + 829551 * 2 ^ 59
def prefixEnd_829551 : Nat := 4983230072969 + 3 ^ 40 * 829551 * 2
def baseEnd_829551 : Nat := 126209893457181958991843

theorem tailTrace_829551 : CollatzResearch.WordTrace tailWord_829551 prefixEnd_829551 126209893457181958991843 := by
  unfold tailWord_829551
  simp only [CollatzResearch.WordTrace]
  refine ⟨30256210617685877876504507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20170807078457251917669671 30256210617685877876504507)
  ·
    refine ⟨45384315926528816814756761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30256210617685877876504507 45384315926528816814756761)
    ·
      refine ⟨34038236944896612611067571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45384315926528816814756761 34038236944896612611067571)
      ·
        refine ⟨51057355417344918916601357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34038236944896612611067571 51057355417344918916601357)
        ·
          refine ⟨19146508281504344593725509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51057355417344918916601357 19146508281504344593725509)
          ·
            refine ⟨3589970302782064611323533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19146508281504344593725509 3589970302782064611323533)
            ·
              refine ⟨1346238863543274229246325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3589970302782064611323533 1346238863543274229246325)
              ·
                refine ⟨126209893457181958991843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1346238863543274229246325 126209893457181958991843)
                ·
                  rfl

theorem cell20_829551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_829551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829551 prefixEnd_829551 := by exact prefixLift 829551
  have htrace : WordTrace (prefixWord ++ tailWord_829551) baseStart_829551 baseEnd_829551 := by
    simpa [prefixWord, tailWord_829551, baseEnd_829551] using wordTrace_append hprefix tailTrace_829551
  have hstable : (prefixWord ++ tailWord_829551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829551).length < 2 ^ (prefixWord ++ tailWord_829551).sum := by decide
  have hdescent : baseEnd_829551 < baseStart_829551 := by decide
  rcases family_descends (prefixWord ++ tailWord_829551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829578 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_829578 : Nat := 118140960795 + 829578 * 2 ^ 59
def prefixEnd_829578 : Nat := 4983230072969 + 3 ^ 40 * 829578 * 2
def baseEnd_829578 : Nat := 378642003907253783075419

theorem tailTrace_829578 : CollatzResearch.WordTrace tailWord_829578 prefixEnd_829578 378642003907253783075419 := by
  unfold tailWord_829578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564298847147015371934347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20171463592392040991824925 7564298847147015371934347)
  ·
    refine ⟨11346448270720523057901521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7564298847147015371934347 11346448270720523057901521)
    ·
      refine ⟨8509836203040392293426141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11346448270720523057901521 8509836203040392293426141)
      ·
        refine ⟨3191188576140147110034803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8509836203040392293426141 3191188576140147110034803)
        ·
          refine ⟨4786782864210220665052205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191188576140147110034803 4786782864210220665052205)
          ·
            refine ⟨1795043574078832749394577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4786782864210220665052205 1795043574078832749394577)
            ·
              refine ⟨1346282680559124562045933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795043574078832749394577 1346282680559124562045933)
              ·
                refine ⟨504856005209671710767225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346282680559124562045933 504856005209671710767225)
                ·
                  refine ⟨378642003907253783075419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504856005209671710767225 378642003907253783075419)
                  ·
                    rfl

theorem cell20_829578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_829578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829578 prefixEnd_829578 := by exact prefixLift 829578
  have htrace : WordTrace (prefixWord ++ tailWord_829578) baseStart_829578 baseEnd_829578 := by
    simpa [prefixWord, tailWord_829578, baseEnd_829578] using wordTrace_append hprefix tailTrace_829578
  have hstable : (prefixWord ++ tailWord_829578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829578).length < 2 ^ (prefixWord ++ tailWord_829578).sum := by decide
  have hdescent : baseEnd_829578 < baseStart_829578 := by decide
  rcases family_descends (prefixWord ++ tailWord_829578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829588 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_829588 : Nat := 118140960795 + 829588 * 2 ^ 59
def prefixEnd_829588 : Nat := 4983230072969 + 3 ^ 40 * 829588 * 2
def baseEnd_829588 : Nat := 378646568179738192742045

theorem tailTrace_829588 : CollatzResearch.WordTrace tailWord_829588 prefixEnd_829588 378646568179738192742045 := by
  unfold tailWord_829588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128780059275916597800709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20171706745701222130400945 15128780059275916597800709)
  ·
    refine ⟨2836646261114234362087633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15128780059275916597800709 2836646261114234362087633)
    ·
      refine ⟨2127484695835675771565725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836646261114234362087633 2127484695835675771565725)
      ·
        refine ⟨797806760938378414337147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2127484695835675771565725 797806760938378414337147)
        ·
          refine ⟨1196710141407567621505721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797806760938378414337147 1196710141407567621505721)
          ·
            refine ⟨897532606055675716129291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196710141407567621505721 897532606055675716129291)
            ·
              refine ⟨1346298909083513574193937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897532606055675716129291 1346298909083513574193937)
              ·
                refine ⟨1009724181812635180645453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346298909083513574193937 1009724181812635180645453)
                ·
                  refine ⟨378646568179738192742045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009724181812635180645453 378646568179738192742045)
                  ·
                    rfl

theorem cell20_829588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_829588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829588 prefixEnd_829588 := by exact prefixLift 829588
  have htrace : WordTrace (prefixWord ++ tailWord_829588) baseStart_829588 baseEnd_829588 := by
    simpa [prefixWord, tailWord_829588, baseEnd_829588] using wordTrace_append hprefix tailTrace_829588
  have hstable : (prefixWord ++ tailWord_829588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829588).length < 2 ^ (prefixWord ++ tailWord_829588).sum := by decide
  have hdescent : baseEnd_829588 < baseStart_829588 := by decide
  rcases family_descends (prefixWord ++ tailWord_829588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829599 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_829599 : Nat := 118140960795 + 829599 * 2 ^ 59
def prefixEnd_829599 : Nat := 4983230072969 + 3 ^ 40 * 829599 * 2
def baseEnd_829599 : Nat := 378651588879471043375333

theorem tailTrace_829599 : CollatzResearch.WordTrace tailWord_829599 prefixEnd_829599 378651588879471043375333 := by
  unfold tailWord_829599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257961321511982074251851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20171974214341321382834567 30257961321511982074251851)
  ·
    refine ⟨45386941982267973111377777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30257961321511982074251851 45386941982267973111377777)
    ·
      refine ⟨34040206486700979833533333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45386941982267973111377777 34040206486700979833533333)
      ·
        refine ⟨1595634679064108429696875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34040206486700979833533333 1595634679064108429696875)
        ·
          refine ⟨2393452018596162644545313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595634679064108429696875 2393452018596162644545313)
          ·
            refine ⟨1795089013947121983408985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393452018596162644545313 1795089013947121983408985)
            ·
              refine ⟨1346316760460341487556739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795089013947121983408985 1346316760460341487556739)
              ·
                refine ⟨2019475140690512231335109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346316760460341487556739 2019475140690512231335109)
                ·
                  refine ⟨378651588879471043375333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019475140690512231335109 378651588879471043375333)
                  ·
                    rfl

theorem cell20_829599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_829599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829599 prefixEnd_829599 := by exact prefixLift 829599
  have htrace : WordTrace (prefixWord ++ tailWord_829599) baseStart_829599 baseEnd_829599 := by
    simpa [prefixWord, tailWord_829599, baseEnd_829599] using wordTrace_append hprefix tailTrace_829599
  have hstable : (prefixWord ++ tailWord_829599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829599).length < 2 ^ (prefixWord ++ tailWord_829599).sum := by decide
  have hdescent : baseEnd_829599 < baseStart_829599 := by decide
  rcases family_descends (prefixWord ++ tailWord_829599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829637 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 2]
def baseStart_829637 : Nat := 118140960795 + 829637 * 2 ^ 59
def prefixEnd_829637 : Nat := 4983230072969 + 3 ^ 40 * 829637 * 2
def baseEnd_829637 : Nat := 378668933114911800108511

theorem tailTrace_829637 : CollatzResearch.WordTrace tailWord_829637 prefixEnd_829637 378668933114911800108511 := by
  unfold tailWord_829637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30259347295374314564135165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20172898196916209709423443 30259347295374314564135165)
  ·
    refine ⟨11347255235765367961550687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30259347295374314564135165 11347255235765367961550687)
    ·
      refine ⟨17020882853648051942326031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11347255235765367961550687 17020882853648051942326031)
      ·
        refine ⟨25531324280472077913489047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17020882853648051942326031 25531324280472077913489047)
        ·
          refine ⟨38296986420708116870233571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25531324280472077913489047 38296986420708116870233571)
          ·
            refine ⟨57445479631062175305350357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38296986420708116870233571 57445479631062175305350357)
            ·
              refine ⟨1346378428853019733719149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57445479631062175305350357 1346378428853019733719149)
              ·
                refine ⟨504891910819882400144681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346378428853019733719149 504891910819882400144681)
                ·
                  refine ⟨378668933114911800108511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504891910819882400144681 378668933114911800108511)
                  ·
                    rfl

theorem cell20_829637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_829637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829637 prefixEnd_829637 := by exact prefixLift 829637
  have htrace : WordTrace (prefixWord ++ tailWord_829637) baseStart_829637 baseEnd_829637 := by
    simpa [prefixWord, tailWord_829637, baseEnd_829637] using wordTrace_append hprefix tailTrace_829637
  have hstable : (prefixWord ++ tailWord_829637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829637).length < 2 ^ (prefixWord ++ tailWord_829637).sum := by decide
  have hdescent : baseEnd_829637 < baseStart_829637 := by decide
  rcases family_descends (prefixWord ++ tailWord_829637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829654 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_829654 : Nat := 118140960795 + 829654 * 2 ^ 59
def prefixEnd_829654 : Nat := 4983230072969 + 3 ^ 40 * 829654 * 2
def baseEnd_829654 : Nat := 378676692378135296541775

theorem tailTrace_829654 : CollatzResearch.WordTrace tailWord_829654 prefixEnd_829654 378676692378135296541775 := by
  unfold tailWord_829654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891247958519545404219001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20173311557541817645002677 1891247958519545404219001)
  ·
    refine ⟨1418435968889659053164251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1891247958519545404219001 1418435968889659053164251)
    ·
      refine ⟨2127653953334488579746377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418435968889659053164251 2127653953334488579746377)
      ·
        refine ⟨1595740465000866434809783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127653953334488579746377 1595740465000866434809783)
        ·
          refine ⟨2393610697501299652214675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595740465000866434809783 2393610697501299652214675)
          ·
            refine ⟨3590416046251949478322013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393610697501299652214675 3590416046251949478322013)
            ·
              refine ⟨1346406017344481054370755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3590416046251949478322013 1346406017344481054370755)
              ·
                refine ⟨2019609026016721581556133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346406017344481054370755 2019609026016721581556133)
                ·
                  refine ⟨378676692378135296541775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019609026016721581556133 378676692378135296541775)
                  ·
                    rfl

theorem cell20_829654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_829654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829654 prefixEnd_829654 := by exact prefixLift 829654
  have htrace : WordTrace (prefixWord ++ tailWord_829654) baseStart_829654 baseEnd_829654 := by
    simpa [prefixWord, tailWord_829654, baseEnd_829654] using wordTrace_append hprefix tailTrace_829654
  have hstable : (prefixWord ++ tailWord_829654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829654).length < 2 ^ (prefixWord ++ tailWord_829654).sum := by decide
  have hdescent : baseEnd_829654 < baseStart_829654 := by decide
  rcases family_descends (prefixWord ++ tailWord_829654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829658 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_829658 : Nat := 118140960795 + 829658 * 2 ^ 59
def prefixEnd_829658 : Nat := 4983230072969 + 3 ^ 40 * 829658 * 2
def baseEnd_829658 : Nat := 378678518087129060408425

theorem tailTrace_829658 : CollatzResearch.WordTrace tailWord_829658 prefixEnd_829658 378678518087129060408425 := by
  unfold tailWord_829658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565028307074558787662407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20173408818865490100433085 7565028307074558787662407)
  ·
    refine ⟨11347542460611838181493611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565028307074558787662407 11347542460611838181493611)
    ·
      refine ⟨17021313690917757272240417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11347542460611838181493611 17021313690917757272240417)
      ·
        refine ⟨12765985268188317954180313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17021313690917757272240417 12765985268188317954180313)
        ·
          refine ⟨9574488951141238465635235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12765985268188317954180313 9574488951141238465635235)
          ·
            refine ⟨14361733426711857698452853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574488951141238465635235 14361733426711857698452853)
            ·
              refine ⟨1346412508754236659229955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14361733426711857698452853 1346412508754236659229955)
              ·
                refine ⟨2019618763131354988844933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346412508754236659229955 2019618763131354988844933)
                ·
                  refine ⟨378678518087129060408425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019618763131354988844933 378678518087129060408425)
                  ·
                    rfl

theorem cell20_829658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_829658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829658 prefixEnd_829658 := by exact prefixLift 829658
  have htrace : WordTrace (prefixWord ++ tailWord_829658) baseStart_829658 baseEnd_829658 := by
    simpa [prefixWord, tailWord_829658, baseEnd_829658] using wordTrace_append hprefix tailTrace_829658
  have hstable : (prefixWord ++ tailWord_829658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829658).length < 2 ^ (prefixWord ++ tailWord_829658).sum := by decide
  have hdescent : baseEnd_829658 < baseStart_829658 := by decide
  rcases family_descends (prefixWord ++ tailWord_829658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829665 : List Nat := [1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_829665 : Nat := 118140960795 + 829665 * 2 ^ 59
def prefixEnd_829665 : Nat := 4983230072969 + 3 ^ 40 * 829665 * 2
def baseEnd_829665 : Nat := 126227237692622715725021

theorem tailTrace_829665 : CollatzResearch.WordTrace tailWord_829665 prefixEnd_829665 126227237692622715725021 := by
  unfold tailWord_829665
  simp only [CollatzResearch.WordTrace]
  refine ⟨30260368539272875346154449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20173579026181916897436299 30260368539272875346154449)
  ·
    refine ⟨22695276404454656509615837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30260368539272875346154449 22695276404454656509615837)
    ·
      refine ⟨8510728651670496191105939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22695276404454656509615837 8510728651670496191105939)
      ·
        refine ⟨12766092977505744286658909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8510728651670496191105939 12766092977505744286658909)
        ·
          refine ⟨4787284866564654107497091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12766092977505744286658909 4787284866564654107497091)
          ·
            refine ⟨7180927299846981161245637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787284866564654107497091 7180927299846981161245637)
            ·
              refine ⟨1346423868721308967733557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7180927299846981161245637 1346423868721308967733557)
              ·
                refine ⟨126227237692622715725021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1346423868721308967733557 126227237692622715725021)
                ·
                  rfl

theorem cell20_829665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_829665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829665 prefixEnd_829665 := by exact prefixLift 829665
  have htrace : WordTrace (prefixWord ++ tailWord_829665) baseStart_829665 baseEnd_829665 := by
    simpa [prefixWord, tailWord_829665, baseEnd_829665] using wordTrace_append hprefix tailTrace_829665
  have hstable : (prefixWord ++ tailWord_829665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829665).length < 2 ^ (prefixWord ++ tailWord_829665).sum := by decide
  have hdescent : baseEnd_829665 < baseStart_829665 := by decide
  rcases family_descends (prefixWord ++ tailWord_829665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829703 : List Nat := [1, 1, 4, 5, 9]
def baseStart_829703 : Nat := 118140960795 + 829703 * 2 ^ 59
def prefixEnd_829703 : Nat := 4983230072969 + 3 ^ 40 * 829703 * 2
def baseEnd_829703 : Nat := 4675297003868011159361

theorem tailTrace_829703 : CollatzResearch.WordTrace tailWord_829703 prefixEnd_829703 4675297003868011159361 := by
  unfold tailWord_829703
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261754513135207836037763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20174503008756805224025175 30261754513135207836037763)
  ·
    refine ⟨45392631769702811754056645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30261754513135207836037763 45392631769702811754056645)
    ·
      refine ⟨8511118456819277203885621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45392631769702811754056645 8511118456819277203885621)
      ·
        refine ⟨797917355326807237864277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8511118456819277203885621 797917355326807237864277)
        ·
          refine ⟨4675297003868011159361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 797917355326807237864277 4675297003868011159361)
          ·
            rfl

theorem cell20_829703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 9].length) (baseStart_829703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829703 prefixEnd_829703 := by exact prefixLift 829703
  have htrace : WordTrace (prefixWord ++ tailWord_829703) baseStart_829703 baseEnd_829703 := by
    simpa [prefixWord, tailWord_829703, baseEnd_829703] using wordTrace_append hprefix tailTrace_829703
  have hstable : (prefixWord ++ tailWord_829703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829703).length < 2 ^ (prefixWord ++ tailWord_829703).sum := by decide
  have hdescent : baseEnd_829703 < baseStart_829703 := by decide
  rcases family_descends (prefixWord ++ tailWord_829703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829713 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 2]
def baseStart_829713 : Nat := 118140960795 + 829713 * 2 ^ 59
def prefixEnd_829713 : Nat := 4983230072969 + 3 ^ 40 * 829713 * 2
def baseEnd_829713 : Nat := 378703621585793313574867

theorem tailTrace_829713 : CollatzResearch.WordTrace tailWord_829713 prefixEnd_829713 378703621585793313574867 := by
  unfold tailWord_829713
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262119243098979543901793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20174746162065986362601195 30262119243098979543901793)
  ·
    refine ⟨22696589432324234657926345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30262119243098979543901793 22696589432324234657926345)
    ·
      refine ⟨17022442074243175993444759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22696589432324234657926345 17022442074243175993444759)
      ·
        refine ⟨25533663111364763990167139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17022442074243175993444759 25533663111364763990167139)
        ·
          refine ⟨38300494667047145985250709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25533663111364763990167139 38300494667047145985250709)
          ·
            refine ⟨1795335687517834968058627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38300494667047145985250709 1795335687517834968058627)
            ·
              refine ⟨2693003531276752452087941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795335687517834968058627 2693003531276752452087941)
              ·
                refine ⟨504938162114391084766489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2693003531276752452087941 504938162114391084766489)
                ·
                  refine ⟨378703621585793313574867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504938162114391084766489 378703621585793313574867)
                  ·
                    rfl

theorem cell20_829713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_829713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829713 prefixEnd_829713 := by exact prefixLift 829713
  have htrace : WordTrace (prefixWord ++ tailWord_829713) baseStart_829713 baseEnd_829713 := by
    simpa [prefixWord, tailWord_829713, baseEnd_829713] using wordTrace_append hprefix tailTrace_829713
  have hstable : (prefixWord ++ tailWord_829713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829713).length < 2 ^ (prefixWord ++ tailWord_829713).sum := by decide
  have hdescent : baseEnd_829713 < baseStart_829713 := by decide
  rcases family_descends (prefixWord ++ tailWord_829713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829727 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_829727 : Nat := 118140960795 + 829727 * 2 ^ 59
def prefixEnd_829727 : Nat := 4983230072969 + 3 ^ 40 * 829727 * 2
def baseEnd_829727 : Nat := 378710011567271487108143

theorem tailTrace_829727 : CollatzResearch.WordTrace tailWord_829727 prefixEnd_829727 378710011567271487108143 := by
  unfold tailWord_829727
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262629865048259934911435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20175086576698839956607623 30262629865048259934911435)
  ·
    refine ⟨45393944797572389902367153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30262629865048259934911435 45393944797572389902367153)
    ·
      refine ⟨34045458598179292426775365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45393944797572389902367153 34045458598179292426775365)
      ·
        refine ⟨6383523487158617330020381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34045458598179292426775365 6383523487158617330020381)
        ·
          refine ⟨2393821307684481498757643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6383523487158617330020381 2393821307684481498757643)
          ·
            refine ⟨3590731961526722248136465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393821307684481498757643 3590731961526722248136465)
            ·
              refine ⟨2693048971145041686102349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590731961526722248136465 2693048971145041686102349)
              ·
                refine ⟨1009893364179390632288381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2693048971145041686102349 1009893364179390632288381)
                ·
                  refine ⟨378710011567271487108143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009893364179390632288381 378710011567271487108143)
                  ·
                    rfl

theorem cell20_829727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_829727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829727 prefixEnd_829727 := by exact prefixLift 829727
  have htrace : WordTrace (prefixWord ++ tailWord_829727) baseStart_829727 baseEnd_829727 := by
    simpa [prefixWord, tailWord_829727, baseEnd_829727] using wordTrace_append hprefix tailTrace_829727
  have hstable : (prefixWord ++ tailWord_829727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829727).length < 2 ^ (prefixWord ++ tailWord_829727).sum := by decide
  have hdescent : baseEnd_829727 < baseStart_829727 := by decide
  rcases family_descends (prefixWord ++ tailWord_829727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829761 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_829761 : Nat := 118140960795 + 829761 * 2 ^ 59
def prefixEnd_829761 : Nat := 4983230072969 + 3 ^ 40 * 829761 * 2
def baseEnd_829761 : Nat := 378725530093718479974671

theorem tailTrace_829761 : CollatzResearch.WordTrace tailWord_829761 prefixEnd_829761 378725530093718479974671 := by
  unfold tailWord_829761
  simp only [CollatzResearch.WordTrace]
  refine ⟨30263869946925083741649137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20175913297950055827766091 30263869946925083741649137)
  ·
    refine ⟨22697902460193812806236853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30263869946925083741649137 22697902460193812806236853)
    ·
      refine ⟨2127928355643169950584705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22697902460193812806236853 2127928355643169950584705)
      ·
        refine ⟨1595946266732377462938529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127928355643169950584705 1595946266732377462938529)
        ·
          refine ⟨1196959700049283097203897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595946266732377462938529 1196959700049283097203897)
          ·
            refine ⟨897719775036962322902923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196959700049283097203897 897719775036962322902923)
            ·
              refine ⟨1346579662555443484354385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897719775036962322902923 1346579662555443484354385)
              ·
                refine ⟨1009934746916582613265789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346579662555443484354385 1009934746916582613265789)
                ·
                  refine ⟨378725530093718479974671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009934746916582613265789 378725530093718479974671)
                  ·
                    rfl

theorem cell20_829761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_829761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829761 prefixEnd_829761 := by exact prefixLift 829761
  have htrace : WordTrace (prefixWord ++ tailWord_829761) baseStart_829761 baseEnd_829761 := by
    simpa [prefixWord, tailWord_829761, baseEnd_829761] using wordTrace_append hprefix tailTrace_829761
  have hstable : (prefixWord ++ tailWord_829761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829761).length < 2 ^ (prefixWord ++ tailWord_829761).sum := by decide
  have hdescent : baseEnd_829761 < baseStart_829761 := by decide
  rcases family_descends (prefixWord ++ tailWord_829761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829772 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_829772 : Nat := 118140960795 + 829772 * 2 ^ 59
def prefixEnd_829772 : Nat := 4983230072969 + 3 ^ 40 * 829772 * 2
def baseEnd_829772 : Nat := 378730550793451330607959

theorem tailTrace_829772 : CollatzResearch.WordTrace tailWord_829772 prefixEnd_829772 378730550793451330607959 := by
  unfold tailWord_829772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15132135574942616310149785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20176180766590155080199713 15132135574942616310149785)
  ·
    refine ⟨11349101681206962232612339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15132135574942616310149785 11349101681206962232612339)
    ·
      refine ⟨17023652521810443348918509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11349101681206962232612339 17023652521810443348918509)
      ·
        refine ⟨6383869695678916255844441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17023652521810443348918509 6383869695678916255844441)
        ·
          refine ⟨4787902271759187191883331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6383869695678916255844441 4787902271759187191883331)
          ·
            refine ⟨7181853407638780787824997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787902271759187191883331 7181853407638780787824997)
            ·
              refine ⟨1346597513932271397717187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7181853407638780787824997 1346597513932271397717187)
              ·
                refine ⟨2019896270898407096575781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346597513932271397717187 2019896270898407096575781)
                ·
                  refine ⟨378730550793451330607959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2019896270898407096575781 378730550793451330607959)
                  ·
                    rfl

theorem cell20_829772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_829772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829772 prefixEnd_829772 := by exact prefixLift 829772
  have htrace : WordTrace (prefixWord ++ tailWord_829772) baseStart_829772 baseEnd_829772 := by
    simpa [prefixWord, tailWord_829772, baseEnd_829772] using wordTrace_append hprefix tailTrace_829772
  have hstable : (prefixWord ++ tailWord_829772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829772).length < 2 ^ (prefixWord ++ tailWord_829772).sum := by decide
  have hdescent : baseEnd_829772 < baseStart_829772 := by decide
  rcases family_descends (prefixWord ++ tailWord_829772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829827 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_829827 : Nat := 118140960795 + 829827 * 2 ^ 59
def prefixEnd_829827 : Nat := 4983230072969 + 3 ^ 40 * 829827 * 2
def baseEnd_829827 : Nat := 378755654292115583774401

theorem tailTrace_829827 : CollatzResearch.WordTrace tailWord_829827 prefixEnd_829827 378755654292115583774401 := by
  unfold tailWord_829827
  simp only [CollatzResearch.WordTrace]
  refine ⟨30266277164685977013551735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20177518109790651342367823 30266277164685977013551735)
  ·
    refine ⟨45399415747028965520327603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30266277164685977013551735 45399415747028965520327603)
    ·
      refine ⟨68099123620543448280491405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45399415747028965520327603 68099123620543448280491405)
      ·
        refine ⟨25537171357703793105184277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68099123620543448280491405 25537171357703793105184277)
        ·
          refine ⟨1197054907392365301805513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25537171357703793105184277 1197054907392365301805513)
          ·
            refine ⟨897791180544273976354135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197054907392365301805513 897791180544273976354135)
            ·
              refine ⟨1346686770816410964531203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897791180544273976354135 1346686770816410964531203)
              ·
                refine ⟨2020030156224616446796805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346686770816410964531203 2020030156224616446796805)
                ·
                  refine ⟨378755654292115583774401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020030156224616446796805 378755654292115583774401)
                  ·
                    rfl

theorem cell20_829827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_829827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829827 prefixEnd_829827 := by exact prefixLift 829827
  have htrace : WordTrace (prefixWord ++ tailWord_829827) baseStart_829827 baseEnd_829827 := by
    simpa [prefixWord, tailWord_829827, baseEnd_829827] using wordTrace_append hprefix tailTrace_829827
  have hstable : (prefixWord ++ tailWord_829827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829827).length < 2 ^ (prefixWord ++ tailWord_829827).sum := by decide
  have hdescent : baseEnd_829827 < baseStart_829827 := by decide
  rcases family_descends (prefixWord ++ tailWord_829827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829879 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_829879 : Nat := 118140960795 + 829879 * 2 ^ 59
def prefixEnd_829879 : Nat := 4983230072969 + 3 ^ 40 * 829879 * 2
def baseEnd_829879 : Nat := 378779388509034514040855

theorem tailTrace_829879 : CollatzResearch.WordTrace tailWord_829879 prefixEnd_829879 378779388509034514040855 := by
  unfold tailWord_829879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30268173760497589894444691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20178782506998393262963127 30268173760497589894444691)
  ·
    refine ⟨45402260640746384841667037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30268173760497589894444691 45402260640746384841667037)
    ·
      refine ⟨17025847740279894315625139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45402260640746384841667037 17025847740279894315625139)
      ·
        refine ⟨25538771610419841473437709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025847740279894315625139 25538771610419841473437709)
        ·
          refine ⟨9577039353907440552539141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25538771610419841473437709 9577039353907440552539141)
          ·
            refine ⟨1795694878857645103601089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9577039353907440552539141 1795694878857645103601089)
            ·
              refine ⟨1346771159143233827700817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795694878857645103601089 1346771159143233827700817)
              ·
                refine ⟨1010078369357425370775613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346771159143233827700817 1010078369357425370775613)
                ·
                  refine ⟨378779388509034514040855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010078369357425370775613 378779388509034514040855)
                  ·
                    rfl

theorem cell20_829879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_829879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829879 prefixEnd_829879 := by exact prefixLift 829879
  have htrace : WordTrace (prefixWord ++ tailWord_829879) baseStart_829879 baseEnd_829879 := by
    simpa [prefixWord, tailWord_829879, baseEnd_829879] using wordTrace_append hprefix tailTrace_829879
  have hstable : (prefixWord ++ tailWord_829879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829879).length < 2 ^ (prefixWord ++ tailWord_829879).sum := by decide
  have hdescent : baseEnd_829879 < baseStart_829879 := by decide
  rcases family_descends (prefixWord ++ tailWord_829879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829934 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_829934 : Nat := 118140960795 + 829934 * 2 ^ 59
def prefixEnd_829934 : Nat := 4983230072969 + 3 ^ 40 * 829934 * 2
def baseEnd_829934 : Nat := 378804492007698767207297

theorem tailTrace_829934 : CollatzResearch.WordTrace tailWord_829934 prefixEnd_829934 378804492007698767207297 := by
  unfold tailWord_829934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783772471912291785962107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20180119850198889525131237 3783772471912291785962107)
  ·
    refine ⟨5675658707868437678943161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3783772471912291785962107 5675658707868437678943161)
    ·
      refine ⟨4256744030901328259207371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5675658707868437678943161 4256744030901328259207371)
      ·
        refine ⟨6385116046351992388811057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256744030901328259207371 6385116046351992388811057)
        ·
          refine ⟨4788837034763994291608293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6385116046351992388811057 4788837034763994291608293)
          ·
            refine ⟨897906944018248929676555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4788837034763994291608293 897906944018248929676555)
            ·
              refine ⟨1346860416027373394514833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897906944018248929676555 1346860416027373394514833)
              ·
                refine ⟨1010145312020530045886125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346860416027373394514833 1010145312020530045886125)
                ·
                  refine ⟨378804492007698767207297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010145312020530045886125 378804492007698767207297)
                  ·
                    rfl

theorem cell20_829934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_829934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829934 prefixEnd_829934 := by exact prefixLift 829934
  have htrace : WordTrace (prefixWord ++ tailWord_829934) baseStart_829934 baseEnd_829934 := by
    simpa [prefixWord, tailWord_829934, baseEnd_829934] using wordTrace_append hprefix tailTrace_829934
  have hstable : (prefixWord ++ tailWord_829934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829934).length < 2 ^ (prefixWord ++ tailWord_829934).sum := by decide
  have hdescent : baseEnd_829934 < baseStart_829934 := by decide
  rcases family_descends (prefixWord ++ tailWord_829934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829945 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_829945 : Nat := 118140960795 + 829945 * 2 ^ 59
def prefixEnd_829945 : Nat := 4983230072969 + 3 ^ 40 * 829945 * 2
def baseEnd_829945 : Nat := 378809512707431617840585

theorem tailTrace_829945 : CollatzResearch.WordTrace tailWord_829945 prefixEnd_829945 378809512707431617840585 := by
  unfold tailWord_829945
  simp only [CollatzResearch.WordTrace]
  refine ⟨30270580978258483166347289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20180387318838988777564859 30270580978258483166347289)
  ·
    refine ⟨22702935733693862374760467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30270580978258483166347289 22702935733693862374760467)
    ·
      refine ⟨34054403600540793562140701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22702935733693862374760467 34054403600540793562140701)
      ·
        refine ⟨12770401350202797585802763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34054403600540793562140701 12770401350202797585802763)
        ·
          refine ⟨19155602025304196378704145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12770401350202797585802763 19155602025304196378704145)
          ·
            refine ⟨14366701518978147284028109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19155602025304196378704145 14366701518978147284028109)
            ·
              refine ⟨5387513069616805231510541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14366701518978147284028109 5387513069616805231510541)
              ·
                refine ⟨2020317401106301961816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5387513069616805231510541 2020317401106301961816453)
                ·
                  refine ⟨378809512707431617840585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2020317401106301961816453 378809512707431617840585)
                  ·
                    rfl

theorem cell20_829945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_829945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829945 prefixEnd_829945 := by exact prefixLift 829945
  have htrace : WordTrace (prefixWord ++ tailWord_829945) baseStart_829945 baseEnd_829945 := by
    simpa [prefixWord, tailWord_829945, baseEnd_829945] using wordTrace_append hprefix tailTrace_829945
  have hstable : (prefixWord ++ tailWord_829945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829945).length < 2 ^ (prefixWord ++ tailWord_829945).sum := by decide
  have hdescent : baseEnd_829945 < baseStart_829945 := by decide
  rcases family_descends (prefixWord ++ tailWord_829945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829955 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 3]
def baseStart_829955 : Nat := 118140960795 + 829955 * 2 ^ 59
def prefixEnd_829955 : Nat := 4983230072969 + 3 ^ 40 * 829955 * 2
def baseEnd_829955 : Nat := 378814076979916027507211

theorem tailTrace_829955 : CollatzResearch.WordTrace tailWord_829955 prefixEnd_829955 378814076979916027507211 := by
  unfold tailWord_829955
  simp only [CollatzResearch.WordTrace]
  refine ⟨30270945708222254874211319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20180630472148169916140879 30270945708222254874211319)
  ·
    refine ⟨45406418562333382311316979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30270945708222254874211319 45406418562333382311316979)
    ·
      refine ⟨68109627843500073466975469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45406418562333382311316979 68109627843500073466975469)
      ·
        refine ⟨25541110441312527550115801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68109627843500073466975469 25541110441312527550115801)
        ·
          refine ⟨19155832830984395662586851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25541110441312527550115801 19155832830984395662586851)
          ·
            refine ⟨28733749246476593493880277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19155832830984395662586851 28733749246476593493880277)
            ·
              refine ⟨673447247964295160012819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28733749246476593493880277 673447247964295160012819)
              ·
                refine ⟨1010170871946442740019229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673447247964295160012819 1010170871946442740019229)
                ·
                  refine ⟨378814076979916027507211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010170871946442740019229 378814076979916027507211)
                  ·
                    rfl

theorem cell20_829955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_829955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829955 prefixEnd_829955 := by exact prefixLift 829955
  have htrace : WordTrace (prefixWord ++ tailWord_829955) baseStart_829955 baseEnd_829955 := by
    simpa [prefixWord, tailWord_829955, baseEnd_829955] using wordTrace_append hprefix tailTrace_829955
  have hstable : (prefixWord ++ tailWord_829955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829955).length < 2 ^ (prefixWord ++ tailWord_829955).sum := by decide
  have hdescent : baseEnd_829955 < baseStart_829955 := by decide
  rcases family_descends (prefixWord ++ tailWord_829955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829965 : List Nat := [1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_829965 : Nat := 118140960795 + 829965 * 2 ^ 59
def prefixEnd_829965 : Nat := 4983230072969 + 3 ^ 40 * 829965 * 2
def baseEnd_829965 : Nat := 126272880417466812391279

theorem tailTrace_829965 : CollatzResearch.WordTrace tailWord_829965 prefixEnd_829965 126272880417466812391279 := by
  unfold tailWord_829965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30271310438186026582075349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20180873625457351054716899 30271310438186026582075349)
  ·
    refine ⟨709483838394984998017391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30271310438186026582075349 709483838394984998017391)
    ·
      refine ⟨1064225757592477497026087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709483838394984998017391 1064225757592477497026087)
      ·
        refine ⟨1596338636388716245539131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064225757592477497026087 1596338636388716245539131)
        ·
          refine ⟨2394507954583074368308697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596338636388716245539131 2394507954583074368308697)
          ·
            refine ⟨1795880965937305776231523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394507954583074368308697 1795880965937305776231523)
            ·
              refine ⟨2693821448905958664347285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795880965937305776231523 2693821448905958664347285)
              ·
                refine ⟨126272880417466812391279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2693821448905958664347285 126272880417466812391279)
                ·
                  rfl

theorem cell20_829965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_829965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829965 prefixEnd_829965 := by exact prefixLift 829965
  have htrace : WordTrace (prefixWord ++ tailWord_829965) baseStart_829965 baseEnd_829965 := by
    simpa [prefixWord, tailWord_829965, baseEnd_829965] using wordTrace_append hprefix tailTrace_829965
  have hstable : (prefixWord ++ tailWord_829965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829965).length < 2 ^ (prefixWord ++ tailWord_829965).sum := by decide
  have hdescent : baseEnd_829965 < baseStart_829965 := by decide
  rcases family_descends (prefixWord ++ tailWord_829965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829975 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 2]
def baseStart_829975 : Nat := 118140960795 + 829975 * 2 ^ 59
def prefixEnd_829975 : Nat := 4983230072969 + 3 ^ 40 * 829975 * 2
def baseEnd_829975 : Nat := 378823205524884846840463

theorem tailTrace_829975 : CollatzResearch.WordTrace tailWord_829975 prefixEnd_829975 378823205524884846840463 := by
  unfold tailWord_829975
  simp only [CollatzResearch.WordTrace]
  refine ⟨30271675168149798289939379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20181116778766532193292919 30271675168149798289939379)
  ·
    refine ⟨45407512752224697434909069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30271675168149798289939379 45407512752224697434909069)
    ·
      refine ⟨17027817282084261538090901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45407512752224697434909069 17027817282084261538090901)
      ·
        refine ⟨798178935097699759598011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17027817282084261538090901 798178935097699759598011)
        ·
          refine ⟨1197268402646549639397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798178935097699759598011 1197268402646549639397017)
          ·
            refine ⟨897951301984912229547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197268402646549639397017 897951301984912229547763)
            ·
              refine ⟨1346926952977368344321645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897951301984912229547763 1346926952977368344321645)
              ·
                refine ⟨505097607366513129120617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346926952977368344321645 505097607366513129120617)
                ·
                  refine ⟨378823205524884846840463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505097607366513129120617 378823205524884846840463)
                  ·
                    rfl

theorem cell20_829975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2].length) (baseStart_829975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829975 prefixEnd_829975 := by exact prefixLift 829975
  have htrace : WordTrace (prefixWord ++ tailWord_829975) baseStart_829975 baseEnd_829975 := by
    simpa [prefixWord, tailWord_829975, baseEnd_829975] using wordTrace_append hprefix tailTrace_829975
  have hstable : (prefixWord ++ tailWord_829975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829975).length < 2 ^ (prefixWord ++ tailWord_829975).sum := by decide
  have hdescent : baseEnd_829975 < baseStart_829975 := by decide
  rcases family_descends (prefixWord ++ tailWord_829975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829976 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_829976 : Nat := 118140960795 + 829976 * 2 ^ 59
def prefixEnd_829976 : Nat := 4983230072969 + 3 ^ 40 * 829976 * 2
def baseEnd_829976 : Nat := 378823661952133287807125

theorem tailTrace_829976 : CollatzResearch.WordTrace tailWord_829976 prefixEnd_829976 378823661952133287807125 := by
  unfold tailWord_829976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15135855820573087730362891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20181141094097450307150521 15135855820573087730362891)
  ·
    refine ⟨22703783730859631595544337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15135855820573087730362891 22703783730859631595544337)
    ·
      refine ⟨17027837798144723696658253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22703783730859631595544337 17027837798144723696658253)
      ·
        refine ⟨6385439174304271386246845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17027837798144723696658253 6385439174304271386246845)
        ·
          refine ⟨2394539690364101769842567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6385439174304271386246845 2394539690364101769842567)
          ·
            refine ⟨3591809535546152654763851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394539690364101769842567 3591809535546152654763851)
            ·
              refine ⟨5387714303319228982145777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591809535546152654763851 5387714303319228982145777)
              ·
                refine ⟨4040785727489421736609333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5387714303319228982145777 4040785727489421736609333)
                ·
                  refine ⟨378823661952133287807125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4040785727489421736609333 378823661952133287807125)
                  ·
                    rfl

theorem cell20_829976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_829976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_829976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_829976 prefixEnd_829976 := by exact prefixLift 829976
  have htrace : WordTrace (prefixWord ++ tailWord_829976) baseStart_829976 baseEnd_829976 := by
    simpa [prefixWord, tailWord_829976, baseEnd_829976] using wordTrace_append hprefix tailTrace_829976
  have hstable : (prefixWord ++ tailWord_829976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829976).length < 2 ^ (prefixWord ++ tailWord_829976).sum := by decide
  have hdescent : baseEnd_829976 < baseStart_829976 := by decide
  rcases family_descends (prefixWord ++ tailWord_829976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830000 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_830000 : Nat := 118140960795 + 830000 * 2 ^ 59
def prefixEnd_830000 : Nat := 4983230072969 + 3 ^ 40 * 830000 * 2
def baseEnd_830000 : Nat := 378834616206095871007027

theorem tailTrace_830000 : CollatzResearch.WordTrace tailWord_830000 prefixEnd_830000 378834616206095871007027 := by
  unfold tailWord_830000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136293496529613779799727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20181724662039485039732969 15136293496529613779799727)
  ·
    refine ⟨22704440244794420669699591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15136293496529613779799727 22704440244794420669699591)
    ·
      refine ⟨34056660367191631004549387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22704440244794420669699591 34056660367191631004549387)
      ·
        refine ⟨51084990550787446506824081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34056660367191631004549387 51084990550787446506824081)
        ·
          refine ⟨38313742913090584880118061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51084990550787446506824081 38313742913090584880118061)
          ·
            refine ⟨14367653592408969330044273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38313742913090584880118061 14367653592408969330044273)
            ·
              refine ⟨10775740194306726997533205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14367653592408969330044273 10775740194306726997533205)
              ·
                refine ⟨505112821608127828009369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10775740194306726997533205 505112821608127828009369)
                ·
                  refine ⟨378834616206095871007027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505112821608127828009369 378834616206095871007027)
                  ·
                    rfl

theorem cell20_830000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_830000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830000 prefixEnd_830000 := by exact prefixLift 830000
  have htrace : WordTrace (prefixWord ++ tailWord_830000) baseStart_830000 baseEnd_830000 := by
    simpa [prefixWord, tailWord_830000, baseEnd_830000] using wordTrace_append hprefix tailTrace_830000
  have hstable : (prefixWord ++ tailWord_830000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830000).length < 2 ^ (prefixWord ++ tailWord_830000).sum := by decide
  have hdescent : baseEnd_830000 < baseStart_830000 := by decide
  rcases family_descends (prefixWord ++ tailWord_830000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830010 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_830010 : Nat := 118140960795 + 830010 * 2 ^ 59
def prefixEnd_830010 : Nat := 4983230072969 + 3 ^ 40 * 830010 * 2
def baseEnd_830010 : Nat := 378839180478580280673653

theorem tailTrace_830010 : CollatzResearch.WordTrace tailWord_830010 prefixEnd_830010 378839180478580280673653 := by
  unfold tailWord_830010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568237930755749816865871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20181967815348666178308989 7568237930755749816865871)
  ·
    refine ⟨11352356896133624725298807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7568237930755749816865871 11352356896133624725298807)
    ·
      refine ⟨17028535344200437087948211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11352356896133624725298807 17028535344200437087948211)
      ·
        refine ⟨25542803016300655631922317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17028535344200437087948211 25542803016300655631922317)
        ·
          refine ⟨9578551131112745861970869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25542803016300655631922317 9578551131112745861970869)
          ·
            refine ⟨897989168541819924559769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9578551131112745861970869 897989168541819924559769)
            ·
              refine ⟨673491876406364943419827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897989168541819924559769 673491876406364943419827)
              ·
                refine ⟨1010237814609547415129741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673491876406364943419827 1010237814609547415129741)
                ·
                  refine ⟨378839180478580280673653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010237814609547415129741 378839180478580280673653)
                  ·
                    rfl

theorem cell20_830010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_830010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830010 prefixEnd_830010 := by exact prefixLift 830010
  have htrace : WordTrace (prefixWord ++ tailWord_830010) baseStart_830010 baseEnd_830010 := by
    simpa [prefixWord, tailWord_830010, baseEnd_830010] using wordTrace_append hprefix tailTrace_830010
  have hstable : (prefixWord ++ tailWord_830010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830010).length < 2 ^ (prefixWord ++ tailWord_830010).sum := by decide
  have hdescent : baseEnd_830010 < baseStart_830010 := by decide
  rcases family_descends (prefixWord ++ tailWord_830010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830028 : List Nat := [2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_830028 : Nat := 118140960795 + 830028 * 2 ^ 59
def prefixEnd_830028 : Nat := 4983230072969 + 3 ^ 40 * 830028 * 2
def baseEnd_830028 : Nat := 126282465389684072691193

theorem tailTrace_830028 : CollatzResearch.WordTrace tailWord_830028 prefixEnd_830028 126282465389684072691193 := by
  unfold tailWord_830028
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136804118478894170809369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20182405491305192227745825 15136804118478894170809369)
  ·
    refine ⟨11352603088859170628107027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15136804118478894170809369 11352603088859170628107027)
    ·
      refine ⟨17028904633288755942160541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11352603088859170628107027 17028904633288755942160541)
      ·
        refine ⟨6385839237483283478310203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17028904633288755942160541 6385839237483283478310203)
        ·
          refine ⟨9578758856224925217465305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385839237483283478310203 9578758856224925217465305)
          ·
            refine ⟨7184069142168693913098979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9578758856224925217465305 7184069142168693913098979)
            ·
              refine ⟨10776103713253040869648469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184069142168693913098979 10776103713253040869648469)
              ·
                refine ⟨126282465389684072691193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10776103713253040869648469 126282465389684072691193)
                ·
                  rfl

theorem cell20_830028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_830028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830028 prefixEnd_830028 := by exact prefixLift 830028
  have htrace : WordTrace (prefixWord ++ tailWord_830028) baseStart_830028 baseEnd_830028 := by
    simpa [prefixWord, tailWord_830028, baseEnd_830028] using wordTrace_append hprefix tailTrace_830028
  have hstable : (prefixWord ++ tailWord_830028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830028).length < 2 ^ (prefixWord ++ tailWord_830028).sum := by decide
  have hdescent : baseEnd_830028 < baseStart_830028 := by decide
  rcases family_descends (prefixWord ++ tailWord_830028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830062 : List Nat := [4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_830062 : Nat := 118140960795 + 830062 * 2 ^ 59
def prefixEnd_830062 : Nat := 4983230072969 + 3 ^ 40 * 830062 * 2
def baseEnd_830062 : Nat := 126287638231833070313369

theorem tailTrace_830062 : CollatzResearch.WordTrace tailWord_830062 prefixEnd_830062 126287638231833070313369 := by
  unfold tailWord_830062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784356039854326518544555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20183232212556408098904293 3784356039854326518544555)
  ·
    refine ⟨5676534059781489777816833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3784356039854326518544555 5676534059781489777816833)
    ·
      refine ⟨4257400544836117333362625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5676534059781489777816833 4257400544836117333362625)
      ·
        refine ⟨3193050408627088000021969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257400544836117333362625 3193050408627088000021969)
        ·
          refine ⟨2394787806470316000016477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193050408627088000021969 2394787806470316000016477)
          ·
            refine ⟨898045427426368500006179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2394787806470316000016477 898045427426368500006179)
            ·
              refine ⟨1347068141139552750009269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898045427426368500006179 1347068141139552750009269)
              ·
                refine ⟨126287638231833070313369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1347068141139552750009269 126287638231833070313369)
                ·
                  rfl

theorem cell20_830062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_830062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830062 prefixEnd_830062 := by exact prefixLift 830062
  have htrace : WordTrace (prefixWord ++ tailWord_830062) baseStart_830062 baseEnd_830062 := by
    simpa [prefixWord, tailWord_830062, baseEnd_830062] using wordTrace_append hprefix tailTrace_830062
  have hstable : (prefixWord ++ tailWord_830062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830062).length < 2 ^ (prefixWord ++ tailWord_830062).sum := by decide
  have hdescent : baseEnd_830062 < baseStart_830062 := by decide
  rcases family_descends (prefixWord ++ tailWord_830062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830104 : List Nat := [2, 1, 2, 4, 1, 1, 9]
def baseStart_830104 : Nat := 118140960795 + 830104 * 2 ^ 59
def prefixEnd_830104 : Nat := 4983230072969 + 3 ^ 40 * 830104 * 2
def baseEnd_830104 : Nat := 42098009404437081282215

theorem tailTrace_830104 : CollatzResearch.WordTrace tailWord_830104 prefixEnd_830104 42098009404437081282215 := by
  unfold tailWord_830104
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138190092341226660692683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20184253456454968880923577 15138190092341226660692683)
  ·
    refine ⟨22707285138511839991039025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15138190092341226660692683 22707285138511839991039025)
    ·
      refine ⟨17030463853883879993279269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22707285138511839991039025 17030463853883879993279269)
      ·
        refine ⟨3193211972603227498739863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17030463853883879993279269 3193211972603227498739863)
        ·
          refine ⟨4789817958904841248109795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193211972603227498739863 4789817958904841248109795)
          ·
            refine ⟨7184726938357261872164693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789817958904841248109795 7184726938357261872164693)
            ·
              refine ⟨42098009404437081282215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7184726938357261872164693 42098009404437081282215)
              ·
                rfl

theorem cell20_830104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_830104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830104 prefixEnd_830104 := by exact prefixLift 830104
  have htrace : WordTrace (prefixWord ++ tailWord_830104) baseStart_830104 baseEnd_830104 := by
    simpa [prefixWord, tailWord_830104, baseEnd_830104] using wordTrace_append hprefix tailTrace_830104
  have hstable : (prefixWord ++ tailWord_830104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830104).length < 2 ^ (prefixWord ++ tailWord_830104).sum := by decide
  have hdescent : baseEnd_830104 < baseStart_830104 := by decide
  rcases family_descends (prefixWord ++ tailWord_830104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830134 : List Nat := [5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_830134 : Nat := 118140960795 + 830134 * 2 ^ 59
def prefixEnd_830134 : Nat := 4983230072969 + 3 ^ 40 * 830134 * 2
def baseEnd_830134 : Nat := 126298592485795653513271

theorem tailTrace_830134 : CollatzResearch.WordTrace tailWord_830134 prefixEnd_830134 126298592485795653513271 := by
  unfold tailWord_830134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892342148410860527811091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20184982916382512296651637 1892342148410860527811091)
  ·
    refine ⟨2838513222616290791716637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892342148410860527811091 2838513222616290791716637)
    ·
      refine ⟨1064442458481109046893739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2838513222616290791716637 1064442458481109046893739)
      ·
        refine ⟨1596663687721663570340609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064442458481109046893739 1596663687721663570340609)
        ·
          refine ⟨1197497765791247677755457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596663687721663570340609 1197497765791247677755457)
          ·
            refine ⟨898123324343435758316593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197497765791247677755457 898123324343435758316593)
            ·
              refine ⟨673592493257576818737445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898123324343435758316593 673592493257576818737445)
              ·
                refine ⟨126298592485795653513271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673592493257576818737445 126298592485795653513271)
                ·
                  rfl

theorem cell20_830134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_830134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830134 prefixEnd_830134 := by exact prefixLift 830134
  have htrace : WordTrace (prefixWord ++ tailWord_830134) baseStart_830134 baseEnd_830134 := by
    simpa [prefixWord, tailWord_830134, baseEnd_830134] using wordTrace_append hprefix tailTrace_830134
  have hstable : (prefixWord ++ tailWord_830134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830134).length < 2 ^ (prefixWord ++ tailWord_830134).sum := by decide
  have hdescent : baseEnd_830134 < baseStart_830134 := by decide
  rcases family_descends (prefixWord ++ tailWord_830134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830148 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_830148 : Nat := 118140960795 + 830148 * 2 ^ 59
def prefixEnd_830148 : Nat := 4983230072969 + 3 ^ 40 * 830148 * 2
def baseEnd_830148 : Nat := 378902167438865134073089

theorem tailTrace_830148 : CollatzResearch.WordTrace tailWord_830148 prefixEnd_830148 378902167438865134073089 := by
  unfold tailWord_830148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138992498261524417993549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20185323331015365890658065 15138992498261524417993549)
  ·
    refine ⟨5677122186848071656747581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15138992498261524417993549 5677122186848071656747581)
    ·
      refine ⟨2128920820068026871280343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5677122186848071656747581 2128920820068026871280343)
      ·
        refine ⟨3193381230102040306920515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128920820068026871280343 3193381230102040306920515)
        ·
          refine ⟨4790071845153060460380773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193381230102040306920515 4790071845153060460380773)
          ·
            refine ⟨898138470966198836321395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4790071845153060460380773 898138470966198836321395)
            ·
              refine ⟨1347207706449298254482093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898138470966198836321395 1347207706449298254482093)
              ·
                refine ⟨505202889918486845430785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347207706449298254482093 505202889918486845430785)
                ·
                  refine ⟨378902167438865134073089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505202889918486845430785 378902167438865134073089)
                  ·
                    rfl

theorem cell20_830148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_830148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830148 prefixEnd_830148 := by exact prefixLift 830148
  have htrace : WordTrace (prefixWord ++ tailWord_830148) baseStart_830148 baseEnd_830148 := by
    simpa [prefixWord, tailWord_830148, baseEnd_830148] using wordTrace_append hprefix tailTrace_830148
  have hstable : (prefixWord ++ tailWord_830148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830148).length < 2 ^ (prefixWord ++ tailWord_830148).sum := by decide
  have hdescent : baseEnd_830148 < baseStart_830148 := by decide
  rcases family_descends (prefixWord ++ tailWord_830148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830165 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 2]
def baseStart_830165 : Nat := 118140960795 + 830165 * 2 ^ 59
def prefixEnd_830165 : Nat := 4983230072969 + 3 ^ 40 * 830165 * 2
def baseEnd_830165 : Nat := 378909926702088630506353

theorem tailTrace_830165 : CollatzResearch.WordTrace tailWord_830165 prefixEnd_830165 378909926702088630506353 := by
  unfold tailWord_830165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30278605037461460739355949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20185736691640973826237299 30278605037461460739355949)
  ·
    refine ⟨11354476889048047777258481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30278605037461460739355949 11354476889048047777258481)
    ·
      refine ⟨8515857666786035832943861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11354476889048047777258481 8515857666786035832943861)
      ·
        refine ⟨798361656261190859338487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8515857666786035832943861 798361656261190859338487)
        ·
          refine ⟨1197542484391786289007731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798361656261190859338487 1197542484391786289007731)
          ·
            refine ⟨1796313726587679433511597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197542484391786289007731 1796313726587679433511597)
            ·
              refine ⟨673617647470379787566849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1796313726587679433511597 673617647470379787566849)
              ·
                refine ⟨505213235602784840675137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673617647470379787566849 505213235602784840675137)
                ·
                  refine ⟨378909926702088630506353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505213235602784840675137 378909926702088630506353)
                  ·
                    rfl

theorem cell20_830165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_830165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830165 prefixEnd_830165 := by exact prefixLift 830165
  have htrace : WordTrace (prefixWord ++ tailWord_830165) baseStart_830165 baseEnd_830165 := by
    simpa [prefixWord, tailWord_830165, baseEnd_830165] using wordTrace_append hprefix tailTrace_830165
  have hstable : (prefixWord ++ tailWord_830165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830165).length < 2 ^ (prefixWord ++ tailWord_830165).sum := by decide
  have hdescent : baseEnd_830165 < baseStart_830165 := by decide
  rcases family_descends (prefixWord ++ tailWord_830165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830169 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 2]
def baseStart_830169 : Nat := 118140960795 + 830169 * 2 ^ 59
def prefixEnd_830169 : Nat := 4983230072969 + 3 ^ 40 * 830169 * 2
def baseEnd_830169 : Nat := 378911752411082394373003

theorem tailTrace_830169 : CollatzResearch.WordTrace tailWord_830169 prefixEnd_830169 378911752411082394373003 := by
  unfold tailWord_830169
  simp only [CollatzResearch.WordTrace]
  refine ⟨30278750929446969422501561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20185833952964646281667707 30278750929446969422501561)
  ·
    refine ⟨22709063197085227066876171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30278750929446969422501561 22709063197085227066876171)
    ·
      refine ⟨34063594795627840600314257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22709063197085227066876171 34063594795627840600314257)
      ·
        refine ⟨25547696096720880450235693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34063594795627840600314257 25547696096720880450235693)
        ·
          refine ⟨9580386036270330168838385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25547696096720880450235693 9580386036270330168838385)
          ·
            refine ⟨7185289527202747626628789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580386036270330168838385 7185289527202747626628789)
            ·
              refine ⟨673620893175257589996449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7185289527202747626628789 673620893175257589996449)
              ·
                refine ⟨505215669881443192497337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673620893175257589996449 505215669881443192497337)
                ·
                  refine ⟨378911752411082394373003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505215669881443192497337 378911752411082394373003)
                  ·
                    rfl

theorem cell20_830169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_830169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830169 prefixEnd_830169 := by exact prefixLift 830169
  have htrace : WordTrace (prefixWord ++ tailWord_830169) baseStart_830169 baseEnd_830169 := by
    simpa [prefixWord, tailWord_830169, baseEnd_830169] using wordTrace_append hprefix tailTrace_830169
  have hstable : (prefixWord ++ tailWord_830169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830169).length < 2 ^ (prefixWord ++ tailWord_830169).sum := by decide
  have hdescent : baseEnd_830169 < baseStart_830169 := by decide
  rcases family_descends (prefixWord ++ tailWord_830169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830180 : List Nat := [2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_830180 : Nat := 118140960795 + 830180 * 2 ^ 59
def prefixEnd_830180 : Nat := 4983230072969 + 3 ^ 40 * 830180 * 2
def baseEnd_830180 : Nat := 126305591036938415002097

theorem tailTrace_830180 : CollatzResearch.WordTrace tailWord_830180 prefixEnd_830180 126305591036938415002097 := by
  unfold tailWord_830180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15139576066203559150575997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20186101421604745534101329 15139576066203559150575997)
  ·
    refine ⟨5677341024826334681465999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15139576066203559150575997 5677341024826334681465999)
    ·
      refine ⟨8516011537239502022198999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5677341024826334681465999 8516011537239502022198999)
      ·
        refine ⟨12774017305859253033298499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8516011537239502022198999 12774017305859253033298499)
        ·
          refine ⟨19161025958788879549947749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12774017305859253033298499 19161025958788879549947749)
          ·
            refine ⟨3592692367272914915615203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19161025958788879549947749 3592692367272914915615203)
            ·
              refine ⟨5389038550909372373422805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592692367272914915615203 5389038550909372373422805)
              ·
                refine ⟨126305591036938415002097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5389038550909372373422805 126305591036938415002097)
                ·
                  rfl

theorem cell20_830180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_830180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830180 prefixEnd_830180 := by exact prefixLift 830180
  have htrace : WordTrace (prefixWord ++ tailWord_830180) baseStart_830180 baseEnd_830180 := by
    simpa [prefixWord, tailWord_830180, baseEnd_830180] using wordTrace_append hprefix tailTrace_830180
  have hstable : (prefixWord ++ tailWord_830180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830180).length < 2 ^ (prefixWord ++ tailWord_830180).sum := by decide
  have hdescent : baseEnd_830180 < baseStart_830180 := by decide
  rcases family_descends (prefixWord ++ tailWord_830180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830225 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_830225 : Nat := 118140960795 + 830225 * 2 ^ 59
def prefixEnd_830225 : Nat := 4983230072969 + 3 ^ 40 * 830225 * 2
def baseEnd_830225 : Nat := 378937312336995088506107

theorem tailTrace_830225 : CollatzResearch.WordTrace tailWord_830225 prefixEnd_830225 378937312336995088506107 := by
  unfold tailWord_830225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30280793417244090986540129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20187195611496060657693419 30280793417244090986540129)
  ·
    refine ⟨22710595062933068239905097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30280793417244090986540129 22710595062933068239905097)
    ·
      refine ⟨17032946297199801179928823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22710595062933068239905097 17032946297199801179928823)
      ·
        refine ⟨25549419445799701769893235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17032946297199801179928823 25549419445799701769893235)
        ·
          refine ⟨38324129168699552654839853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25549419445799701769893235 38324129168699552654839853)
          ·
            refine ⟨14371548438262332245564945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38324129168699552654839853 14371548438262332245564945)
            ·
              refine ⟨10778661328696749184173709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14371548438262332245564945 10778661328696749184173709)
              ·
                refine ⟨4041997998261280944065141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10778661328696749184173709 4041997998261280944065141)
                ·
                  refine ⟨378937312336995088506107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4041997998261280944065141 378937312336995088506107)
                  ·
                    rfl

theorem cell20_830225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_830225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830225 prefixEnd_830225 := by exact prefixLift 830225
  have htrace : WordTrace (prefixWord ++ tailWord_830225) baseStart_830225 baseEnd_830225 := by
    simpa [prefixWord, tailWord_830225, baseEnd_830225] using wordTrace_append hprefix tailTrace_830225
  have hstable : (prefixWord ++ tailWord_830225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830225).length < 2 ^ (prefixWord ++ tailWord_830225).sum := by decide
  have hdescent : baseEnd_830225 < baseStart_830225 := by decide
  rcases family_descends (prefixWord ++ tailWord_830225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830263 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_830263 : Nat := 118140960795 + 830263 * 2 ^ 59
def prefixEnd_830263 : Nat := 4983230072969 + 3 ^ 40 * 830263 * 2
def baseEnd_830263 : Nat := 378954656572435845239285

theorem tailTrace_830263 : CollatzResearch.WordTrace tailWord_830263 prefixEnd_830263 378954656572435845239285 := by
  unfold tailWord_830263
  simp only [CollatzResearch.WordTrace]
  refine ⟨30282179391106423476423443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20188119594070948984282295 30282179391106423476423443)
  ·
    refine ⟨45423269086659635214635165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30282179391106423476423443 45423269086659635214635165)
    ·
      refine ⟨17033725907497363205488187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45423269086659635214635165 17033725907497363205488187)
      ·
        refine ⟨25550588861246044808232281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17033725907497363205488187 25550588861246044808232281)
        ·
          refine ⟨19162941645934533606174211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25550588861246044808232281 19162941645934533606174211)
          ·
            refine ⟨28744412468901800409261317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19162941645934533606174211 28744412468901800409261317)
            ·
              refine ⟨5389577337919087576736497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28744412468901800409261317 5389577337919087576736497)
              ·
                refine ⟨4042183003439315682552373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389577337919087576736497 4042183003439315682552373)
                ·
                  refine ⟨378954656572435845239285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042183003439315682552373 378954656572435845239285)
                  ·
                    rfl

theorem cell20_830263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_830263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830263 prefixEnd_830263 := by exact prefixLift 830263
  have htrace : WordTrace (prefixWord ++ tailWord_830263) baseStart_830263 baseEnd_830263 := by
    simpa [prefixWord, tailWord_830263, baseEnd_830263] using wordTrace_append hprefix tailTrace_830263
  have hstable : (prefixWord ++ tailWord_830263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830263).length < 2 ^ (prefixWord ++ tailWord_830263).sum := by decide
  have hdescent : baseEnd_830263 < baseStart_830263 := by decide
  rcases family_descends (prefixWord ++ tailWord_830263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830276 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_830276 : Nat := 118140960795 + 830276 * 2 ^ 59
def prefixEnd_830276 : Nat := 4983230072969 + 3 ^ 40 * 830276 * 2
def baseEnd_830276 : Nat := 378960590126665577805899

theorem tailTrace_830276 : CollatzResearch.WordTrace tailWord_830276 prefixEnd_830276 378960590126665577805899 := by
  unfold tailWord_830276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141326770029663348323341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20188435693372884464431121 15141326770029663348323341)
  ·
    refine ⟨5677997538761123755621253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15141326770029663348323341 5677997538761123755621253)
    ·
      refine ⟨1064624538517710704178985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5677997538761123755621253 1064624538517710704178985)
      ·
        refine ⟨798468403888283028134239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064624538517710704178985 798468403888283028134239)
        ·
          refine ⟨1197702605832424542201359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798468403888283028134239 1197702605832424542201359)
          ·
            refine ⟨1796553908748636813302039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197702605832424542201359 1796553908748636813302039)
            ·
              refine ⟨2694830863122955219953059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796553908748636813302039 2694830863122955219953059)
              ·
                refine ⟨4042246294684432829929589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694830863122955219953059 4042246294684432829929589)
                ·
                  refine ⟨378960590126665577805899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042246294684432829929589 378960590126665577805899)
                  ·
                    rfl

theorem cell20_830276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_830276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830276 prefixEnd_830276 := by exact prefixLift 830276
  have htrace : WordTrace (prefixWord ++ tailWord_830276) baseStart_830276 baseEnd_830276 := by
    simpa [prefixWord, tailWord_830276, baseEnd_830276] using wordTrace_append hprefix tailTrace_830276
  have hstable : (prefixWord ++ tailWord_830276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830276).length < 2 ^ (prefixWord ++ tailWord_830276).sum := by decide
  have hdescent : baseEnd_830276 < baseStart_830276 := by decide
  rcases family_descends (prefixWord ++ tailWord_830276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830297 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 3]
def baseStart_830297 : Nat := 118140960795 + 830297 * 2 ^ 59
def prefixEnd_830297 : Nat := 4983230072969 + 3 ^ 40 * 830297 * 2
def baseEnd_830297 : Nat := 378970175098882838105813

theorem tailTrace_830297 : CollatzResearch.WordTrace tailWord_830297 prefixEnd_830297 378970175098882838105813 := by
  unfold tailWord_830297
  simp only [CollatzResearch.WordTrace]
  refine ⟨30283419472983247283161145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20188946315322164855440763 30283419472983247283161145)
  ·
    refine ⟨22712564604737435462370859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30283419472983247283161145 22712564604737435462370859)
    ·
      refine ⟨34068846907106153193556289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22712564604737435462370859 34068846907106153193556289)
      ·
        refine ⟨25551635180329614895167217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34068846907106153193556289 25551635180329614895167217)
        ·
          refine ⟨19163726385247211171375413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25551635180329614895167217 19163726385247211171375413)
          ·
            refine ⟨1796599348616926047316445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19163726385247211171375413 1796599348616926047316445)
            ·
              refine ⟨673724755731347267743667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1796599348616926047316445 673724755731347267743667)
              ·
                refine ⟨1010587133597020901615501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673724755731347267743667 1010587133597020901615501)
                ·
                  refine ⟨378970175098882838105813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010587133597020901615501 378970175098882838105813)
                  ·
                    rfl

theorem cell20_830297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_830297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830297 prefixEnd_830297 := by exact prefixLift 830297
  have htrace : WordTrace (prefixWord ++ tailWord_830297) baseStart_830297 baseEnd_830297 := by
    simpa [prefixWord, tailWord_830297, baseEnd_830297] using wordTrace_append hprefix tailTrace_830297
  have hstable : (prefixWord ++ tailWord_830297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830297).length < 2 ^ (prefixWord ++ tailWord_830297).sum := by decide
  have hdescent : baseEnd_830297 < baseStart_830297 := by decide
  rcases family_descends (prefixWord ++ tailWord_830297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830311 : List Nat := [1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_830311 : Nat := 118140960795 + 830311 * 2 ^ 59
def prefixEnd_830311 : Nat := 4983230072969 + 3 ^ 40 * 830311 * 2
def baseEnd_830311 : Nat := 126325521693453670546363

theorem tailTrace_830311 : CollatzResearch.WordTrace tailWord_830311 prefixEnd_830311 126325521693453670546363 := by
  unfold tailWord_830311
  simp only [CollatzResearch.WordTrace]
  refine ⟨30283930094932527674170787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20189286729955018449447191 30283930094932527674170787)
  ·
    refine ⟨45425895142398791511256181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30283930094932527674170787 45425895142398791511256181)
    ·
      refine ⟨4258677669599886704180267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45425895142398791511256181 4258677669599886704180267)
      ·
        refine ⟨6388016504399830056270401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258677669599886704180267 6388016504399830056270401)
        ·
          refine ⟨4791012378299872542202801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6388016504399830056270401 4791012378299872542202801)
          ·
            refine ⟨3593259283724904406652101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4791012378299872542202801 3593259283724904406652101)
            ·
              refine ⟨673736115698419576247269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3593259283724904406652101 673736115698419576247269)
              ·
                refine ⟨126325521693453670546363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673736115698419576247269 126325521693453670546363)
                ·
                  rfl

theorem cell20_830311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_830311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830311 prefixEnd_830311 := by exact prefixLift 830311
  have htrace : WordTrace (prefixWord ++ tailWord_830311) baseStart_830311 baseEnd_830311 := by
    simpa [prefixWord, tailWord_830311, baseEnd_830311] using wordTrace_append hprefix tailTrace_830311
  have hstable : (prefixWord ++ tailWord_830311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830311).length < 2 ^ (prefixWord ++ tailWord_830311).sum := by decide
  have hdescent : baseEnd_830311 < baseStart_830311 := by decide
  rcases family_descends (prefixWord ++ tailWord_830311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830321 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 2]
def baseStart_830321 : Nat := 118140960795 + 830321 * 2 ^ 59
def prefixEnd_830321 : Nat := 4983230072969 + 3 ^ 40 * 830321 * 2
def baseEnd_830321 : Nat := 378981129352845421305715

theorem tailTrace_830321 : CollatzResearch.WordTrace tailWord_830321 prefixEnd_830321 378981129352845421305715 := by
  unfold tailWord_830321
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284294824896299382034817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20189529883264199588023211 30284294824896299382034817)
  ·
    refine ⟨22713221118672224536526113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30284294824896299382034817 22713221118672224536526113)
    ·
      refine ⟨17034915839004168402394585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22713221118672224536526113 17034915839004168402394585)
      ·
        refine ⟨12776186879253126301795939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17034915839004168402394585 12776186879253126301795939)
        ·
          refine ⟨19164280318879689452693909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776186879253126301795939 19164280318879689452693909)
          ·
            refine ⟨898325639947485443095027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19164280318879689452693909 898325639947485443095027)
            ·
              refine ⟨1347488459921228164642541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898325639947485443095027 1347488459921228164642541)
              ·
                refine ⟨505308172470460561740953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347488459921228164642541 505308172470460561740953)
                ·
                  refine ⟨378981129352845421305715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505308172470460561740953 378981129352845421305715)
                  ·
                    rfl

theorem cell20_830321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_830321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830321 prefixEnd_830321 := by exact prefixLift 830321
  have htrace : WordTrace (prefixWord ++ tailWord_830321) baseStart_830321 baseEnd_830321 := by
    simpa [prefixWord, tailWord_830321, baseEnd_830321] using wordTrace_append hprefix tailTrace_830321
  have hstable : (prefixWord ++ tailWord_830321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830321).length < 2 ^ (prefixWord ++ tailWord_830321).sum := by decide
  have hdescent : baseEnd_830321 < baseStart_830321 := by decide
  rcases family_descends (prefixWord ++ tailWord_830321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830339 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_830339 : Nat := 118140960795 + 830339 * 2 ^ 59
def prefixEnd_830339 : Nat := 4983230072969 + 3 ^ 40 * 830339 * 2
def baseEnd_830339 : Nat := 378989345043317358705641

theorem tailTrace_830339 : CollatzResearch.WordTrace tailWord_830339 prefixEnd_830339 378989345043317358705641 := by
  unfold tailWord_830339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284951338831088456190071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20189967559220725637460047 30284951338831088456190071)
  ·
    refine ⟨45427427008246632684285107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30284951338831088456190071 45427427008246632684285107)
    ·
      refine ⟨68141140512369949026427661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45427427008246632684285107 68141140512369949026427661)
      ·
        refine ⟨25552927692138730884910373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68141140512369949026427661 25552927692138730884910373)
        ·
          refine ⟨4791173942276012040920695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25552927692138730884910373 4791173942276012040920695)
          ·
            refine ⟨7186760913414018061381043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791173942276012040920695 7186760913414018061381043)
            ·
              refine ⟨10780141370121027092071565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7186760913414018061381043 10780141370121027092071565)
              ·
                refine ⟨4042553013795385159526837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10780141370121027092071565 4042553013795385159526837)
                ·
                  refine ⟨378989345043317358705641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4042553013795385159526837 378989345043317358705641)
                  ·
                    rfl

theorem cell20_830339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_830339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830339 prefixEnd_830339 := by exact prefixLift 830339
  have htrace : WordTrace (prefixWord ++ tailWord_830339) baseStart_830339 baseEnd_830339 := by
    simpa [prefixWord, tailWord_830339, baseEnd_830339] using wordTrace_append hprefix tailTrace_830339
  have hstable : (prefixWord ++ tailWord_830339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830339).length < 2 ^ (prefixWord ++ tailWord_830339).sum := by decide
  have hdescent : baseEnd_830339 < baseStart_830339 := by decide
  rcases family_descends (prefixWord ++ tailWord_830339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830394 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_830394 : Nat := 118140960795 + 830394 * 2 ^ 59
def prefixEnd_830394 : Nat := 4983230072969 + 3 ^ 40 * 830394 * 2
def baseEnd_830394 : Nat := 379014448541981611872083

theorem tailTrace_830394 : CollatzResearch.WordTrace tailWord_830394 prefixEnd_830394 379014448541981611872083 := by
  unfold tailWord_830394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571739338407958212360559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20191304902421221899628157 7571739338407958212360559)
  ·
    refine ⟨11357609007611937318540839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7571739338407958212360559 11357609007611937318540839)
    ·
      refine ⟨17036413511417905977811259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11357609007611937318540839 17036413511417905977811259)
      ·
        refine ⟨25554620267126858966716889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17036413511417905977811259 25554620267126858966716889)
        ·
          refine ⟨19165965200345144225037667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25554620267126858966716889 19165965200345144225037667)
          ·
            refine ⟨28748947800517716337556501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19165965200345144225037667 28748947800517716337556501)
            ·
              refine ⟨1347606928149267953322961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28748947800517716337556501 1347606928149267953322961)
              ·
                refine ⟨1010705196111950964992221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347606928149267953322961 1010705196111950964992221)
                ·
                  refine ⟨379014448541981611872083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010705196111950964992221 379014448541981611872083)
                  ·
                    rfl

theorem cell20_830394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_830394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830394 prefixEnd_830394 := by exact prefixLift 830394
  have htrace : WordTrace (prefixWord ++ tailWord_830394) baseStart_830394 baseEnd_830394 := by
    simpa [prefixWord, tailWord_830394, baseEnd_830394] using wordTrace_append hprefix tailTrace_830394
  have hstable : (prefixWord ++ tailWord_830394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830394).length < 2 ^ (prefixWord ++ tailWord_830394).sum := by decide
  have hdescent : baseEnd_830394 < baseStart_830394 := by decide
  rcases family_descends (prefixWord ++ tailWord_830394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830397 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 2]
def baseStart_830397 : Nat := 118140960795 + 830397 * 2 ^ 59
def prefixEnd_830397 : Nat := 4983230072969 + 3 ^ 40 * 830397 * 2
def baseEnd_830397 : Nat := 379015817823726934772071

theorem tailTrace_830397 : CollatzResearch.WordTrace tailWord_830397 prefixEnd_830397 379015817823726934772071 := by
  unfold tailWord_830397
  simp only [CollatzResearch.WordTrace]
  refine ⟨30287066772620964361801445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20191377848413976241200963 30287066772620964361801445)
  ·
    refine ⟨5678825019866430817837771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30287066772620964361801445 5678825019866430817837771)
    ·
      refine ⟨8518237529799646226756657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678825019866430817837771 8518237529799646226756657)
      ·
        refine ⟨6388678147349734670067493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8518237529799646226756657 6388678147349734670067493)
        ·
          refine ⟨1197877152628075250637655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6388678147349734670067493 1197877152628075250637655)
          ·
            refine ⟨1796815728942112875956483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197877152628075250637655 1796815728942112875956483)
            ·
              refine ⟨2695223593413169313934725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796815728942112875956483 2695223593413169313934725)
              ·
                refine ⟨505354423764969246362761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2695223593413169313934725 505354423764969246362761)
                ·
                  refine ⟨379015817823726934772071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505354423764969246362761 379015817823726934772071)
                  ·
                    rfl

theorem cell20_830397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_830397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830397 prefixEnd_830397 := by exact prefixLift 830397
  have htrace : WordTrace (prefixWord ++ tailWord_830397) baseStart_830397 baseEnd_830397 := by
    simpa [prefixWord, tailWord_830397, baseEnd_830397] using wordTrace_append hprefix tailTrace_830397
  have hstable : (prefixWord ++ tailWord_830397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830397).length < 2 ^ (prefixWord ++ tailWord_830397).sum := by decide
  have hdescent : baseEnd_830397 < baseStart_830397 := by decide
  rcases family_descends (prefixWord ++ tailWord_830397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830418 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_830418 : Nat := 118140960795 + 830418 * 2 ^ 59
def prefixEnd_830418 : Nat := 4983230072969 + 3 ^ 40 * 830418 * 2
def baseEnd_830418 : Nat := 379025402795944195071985

theorem tailTrace_830418 : CollatzResearch.WordTrace tailWord_830418 prefixEnd_830418 379025402795944195071985 := by
  unfold tailWord_830418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7571958176386221237078977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20191888470363256632210605 7571958176386221237078977)
  ·
    refine ⟨5678968632289665927809233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7571958176386221237078977 5678968632289665927809233)
    ·
      refine ⟨4259226474217249445856925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5678968632289665927809233 4259226474217249445856925)
      ·
        refine ⟨1597209927831468542196347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4259226474217249445856925 1597209927831468542196347)
        ·
          refine ⟨2395814891747202813294521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597209927831468542196347 2395814891747202813294521)
          ·
            refine ⟨1796861168810402109970891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395814891747202813294521 1796861168810402109970891)
            ·
              refine ⟨2695291753215603164956337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796861168810402109970891 2695291753215603164956337)
              ·
                refine ⟨2021468814911702373717253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695291753215603164956337 2021468814911702373717253)
                ·
                  refine ⟨379025402795944195071985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021468814911702373717253 379025402795944195071985)
                  ·
                    rfl

theorem cell20_830418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_830418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830418 prefixEnd_830418 := by exact prefixLift 830418
  have htrace : WordTrace (prefixWord ++ tailWord_830418) baseStart_830418 baseEnd_830418 := by
    simpa [prefixWord, tailWord_830418, baseEnd_830418] using wordTrace_append hprefix tailTrace_830418
  have hstable : (prefixWord ++ tailWord_830418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830418).length < 2 ^ (prefixWord ++ tailWord_830418).sum := by decide
  have hdescent : baseEnd_830418 < baseStart_830418 := by decide
  rcases family_descends (prefixWord ++ tailWord_830418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830425 : List Nat := [1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_830425 : Nat := 118140960795 + 830425 * 2 ^ 59
def prefixEnd_830425 : Nat := 4983230072969 + 3 ^ 40 * 830425 * 2
def baseEnd_830425 : Nat := 126342865928894427279541

theorem tailTrace_830425 : CollatzResearch.WordTrace tailWord_830425 prefixEnd_830425 126342865928894427279541 := by
  unfold tailWord_830425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288088016519525143820729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20192058677679683429213819 30288088016519525143820729)
  ·
    refine ⟨22716066012389643857865547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30288088016519525143820729 22716066012389643857865547)
    ·
      refine ⟨34074099018584465786798321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22716066012389643857865547 34074099018584465786798321)
      ·
        refine ⟨25555574263938349340098741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34074099018584465786798321 25555574263938349340098741)
        ·
          refine ⟨2395835087244220250634257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25555574263938349340098741 2395835087244220250634257)
          ·
            refine ⟨1796876315433165187975693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395835087244220250634257 1796876315433165187975693)
            ·
              refine ⟨673828618287436945490885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1796876315433165187975693 673828618287436945490885)
              ·
                refine ⟨126342865928894427279541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673828618287436945490885 126342865928894427279541)
                ·
                  rfl

theorem cell20_830425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_830425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830425 prefixEnd_830425 := by exact prefixLift 830425
  have htrace : WordTrace (prefixWord ++ tailWord_830425) baseStart_830425 baseEnd_830425 := by
    simpa [prefixWord, tailWord_830425, baseEnd_830425] using wordTrace_append hprefix tailTrace_830425
  have hstable : (prefixWord ++ tailWord_830425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830425).length < 2 ^ (prefixWord ++ tailWord_830425).sum := by decide
  have hdescent : baseEnd_830425 < baseStart_830425 := by decide
  rcases family_descends (prefixWord ++ tailWord_830425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830449 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_830449 : Nat := 118140960795 + 830449 * 2 ^ 59
def prefixEnd_830449 : Nat := 4983230072969 + 3 ^ 40 * 830449 * 2
def baseEnd_830449 : Nat := 379039552040645865038525

theorem tailTrace_830449 : CollatzResearch.WordTrace tailWord_830449 prefixEnd_830449 379039552040645865038525 := by
  unfold tailWord_830449
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288963368432577242694401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20192642245621718161796267 30288963368432577242694401)
  ·
    refine ⟨22716722526324432932020801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30288963368432577242694401 22716722526324432932020801)
    ·
      refine ⟨17037541894743324699015601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22716722526324432932020801 17037541894743324699015601)
      ·
        refine ⟨12778156421057493524261701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17037541894743324699015601 12778156421057493524261701)
        ·
          refine ⟨2395904328948280035799069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12778156421057493524261701 2395904328948280035799069)
          ·
            refine ⟨898464123355605013424651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2395904328948280035799069 898464123355605013424651)
            ·
              refine ⟨1347696185033407520136977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898464123355605013424651 1347696185033407520136977)
              ·
                refine ⟨1010772138775055640102733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347696185033407520136977 1010772138775055640102733)
                ·
                  refine ⟨379039552040645865038525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010772138775055640102733 379039552040645865038525)
                  ·
                    rfl

theorem cell20_830449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_830449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830449 prefixEnd_830449 := by exact prefixLift 830449
  have htrace : WordTrace (prefixWord ++ tailWord_830449) baseStart_830449 baseEnd_830449 := by
    simpa [prefixWord, tailWord_830449, baseEnd_830449] using wordTrace_append hprefix tailTrace_830449
  have hstable : (prefixWord ++ tailWord_830449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830449).length < 2 ^ (prefixWord ++ tailWord_830449).sum := by decide
  have hdescent : baseEnd_830449 < baseStart_830449 := by decide
  rcases family_descends (prefixWord ++ tailWord_830449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830525 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 3]
def baseStart_830525 : Nat := 118140960795 + 830525 * 2 ^ 59
def prefixEnd_830525 : Nat := 4983230072969 + 3 ^ 40 * 830525 * 2
def baseEnd_830525 : Nat := 379074240511527378504881

theorem tailTrace_830525 : CollatzResearch.WordTrace tailWord_830525 prefixEnd_830525 379074240511527378504881 := by
  unfold tailWord_830525
  simp only [CollatzResearch.WordTrace]
  refine ⟨30291735316157242222461029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20194490210771494814974019 30291735316157242222461029)
  ·
    refine ⟨5679700371779482916711443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30291735316157242222461029 5679700371779482916711443)
    ·
      refine ⟨8519550557669224375067165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679700371779482916711443 8519550557669224375067165)
      ·
        refine ⟨3194831459125959140650187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8519550557669224375067165 3194831459125959140650187)
        ·
          refine ⟨4792247188688938710975281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194831459125959140650187 4792247188688938710975281)
          ·
            refine ⟨3594185391516704033231461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4792247188688938710975281 3594185391516704033231461)
            ·
              refine ⟨673909760909382006230899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3594185391516704033231461 673909760909382006230899)
              ·
                refine ⟨1010864641364073009346349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673909760909382006230899 1010864641364073009346349)
                ·
                  refine ⟨379074240511527378504881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1010864641364073009346349 379074240511527378504881)
                  ·
                    rfl

theorem cell20_830525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_830525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830525 prefixEnd_830525 := by exact prefixLift 830525
  have htrace : WordTrace (prefixWord ++ tailWord_830525) baseStart_830525 baseEnd_830525 := by
    simpa [prefixWord, tailWord_830525, baseEnd_830525] using wordTrace_append hprefix tailTrace_830525
  have hstable : (prefixWord ++ tailWord_830525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830525).length < 2 ^ (prefixWord ++ tailWord_830525).sum := by decide
  have hdescent : baseEnd_830525 < baseStart_830525 := by decide
  rcases family_descends (prefixWord ++ tailWord_830525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830536 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_830536 : Nat := 118140960795 + 830536 * 2 ^ 59
def prefixEnd_830536 : Nat := 4983230072969 + 3 ^ 40 * 830536 * 2
def baseEnd_830536 : Nat := 379079261211260229138169

theorem tailTrace_830536 : CollatzResearch.WordTrace tailWord_830536 prefixEnd_830536 379079261211260229138169 := by
  unfold tailWord_830536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146068259558695550555731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20194757679411594067407641 15146068259558695550555731)
  ·
    refine ⟨22719102389338043325833597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15146068259558695550555731 22719102389338043325833597)
    ·
      refine ⟨8519663396001766247187599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22719102389338043325833597 8519663396001766247187599)
      ·
        refine ⟨12779495094002649370781399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519663396001766247187599 12779495094002649370781399)
        ·
          refine ⟨19169242641003974056172099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12779495094002649370781399 19169242641003974056172099)
          ·
            refine ⟨28753863961505961084258149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19169242641003974056172099 28753863961505961084258149)
            ·
              refine ⟨5391349492782367703298403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28753863961505961084258149 5391349492782367703298403)
              ·
                refine ⟨8087024239173551554947605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391349492782367703298403 8087024239173551554947605)
                ·
                  refine ⟨379079261211260229138169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8087024239173551554947605 379079261211260229138169)
                  ·
                    rfl

theorem cell20_830536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_830536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830536 prefixEnd_830536 := by exact prefixLift 830536
  have htrace : WordTrace (prefixWord ++ tailWord_830536) baseStart_830536 baseEnd_830536 := by
    simpa [prefixWord, tailWord_830536, baseEnd_830536] using wordTrace_append hprefix tailTrace_830536
  have hstable : (prefixWord ++ tailWord_830536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830536).length < 2 ^ (prefixWord ++ tailWord_830536).sum := by decide
  have hdescent : baseEnd_830536 < baseStart_830536 := by decide
  rcases family_descends (prefixWord ++ tailWord_830536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830590 : List Nat := [4, 2, 4, 1, 1, 1, 3, 4]
def baseStart_830590 : Nat := 118140960795 + 830590 * 2 ^ 59
def prefixEnd_830590 : Nat := 4983230072969 + 3 ^ 40 * 830590 * 2
def baseEnd_830590 : Nat := 126367969427558680445983

theorem tailTrace_830590 : CollatzResearch.WordTrace tailWord_830590 prefixEnd_830590 126367969427558680445983 := by
  unfold tailWord_830590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786763257615219790447153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20196070707281172215718149 3786763257615219790447153)
  ·
    refine ⟨2840072443211414842835365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3786763257615219790447153 2840072443211414842835365)
    ·
      refine ⟨532513583102140283031631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2840072443211414842835365 532513583102140283031631)
      ·
        refine ⟨798770374653210424547447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532513583102140283031631 798770374653210424547447)
        ·
          refine ⟨1198155561979815636821171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798770374653210424547447 1198155561979815636821171)
          ·
            refine ⟨1797233342969723455231757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198155561979815636821171 1797233342969723455231757)
            ·
              refine ⟨673962503613646295711909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797233342969723455231757 673962503613646295711909)
              ·
                refine ⟨126367969427558680445983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673962503613646295711909 126367969427558680445983)
                ·
                  rfl

theorem cell20_830590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_830590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830590 prefixEnd_830590 := by exact prefixLift 830590
  have htrace : WordTrace (prefixWord ++ tailWord_830590) baseStart_830590 baseEnd_830590 := by
    simpa [prefixWord, tailWord_830590, baseEnd_830590] using wordTrace_append hprefix tailTrace_830590
  have hstable : (prefixWord ++ tailWord_830590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830590).length < 2 ^ (prefixWord ++ tailWord_830590).sum := by decide
  have hdescent : baseEnd_830590 < baseStart_830590 := by decide
  rcases family_descends (prefixWord ++ tailWord_830590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830629 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_830629 : Nat := 118140960795 + 830629 * 2 ^ 59
def prefixEnd_830629 : Nat := 4983230072969 + 3 ^ 40 * 830629 * 2
def baseEnd_830629 : Nat := 379121708945365239037789

theorem tailTrace_830629 : CollatzResearch.WordTrace tailWord_830629 prefixEnd_830629 379121708945365239037789 := by
  unfold tailWord_830629
  simp only [CollatzResearch.WordTrace]
  refine ⟨30295528507780467984246941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197019005186978656164627 30295528507780467984246941)
  ·
    refine ⟨11360823190417675494092603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30295528507780467984246941 11360823190417675494092603)
    ·
      refine ⟨17041234785626513241138905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11360823190417675494092603 17041234785626513241138905)
      ·
        refine ⟨12780926089219884930854179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17041234785626513241138905 12780926089219884930854179)
        ·
          refine ⟨19171389133829827396281269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780926089219884930854179 19171389133829827396281269)
          ·
            refine ⟨1797317731296546318401369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19171389133829827396281269 1797317731296546318401369)
            ·
              refine ⟨1347988298472409738801027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797317731296546318401369 1347988298472409738801027)
              ·
                refine ⟨2021982447708614608201541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347988298472409738801027 2021982447708614608201541)
                ·
                  refine ⟨379121708945365239037789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2021982447708614608201541 379121708945365239037789)
                  ·
                    rfl

theorem cell20_830629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_830629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830629 prefixEnd_830629 := by exact prefixLift 830629
  have htrace : WordTrace (prefixWord ++ tailWord_830629) baseStart_830629 baseEnd_830629 := by
    simpa [prefixWord, tailWord_830629, baseEnd_830629] using wordTrace_append hprefix tailTrace_830629
  have hstable : (prefixWord ++ tailWord_830629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830629).length < 2 ^ (prefixWord ++ tailWord_830629).sum := by decide
  have hdescent : baseEnd_830629 < baseStart_830629 := by decide
  rcases family_descends (prefixWord ++ tailWord_830629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830643 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_830643 : Nat := 118140960795 + 830643 * 2 ^ 59
def prefixEnd_830643 : Nat := 4983230072969 + 3 ^ 40 * 830643 * 2
def baseEnd_830643 : Nat := 379128098926843412571065

theorem tailTrace_830643 : CollatzResearch.WordTrace tailWord_830643 prefixEnd_830643 379128098926843412571065 := by
  unfold tailWord_830643
  simp only [CollatzResearch.WordTrace]
  refine ⟨30296039129729748375256583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197359419819832250171055 30296039129729748375256583)
  ·
    refine ⟨45444058694594622562884875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30296039129729748375256583 45444058694594622562884875)
    ·
      refine ⟨68166088041891933844327313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45444058694594622562884875 68166088041891933844327313)
      ·
        refine ⟨51124566031418950383245485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68166088041891933844327313 51124566031418950383245485)
        ·
          refine ⟨19171712261782106393717057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51124566031418950383245485 19171712261782106393717057)
          ·
            refine ⟨14378784196336579795287793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171712261782106393717057 14378784196336579795287793)
            ·
              refine ⟨10784088147252434846465845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14378784196336579795287793 10784088147252434846465845)
              ·
                refine ⟨1011008263804915766856173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10784088147252434846465845 1011008263804915766856173)
                ·
                  refine ⟨379128098926843412571065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011008263804915766856173 379128098926843412571065)
                  ·
                    rfl

theorem cell20_830643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_830643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830643 prefixEnd_830643 := by exact prefixLift 830643
  have htrace : WordTrace (prefixWord ++ tailWord_830643) baseStart_830643 baseEnd_830643 := by
    simpa [prefixWord, tailWord_830643, baseEnd_830643] using wordTrace_append hprefix tailTrace_830643
  have hstable : (prefixWord ++ tailWord_830643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830643).length < 2 ^ (prefixWord ++ tailWord_830643).sum := by decide
  have hdescent : baseEnd_830643 < baseStart_830643 := by decide
  rcases family_descends (prefixWord ++ tailWord_830643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830667 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 2]
def baseStart_830667 : Nat := 118140960795 + 830667 * 2 ^ 59
def prefixEnd_830667 : Nat := 4983230072969 + 3 ^ 40 * 830667 * 2
def baseEnd_830667 : Nat := 379139053180805995770967

theorem tailTrace_830667 : CollatzResearch.WordTrace tailWord_830667 prefixEnd_830667 379139053180805995770967 := by
  unfold tailWord_830667
  simp only [CollatzResearch.WordTrace]
  refine ⟨30296914481642800474130255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197942987761866982753503 30296914481642800474130255)
  ·
    refine ⟨45445371722464200711195383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30296914481642800474130255 45445371722464200711195383)
    ·
      refine ⟨68168057583696301066793075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45445371722464200711195383 68168057583696301066793075)
      ·
        refine ⟨102252086375544451600189613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68168057583696301066793075 102252086375544451600189613)
        ·
          refine ⟨38344532390829169350071105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102252086375544451600189613 38344532390829169350071105)
          ·
            refine ⟨28758399293121877012553329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38344532390829169350071105 28758399293121877012553329)
            ·
              refine ⟨21568799469841407759414997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28758399293121877012553329 21568799469841407759414997)
              ·
                refine ⟨505518737574407994361289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21568799469841407759414997 505518737574407994361289)
                ·
                  refine ⟨379139053180805995770967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505518737574407994361289 379139053180805995770967)
                  ·
                    rfl

theorem cell20_830667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2].length) (baseStart_830667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830667 prefixEnd_830667 := by exact prefixLift 830667
  have htrace : WordTrace (prefixWord ++ tailWord_830667) baseStart_830667 baseEnd_830667 := by
    simpa [prefixWord, tailWord_830667, baseEnd_830667] using wordTrace_append hprefix tailTrace_830667
  have hstable : (prefixWord ++ tailWord_830667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830667).length < 2 ^ (prefixWord ++ tailWord_830667).sum := by decide
  have hdescent : baseEnd_830667 < baseStart_830667 := by decide
  rcases family_descends (prefixWord ++ tailWord_830667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830681 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_830681 : Nat := 118140960795 + 830681 * 2 ^ 59
def prefixEnd_830681 : Nat := 4983230072969 + 3 ^ 40 * 830681 * 2
def baseEnd_830681 : Nat := 379145443162284169304243

theorem tailTrace_830681 : CollatzResearch.WordTrace tailWord_830681 prefixEnd_830681 379145443162284169304243 := by
  unfold tailWord_830681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30297425103592080865139897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20198283402394720576759931 30297425103592080865139897)
  ·
    refine ⟨22723068827694060648854923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30297425103592080865139897 22723068827694060648854923)
    ·
      refine ⟨34084603241541090973282385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22723068827694060648854923 34084603241541090973282385)
      ·
        refine ⟨25563452431155818229961789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34084603241541090973282385 25563452431155818229961789)
        ·
          refine ⟨9586294661683431836235671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25563452431155818229961789 9586294661683431836235671)
          ·
            refine ⟨14379441992525147754353507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9586294661683431836235671 14379441992525147754353507)
            ·
              refine ⟨21569162988787721631530261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14379441992525147754353507 21569162988787721631530261)
              ·
                refine ⟨1011054515099424451477981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21569162988787721631530261 1011054515099424451477981)
                ·
                  refine ⟨379145443162284169304243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011054515099424451477981 379145443162284169304243)
                  ·
                    rfl

theorem cell20_830681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_830681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830681 prefixEnd_830681 := by exact prefixLift 830681
  have htrace : WordTrace (prefixWord ++ tailWord_830681) baseStart_830681 baseEnd_830681 := by
    simpa [prefixWord, tailWord_830681, baseEnd_830681] using wordTrace_append hprefix tailTrace_830681
  have hstable : (prefixWord ++ tailWord_830681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830681).length < 2 ^ (prefixWord ++ tailWord_830681).sum := by decide
  have hdescent : baseEnd_830681 < baseStart_830681 := by decide
  rcases family_descends (prefixWord ++ tailWord_830681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830698 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_830698 : Nat := 118140960795 + 830698 * 2 ^ 59
def prefixEnd_830698 : Nat := 4983230072969 + 3 ^ 40 * 830698 * 2
def baseEnd_830698 : Nat := 379153202425507665737507

theorem tailTrace_830698 : CollatzResearch.WordTrace tailWord_830698 prefixEnd_830698 379153202425507665737507 := by
  unfold tailWord_830698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574511286132623192127187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20198696763020328512339165 7574511286132623192127187)
  ·
    refine ⟨11361766929198934788190781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574511286132623192127187 11361766929198934788190781)
    ·
      refine ⟨4260662598449600545571543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11361766929198934788190781 4260662598449600545571543)
      ·
        refine ⟨6390993897674400818357315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260662598449600545571543 6390993897674400818357315)
        ·
          refine ⟨9586490846511601227535973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6390993897674400818357315 9586490846511601227535973)
          ·
            refine ⟨1797467033720925230162995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9586490846511601227535973 1797467033720925230162995)
            ·
              refine ⟨2696200550581387845244493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797467033720925230162995 2696200550581387845244493)
              ·
                refine ⟨1011075206468020441966685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2696200550581387845244493 1011075206468020441966685)
                ·
                  refine ⟨379153202425507665737507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011075206468020441966685 379153202425507665737507)
                  ·
                    rfl

theorem cell20_830698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_830698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830698 prefixEnd_830698 := by exact prefixLift 830698
  have htrace : WordTrace (prefixWord ++ tailWord_830698) baseStart_830698 baseEnd_830698 := by
    simpa [prefixWord, tailWord_830698, baseEnd_830698] using wordTrace_append hprefix tailTrace_830698
  have hstable : (prefixWord ++ tailWord_830698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830698).length < 2 ^ (prefixWord ++ tailWord_830698).sum := by decide
  have hdescent : baseEnd_830698 < baseStart_830698 := by decide
  rcases family_descends (prefixWord ++ tailWord_830698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830777 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 2]
def baseStart_830777 : Nat := 118140960795 + 830777 * 2 ^ 59
def prefixEnd_830777 : Nat := 4983230072969 + 3 ^ 40 * 830777 * 2
def baseEnd_830777 : Nat := 379189260178134502103851

theorem tailTrace_830777 : CollatzResearch.WordTrace tailWord_830777 prefixEnd_830777 379189260178134502103851 := by
  unfold tailWord_830777
  simp only [CollatzResearch.WordTrace]
  refine ⟨30300926511244289260634585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20200617674162859507089723 30300926511244289260634585)
  ·
    refine ⟨22725694883433216945475939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30300926511244289260634585 22725694883433216945475939)
    ·
      refine ⟨34088542325149825418213909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22725694883433216945475939 34088542325149825418213909)
      ·
        refine ⟨1597900421491398066478777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34088542325149825418213909 1597900421491398066478777)
        ·
          refine ⟨1198425316118548549859083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597900421491398066478777 1198425316118548549859083)
          ·
            refine ⟨1797637974177822824788625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198425316118548549859083 1797637974177822824788625)
            ·
              refine ⟨1348228480633367118591469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797637974177822824788625 1348228480633367118591469)
              ·
                refine ⟨505585680237512669471801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348228480633367118591469 505585680237512669471801)
                ·
                  refine ⟨379189260178134502103851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505585680237512669471801 379189260178134502103851)
                  ·
                    rfl

theorem cell20_830777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_830777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830777 prefixEnd_830777 := by exact prefixLift 830777
  have htrace : WordTrace (prefixWord ++ tailWord_830777) baseStart_830777 baseEnd_830777 := by
    simpa [prefixWord, tailWord_830777, baseEnd_830777] using wordTrace_append hprefix tailTrace_830777
  have hstable : (prefixWord ++ tailWord_830777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830777).length < 2 ^ (prefixWord ++ tailWord_830777).sum := by decide
  have hdescent : baseEnd_830777 < baseStart_830777 := by decide
  rcases family_descends (prefixWord ++ tailWord_830777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830892 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_830892 : Nat := 118140960795 + 830892 * 2 ^ 59
def prefixEnd_830892 : Nat := 4983230072969 + 3 ^ 40 * 830892 * 2
def baseEnd_830892 : Nat := 379241749311705213270047

theorem tailTrace_830892 : CollatzResearch.WordTrace tailWord_830892 prefixEnd_830892 379241749311705213270047 := by
  unfold tailWord_830892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152560452913831950535465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20203413937218442600713953 15152560452913831950535465)
  ·
    refine ⟨11364420339685373962901599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15152560452913831950535465 11364420339685373962901599)
    ·
      refine ⟨17046630509528060944352399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11364420339685373962901599 17046630509528060944352399)
      ·
        refine ⟨25569945764292091416528599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17046630509528060944352399 25569945764292091416528599)
        ·
          refine ⟨38354918646438137124792899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25569945764292091416528599 38354918646438137124792899)
          ·
            refine ⟨57532377969657205687189349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38354918646438137124792899 57532377969657205687189349)
            ·
              refine ⟨10787320869310726066348003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57532377969657205687189349 10787320869310726066348003)
              ·
                refine ⟨16180981303966089099522005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787320869310726066348003 16180981303966089099522005)
                ·
                  refine ⟨379241749311705213270047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16180981303966089099522005 379241749311705213270047)
                  ·
                    rfl

theorem cell20_830892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_830892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830892 prefixEnd_830892 := by exact prefixLift 830892
  have htrace : WordTrace (prefixWord ++ tailWord_830892) baseStart_830892 baseEnd_830892 := by
    simpa [prefixWord, tailWord_830892, baseEnd_830892] using wordTrace_append hprefix tailTrace_830892
  have hstable : (prefixWord ++ tailWord_830892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830892).length < 2 ^ (prefixWord ++ tailWord_830892).sum := by decide
  have hdescent : baseEnd_830892 < baseStart_830892 := by decide
  rcases family_descends (prefixWord ++ tailWord_830892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830908 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_830908 : Nat := 118140960795 + 830908 * 2 ^ 59
def prefixEnd_830908 : Nat := 4983230072969 + 3 ^ 40 * 830908 * 2
def baseEnd_830908 : Nat := 379249052147680268736649

theorem tailTrace_830908 : CollatzResearch.WordTrace tailWord_830908 prefixEnd_830908 379249052147680268736649 := by
  unfold tailWord_830908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152852236884849316826689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20203802982513132422435585 15152852236884849316826689)
  ·
    refine ⟨11364639177663636987620017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15152852236884849316826689 11364639177663636987620017)
    ·
      refine ⟨8523479383247727740715013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11364639177663636987620017 8523479383247727740715013)
      ·
        refine ⟨1598152384358948951384065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8523479383247727740715013 1598152384358948951384065)
        ·
          refine ⟨1198614288269211713538049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598152384358948951384065 1198614288269211713538049)
          ·
            refine ⟨898960716201908785153537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198614288269211713538049 898960716201908785153537)
            ·
              refine ⟨674220537151431588865153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898960716201908785153537 674220537151431588865153)
              ·
                refine ⟨505665402863573691648865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674220537151431588865153 505665402863573691648865)
                ·
                  refine ⟨379249052147680268736649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505665402863573691648865 379249052147680268736649)
                  ·
                    rfl

theorem cell20_830908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_830908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830908 prefixEnd_830908 := by exact prefixLift 830908
  have htrace : WordTrace (prefixWord ++ tailWord_830908) baseStart_830908 baseEnd_830908 := by
    simpa [prefixWord, tailWord_830908, baseEnd_830908] using wordTrace_append hprefix tailTrace_830908
  have hstable : (prefixWord ++ tailWord_830908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830908).length < 2 ^ (prefixWord ++ tailWord_830908).sum := by decide
  have hdescent : baseEnd_830908 < baseStart_830908 := by decide
  rcases family_descends (prefixWord ++ tailWord_830908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830912 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_830912 : Nat := 118140960795 + 830912 * 2 ^ 59
def prefixEnd_830912 : Nat := 4983230072969 + 3 ^ 40 * 830912 * 2
def baseEnd_830912 : Nat := 379250877856674032603299

theorem tailTrace_830912 : CollatzResearch.WordTrace tailWord_830912 prefixEnd_830912 379250877856674032603299 := by
  unfold tailWord_830912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152925182877603658399495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20203900243836804877865993 15152925182877603658399495)
  ·
    refine ⟨22729387774316405487599243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152925182877603658399495 22729387774316405487599243)
    ·
      refine ⟨34094081661474608231398865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729387774316405487599243 34094081661474608231398865)
      ·
        refine ⟨25570561246105956173549149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34094081661474608231398865 25570561246105956173549149)
        ·
          refine ⟨9588960467289733565080931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25570561246105956173549149 9588960467289733565080931)
          ·
            refine ⟨14383440700934600347621397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588960467289733565080931 14383440700934600347621397)
            ·
              refine ⟨674223782856309391294753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14383440700934600347621397 674223782856309391294753)
              ·
                refine ⟨505667837142232043471065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674223782856309391294753 505667837142232043471065)
                ·
                  refine ⟨379250877856674032603299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505667837142232043471065 379250877856674032603299)
                  ·
                    rfl

theorem cell20_830912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_830912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830912 prefixEnd_830912 := by exact prefixLift 830912
  have htrace : WordTrace (prefixWord ++ tailWord_830912) baseStart_830912 baseEnd_830912 := by
    simpa [prefixWord, tailWord_830912, baseEnd_830912] using wordTrace_append hprefix tailTrace_830912
  have hstable : (prefixWord ++ tailWord_830912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830912).length < 2 ^ (prefixWord ++ tailWord_830912).sum := by decide
  have hdescent : baseEnd_830912 < baseStart_830912 := by decide
  rcases family_descends (prefixWord ++ tailWord_830912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830923 : List Nat := [1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_830923 : Nat := 118140960795 + 830923 * 2 ^ 59
def prefixEnd_830923 : Nat := 4983230072969 + 3 ^ 40 * 830923 * 2
def baseEnd_830923 : Nat := 126418632852135627745529

theorem tailTrace_830923 : CollatzResearch.WordTrace tailWord_830923 prefixEnd_830923 126418632852135627745529 := by
  unfold tailWord_830923
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306251568715356195449423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20204167712476904130299615 30306251568715356195449423)
  ·
    refine ⟨45459377353073034293174135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30306251568715356195449423 45459377353073034293174135)
    ·
      refine ⟨68189066029609551439761203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45459377353073034293174135 68189066029609551439761203)
      ·
        refine ⟨102283599044414327159641805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68189066029609551439761203 102283599044414327159641805)
        ·
          refine ⟨38356349641655372684865677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102283599044414327159641805 38356349641655372684865677)
          ·
            refine ⟨14383631115620764756824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38356349641655372684865677 14383631115620764756824629)
            ·
              refine ⟨1348465417089446695952309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14383631115620764756824629 1348465417089446695952309)
              ·
                refine ⟨126418632852135627745529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1348465417089446695952309 126418632852135627745529)
                ·
                  rfl

theorem cell20_830923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_830923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830923 prefixEnd_830923 := by exact prefixLift 830923
  have htrace : WordTrace (prefixWord ++ tailWord_830923) baseStart_830923 baseEnd_830923 := by
    simpa [prefixWord, tailWord_830923, baseEnd_830923] using wordTrace_append hprefix tailTrace_830923
  have hstable : (prefixWord ++ tailWord_830923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830923).length < 2 ^ (prefixWord ++ tailWord_830923).sum := by decide
  have hdescent : baseEnd_830923 < baseStart_830923 := by decide
  rcases family_descends (prefixWord ++ tailWord_830923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830961 : List Nat := [1, 2, 2, 2, 3, 3, 7]
def baseStart_830961 : Nat := 118140960795 + 830961 * 2 ^ 59
def prefixEnd_830961 : Nat := 4983230072969 + 3 ^ 40 * 830961 * 2
def baseEnd_830961 : Nat := 42141471421316404441085

theorem tailTrace_830961 : CollatzResearch.WordTrace tailWord_830961 prefixEnd_830961 42141471421316404441085 := by
  unfold tailWord_830961
  simp only [CollatzResearch.WordTrace]
  refine ⟨30307637542577688685332737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20205091695051792456888491 30307637542577688685332737)
  ·
    refine ⟨22730728156933266513999553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30307637542577688685332737 22730728156933266513999553)
    ·
      refine ⟨17048046117699949885499665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22730728156933266513999553 17048046117699949885499665)
      ·
        refine ⟨12786034588274962414124749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17048046117699949885499665 12786034588274962414124749)
        ·
          refine ⟨4794762970603110905296781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12786034588274962414124749 4794762970603110905296781)
          ·
            refine ⟨1798036113976166589486293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4794762970603110905296781 1798036113976166589486293)
            ·
              refine ⟨42141471421316404441085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1798036113976166589486293 42141471421316404441085)
              ·
                rfl

theorem cell20_830961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_830961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_830961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_830961 prefixEnd_830961 := by exact prefixLift 830961
  have htrace : WordTrace (prefixWord ++ tailWord_830961) baseStart_830961 baseEnd_830961 := by
    simpa [prefixWord, tailWord_830961, baseEnd_830961] using wordTrace_append hprefix tailTrace_830961
  have hstable : (prefixWord ++ tailWord_830961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830961).length < 2 ^ (prefixWord ++ tailWord_830961).sum := by decide
  have hdescent : baseEnd_830961 < baseStart_830961 := by decide
  rcases family_descends (prefixWord ++ tailWord_830961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831036 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_831036 : Nat := 118140960795 + 831036 * 2 ^ 59
def prefixEnd_831036 : Nat := 4983230072969 + 3 ^ 40 * 831036 * 2
def baseEnd_831036 : Nat := 379307474835480712469459

theorem tailTrace_831036 : CollatzResearch.WordTrace tailWord_831036 prefixEnd_831036 379307474835480712469459 := by
  unfold tailWord_831036
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155186508652988247156481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20206915344870650996208641 15155186508652988247156481)
  ·
    refine ⟨11366389881489741185367361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15155186508652988247156481 11366389881489741185367361)
    ·
      refine ⟨8524792411117305889025521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11366389881489741185367361 8524792411117305889025521)
      ·
        refine ⟨6393594308337979416769141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8524792411117305889025521 6393594308337979416769141)
        ·
          refine ⟨599399466406685570322107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6393594308337979416769141 599399466406685570322107)
          ·
            refine ⟨899099199610028355483161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599399466406685570322107 899099199610028355483161)
            ·
              refine ⟨674324399707521266612371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899099199610028355483161 674324399707521266612371)
              ·
                refine ⟨1011486599561281899918557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674324399707521266612371 1011486599561281899918557)
                ·
                  refine ⟨379307474835480712469459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011486599561281899918557 379307474835480712469459)
                  ·
                    rfl

theorem cell20_831036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_831036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831036 prefixEnd_831036 := by exact prefixLift 831036
  have htrace : WordTrace (prefixWord ++ tailWord_831036) baseStart_831036 baseEnd_831036 := by
    simpa [prefixWord, tailWord_831036, baseEnd_831036] using wordTrace_append hprefix tailTrace_831036
  have hstable : (prefixWord ++ tailWord_831036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831036).length < 2 ^ (prefixWord ++ tailWord_831036).sum := by decide
  have hdescent : baseEnd_831036 < baseStart_831036 := by decide
  rcases family_descends (prefixWord ++ tailWord_831036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831051 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_831051 : Nat := 118140960795 + 831051 * 2 ^ 59
def prefixEnd_831051 : Nat := 4983230072969 + 3 ^ 40 * 831051 * 2
def baseEnd_831051 : Nat := 379314321244207326969397

theorem tailTrace_831051 : CollatzResearch.WordTrace tailWord_831051 prefixEnd_831051 379314321244207326969397 := by
  unfold tailWord_831051
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310920112251634056109007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20207280074834422704072671 30310920112251634056109007)
  ·
    refine ⟨45466380168377451084163511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30310920112251634056109007 45466380168377451084163511)
    ·
      refine ⟨68199570252566176626245267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45466380168377451084163511 68199570252566176626245267)
      ·
        refine ⟨102299355378849264939367901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68199570252566176626245267 102299355378849264939367901)
        ·
          refine ⟨38362258267068474352262963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102299355378849264939367901 38362258267068474352262963)
          ·
            refine ⟨57543387400602711528394445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38362258267068474352262963 57543387400602711528394445)
            ·
              refine ⟨21578770275226016823147917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57543387400602711528394445 21578770275226016823147917)
              ·
                refine ⟨8092038853209756308680469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21578770275226016823147917 8092038853209756308680469)
                ·
                  refine ⟨379314321244207326969397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8092038853209756308680469 379314321244207326969397)
                  ·
                    rfl

theorem cell20_831051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_831051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831051 prefixEnd_831051 := by exact prefixLift 831051
  have htrace : WordTrace (prefixWord ++ tailWord_831051) baseStart_831051 baseEnd_831051 := by
    simpa [prefixWord, tailWord_831051, baseEnd_831051] using wordTrace_append hprefix tailTrace_831051
  have hstable : (prefixWord ++ tailWord_831051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831051).length < 2 ^ (prefixWord ++ tailWord_831051).sum := by decide
  have hdescent : baseEnd_831051 < baseStart_831051 := by decide
  rcases family_descends (prefixWord ++ tailWord_831051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831089 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_831089 : Nat := 118140960795 + 831089 * 2 ^ 59
def prefixEnd_831089 : Nat := 4983230072969 + 3 ^ 40 * 831089 * 2
def baseEnd_831089 : Nat := 379331665479648083702575

theorem tailTrace_831089 : CollatzResearch.WordTrace tailWord_831089 prefixEnd_831089 379331665479648083702575 := by
  unfold tailWord_831089
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312306086113966545992321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20208204057409311030661547 30312306086113966545992321)
  ·
    refine ⟨22734229564585474909494241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30312306086113966545992321 22734229564585474909494241)
    ·
      refine ⟨17050672173439106182120681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22734229564585474909494241 17050672173439106182120681)
      ·
        refine ⟨12788004130079329636590511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17050672173439106182120681 12788004130079329636590511)
        ·
          refine ⟨19182006195118994454885767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12788004130079329636590511 19182006195118994454885767)
          ·
            refine ⟨28773009292678491682328651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19182006195118994454885767 28773009292678491682328651)
            ·
              refine ⟨43159513939017737523492977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28773009292678491682328651 43159513939017737523492977)
              ·
                refine ⟨32369635454263303142619733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43159513939017737523492977 32369635454263303142619733)
                ·
                  refine ⟨379331665479648083702575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32369635454263303142619733 379331665479648083702575)
                  ·
                    rfl

theorem cell20_831089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_831089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831089 prefixEnd_831089 := by exact prefixLift 831089
  have htrace : WordTrace (prefixWord ++ tailWord_831089) baseStart_831089 baseEnd_831089 := by
    simpa [prefixWord, tailWord_831089, baseEnd_831089] using wordTrace_append hprefix tailTrace_831089
  have hstable : (prefixWord ++ tailWord_831089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831089).length < 2 ^ (prefixWord ++ tailWord_831089).sum := by decide
  have hdescent : baseEnd_831089 < baseStart_831089 := by decide
  rcases family_descends (prefixWord ++ tailWord_831089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831137 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_831137 : Nat := 118140960795 + 831137 * 2 ^ 59
def prefixEnd_831137 : Nat := 4983230072969 + 3 ^ 40 * 831137 * 2
def baseEnd_831137 : Nat := 379353573987573250102379

theorem tailTrace_831137 : CollatzResearch.WordTrace tailWord_831137 prefixEnd_831137 379353573987573250102379 := by
  unfold tailWord_831137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30314056789940070743739665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20209371193293380495826443 30314056789940070743739665)
  ·
    refine ⟨22735542592455053057804749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30314056789940070743739665 22735542592455053057804749)
    ·
      refine ⟨8525828472170644896676781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22735542592455053057804749 8525828472170644896676781)
      ·
        refine ⟨3197185677063991836253793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8525828472170644896676781 3197185677063991836253793)
        ·
          refine ⟨2397889257797993877190345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3197185677063991836253793 2397889257797993877190345)
          ·
            refine ⟨1798416943348495407892759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397889257797993877190345 1798416943348495407892759)
            ·
              refine ⟨2697625415022743111839139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798416943348495407892759 2697625415022743111839139)
              ·
                refine ⟨4046438122534114667758709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697625415022743111839139 4046438122534114667758709)
                ·
                  refine ⟨379353573987573250102379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4046438122534114667758709 379353573987573250102379)
                  ·
                    rfl

theorem cell20_831137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_831137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831137 prefixEnd_831137 := by exact prefixLift 831137
  have htrace : WordTrace (prefixWord ++ tailWord_831137) baseStart_831137 baseEnd_831137 := by
    simpa [prefixWord, tailWord_831137, baseEnd_831137] using wordTrace_append hprefix tailTrace_831137
  have hstable : (prefixWord ++ tailWord_831137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831137).length < 2 ^ (prefixWord ++ tailWord_831137).sum := by decide
  have hdescent : baseEnd_831137 < baseStart_831137 := by decide
  rcases family_descends (prefixWord ++ tailWord_831137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831150 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_831150 : Nat := 118140960795 + 831150 * 2 ^ 59
def prefixEnd_831150 : Nat := 4983230072969 + 3 ^ 40 * 831150 * 2
def baseEnd_831150 : Nat := 379359507541802982668993

theorem tailTrace_831150 : CollatzResearch.WordTrace tailWord_831150 prefixEnd_831150 379359507541802982668993 := by
  unfold tailWord_831150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789316367361621745495363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20209687292595315975975269 3789316367361621745495363)
  ·
    refine ⟨5683974551042432618243045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789316367361621745495363 5683974551042432618243045)
    ·
      refine ⟨1065745228320456115920571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5683974551042432618243045 1065745228320456115920571)
      ·
        refine ⟨1598617842480684173880857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065745228320456115920571 1598617842480684173880857)
        ·
          refine ⟨1198963381860513130410643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598617842480684173880857 1198963381860513130410643)
          ·
            refine ⟨1798445072790769695615965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198963381860513130410643 1798445072790769695615965)
            ·
              refine ⟨674416902296538635855987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1798445072790769695615965 674416902296538635855987)
              ·
                refine ⟨1011625353444807953783981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674416902296538635855987 1011625353444807953783981)
                ·
                  refine ⟨379359507541802982668993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011625353444807953783981 379359507541802982668993)
                  ·
                    rfl

theorem cell20_831150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_831150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831150 prefixEnd_831150 := by exact prefixLift 831150
  have htrace : WordTrace (prefixWord ++ tailWord_831150) baseStart_831150 baseEnd_831150 := by
    simpa [prefixWord, tailWord_831150, baseEnd_831150] using wordTrace_append hprefix tailTrace_831150
  have hstable : (prefixWord ++ tailWord_831150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831150).length < 2 ^ (prefixWord ++ tailWord_831150).sum := by decide
  have hdescent : baseEnd_831150 < baseStart_831150 := by decide
  rcases family_descends (prefixWord ++ tailWord_831150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831170 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_831170 : Nat := 118140960795 + 831170 * 2 ^ 59
def prefixEnd_831170 : Nat := 4983230072969 + 3 ^ 40 * 831170 * 2
def baseEnd_831170 : Nat := 379368636086771802002245

theorem tailTrace_831170 : CollatzResearch.WordTrace tailWord_831170 prefixEnd_831170 379368636086771802002245 := by
  unfold tailWord_831170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578815099705129344922741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20210173599213678253127309 7578815099705129344922741)
  ·
    refine ⟨710513915597355876086507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7578815099705129344922741 710513915597355876086507)
    ·
      refine ⟨1065770873396033814129761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710513915597355876086507 1065770873396033814129761)
      ·
        refine ⟨799328155047025360597321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1065770873396033814129761 799328155047025360597321)
        ·
          refine ⟨599496116285269020447991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799328155047025360597321 599496116285269020447991)
          ·
            refine ⟨899244174427903530671987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599496116285269020447991 899244174427903530671987)
            ·
              refine ⟨1348866261641855296007981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899244174427903530671987 1348866261641855296007981)
              ·
                refine ⟨505824848115695736002993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348866261641855296007981 505824848115695736002993)
                ·
                  refine ⟨379368636086771802002245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505824848115695736002993 379368636086771802002245)
                  ·
                    rfl

theorem cell20_831170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_831170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831170 prefixEnd_831170 := by exact prefixLift 831170
  have htrace : WordTrace (prefixWord ++ tailWord_831170) baseStart_831170 baseEnd_831170 := by
    simpa [prefixWord, tailWord_831170, baseEnd_831170] using wordTrace_append hprefix tailTrace_831170
  have hstable : (prefixWord ++ tailWord_831170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831170).length < 2 ^ (prefixWord ++ tailWord_831170).sum := by decide
  have hdescent : baseEnd_831170 < baseStart_831170 := by decide
  rcases family_descends (prefixWord ++ tailWord_831170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831174 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_831174 : Nat := 118140960795 + 831174 * 2 ^ 59
def prefixEnd_831174 : Nat := 4983230072969 + 3 ^ 40 * 831174 * 2
def baseEnd_831174 : Nat := 379370461795765565868895

theorem tailTrace_831174 : CollatzResearch.WordTrace tailWord_831174 prefixEnd_831174 379370461795765565868895 := by
  unfold tailWord_831174
  simp only [CollatzResearch.WordTrace]
  refine ⟨947356446587688314463643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20210270860537350708557717 947356446587688314463643)
  ·
    refine ⟨1421034669881532471695465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947356446587688314463643 1421034669881532471695465)
    ·
      refine ⟨1065776002411149353771599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1421034669881532471695465 1065776002411149353771599)
      ·
        refine ⟨1598664003616724030657399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065776002411149353771599 1598664003616724030657399)
        ·
          refine ⟨2397996005425086045986099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598664003616724030657399 2397996005425086045986099)
          ·
            refine ⟨3596994008137629068979149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397996005425086045986099 3596994008137629068979149)
            ·
              refine ⟨1348872753051610900867181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3596994008137629068979149 1348872753051610900867181)
              ·
                refine ⟨505827282394354087825193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348872753051610900867181 505827282394354087825193)
                ·
                  refine ⟨379370461795765565868895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505827282394354087825193 379370461795765565868895)
                  ·
                    rfl

theorem cell20_831174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_831174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831174 prefixEnd_831174 := by exact prefixLift 831174
  have htrace : WordTrace (prefixWord ++ tailWord_831174) baseStart_831174 baseEnd_831174 := by
    simpa [prefixWord, tailWord_831174, baseEnd_831174] using wordTrace_append hprefix tailTrace_831174
  have hstable : (prefixWord ++ tailWord_831174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831174).length < 2 ^ (prefixWord ++ tailWord_831174).sum := by decide
  have hdescent : baseEnd_831174 < baseStart_831174 := by decide
  rcases family_descends (prefixWord ++ tailWord_831174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831250 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_831250 : Nat := 118140960795 + 831250 * 2 ^ 59
def prefixEnd_831250 : Nat := 4983230072969 + 3 ^ 40 * 831250 * 2
def baseEnd_831250 : Nat := 379405150266647079335251

theorem tailTrace_831250 : CollatzResearch.WordTrace tailWord_831250 prefixEnd_831250 379405150266647079335251 := by
  unfold tailWord_831250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579544559632672760650801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20212118825687127361735469 7579544559632672760650801)
  ·
    refine ⟨5684658419724504570488101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7579544559632672760650801 5684658419724504570488101)
    ·
      refine ⟨1065873453698344606966519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5684658419724504570488101 1065873453698344606966519)
      ·
        refine ⟨1598810180547516910449779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065873453698344606966519 1598810180547516910449779)
        ·
          refine ⟨2398215270821275365674669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598810180547516910449779 2398215270821275365674669)
          ·
            refine ⟨899330726557978262128001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398215270821275365674669 899330726557978262128001)
            ·
              refine ⟨674498044918483696596001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899330726557978262128001 674498044918483696596001)
              ·
                refine ⟨505873533688862772447001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674498044918483696596001 505873533688862772447001)
                ·
                  refine ⟨379405150266647079335251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505873533688862772447001 379405150266647079335251)
                  ·
                    rfl

theorem cell20_831250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_831250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831250 prefixEnd_831250 := by exact prefixLift 831250
  have htrace : WordTrace (prefixWord ++ tailWord_831250) baseStart_831250 baseEnd_831250 := by
    simpa [prefixWord, tailWord_831250, baseEnd_831250] using wordTrace_append hprefix tailTrace_831250
  have hstable : (prefixWord ++ tailWord_831250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831250).length < 2 ^ (prefixWord ++ tailWord_831250).sum := by decide
  have hdescent : baseEnd_831250 < baseStart_831250 := by decide
  rcases family_descends (prefixWord ++ tailWord_831250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831265 : List Nat := [1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_831265 : Nat := 118140960795 + 831265 * 2 ^ 59
def prefixEnd_831265 : Nat := 4983230072969 + 3 ^ 40 * 831265 * 2
def baseEnd_831265 : Nat := 126470665558457897945063

theorem tailTrace_831265 : CollatzResearch.WordTrace tailWord_831265 prefixEnd_831265 126470665558457897945063 := by
  unfold tailWord_831265
  simp only [CollatzResearch.WordTrace]
  refine ⟨30318725333476348604399249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20212483555650899069599499 30318725333476348604399249)
  ·
    refine ⟨22739044000107261453299437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30318725333476348604399249 22739044000107261453299437)
    ·
      refine ⟨8527141500040223044987289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22739044000107261453299437 8527141500040223044987289)
      ·
        refine ⟨6395356125030167283740467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8527141500040223044987289 6395356125030167283740467)
        ·
          refine ⟨9593034187545250925610701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395356125030167283740467 9593034187545250925610701)
          ·
            refine ⟨3597387820329469097104013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9593034187545250925610701 3597387820329469097104013)
            ·
              refine ⟨1349020432623550911414005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3597387820329469097104013 1349020432623550911414005)
              ·
                refine ⟨126470665558457897945063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349020432623550911414005 126470665558457897945063)
                ·
                  rfl

theorem cell20_831265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_831265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831265 prefixEnd_831265 := by exact prefixLift 831265
  have htrace : WordTrace (prefixWord ++ tailWord_831265) baseStart_831265 baseEnd_831265 := by
    simpa [prefixWord, tailWord_831265, baseEnd_831265] using wordTrace_append hprefix tailTrace_831265
  have hstable : (prefixWord ++ tailWord_831265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831265).length < 2 ^ (prefixWord ++ tailWord_831265).sum := by decide
  have hdescent : baseEnd_831265 < baseStart_831265 := by decide
  rcases family_descends (prefixWord ++ tailWord_831265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831279 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_831279 : Nat := 118140960795 + 831279 * 2 ^ 59
def prefixEnd_831279 : Nat := 4983230072969 + 3 ^ 40 * 831279 * 2
def baseEnd_831279 : Nat := 379418386656851867368465

theorem tailTrace_831279 : CollatzResearch.WordTrace tailWord_831279 prefixEnd_831279 379418386656851867368465 := by
  unfold tailWord_831279
  simp only [CollatzResearch.WordTrace]
  refine ⟨30319235955425628995408891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20212823970283752663605927 30319235955425628995408891)
  ·
    refine ⟨45478853933138443493113337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30319235955425628995408891 45478853933138443493113337)
    ·
      refine ⟨34109140449853832619835003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45478853933138443493113337 34109140449853832619835003)
      ·
        refine ⟨51163710674780748929752505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34109140449853832619835003 51163710674780748929752505)
        ·
          refine ⟨38372783006085561697314379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51163710674780748929752505 38372783006085561697314379)
          ·
            refine ⟨57559174509128342545971569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38372783006085561697314379 57559174509128342545971569)
            ·
              refine ⟨43169380881846256909478677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57559174509128342545971569 43169380881846256909478677)
              ·
                refine ⟨2023564728836543292631813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43169380881846256909478677 2023564728836543292631813)
                ·
                  refine ⟨379418386656851867368465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023564728836543292631813 379418386656851867368465)
                  ·
                    rfl

theorem cell20_831279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_831279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831279 prefixEnd_831279 := by exact prefixLift 831279
  have htrace : WordTrace (prefixWord ++ tailWord_831279) baseStart_831279 baseEnd_831279 := by
    simpa [prefixWord, tailWord_831279, baseEnd_831279] using wordTrace_append hprefix tailTrace_831279
  have hstable : (prefixWord ++ tailWord_831279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831279).length < 2 ^ (prefixWord ++ tailWord_831279).sum := by decide
  have hdescent : baseEnd_831279 < baseStart_831279 := by decide
  rcases family_descends (prefixWord ++ tailWord_831279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831282 : List Nat := [3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_831282 : Nat := 118140960795 + 831282 * 2 ^ 59
def prefixEnd_831282 : Nat := 4983230072969 + 3 ^ 40 * 831282 * 2
def baseEnd_831282 : Nat := 126473251979532396756151

theorem tailTrace_831282 : CollatzResearch.WordTrace tailWord_831282 prefixEnd_831282 126473251979532396756151 := by
  unfold tailWord_831282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7579836343603690126942025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20212896916276507005178733 7579836343603690126942025)
  ·
    refine ⟨5684877257702767595206519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7579836343603690126942025 5684877257702767595206519)
    ·
      refine ⟨8527315886554151392809779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684877257702767595206519 8527315886554151392809779)
      ·
        refine ⟨12790973829831227089214669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527315886554151392809779 12790973829831227089214669)
        ·
          refine ⟨4796615186186710158455501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12790973829831227089214669 4796615186186710158455501)
          ·
            refine ⟨1798730694820016309420813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4796615186186710158455501 1798730694820016309420813)
            ·
              refine ⟨674524010557506116032805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1798730694820016309420813 674524010557506116032805)
              ·
                refine ⟨126473251979532396756151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674524010557506116032805 126473251979532396756151)
                ·
                  rfl

theorem cell20_831282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_831282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831282 prefixEnd_831282 := by exact prefixLift 831282
  have htrace : WordTrace (prefixWord ++ tailWord_831282) baseStart_831282 baseEnd_831282 := by
    simpa [prefixWord, tailWord_831282, baseEnd_831282] using wordTrace_append hprefix tailTrace_831282
  have hstable : (prefixWord ++ tailWord_831282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831282).length < 2 ^ (prefixWord ++ tailWord_831282).sum := by decide
  have hdescent : baseEnd_831282 < baseStart_831282 := by decide
  rcases family_descends (prefixWord ++ tailWord_831282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831302 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_831302 : Nat := 118140960795 + 831302 * 2 ^ 59
def prefixEnd_831302 : Nat := 4983230072969 + 3 ^ 40 * 831302 * 2
def baseEnd_831302 : Nat := 379428884483566009601705

theorem tailTrace_831302 : CollatzResearch.WordTrace tailWord_831302 prefixEnd_831302 379428884483566009601705 := by
  unfold tailWord_831302
  simp only [CollatzResearch.WordTrace]
  refine ⟨947502338573196997609255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20213383222894869282330773 947502338573196997609255)
  ·
    refine ⟨1421253507859795496413883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947502338573196997609255 1421253507859795496413883)
    ·
      refine ⟨2131880261789693244620825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421253507859795496413883 2131880261789693244620825)
      ·
        refine ⟨1598910196342269933465619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131880261789693244620825 1598910196342269933465619)
        ·
          refine ⟨2398365294513404900198429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598910196342269933465619 2398365294513404900198429)
          ·
            refine ⟨899386985442526837574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2398365294513404900198429 899386985442526837574411)
            ·
              refine ⟨1349080478163790256361617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899386985442526837574411 1349080478163790256361617)
              ·
                refine ⟨1011810358622842692271213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349080478163790256361617 1011810358622842692271213)
                ·
                  refine ⟨379428884483566009601705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011810358622842692271213 379428884483566009601705)
                  ·
                    rfl

theorem cell20_831302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_831302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831302 prefixEnd_831302 := by exact prefixLift 831302
  have htrace : WordTrace (prefixWord ++ tailWord_831302) baseStart_831302 baseEnd_831302 := by
    simpa [prefixWord, tailWord_831302, baseEnd_831302] using wordTrace_append hprefix tailTrace_831302
  have hstable : (prefixWord ++ tailWord_831302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831302).length < 2 ^ (prefixWord ++ tailWord_831302).sum := by decide
  have hdescent : baseEnd_831302 < baseStart_831302 := by decide
  rcases family_descends (prefixWord ++ tailWord_831302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831313 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 2]
def baseStart_831313 : Nat := 118140960795 + 831313 * 2 ^ 59
def prefixEnd_831313 : Nat := 4983230072969 + 3 ^ 40 * 831313 * 2
def baseEnd_831313 : Nat := 379433905183298860234993

theorem tailTrace_831313 : CollatzResearch.WordTrace tailWord_831313 prefixEnd_831313 379433905183298860234993 := by
  unfold tailWord_831313
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320476037302452802146593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20213650691534968534764395 30320476037302452802146593)
  ·
    refine ⟨22740357027976839601609945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30320476037302452802146593 22740357027976839601609945)
    ·
      refine ⟨17055267770982629701207459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22740357027976839601609945 17055267770982629701207459)
      ·
        refine ⟨25582901656473944551811189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17055267770982629701207459 25582901656473944551811189)
        ·
          refine ⟨2398397030294432301732299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25582901656473944551811189 2398397030294432301732299)
          ·
            refine ⟨3597595545441648452598449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398397030294432301732299 3597595545441648452598449)
            ·
              refine ⟨2698196659081236339448837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597595545441648452598449 2698196659081236339448837)
              ·
                refine ⟨505911873577731813646657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2698196659081236339448837 505911873577731813646657)
                ·
                  refine ⟨379433905183298860234993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505911873577731813646657 379433905183298860234993)
                  ·
                    rfl

theorem cell20_831313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_831313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831313 prefixEnd_831313 := by exact prefixLift 831313
  have htrace : WordTrace (prefixWord ++ tailWord_831313) baseStart_831313 baseEnd_831313 := by
    simpa [prefixWord, tailWord_831313, baseEnd_831313] using wordTrace_append hprefix tailTrace_831313
  have hstable : (prefixWord ++ tailWord_831313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831313).length < 2 ^ (prefixWord ++ tailWord_831313).sum := by decide
  have hdescent : baseEnd_831313 < baseStart_831313 := by decide
  rcases family_descends (prefixWord ++ tailWord_831313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831358 : List Nat := [4, 2, 3, 1, 1, 1, 8]
def baseStart_831358 : Nat := 118140960795 + 831358 * 2 ^ 59
def prefixEnd_831358 : Nat := 4983230072969 + 3 ^ 40 * 831358 * 2
def baseEnd_831358 : Nat := 42161604934386522637201

theorem tailTrace_831358 : CollatzResearch.WordTrace tailWord_831358 prefixEnd_831358 42161604934386522637201 := by
  unfold tailWord_831358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790264665267428185941841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20214744881426283658356485 3790264665267428185941841)
  ·
    refine ⟨2842698498950571139456381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3790264665267428185941841 2842698498950571139456381)
    ·
      refine ⟨1066011937106464177296143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2842698498950571139456381 1066011937106464177296143)
      ·
        refine ⟨1599017905659696265944215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066011937106464177296143 1599017905659696265944215)
        ·
          refine ⟨2398526858489544398916323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599017905659696265944215 2398526858489544398916323)
          ·
            refine ⟨3597790287734316598374485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398526858489544398916323 3597790287734316598374485)
            ·
              refine ⟨42161604934386522637201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3597790287734316598374485 42161604934386522637201)
              ·
                rfl

theorem cell20_831358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_831358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831358 prefixEnd_831358 := by exact prefixLift 831358
  have htrace : WordTrace (prefixWord ++ tailWord_831358) baseStart_831358 baseEnd_831358 := by
    simpa [prefixWord, tailWord_831358, baseEnd_831358] using wordTrace_append hprefix tailTrace_831358
  have hstable : (prefixWord ++ tailWord_831358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831358).length < 2 ^ (prefixWord ++ tailWord_831358).sum := by decide
  have hdescent : baseEnd_831358 < baseStart_831358 := by decide
  rcases family_descends (prefixWord ++ tailWord_831358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831368 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_831368 : Nat := 118140960795 + 831368 * 2 ^ 59
def prefixEnd_831368 : Nat := 4983230072969 + 3 ^ 40 * 831368 * 2
def baseEnd_831368 : Nat := 379459008681963113401435

theorem tailTrace_831368 : CollatzResearch.WordTrace tailWord_831368 prefixEnd_831368 379459008681963113401435 := by
  unfold tailWord_831368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161241026051598597699379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20214988034735464796932505 15161241026051598597699379)
  ·
    refine ⟨22741861539077397896549069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15161241026051598597699379 22741861539077397896549069)
    ·
      refine ⟨8528198077154024211205901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22741861539077397896549069 8528198077154024211205901)
      ·
        refine ⟨3198074278932759079202213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8528198077154024211205901 3198074278932759079202213)
        ·
          refine ⟨599638927299892327350415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3198074278932759079202213 599638927299892327350415)
          ·
            refine ⟨899458390949838491025623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599638927299892327350415 899458390949838491025623)
            ·
              refine ⟨1349187586424757736538435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899458390949838491025623 1349187586424757736538435)
              ·
                refine ⟨2023781379637136604807653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349187586424757736538435 2023781379637136604807653)
                ·
                  refine ⟨379459008681963113401435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023781379637136604807653 379459008681963113401435)
                  ·
                    rfl

theorem cell20_831368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_831368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831368 prefixEnd_831368 := by exact prefixLift 831368
  have htrace : WordTrace (prefixWord ++ tailWord_831368) baseStart_831368 baseEnd_831368 := by
    simpa [prefixWord, tailWord_831368, baseEnd_831368] using wordTrace_append hprefix tailTrace_831368
  have hstable : (prefixWord ++ tailWord_831368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831368).length < 2 ^ (prefixWord ++ tailWord_831368).sum := by decide
  have hdescent : baseEnd_831368 < baseStart_831368 := by decide
  rcases family_descends (prefixWord ++ tailWord_831368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831431 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_831431 : Nat := 118140960795 + 831431 * 2 ^ 59
def prefixEnd_831431 : Nat := 4983230072969 + 3 ^ 40 * 831431 * 2
def baseEnd_831431 : Nat := 379487763598614894301177

theorem tailTrace_831431 : CollatzResearch.WordTrace tailWord_831431 prefixEnd_831431 379487763598614894301177 := by
  unfold tailWord_831431
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324779850874958954942147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20216519900583305969961431 30324779850874958954942147)
  ·
    refine ⟨45487169776312438432413221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30324779850874958954942147 45487169776312438432413221)
    ·
      refine ⟨8528844333058582206077479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45487169776312438432413221 8528844333058582206077479)
      ·
        refine ⟨12793266499587873309116219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528844333058582206077479 12793266499587873309116219)
        ·
          refine ⟨19189899749381809963674329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12793266499587873309116219 19189899749381809963674329)
          ·
            refine ⟨14392424812036357472755747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19189899749381809963674329 14392424812036357472755747)
            ·
              refine ⟨21588637218054536209133621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14392424812036357472755747 21588637218054536209133621)
              ·
                refine ⟨2023934739192612769606277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21588637218054536209133621 2023934739192612769606277)
                ·
                  refine ⟨379487763598614894301177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023934739192612769606277 379487763598614894301177)
                  ·
                    rfl

theorem cell20_831431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_831431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831431 prefixEnd_831431 := by exact prefixLift 831431
  have htrace : WordTrace (prefixWord ++ tailWord_831431) baseStart_831431 baseEnd_831431 := by
    simpa [prefixWord, tailWord_831431, baseEnd_831431] using wordTrace_append hprefix tailTrace_831431
  have hstable : (prefixWord ++ tailWord_831431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831431).length < 2 ^ (prefixWord ++ tailWord_831431).sum := by decide
  have hdescent : baseEnd_831431 < baseStart_831431 := by decide
  rcases family_descends (prefixWord ++ tailWord_831431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831507 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_831507 : Nat := 118140960795 + 831507 * 2 ^ 59
def prefixEnd_831507 : Nat := 4983230072969 + 3 ^ 40 * 831507 * 2
def baseEnd_831507 : Nat := 379522452069496407767533

theorem tailTrace_831507 : CollatzResearch.WordTrace tailWord_831507 prefixEnd_831507 379522452069496407767533 := by
  unfold tailWord_831507
  simp only [CollatzResearch.WordTrace]
  refine ⟨30327551798599623934708775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20218367865733082623139183 30327551798599623934708775)
  ·
    refine ⟨45491327697899435902063163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30327551798599623934708775 45491327697899435902063163)
    ·
      refine ⟨68236991546849153853094745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45491327697899435902063163 68236991546849153853094745)
      ·
        refine ⟨51177743660136865389821059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68236991546849153853094745 51177743660136865389821059)
        ·
          refine ⟨76766615490205298084731589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51177743660136865389821059 76766615490205298084731589)
          ·
            refine ⟨14393740404413493390887173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76766615490205298084731589 14393740404413493390887173)
            ·
              refine ⟨2698826325827530010791345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14393740404413493390887173 2698826325827530010791345)
              ·
                refine ⟨2024119744370647508093509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698826325827530010791345 2024119744370647508093509)
                ·
                  refine ⟨379522452069496407767533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024119744370647508093509 379522452069496407767533)
                  ·
                    rfl

theorem cell20_831507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_831507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831507 prefixEnd_831507 := by exact prefixLift 831507
  have htrace : WordTrace (prefixWord ++ tailWord_831507) baseStart_831507 baseEnd_831507 := by
    simpa [prefixWord, tailWord_831507, baseEnd_831507] using wordTrace_append hprefix tailTrace_831507
  have hstable : (prefixWord ++ tailWord_831507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831507).length < 2 ^ (prefixWord ++ tailWord_831507).sum := by decide
  have hdescent : baseEnd_831507 < baseStart_831507 := by decide
  rcases family_descends (prefixWord ++ tailWord_831507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831527 : List Nat := [1, 1, 7, 1, 3, 1, 6]
def baseStart_831527 : Nat := 118140960795 + 831527 * 2 ^ 59
def prefixEnd_831527 : Nat := 4983230072969 + 3 ^ 40 * 831527 * 2
def baseEnd_831527 : Nat := 42170175623829469677865

theorem tailTrace_831527 : CollatzResearch.WordTrace tailWord_831527 prefixEnd_831527 42170175623829469677865 := by
  unfold tailWord_831527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30328281258527167350436835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20218854172351444900291223 30328281258527167350436835)
  ·
    refine ⟨45492421887790751025655253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30328281258527167350436835 45492421887790751025655253)
    ·
      refine ⟨1066228637995095727163795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45492421887790751025655253 1066228637995095727163795)
      ·
        refine ⟨1599342956992643590745693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066228637995095727163795 1599342956992643590745693)
        ·
          refine ⟨599753608872241346529635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1599342956992643590745693 599753608872241346529635)
          ·
            refine ⟨899630413308362019794453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599753608872241346529635 899630413308362019794453)
            ·
              refine ⟨42170175623829469677865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 899630413308362019794453 42170175623829469677865)
              ·
                rfl

theorem cell20_831527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 6].length) (baseStart_831527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831527 prefixEnd_831527 := by exact prefixLift 831527
  have htrace : WordTrace (prefixWord ++ tailWord_831527) baseStart_831527 baseEnd_831527 := by
    simpa [prefixWord, tailWord_831527, baseEnd_831527] using wordTrace_append hprefix tailTrace_831527
  have hstable : (prefixWord ++ tailWord_831527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831527).length < 2 ^ (prefixWord ++ tailWord_831527).sum := by decide
  have hdescent : baseEnd_831527 < baseStart_831527 := by decide
  rcases family_descends (prefixWord ++ tailWord_831527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831538 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_831538 : Nat := 118140960795 + 831538 * 2 ^ 59
def prefixEnd_831538 : Nat := 4983230072969 + 3 ^ 40 * 831538 * 2
def baseEnd_831538 : Nat := 379536601314198077734073

theorem tailTrace_831538 : CollatzResearch.WordTrace tailWord_831538 prefixEnd_831538 379536601314198077734073 := by
  unfold tailWord_831538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582170615371829057271817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20219121640991544152724845 7582170615371829057271817)
  ·
    refine ⟨5686627961528871792953863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7582170615371829057271817 5686627961528871792953863)
    ·
      refine ⟨8529941942293307689430795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686627961528871792953863 8529941942293307689430795)
      ·
        refine ⟨12794912913439961534146193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529941942293307689430795 12794912913439961534146193)
        ·
          refine ⟨9596184685079971150609645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12794912913439961534146193 9596184685079971150609645)
          ·
            refine ⟨3598569256904989181478617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9596184685079971150609645 3598569256904989181478617)
            ·
              refine ⟨2698926942678741886108963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3598569256904989181478617 2698926942678741886108963)
              ·
                refine ⟨4048390414018112829163445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698926942678741886108963 4048390414018112829163445)
                ·
                  refine ⟨379536601314198077734073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048390414018112829163445 379536601314198077734073)
                  ·
                    rfl

theorem cell20_831538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_831538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831538 prefixEnd_831538 := by exact prefixLift 831538
  have htrace : WordTrace (prefixWord ++ tailWord_831538) baseStart_831538 baseEnd_831538 := by
    simpa [prefixWord, tailWord_831538, baseEnd_831538] using wordTrace_append hprefix tailTrace_831538
  have hstable : (prefixWord ++ tailWord_831538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831538).length < 2 ^ (prefixWord ++ tailWord_831538).sum := by decide
  have hdescent : baseEnd_831538 < baseStart_831538 := by decide
  rcases family_descends (prefixWord ++ tailWord_831538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831552 : List Nat := [2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_831552 : Nat := 118140960795 + 831552 * 2 ^ 59
def prefixEnd_831552 : Nat := 4983230072969 + 3 ^ 40 * 831552 * 2
def baseEnd_831552 : Nat := 126514330431892083755783

theorem tailTrace_831552 : CollatzResearch.WordTrace tailWord_831552 prefixEnd_831552 126514330431892083755783 := by
  unfold tailWord_831552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164596541718298310048455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20219462055624397746731273 15164596541718298310048455)
  ·
    refine ⟨22746894812577447465072683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15164596541718298310048455 22746894812577447465072683)
    ·
      refine ⟨34120342218866171197609025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22746894812577447465072683 34120342218866171197609025)
      ·
        refine ⟨25590256664149628398206769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34120342218866171197609025 25590256664149628398206769)
        ·
          refine ⟨19192692498112221298655077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25590256664149628398206769 19192692498112221298655077)
          ·
            refine ⟨3598629843396041493497827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19192692498112221298655077 3598629843396041493497827)
            ·
              refine ⟨5397944765094062240246741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598629843396041493497827 5397944765094062240246741)
              ·
                refine ⟨126514330431892083755783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5397944765094062240246741 126514330431892083755783)
                ·
                  rfl

theorem cell20_831552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_831552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831552 prefixEnd_831552 := by exact prefixLift 831552
  have htrace : WordTrace (prefixWord ++ tailWord_831552) baseStart_831552 baseEnd_831552 := by
    simpa [prefixWord, tailWord_831552, baseEnd_831552] using wordTrace_append hprefix tailTrace_831552
  have hstable : (prefixWord ++ tailWord_831552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831552).length < 2 ^ (prefixWord ++ tailWord_831552).sum := by decide
  have hdescent : baseEnd_831552 < baseStart_831552 := by decide
  rcases family_descends (prefixWord ++ tailWord_831552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831586 : List Nat := [3, 3, 2, 2, 3, 7]
def baseStart_831586 : Nat := 118140960795 + 831586 * 2 ^ 59
def prefixEnd_831586 : Nat := 4983230072969 + 3 ^ 40 * 831586 * 2
def baseEnd_831586 : Nat := 14057722586004564597551

theorem tailTrace_831586 : CollatzResearch.WordTrace tailWord_831586 prefixEnd_831586 14057722586004564597551 := by
  unfold tailWord_831586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582608291328355106708653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20220288776875613617889741 7582608291328355106708653)
  ·
    refine ⟨2843478109248133165015745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7582608291328355106708653 2843478109248133165015745)
    ·
      refine ⟨2132608581936099873761809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843478109248133165015745 2132608581936099873761809)
      ·
        refine ⟨1599456436452074905321357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132608581936099873761809 1599456436452074905321357)
        ·
          refine ⟨599796163669528089495509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1599456436452074905321357 599796163669528089495509)
          ·
            refine ⟨14057722586004564597551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 599796163669528089495509 14057722586004564597551)
            ·
              rfl

theorem cell20_831586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 7].length) (baseStart_831586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831586 prefixEnd_831586 := by exact prefixLift 831586
  have htrace : WordTrace (prefixWord ++ tailWord_831586) baseStart_831586 baseEnd_831586 := by
    simpa [prefixWord, tailWord_831586, baseEnd_831586] using wordTrace_append hprefix tailTrace_831586
  have hstable : (prefixWord ++ tailWord_831586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831586).length < 2 ^ (prefixWord ++ tailWord_831586).sum := by decide
  have hdescent : baseEnd_831586 < baseStart_831586 := by decide
  rcases family_descends (prefixWord ++ tailWord_831586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831596 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_831596 : Nat := 118140960795 + 831596 * 2 ^ 59
def prefixEnd_831596 : Nat := 4983230072969 + 3 ^ 40 * 831596 * 2
def baseEnd_831596 : Nat := 379563074094607653800503

theorem tailTrace_831596 : CollatzResearch.WordTrace tailWord_831596 prefixEnd_831596 379563074094607653800503 := by
  unfold tailWord_831596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165398947638596067349321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20220531930184794756465761 15165398947638596067349321)
  ·
    refine ⟨11374049210728947050511991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15165398947638596067349321 11374049210728947050511991)
    ·
      refine ⟨17061073816093420575767987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11374049210728947050511991 17061073816093420575767987)
      ·
        refine ⟨25591610724140130863651981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17061073816093420575767987 25591610724140130863651981)
        ·
          refine ⟨9596854021552549073869493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25591610724140130863651981 9596854021552549073869493)
          ·
            refine ⟨899705064520551475675265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9596854021552549073869493 899705064520551475675265)
            ·
              refine ⟨674778798390413606756449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899705064520551475675265 674778798390413606756449)
              ·
                refine ⟨506084098792810205067337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674778798390413606756449 506084098792810205067337)
                ·
                  refine ⟨379563074094607653800503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506084098792810205067337 379563074094607653800503)
                  ·
                    rfl

theorem cell20_831596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_831596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831596 prefixEnd_831596 := by exact prefixLift 831596
  have htrace : WordTrace (prefixWord ++ tailWord_831596) baseStart_831596 baseEnd_831596 := by
    simpa [prefixWord, tailWord_831596, baseEnd_831596] using wordTrace_append hprefix tailTrace_831596
  have hstable : (prefixWord ++ tailWord_831596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831596).length < 2 ^ (prefixWord ++ tailWord_831596).sum := by decide
  have hdescent : baseEnd_831596 < baseStart_831596 := by decide
  rcases family_descends (prefixWord ++ tailWord_831596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831607 : List Nat := [1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_831607 : Nat := 118140960795 + 831607 * 2 ^ 59
def prefixEnd_831607 : Nat := 4983230072969 + 3 ^ 40 * 831607 * 2
def baseEnd_831607 : Nat := 126522698264780168144597

theorem tailTrace_831607 : CollatzResearch.WordTrace tailWord_831607 prefixEnd_831607 126522698264780168144597 := by
  unfold tailWord_831607
  simp only [CollatzResearch.WordTrace]
  refine ⟨30331199098237341013349075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20220799398824894008899383 30331199098237341013349075)
  ·
    refine ⟨45496798647356011520023613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30331199098237341013349075 45496798647356011520023613)
    ·
      refine ⟨17061299492758504320008855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45496798647356011520023613 17061299492758504320008855)
      ·
        refine ⟨25591949239137756480013283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17061299492758504320008855 25591949239137756480013283)
        ·
          refine ⟨38387923858706634720019925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25591949239137756480013283 38387923858706634720019925)
          ·
            refine ⟨899716965438436751250467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 38387923858706634720019925 899716965438436751250467)
            ·
              refine ⟨1349575448157655126875701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899716965438436751250467 1349575448157655126875701)
              ·
                refine ⟨126522698264780168144597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1349575448157655126875701 126522698264780168144597)
                ·
                  rfl

theorem cell20_831607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_831607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831607 prefixEnd_831607 := by exact prefixLift 831607
  have htrace : WordTrace (prefixWord ++ tailWord_831607) baseStart_831607 baseEnd_831607 := by
    simpa [prefixWord, tailWord_831607, baseEnd_831607] using wordTrace_append hprefix tailTrace_831607
  have hstable : (prefixWord ++ tailWord_831607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831607).length < 2 ^ (prefixWord ++ tailWord_831607).sum := by decide
  have hdescent : baseEnd_831607 < baseStart_831607 := by decide
  rcases family_descends (prefixWord ++ tailWord_831607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831621 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_831621 : Nat := 118140960795 + 831621 * 2 ^ 59
def prefixEnd_831621 : Nat := 4983230072969 + 3 ^ 40 * 831621 * 2
def baseEnd_831621 : Nat := 379574484775818677967067

theorem tailTrace_831621 : CollatzResearch.WordTrace tailWord_831621 prefixEnd_831621 379574484775818677967067 := by
  unfold tailWord_831621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30331709720186621404358717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20221139813457747602905811 30331709720186621404358717)
  ·
    refine ⟨11374391145069983026634519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30331709720186621404358717 11374391145069983026634519)
    ·
      refine ⟨17061586717604974539951779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11374391145069983026634519 17061586717604974539951779)
      ·
        refine ⟨25592380076407461809927669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17061586717604974539951779 25592380076407461809927669)
        ·
          refine ⟨2399285632163199544680719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25592380076407461809927669 2399285632163199544680719)
          ·
            refine ⟨3598928448244799317021079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399285632163199544680719 3598928448244799317021079)
            ·
              refine ⟨5398392672367198975531619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598928448244799317021079 5398392672367198975531619)
              ·
                refine ⟨8097589008550798463297429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398392672367198975531619 8097589008550798463297429)
                ·
                  refine ⟨379574484775818677967067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8097589008550798463297429 379574484775818677967067)
                  ·
                    rfl

theorem cell20_831621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_831621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831621 prefixEnd_831621 := by exact prefixLift 831621
  have htrace : WordTrace (prefixWord ++ tailWord_831621) baseStart_831621 baseEnd_831621 := by
    simpa [prefixWord, tailWord_831621, baseEnd_831621] using wordTrace_append hprefix tailTrace_831621
  have hstable : (prefixWord ++ tailWord_831621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831621).length < 2 ^ (prefixWord ++ tailWord_831621).sum := by decide
  have hdescent : baseEnd_831621 < baseStart_831621 := by decide
  rcases family_descends (prefixWord ++ tailWord_831621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831624 : List Nat := [2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_831624 : Nat := 118140960795 + 831624 * 2 ^ 59
def prefixEnd_831624 : Nat := 4983230072969 + 3 ^ 40 * 831624 * 2
def baseEnd_831624 : Nat := 126525284685854666955685

theorem tailTrace_831624 : CollatzResearch.WordTrace tailWord_831624 prefixEnd_831624 126525284685854666955685 := by
  unfold tailWord_831624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165909569587876458358963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20221212759450501944478617 15165909569587876458358963)
  ·
    refine ⟨22748864354381814687538445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15165909569587876458358963 22748864354381814687538445)
    ·
      refine ⟨8530824132893180507826917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22748864354381814687538445 8530824132893180507826917)
      ·
        refine ⟨1599529524917471345217547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8530824132893180507826917 1599529524917471345217547)
        ·
          refine ⟨2399294287376207017826321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599529524917471345217547 2399294287376207017826321)
          ·
            refine ⟨1799470715532155263369741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399294287376207017826321 1799470715532155263369741)
            ·
              refine ⟨674801518324558223763653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1799470715532155263369741 674801518324558223763653)
              ·
                refine ⟨126525284685854666955685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674801518324558223763653 126525284685854666955685)
                ·
                  rfl

theorem cell20_831624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_831624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831624 prefixEnd_831624 := by exact prefixLift 831624
  have htrace : WordTrace (prefixWord ++ tailWord_831624) baseStart_831624 baseEnd_831624 := by
    simpa [prefixWord, tailWord_831624, baseEnd_831624] using wordTrace_append hprefix tailTrace_831624
  have hstable : (prefixWord ++ tailWord_831624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831624).length < 2 ^ (prefixWord ++ tailWord_831624).sum := by decide
  have hdescent : baseEnd_831624 < baseStart_831624 := by decide
  rcases family_descends (prefixWord ++ tailWord_831624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831635 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_831635 : Nat := 118140960795 + 831635 * 2 ^ 59
def prefixEnd_831635 : Nat := 4983230072969 + 3 ^ 40 * 831635 * 2
def baseEnd_831635 : Nat := 379580874757296851500343

theorem tailTrace_831635 : CollatzResearch.WordTrace tailWord_831635 prefixEnd_831635 379580874757296851500343 := by
  unfold tailWord_831635
  simp only [CollatzResearch.WordTrace]
  refine ⟨30332220342135901795368359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20221480228090601196912239 30332220342135901795368359)
  ·
    refine ⟨45498330513203852693052539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30332220342135901795368359 45498330513203852693052539)
    ·
      refine ⟨68247495769805779039578809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45498330513203852693052539 68247495769805779039578809)
      ·
        refine ⟨51185621827354334279684107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68247495769805779039578809 51185621827354334279684107)
        ·
          refine ⟨76778432741031501419526161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51185621827354334279684107 76778432741031501419526161)
          ·
            refine ⟨57583824555773626064644621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76778432741031501419526161 57583824555773626064644621)
            ·
              refine ⟨21593934208415109774241733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57583824555773626064644621 21593934208415109774241733)
              ·
                refine ⟨4048862664077833082670325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21593934208415109774241733 4048862664077833082670325)
                ·
                  refine ⟨379580874757296851500343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4048862664077833082670325 379580874757296851500343)
                  ·
                    rfl

theorem cell20_831635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_831635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831635 prefixEnd_831635 := by exact prefixLift 831635
  have htrace : WordTrace (prefixWord ++ tailWord_831635) baseStart_831635 baseEnd_831635 := by
    simpa [prefixWord, tailWord_831635, baseEnd_831635] using wordTrace_append hprefix tailTrace_831635
  have hstable : (prefixWord ++ tailWord_831635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831635).length < 2 ^ (prefixWord ++ tailWord_831635).sum := by decide
  have hdescent : baseEnd_831635 < baseStart_831635 := by decide
  rcases family_descends (prefixWord ++ tailWord_831635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831655 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_831655 : Nat := 118140960795 + 831655 * 2 ^ 59
def prefixEnd_831655 : Nat := 4983230072969 + 3 ^ 40 * 831655 * 2
def baseEnd_831655 : Nat := 379590003302265670833595

theorem tailTrace_831655 : CollatzResearch.WordTrace tailWord_831655 prefixEnd_831655 379590003302265670833595 := by
  unfold tailWord_831655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30332949802063445211096419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20221966534708963474064279 30332949802063445211096419)
  ·
    refine ⟨45499424703095167816644629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30332949802063445211096419 45499424703095167816644629)
    ·
      refine ⟨2132785532957585991405217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45499424703095167816644629 2132785532957585991405217)
      ·
        refine ⟨1599589149718189493553913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132785532957585991405217 1599589149718189493553913)
        ·
          refine ⟨1199691862288642120165435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599589149718189493553913 1199691862288642120165435)
          ·
            refine ⟨1799537793432963180248153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199691862288642120165435 1799537793432963180248153)
            ·
              refine ⟨1349653345074722385186115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799537793432963180248153 1349653345074722385186115)
              ·
                refine ⟨2024480017612083577779173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349653345074722385186115 2024480017612083577779173)
                ·
                  refine ⟨379590003302265670833595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024480017612083577779173 379590003302265670833595)
                  ·
                    rfl

theorem cell20_831655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_831655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831655 prefixEnd_831655 := by exact prefixLift 831655
  have htrace : WordTrace (prefixWord ++ tailWord_831655) baseStart_831655 baseEnd_831655 := by
    simpa [prefixWord, tailWord_831655, baseEnd_831655] using wordTrace_append hprefix tailTrace_831655
  have hstable : (prefixWord ++ tailWord_831655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831655).length < 2 ^ (prefixWord ++ tailWord_831655).sum := by decide
  have hdescent : baseEnd_831655 < baseStart_831655 := by decide
  rcases family_descends (prefixWord ++ tailWord_831655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831666 : List Nat := [3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_831666 : Nat := 118140960795 + 831666 * 2 ^ 59
def prefixEnd_831666 : Nat := 4983230072969 + 3 ^ 40 * 831666 * 2
def baseEnd_831666 : Nat := 126531674667332840488961

theorem tailTrace_831666 : CollatzResearch.WordTrace tailWord_831666 prefixEnd_831666 126531674667332840488961 := by
  unfold tailWord_831666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583337751255898522436713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20222234003349062726497901 7583337751255898522436713)
  ·
    refine ⟨5687503313441923891827535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7583337751255898522436713 5687503313441923891827535)
    ·
      refine ⟨8531254970162885837741303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687503313441923891827535 8531254970162885837741303)
      ·
        refine ⟨12796882455244328756611955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531254970162885837741303 12796882455244328756611955)
        ·
          refine ⟨19195323682866493134917933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12796882455244328756611955 19195323682866493134917933)
          ·
            refine ⟨7198246381074934925594225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19195323682866493134917933 7198246381074934925594225)
            ·
              refine ⟨5398684785806201194195669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198246381074934925594225 5398684785806201194195669)
              ·
                refine ⟨126531674667332840488961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5398684785806201194195669 126531674667332840488961)
                ·
                  rfl

theorem cell20_831666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_831666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831666 prefixEnd_831666 := by exact prefixLift 831666
  have htrace : WordTrace (prefixWord ++ tailWord_831666) baseStart_831666 baseEnd_831666 := by
    simpa [prefixWord, tailWord_831666, baseEnd_831666] using wordTrace_append hprefix tailTrace_831666
  have hstable : (prefixWord ++ tailWord_831666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831666).length < 2 ^ (prefixWord ++ tailWord_831666).sum := by decide
  have hdescent : baseEnd_831666 < baseStart_831666 := by decide
  rcases family_descends (prefixWord ++ tailWord_831666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831704 : List Nat := [2, 1, 2, 2, 4, 1, 8]
def baseStart_831704 : Nat := 118140960795 + 831704 * 2 ^ 59
def prefixEnd_831704 : Nat := 4983230072969 + 3 ^ 40 * 831704 * 2
def baseEnd_831704 : Nat := 42179152026382142022229

theorem tailTrace_831704 : CollatzResearch.WordTrace tailWord_831704 prefixEnd_831704 42179152026382142022229 := by
  unfold tailWord_831704
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167368489442963289815083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20223157985923951053086777 15167368489442963289815083)
  ·
    refine ⟨22751052734164444934722625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15167368489442963289815083 22751052734164444934722625)
    ·
      refine ⟨17063289550623333701041969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22751052734164444934722625 17063289550623333701041969)
      ·
        refine ⟨12797467162967500275781477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17063289550623333701041969 12797467162967500275781477)
        ·
          refine ⟨2399525093056406301709027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12797467162967500275781477 2399525093056406301709027)
          ·
            refine ⟨3599287639584609452563541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399525093056406301709027 3599287639584609452563541)
            ·
              refine ⟨42179152026382142022229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3599287639584609452563541 42179152026382142022229)
              ·
                rfl

theorem cell20_831704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_831704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831704 prefixEnd_831704 := by exact prefixLift 831704
  have htrace : WordTrace (prefixWord ++ tailWord_831704) baseStart_831704 baseEnd_831704 := by
    simpa [prefixWord, tailWord_831704, baseEnd_831704] using wordTrace_append hprefix tailTrace_831704
  have hstable : (prefixWord ++ tailWord_831704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831704).length < 2 ^ (prefixWord ++ tailWord_831704).sum := by decide
  have hdescent : baseEnd_831704 < baseStart_831704 := by decide
  rcases family_descends (prefixWord ++ tailWord_831704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831749 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_831749 : Nat := 118140960795 + 831749 * 2 ^ 59
def prefixEnd_831749 : Nat := 4983230072969 + 3 ^ 40 * 831749 * 2
def baseEnd_831749 : Nat := 379632907463619121699877

theorem tailTrace_831749 : CollatzResearch.WordTrace tailWord_831749 prefixEnd_831749 379632907463619121699877 := by
  unfold tailWord_831749
  simp only [CollatzResearch.WordTrace]
  refine ⟨30336378263722899265018301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20224252175815266176678867 30336378263722899265018301)
  ·
    refine ⟨11376141848896087224381863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30336378263722899265018301 11376141848896087224381863)
    ·
      refine ⟨17064212773344130836572795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11376141848896087224381863 17064212773344130836572795)
      ·
        refine ⟨25596319160016196254859193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17064212773344130836572795 25596319160016196254859193)
        ·
          refine ⟨19197239370012147191144395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25596319160016196254859193 19197239370012147191144395)
          ·
            refine ⟨28795859055018220786716593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19197239370012147191144395 28795859055018220786716593)
            ·
              refine ⟨21596894291263665590037445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28795859055018220786716593 21596894291263665590037445)
              ·
                refine ⟨4049417679611937298132021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21596894291263665590037445 4049417679611937298132021)
                ·
                  refine ⟨379632907463619121699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4049417679611937298132021 379632907463619121699877)
                  ·
                    rfl

theorem cell20_831749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_831749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831749 prefixEnd_831749 := by exact prefixLift 831749
  have htrace : WordTrace (prefixWord ++ tailWord_831749) baseStart_831749 baseEnd_831749 := by
    simpa [prefixWord, tailWord_831749, baseEnd_831749] using wordTrace_append hprefix tailTrace_831749
  have hstable : (prefixWord ++ tailWord_831749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831749).length < 2 ^ (prefixWord ++ tailWord_831749).sum := by decide
  have hdescent : baseEnd_831749 < baseStart_831749 := by decide
  rcases family_descends (prefixWord ++ tailWord_831749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831797 : List Nat := [1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_831797 : Nat := 118140960795 + 831797 * 2 ^ 59
def prefixEnd_831797 : Nat := 4983230072969 + 3 ^ 40 * 831797 * 2
def baseEnd_831797 : Nat := 126551605323848096033227

theorem tailTrace_831797 : CollatzResearch.WordTrace tailWord_831797 prefixEnd_831797 126551605323848096033227 := by
  unfold tailWord_831797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30338128967549003462765645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20225419311699335641843763 30338128967549003462765645)
  ·
    refine ⟨11376798362830876298537117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30338128967549003462765645 11376798362830876298537117)
    ·
      refine ⟨4266299386061578611951419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11376798362830876298537117 4266299386061578611951419)
      ·
        refine ⟨6399449079092367917927129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266299386061578611951419 6399449079092367917927129)
        ·
          refine ⟨4799586809319275938445347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6399449079092367917927129 4799586809319275938445347)
          ·
            refine ⟨7199380213978913907668021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799586809319275938445347 7199380213978913907668021)
            ·
              refine ⟨674941895060523178843877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7199380213978913907668021 674941895060523178843877)
              ·
                refine ⟨126551605323848096033227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674941895060523178843877 126551605323848096033227)
                ·
                  rfl

theorem cell20_831797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_831797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831797 prefixEnd_831797 := by exact prefixLift 831797
  have htrace : WordTrace (prefixWord ++ tailWord_831797) baseStart_831797 baseEnd_831797 := by
    simpa [prefixWord, tailWord_831797, baseEnd_831797] using wordTrace_append hprefix tailTrace_831797
  have hstable : (prefixWord ++ tailWord_831797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831797).length < 2 ^ (prefixWord ++ tailWord_831797).sum := by decide
  have hdescent : baseEnd_831797 < baseStart_831797 := by decide
  rcases family_descends (prefixWord ++ tailWord_831797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831828 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_831828 : Nat := 118140960795 + 831828 * 2 ^ 59
def prefixEnd_831828 : Nat := 4983230072969 + 3 ^ 40 * 831828 * 2
def baseEnd_831828 : Nat := 379668965216245958066221

theorem tailTrace_831828 : CollatzResearch.WordTrace tailWord_831828 prefixEnd_831828 379668965216245958066221 := by
  unfold tailWord_831828
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169629815218347878572069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20226173086957797171429425 15169629815218347878572069)
  ·
    refine ⟨2844305590353440227232263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15169629815218347878572069 2844305590353440227232263)
    ·
      refine ⟨4266458385530160340848395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844305590353440227232263 4266458385530160340848395)
      ·
        refine ⟨6399687578295240511272593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266458385530160340848395 6399687578295240511272593)
        ·
          refine ⟨4799765683721430383454445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6399687578295240511272593 4799765683721430383454445)
          ·
            refine ⟨1799912131395536393795417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4799765683721430383454445 1799912131395536393795417)
            ·
              refine ⟨1349934098546652295346563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799912131395536393795417 1349934098546652295346563)
              ·
                refine ⟨2024901147819978443019845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349934098546652295346563 2024901147819978443019845)
                ·
                  refine ⟨379668965216245958066221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2024901147819978443019845 379668965216245958066221)
                  ·
                    rfl

theorem cell20_831828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_831828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831828 prefixEnd_831828 := by exact prefixLift 831828
  have htrace : WordTrace (prefixWord ++ tailWord_831828) baseStart_831828 baseEnd_831828 := by
    simpa [prefixWord, tailWord_831828, baseEnd_831828] using wordTrace_append hprefix tailTrace_831828
  have hstable : (prefixWord ++ tailWord_831828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831828).length < 2 ^ (prefixWord ++ tailWord_831828).sum := by decide
  have hdescent : baseEnd_831828 < baseStart_831828 := by decide
  rcases family_descends (prefixWord ++ tailWord_831828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831852 : List Nat := [2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_831852 : Nat := 118140960795 + 831852 * 2 ^ 59
def prefixEnd_831852 : Nat := 4983230072969 + 3 ^ 40 * 831852 * 2
def baseEnd_831852 : Nat := 126559973156736180422041

theorem tailTrace_831852 : CollatzResearch.WordTrace tailWord_831852 prefixEnd_831852 126559973156736180422041 := by
  unfold tailWord_831852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170067491174873928008905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20226756654899831904011873 15170067491174873928008905)
  ·
    refine ⟨11377550618381155446006679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15170067491174873928008905 11377550618381155446006679)
    ·
      refine ⟨17066325927571733169010019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11377550618381155446006679 17066325927571733169010019)
      ·
        refine ⟨25599488891357599753515029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17066325927571733169010019 25599488891357599753515029)
        ·
          refine ⟨1199976041782387488446017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25599488891357599753515029 1199976041782387488446017)
          ·
            refine ⟨899982031336790616334513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199976041782387488446017 899982031336790616334513)
            ·
              refine ⟨674986523502592962250885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899982031336790616334513 674986523502592962250885)
              ·
                refine ⟨126559973156736180422041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674986523502592962250885 126559973156736180422041)
                ·
                  rfl

theorem cell20_831852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_831852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831852 prefixEnd_831852 := by exact prefixLift 831852
  have htrace : WordTrace (prefixWord ++ tailWord_831852) baseStart_831852 baseEnd_831852 := by
    simpa [prefixWord, tailWord_831852, baseEnd_831852] using wordTrace_append hprefix tailTrace_831852
  have hstable : (prefixWord ++ tailWord_831852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831852).length < 2 ^ (prefixWord ++ tailWord_831852).sum := by decide
  have hdescent : baseEnd_831852 < baseStart_831852 := by decide
  rcases family_descends (prefixWord ++ tailWord_831852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831856 : List Nat := [2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_831856 : Nat := 118140960795 + 831856 * 2 ^ 59
def prefixEnd_831856 : Nat := 4983230072969 + 3 ^ 40 * 831856 * 2
def baseEnd_831856 : Nat := 126560581726400768377591

theorem tailTrace_831856 : CollatzResearch.WordTrace tailWord_831856 prefixEnd_831856 126560581726400768377591 := by
  unfold tailWord_831856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170140437167628269581711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20226853916223504359442281 15170140437167628269581711)
  ·
    refine ⟨22755210655751442404372567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15170140437167628269581711 22755210655751442404372567)
    ·
      refine ⟨34132815983627163606558851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755210655751442404372567 34132815983627163606558851)
      ·
        refine ⟨51199223975440745409838277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34132815983627163606558851 51199223975440745409838277)
        ·
          refine ⟨9599854495395139764344677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51199223975440745409838277 9599854495395139764344677)
          ·
            refine ⟨1799972717886588705814627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9599854495395139764344677 1799972717886588705814627)
            ·
              refine ⟨2699959076829883058721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799972717886588705814627 2699959076829883058721941)
              ·
                refine ⟨126560581726400768377591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2699959076829883058721941 126560581726400768377591)
                ·
                  rfl

theorem cell20_831856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_831856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831856 prefixEnd_831856 := by exact prefixLift 831856
  have htrace : WordTrace (prefixWord ++ tailWord_831856) baseStart_831856 baseEnd_831856 := by
    simpa [prefixWord, tailWord_831856, baseEnd_831856] using wordTrace_append hprefix tailTrace_831856
  have hstable : (prefixWord ++ tailWord_831856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831856).length < 2 ^ (prefixWord ++ tailWord_831856).sum := by decide
  have hdescent : baseEnd_831856 < baseStart_831856 := by decide
  rcases family_descends (prefixWord ++ tailWord_831856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831873 : List Nat := [1, 2, 4, 3, 1, 3, 6]
def baseStart_831873 : Nat := 118140960795 + 831873 * 2 ^ 59
def prefixEnd_831873 : Nat := 4983230072969 + 3 ^ 40 * 831873 * 2
def baseEnd_831873 : Nat := 42187722715825089062893

theorem tailTrace_831873 : CollatzResearch.WordTrace tailWord_831873 prefixEnd_831873 42187722715825089062893 := by
  unfold tailWord_831873
  simp only [CollatzResearch.WordTrace]
  refine ⟨30340900915273668442532273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20227267276849112295021515 30340900915273668442532273)
  ·
    refine ⟨22755675686455251331899205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30340900915273668442532273 22755675686455251331899205)
    ·
      refine ⟨4266689191210359624731101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22755675686455251331899205 4266689191210359624731101)
      ·
        refine ⟨1600008446703884859274163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4266689191210359624731101 1600008446703884859274163)
        ·
          refine ⟨2400012670055827288911245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600008446703884859274163 2400012670055827288911245)
          ·
            refine ⟨900004751270935233341717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2400012670055827288911245 900004751270935233341717)
            ·
              refine ⟨42187722715825089062893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 900004751270935233341717 42187722715825089062893)
              ·
                rfl

theorem cell20_831873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_831873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831873 prefixEnd_831873 := by exact prefixLift 831873
  have htrace : WordTrace (prefixWord ++ tailWord_831873) baseStart_831873 baseEnd_831873 := by
    simpa [prefixWord, tailWord_831873, baseEnd_831873] using wordTrace_append hprefix tailTrace_831873
  have hstable : (prefixWord ++ tailWord_831873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831873).length < 2 ^ (prefixWord ++ tailWord_831873).sum := by decide
  have hdescent : baseEnd_831873 < baseStart_831873 := by decide
  rcases family_descends (prefixWord ++ tailWord_831873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831880 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_831880 : Nat := 118140960795 + 831880 * 2 ^ 59
def prefixEnd_831880 : Nat := 4983230072969 + 3 ^ 40 * 831880 * 2
def baseEnd_831880 : Nat := 379692699433164888332675

theorem tailTrace_831880 : CollatzResearch.WordTrace tailWord_831880 prefixEnd_831880 379692699433164888332675 := by
  unfold tailWord_831880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170578113124154319018547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20227437484165539092024729 15170578113124154319018547)
  ·
    refine ⟨22755867169686231478527821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15170578113124154319018547 22755867169686231478527821)
    ·
      refine ⟨8533450188632336804447933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22755867169686231478527821 8533450188632336804447933)
      ·
        refine ⟨3200043820737126301667975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8533450188632336804447933 3200043820737126301667975)
        ·
          refine ⟨4800065731105689452501963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200043820737126301667975 4800065731105689452501963)
          ·
            refine ⟨7200098596658534178752945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800065731105689452501963 7200098596658534178752945)
            ·
              refine ⟨5400073947493900634064709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200098596658534178752945 5400073947493900634064709)
              ·
                refine ⟨1012513865155106368887133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5400073947493900634064709 1012513865155106368887133)
                ·
                  refine ⟨379692699433164888332675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012513865155106368887133 379692699433164888332675)
                  ·
                    rfl

theorem cell20_831880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_831880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831880 prefixEnd_831880 := by exact prefixLift 831880
  have htrace : WordTrace (prefixWord ++ tailWord_831880) baseStart_831880 baseEnd_831880 := by
    simpa [prefixWord, tailWord_831880, baseEnd_831880] using wordTrace_append hprefix tailTrace_831880
  have hstable : (prefixWord ++ tailWord_831880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831880).length < 2 ^ (prefixWord ++ tailWord_831880).sum := by decide
  have hdescent : baseEnd_831880 < baseStart_831880 := by decide
  rcases family_descends (prefixWord ++ tailWord_831880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831883 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 2]
def baseStart_831883 : Nat := 118140960795 + 831883 * 2 ^ 59
def prefixEnd_831883 : Nat := 4983230072969 + 3 ^ 40 * 831883 * 2
def baseEnd_831883 : Nat := 379694068714910211232663

theorem tailTrace_831883 : CollatzResearch.WordTrace tailWord_831883 prefixEnd_831883 379694068714910211232663 := by
  unfold tailWord_831883
  simp only [CollatzResearch.WordTrace]
  refine ⟨30341265645237440150396303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20227510430158293433597535 30341265645237440150396303)
  ·
    refine ⟨45511898467856160225594455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30341265645237440150396303 45511898467856160225594455)
    ·
      refine ⟨68267847701784240338391683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45511898467856160225594455 68267847701784240338391683)
      ·
        refine ⟨102401771552676360507587525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68267847701784240338391683 102401771552676360507587525)
        ·
          refine ⟨19200332166126817595172661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102401771552676360507587525 19200332166126817595172661)
          ·
            refine ⟨1800031140574389149547437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19200332166126817595172661 1800031140574389149547437)
            ·
              refine ⟨675011677715395931080289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1800031140574389149547437 675011677715395931080289)
              ·
                refine ⟨506258758286546948310217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675011677715395931080289 506258758286546948310217)
                ·
                  refine ⟨379694068714910211232663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506258758286546948310217 379694068714910211232663)
                  ·
                    rfl

theorem cell20_831883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2].length) (baseStart_831883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831883 prefixEnd_831883 := by exact prefixLift 831883
  have htrace : WordTrace (prefixWord ++ tailWord_831883) baseStart_831883 baseEnd_831883 := by
    simpa [prefixWord, tailWord_831883, baseEnd_831883] using wordTrace_append hprefix tailTrace_831883
  have hstable : (prefixWord ++ tailWord_831883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831883).length < 2 ^ (prefixWord ++ tailWord_831883).sum := by decide
  have hdescent : baseEnd_831883 < baseStart_831883 := by decide
  rcases family_descends (prefixWord ++ tailWord_831883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831932 : List Nat := [2, 2, 2, 4, 1, 9]
def baseStart_831932 : Nat := 118140960795 + 831932 * 2 ^ 59
def prefixEnd_831932 : Nat := 4983230072969 + 3 ^ 40 * 831932 * 2
def baseEnd_831932 : Nat := 14063571616669771059227

theorem tailTrace_831932 : CollatzResearch.WordTrace tailWord_831932 prefixEnd_831932 14063571616669771059227 := by
  unfold tailWord_831932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171526411029960759465025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20228701881373281012620033 15171526411029960759465025)
  ·
    refine ⟨11378644808272470569598769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15171526411029960759465025 11378644808272470569598769)
    ·
      refine ⟨8533983606204352927199077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11378644808272470569598769 8533983606204352927199077)
      ·
        refine ⟨1600121926163316173849827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8533983606204352927199077 1600121926163316173849827)
        ·
          refine ⟨2400182889244974260774741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600121926163316173849827 2400182889244974260774741)
          ·
            refine ⟨14063571616669771059227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2400182889244974260774741 14063571616669771059227)
            ·
              rfl

theorem cell20_831932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 9].length) (baseStart_831932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831932 prefixEnd_831932 := by exact prefixLift 831932
  have htrace : WordTrace (prefixWord ++ tailWord_831932) baseStart_831932 baseEnd_831932 := by
    simpa [prefixWord, tailWord_831932, baseEnd_831932] using wordTrace_append hprefix tailTrace_831932
  have hstable : (prefixWord ++ tailWord_831932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831932).length < 2 ^ (prefixWord ++ tailWord_831932).sum := by decide
  have hdescent : baseEnd_831932 < baseStart_831932 := by decide
  rcases family_descends (prefixWord ++ tailWord_831932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831980 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_831980 : Nat := 118140960795 + 831980 * 2 ^ 59
def prefixEnd_831980 : Nat := 4983230072969 + 3 ^ 40 * 831980 * 2
def baseEnd_831980 : Nat := 379738342158008984998933

theorem tailTrace_831980 : CollatzResearch.WordTrace tailWord_831980 prefixEnd_831980 379738342158008984998933 := by
  unfold tailWord_831980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172401762943012858338697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20229869017257350477784929 15172401762943012858338697)
  ·
    refine ⟨11379301322207259643754023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15172401762943012858338697 11379301322207259643754023)
    ·
      refine ⟨17068951983310889465631035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11379301322207259643754023 17068951983310889465631035)
      ·
        refine ⟨25603427974966334198446553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17068951983310889465631035 25603427974966334198446553)
        ·
          refine ⟨19202570981224750648834915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25603427974966334198446553 19202570981224750648834915)
          ·
            refine ⟨28803856471837125973252373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19202570981224750648834915 28803856471837125973252373)
            ·
              refine ⟨1350180772117365279996205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28803856471837125973252373 1350180772117365279996205)
              ·
                refine ⟨506317789544011979998577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350180772117365279996205 506317789544011979998577)
                ·
                  refine ⟨379738342158008984998933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506317789544011979998577 379738342158008984998933)
                  ·
                    rfl

theorem cell20_831980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_831980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831980 prefixEnd_831980 := by exact prefixLift 831980
  have htrace : WordTrace (prefixWord ++ tailWord_831980) baseStart_831980 baseEnd_831980 := by
    simpa [prefixWord, tailWord_831980, baseEnd_831980] using wordTrace_append hprefix tailTrace_831980
  have hstable : (prefixWord ++ tailWord_831980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831980).length < 2 ^ (prefixWord ++ tailWord_831980).sum := by decide
  have hdescent : baseEnd_831980 < baseStart_831980 := by decide
  rcases family_descends (prefixWord ++ tailWord_831980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831984 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_831984 : Nat := 118140960795 + 831984 * 2 ^ 59
def prefixEnd_831984 : Nat := 4983230072969 + 3 ^ 40 * 831984 * 2
def baseEnd_831984 : Nat := 379740167867002748865583

theorem tailTrace_831984 : CollatzResearch.WordTrace tailWord_831984 prefixEnd_831984 379740167867002748865583 := by
  unfold tailWord_831984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172474708935767199911503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20229966278581022933215337 15172474708935767199911503)
  ·
    refine ⟨22758712063403650799867255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15172474708935767199911503 22758712063403650799867255)
    ·
      refine ⟨34138068095105476199800883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22758712063403650799867255 34138068095105476199800883)
      ·
        refine ⟨51207102142658214299701325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34138068095105476199800883 51207102142658214299701325)
        ·
          refine ⟨19202663303496830362387997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51207102142658214299701325 19202663303496830362387997)
          ·
            refine ⟨7200998738811311385895499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19202663303496830362387997 7200998738811311385895499)
            ·
              refine ⟨10801498108216967078843249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200998738811311385895499 10801498108216967078843249)
              ·
                refine ⟨8101123581162725309132437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10801498108216967078843249 8101123581162725309132437)
                ·
                  refine ⟨379740167867002748865583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8101123581162725309132437 379740167867002748865583)
                  ·
                    rfl

theorem cell20_831984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_831984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_831984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_831984 prefixEnd_831984 := by exact prefixLift 831984
  have htrace : WordTrace (prefixWord ++ tailWord_831984) baseStart_831984 baseEnd_831984 := by
    simpa [prefixWord, tailWord_831984, baseEnd_831984] using wordTrace_append hprefix tailTrace_831984
  have hstable : (prefixWord ++ tailWord_831984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831984).length < 2 ^ (prefixWord ++ tailWord_831984).sum := by decide
  have hdescent : baseEnd_831984 < baseStart_831984 := by decide
  rcases family_descends (prefixWord ++ tailWord_831984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832001 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_832001 : Nat := 118140960795 + 832001 * 2 ^ 59
def prefixEnd_832001 : Nat := 4983230072969 + 3 ^ 40 * 832001 * 2
def baseEnd_832001 : Nat := 379747927130226245298847

theorem tailTrace_832001 : CollatzResearch.WordTrace tailWord_832001 prefixEnd_832001 379747927130226245298847 := by
  unfold tailWord_832001
  simp only [CollatzResearch.WordTrace]
  refine ⟨30345569458809946303191857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20230379639206630868794571 30345569458809946303191857)
  ·
    refine ⟨22759177094107459727393893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30345569458809946303191857 22759177094107459727393893)
    ·
      refine ⟨4267345705145148698886355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22759177094107459727393893 4267345705145148698886355)
      ·
        refine ⟨6401018557717723048329533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267345705145148698886355 6401018557717723048329533)
        ·
          refine ⟨2400381959144146143123575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6401018557717723048329533 2400381959144146143123575)
          ·
            refine ⟨3600572938716219214685363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400381959144146143123575 3600572938716219214685363)
            ·
              refine ⟨5400859408074328822028045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600572938716219214685363 5400859408074328822028045)
              ·
                refine ⟨2025322278027873308260517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5400859408074328822028045 2025322278027873308260517)
                ·
                  refine ⟨379747927130226245298847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025322278027873308260517 379747927130226245298847)
                  ·
                    rfl

theorem cell20_832001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_832001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832001 prefixEnd_832001 := by exact prefixLift 832001
  have htrace : WordTrace (prefixWord ++ tailWord_832001) baseStart_832001 baseEnd_832001 := by
    simpa [prefixWord, tailWord_832001, baseEnd_832001] using wordTrace_append hprefix tailTrace_832001
  have hstable : (prefixWord ++ tailWord_832001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832001).length < 2 ^ (prefixWord ++ tailWord_832001).sum := by decide
  have hdescent : baseEnd_832001 < baseStart_832001 := by decide
  rcases family_descends (prefixWord ++ tailWord_832001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832011 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 3]
def baseStart_832011 : Nat := 118140960795 + 832011 * 2 ^ 59
def prefixEnd_832011 : Nat := 4983230072969 + 3 ^ 40 * 832011 * 2
def baseEnd_832011 : Nat := 379752491402710654965473

theorem tailTrace_832011 : CollatzResearch.WordTrace tailWord_832011 prefixEnd_832011 379752491402710654965473 := by
  unfold tailWord_832011
  simp only [CollatzResearch.WordTrace]
  refine ⟨30345934188773718011055887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20230622792515812007370591 30345934188773718011055887)
  ·
    refine ⟨45518901283160577016583831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30345934188773718011055887 45518901283160577016583831)
    ·
      refine ⟨68278351924740865524875747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45518901283160577016583831 68278351924740865524875747)
      ·
        refine ⟨102417527887111298287313621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68278351924740865524875747 102417527887111298287313621)
        ·
          refine ⟨2400410809854171053608913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 102417527887111298287313621 2400410809854171053608913)
          ·
            refine ⟨1800308107390628290206685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400410809854171053608913 1800308107390628290206685)
            ·
              refine ⟨675115540271485608827507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1800308107390628290206685 675115540271485608827507)
              ·
                refine ⟨1012673310407228413241261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675115540271485608827507 1012673310407228413241261)
                ·
                  refine ⟨379752491402710654965473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012673310407228413241261 379752491402710654965473)
                  ·
                    rfl

theorem cell20_832011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_832011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832011 prefixEnd_832011 := by exact prefixLift 832011
  have htrace : WordTrace (prefixWord ++ tailWord_832011) baseStart_832011 baseEnd_832011 := by
    simpa [prefixWord, tailWord_832011, baseEnd_832011] using wordTrace_append hprefix tailTrace_832011
  have hstable : (prefixWord ++ tailWord_832011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832011).length < 2 ^ (prefixWord ++ tailWord_832011).sum := by decide
  have hdescent : baseEnd_832011 < baseStart_832011 := by decide
  rcases family_descends (prefixWord ++ tailWord_832011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832035 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 2]
def baseStart_832035 : Nat := 118140960795 + 832035 * 2 ^ 59
def prefixEnd_832035 : Nat := 4983230072969 + 3 ^ 40 * 832035 * 2
def baseEnd_832035 : Nat := 379763445656673238165375

theorem tailTrace_832035 : CollatzResearch.WordTrace tailWord_832035 prefixEnd_832035 379763445656673238165375 := by
  unfold tailWord_832035
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346809540686770109929559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20231206360457846739953039 30346809540686770109929559)
  ·
    refine ⟨45520214311030155164894339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30346809540686770109929559 45520214311030155164894339)
    ·
      refine ⟨68280321466545232747341509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45520214311030155164894339 68280321466545232747341509)
      ·
        refine ⟨12802560274977231140126533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68280321466545232747341509 12802560274977231140126533)
        ·
          refine ⟨2400480051558230838773725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12802560274977231140126533 2400480051558230838773725)
          ·
            refine ⟨900180019334336564540147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2400480051558230838773725 900180019334336564540147)
            ·
              refine ⟨1350270029001504846810221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900180019334336564540147 1350270029001504846810221)
              ·
                refine ⟨506351260875564317553833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350270029001504846810221 506351260875564317553833)
                ·
                  refine ⟨379763445656673238165375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506351260875564317553833 379763445656673238165375)
                  ·
                    rfl

theorem cell20_832035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2].length) (baseStart_832035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832035 prefixEnd_832035 := by exact prefixLift 832035
  have htrace : WordTrace (prefixWord ++ tailWord_832035) baseStart_832035 baseEnd_832035 := by
    simpa [prefixWord, tailWord_832035, baseEnd_832035] using wordTrace_append hprefix tailTrace_832035
  have hstable : (prefixWord ++ tailWord_832035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832035).length < 2 ^ (prefixWord ++ tailWord_832035).sum := by decide
  have hdescent : baseEnd_832035 < baseStart_832035 := by decide
  rcases family_descends (prefixWord ++ tailWord_832035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832052 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_832052 : Nat := 118140960795 + 832052 * 2 ^ 59
def prefixEnd_832052 : Nat := 4983230072969 + 3 ^ 40 * 832052 * 2
def baseEnd_832052 : Nat := 379771204919896734598639

theorem tailTrace_832052 : CollatzResearch.WordTrace tailWord_832052 prefixEnd_832052 379771204919896734598639 := by
  unfold tailWord_832052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173714790812591006649205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20231619721083454675532273 15173714790812591006649205)
  ·
    refine ⟨1422535761638680406873363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15173714790812591006649205 1422535761638680406873363)
    ·
      refine ⟨2133803642458020610310045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422535761638680406873363 2133803642458020610310045)
      ·
        refine ⟨800176365921757728866267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2133803642458020610310045 800176365921757728866267)
        ·
          refine ⟨1200264548882636593299401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800176365921757728866267 1200264548882636593299401)
          ·
            refine ⟨900198411661977444974551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200264548882636593299401 900198411661977444974551)
            ·
              refine ⟨1350297617492966167461827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900198411661977444974551 1350297617492966167461827)
              ·
                refine ⟨2025446426239449251192741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350297617492966167461827 2025446426239449251192741)
                ·
                  refine ⟨379771204919896734598639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025446426239449251192741 379771204919896734598639)
                  ·
                    rfl

theorem cell20_832052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_832052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832052 prefixEnd_832052 := by exact prefixLift 832052
  have htrace : WordTrace (prefixWord ++ tailWord_832052) baseStart_832052 baseEnd_832052 := by
    simpa [prefixWord, tailWord_832052, baseEnd_832052] using wordTrace_append hprefix tailTrace_832052
  have hstable : (prefixWord ++ tailWord_832052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832052).length < 2 ^ (prefixWord ++ tailWord_832052).sum := by decide
  have hdescent : baseEnd_832052 < baseStart_832052 := by decide
  rcases family_descends (prefixWord ++ tailWord_832052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832053 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_832053 : Nat := 118140960795 + 832053 * 2 ^ 59
def prefixEnd_832053 : Nat := 4983230072969 + 3 ^ 40 * 832053 * 2
def baseEnd_832053 : Nat := 379771661347145175565301

theorem tailTrace_832053 : CollatzResearch.WordTrace tailWord_832053 prefixEnd_832053 379771661347145175565301 := by
  unfold tailWord_832053
  simp only [CollatzResearch.WordTrace]
  refine ⟨30347466054621559184084813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20231644036414372789389875 30347466054621559184084813)
  ·
    refine ⟨11380299770483084694031805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30347466054621559184084813 11380299770483084694031805)
    ·
      refine ⟨4267612413931156760261927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11380299770483084694031805 4267612413931156760261927)
      ·
        refine ⟨6401418620896735140392891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267612413931156760261927 6401418620896735140392891)
        ·
          refine ⟨9602127931345102710589337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401418620896735140392891 9602127931345102710589337)
          ·
            refine ⟨7201595948508827032942003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602127931345102710589337 7201595948508827032942003)
            ·
              refine ⟨10802393922763240549413005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201595948508827032942003 10802393922763240549413005)
              ·
                refine ⟨4050897721036215206029877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10802393922763240549413005 4050897721036215206029877)
                ·
                  refine ⟨379771661347145175565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4050897721036215206029877 379771661347145175565301)
                  ·
                    rfl

theorem cell20_832053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_832053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832053 prefixEnd_832053 := by exact prefixLift 832053
  have htrace : WordTrace (prefixWord ++ tailWord_832053) baseStart_832053 baseEnd_832053 := by
    simpa [prefixWord, tailWord_832053, baseEnd_832053] using wordTrace_append hprefix tailTrace_832053
  have hstable : (prefixWord ++ tailWord_832053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832053).length < 2 ^ (prefixWord ++ tailWord_832053).sum := by decide
  have hdescent : baseEnd_832053 < baseStart_832053 := by decide
  rcases family_descends (prefixWord ++ tailWord_832053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832062 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_832062 : Nat := 118140960795 + 832062 * 2 ^ 59
def prefixEnd_832062 : Nat := 4983230072969 + 3 ^ 40 * 832062 * 2
def baseEnd_832062 : Nat := 379775769192381144265265

theorem tailTrace_832062 : CollatzResearch.WordTrace tailWord_832062 prefixEnd_832062 379775769192381144265265 := by
  unfold tailWord_832062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3793474288948619215145305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20231862874392635814108293 3793474288948619215145305)
  ·
    refine ⟨2845105716711464411358979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3793474288948619215145305 2845105716711464411358979)
    ·
      refine ⟨4267658575067196617038469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845105716711464411358979 4267658575067196617038469)
      ·
        refine ⟨800185982825099365694713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4267658575067196617038469 800185982825099365694713)
        ·
          refine ⟨600139487118824524271035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800185982825099365694713 600139487118824524271035)
          ·
            refine ⟨900209230678236786406553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600139487118824524271035 900209230678236786406553)
            ·
              refine ⟨675156923008677589804915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900209230678236786406553 675156923008677589804915)
              ·
                refine ⟨1012735384513016384707373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675156923008677589804915 1012735384513016384707373)
                ·
                  refine ⟨379775769192381144265265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012735384513016384707373 379775769192381144265265)
                  ·
                    rfl

theorem cell20_832062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_832062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832062 prefixEnd_832062 := by exact prefixLift 832062
  have htrace : WordTrace (prefixWord ++ tailWord_832062) baseStart_832062 baseEnd_832062 := by
    simpa [prefixWord, tailWord_832062, baseEnd_832062] using wordTrace_append hprefix tailTrace_832062
  have hstable : (prefixWord ++ tailWord_832062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832062).length < 2 ^ (prefixWord ++ tailWord_832062).sum := by decide
  have hdescent : baseEnd_832062 < baseStart_832062 := by decide
  rcases family_descends (prefixWord ++ tailWord_832062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832084 : List Nat := [2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_832084 : Nat := 118140960795 + 832084 * 2 ^ 59
def prefixEnd_832084 : Nat := 4983230072969 + 3 ^ 40 * 832084 * 2
def baseEnd_832084 : Nat := 126595270197282281843947

theorem tailTrace_832084 : CollatzResearch.WordTrace tailWord_832084 prefixEnd_832084 126595270197282281843947 := by
  unfold tailWord_832084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174298358754625739231653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20232397811672834318975537 15174298358754625739231653)
  ·
    refine ⟨2845180942266492326105935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15174298358754625739231653 2845180942266492326105935)
    ·
      refine ⟨4267771413399738489158903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845180942266492326105935 4267771413399738489158903)
      ·
        refine ⟨6401657120099607733738355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267771413399738489158903 6401657120099607733738355)
        ·
          refine ⟨9602485680149411600607533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401657120099607733738355 9602485680149411600607533)
          ·
            refine ⟨3600932130056029350227825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9602485680149411600607533 3600932130056029350227825)
            ·
              refine ⟨2700699097542022012670869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600932130056029350227825 2700699097542022012670869)
              ·
                refine ⟨126595270197282281843947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2700699097542022012670869 126595270197282281843947)
                ·
                  rfl

theorem cell20_832084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_832084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832084 prefixEnd_832084 := by exact prefixLift 832084
  have htrace : WordTrace (prefixWord ++ tailWord_832084) baseStart_832084 baseEnd_832084 := by
    simpa [prefixWord, tailWord_832084, baseEnd_832084] using wordTrace_append hprefix tailTrace_832084
  have hstable : (prefixWord ++ tailWord_832084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832084).length < 2 ^ (prefixWord ++ tailWord_832084).sum := by decide
  have hdescent : baseEnd_832084 < baseStart_832084 := by decide
  rcases family_descends (prefixWord ++ tailWord_832084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832118 : List Nat := [5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_832118 : Nat := 118140960795 + 832118 * 2 ^ 59
def prefixEnd_832118 : Nat := 4983230072969 + 3 ^ 40 * 832118 * 2
def baseEnd_832118 : Nat := 126600443039431279466123

theorem tailTrace_832118 : CollatzResearch.WordTrace tailWord_832118 prefixEnd_832118 126600443039431279466123 := by
  unfold tailWord_832118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896864799961629705325063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20233224532924050190134005 1896864799961629705325063)
  ·
    refine ⟨2845297199942444557987595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896864799961629705325063 2845297199942444557987595)
    ·
      refine ⟨4267945799913666836981393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845297199942444557987595 4267945799913666836981393)
      ·
        refine ⟨3200959349935250127736045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4267945799913666836981393 3200959349935250127736045)
        ·
          refine ⟨1200359756225718797901017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3200959349935250127736045 1200359756225718797901017)
          ·
            refine ⟨900269817169289098425763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200359756225718797901017 900269817169289098425763)
            ·
              refine ⟨1350404725753933647638645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900269817169289098425763 1350404725753933647638645)
              ·
                refine ⟨126600443039431279466123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1350404725753933647638645 126600443039431279466123)
                ·
                  rfl

theorem cell20_832118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_832118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832118 prefixEnd_832118 := by exact prefixLift 832118
  have htrace : WordTrace (prefixWord ++ tailWord_832118) baseStart_832118 baseEnd_832118 := by
    simpa [prefixWord, tailWord_832118, baseEnd_832118] using wordTrace_append hprefix tailTrace_832118
  have hstable : (prefixWord ++ tailWord_832118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832118).length < 2 ^ (prefixWord ++ tailWord_832118).sum := by decide
  have hdescent : baseEnd_832118 < baseStart_832118 := by decide
  rcases family_descends (prefixWord ++ tailWord_832118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832160 : List Nat := [2, 1, 1, 4, 4, 1, 7]
def baseStart_832160 : Nat := 118140960795 + 832160 * 2 ^ 59
def prefixEnd_832160 : Nat := 4983230072969 + 3 ^ 40 * 832160 * 2
def baseEnd_832160 : Nat := 42202277673636484333133

theorem tailTrace_832160 : CollatzResearch.WordTrace tailWord_832160 prefixEnd_832160 42202277673636484333133 := by
  unfold tailWord_832160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175684332616958229114967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20234245776822610972153289 15175684332616958229114967)
  ·
    refine ⟨22763526498925437343672451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175684332616958229114967 22763526498925437343672451)
    ·
      refine ⟨34145289748388156015508677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22763526498925437343672451 34145289748388156015508677)
      ·
        refine ⟨6402241827822779252907877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34145289748388156015508677 6402241827822779252907877)
        ·
          refine ⟨1200420342716771109920227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6402241827822779252907877 1200420342716771109920227)
          ·
            refine ⟨1800630514075156664880341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200420342716771109920227 1800630514075156664880341)
            ·
              refine ⟨42202277673636484333133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1800630514075156664880341 42202277673636484333133)
              ·
                rfl

theorem cell20_832160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_832160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832160 prefixEnd_832160 := by exact prefixLift 832160
  have htrace : WordTrace (prefixWord ++ tailWord_832160) baseStart_832160 baseEnd_832160 := by
    simpa [prefixWord, tailWord_832160, baseEnd_832160] using wordTrace_append hprefix tailTrace_832160
  have hstable : (prefixWord ++ tailWord_832160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832160).length < 2 ^ (prefixWord ++ tailWord_832160).sum := by decide
  have hdescent : baseEnd_832160 < baseStart_832160 := by decide
  rcases family_descends (prefixWord ++ tailWord_832160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832225 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 2]
def baseStart_832225 : Nat := 118140960795 + 832225 * 2 ^ 59
def prefixEnd_832225 : Nat := 4983230072969 + 3 ^ 40 * 832225 * 2
def baseEnd_832225 : Nat := 379850166833877021831265

theorem tailTrace_832225 : CollatzResearch.WordTrace tailWord_832225 prefixEnd_832225 379850166833877021831265 := by
  unfold tailWord_832225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353739409998432559346129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20235826273332288372897419 30353739409998432559346129)
  ·
    refine ⟨22765304557498824419509597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30353739409998432559346129 22765304557498824419509597)
    ·
      refine ⟨8536989209062059157316099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22765304557498824419509597 8536989209062059157316099)
      ·
        refine ⟨12805483813593088735974149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536989209062059157316099 12805483813593088735974149)
        ·
          refine ⟨2401028215048704137995153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12805483813593088735974149 2401028215048704137995153)
          ·
            refine ⟨1800771161286528103496365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401028215048704137995153 1800771161286528103496365)
            ·
              refine ⟨675289185482448038811137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1800771161286528103496365 675289185482448038811137)
              ·
                refine ⟨506466889111836029108353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675289185482448038811137 506466889111836029108353)
                ·
                  refine ⟨379850166833877021831265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506466889111836029108353 379850166833877021831265)
                  ·
                    rfl

theorem cell20_832225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_832225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832225 prefixEnd_832225 := by exact prefixLift 832225
  have htrace : WordTrace (prefixWord ++ tailWord_832225) baseStart_832225 baseEnd_832225 := by
    simpa [prefixWord, tailWord_832225, baseEnd_832225] using wordTrace_append hprefix tailTrace_832225
  have hstable : (prefixWord ++ tailWord_832225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832225).length < 2 ^ (prefixWord ++ tailWord_832225).sum := by decide
  have hdescent : baseEnd_832225 < baseStart_832225 := by decide
  rcases family_descends (prefixWord ++ tailWord_832225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832229 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_832229 : Nat := 118140960795 + 832229 * 2 ^ 59
def prefixEnd_832229 : Nat := 4983230072969 + 3 ^ 40 * 832229 * 2
def baseEnd_832229 : Nat := 379851992542870785697915

theorem tailTrace_832229 : CollatzResearch.WordTrace tailWord_832229 prefixEnd_832229 379851992542870785697915 := by
  unfold tailWord_832229
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353885301983941242491741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20235923534655960828327827 30353885301983941242491741)
  ·
    refine ⟨11382706988243977965934403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30353885301983941242491741 11382706988243977965934403)
    ·
      refine ⟨17074060482365966948901605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382706988243977965934403 17074060482365966948901605)
      ·
        refine ⟨3201386340443618802919051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17074060482365966948901605 3201386340443618802919051)
        ·
          refine ⟨4802079510665428204378577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201386340443618802919051 4802079510665428204378577)
          ·
            refine ⟨3601559632999071153283933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4802079510665428204378577 3601559632999071153283933)
            ·
              refine ⟨1350584862374651682481475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3601559632999071153283933 1350584862374651682481475)
              ·
                refine ⟨2025877293561977523722213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350584862374651682481475 2025877293561977523722213)
                ·
                  refine ⟨379851992542870785697915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025877293561977523722213 379851992542870785697915)
                  ·
                    rfl

theorem cell20_832229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_832229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832229 prefixEnd_832229 := by exact prefixLift 832229
  have htrace : WordTrace (prefixWord ++ tailWord_832229) baseStart_832229 baseEnd_832229 := by
    simpa [prefixWord, tailWord_832229, baseEnd_832229] using wordTrace_append hprefix tailTrace_832229
  have hstable : (prefixWord ++ tailWord_832229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832229).length < 2 ^ (prefixWord ++ tailWord_832229).sum := by decide
  have hdescent : baseEnd_832229 < baseStart_832229 := by decide
  rcases family_descends (prefixWord ++ tailWord_832229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832239 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 3]
def baseStart_832239 : Nat := 118140960795 + 832239 * 2 ^ 59
def prefixEnd_832239 : Nat := 4983230072969 + 3 ^ 40 * 832239 * 2
def baseEnd_832239 : Nat := 379856556815355195364541

theorem tailTrace_832239 : CollatzResearch.WordTrace tailWord_832239 prefixEnd_832239 379856556815355195364541 := by
  unfold tailWord_832239
  simp only [CollatzResearch.WordTrace]
  refine ⟨30354250031947712950355771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20236166687965141966903847 30354250031947712950355771)
  ·
    refine ⟨45531375047921569425533657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30354250031947712950355771 45531375047921569425533657)
    ·
      refine ⟨34148531285941177069150243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45531375047921569425533657 34148531285941177069150243)
      ·
        refine ⟨51222796928911765603725365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34148531285941177069150243 51222796928911765603725365)
        ·
          refine ⟨4802137212085478025349253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51222796928911765603725365 4802137212085478025349253)
          ·
            refine ⟨900400727266027129752985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4802137212085478025349253 900400727266027129752985)
            ·
              refine ⟨675300545449520347314739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900400727266027129752985 675300545449520347314739)
              ·
                refine ⟨1012950818174280520972109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675300545449520347314739 1012950818174280520972109)
                ·
                  refine ⟨379856556815355195364541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012950818174280520972109 379856556815355195364541)
                  ·
                    rfl

theorem cell20_832239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_832239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832239 prefixEnd_832239 := by exact prefixLift 832239
  have htrace : WordTrace (prefixWord ++ tailWord_832239) baseStart_832239 baseEnd_832239 := by
    simpa [prefixWord, tailWord_832239, baseEnd_832239] using wordTrace_append hprefix tailTrace_832239
  have hstable : (prefixWord ++ tailWord_832239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832239).length < 2 ^ (prefixWord ++ tailWord_832239).sum := by decide
  have hdescent : baseEnd_832239 < baseStart_832239 := by decide
  rcases family_descends (prefixWord ++ tailWord_832239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832250 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_832250 : Nat := 118140960795 + 832250 * 2 ^ 59
def prefixEnd_832250 : Nat := 4983230072969 + 3 ^ 40 * 832250 * 2
def baseEnd_832250 : Nat := 379861577515088045997829

theorem tailTrace_832250 : CollatzResearch.WordTrace tailWord_832250 prefixEnd_832250 379861577515088045997829 := by
  unfold tailWord_832250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588662808726965457251551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20236434156605241219337469 7588662808726965457251551)
  ·
    refine ⟨11382994213090448185877327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7588662808726965457251551 11382994213090448185877327)
    ·
      refine ⟨17074491319635672278815991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382994213090448185877327 17074491319635672278815991)
      ·
        refine ⟨25611736979453508418223987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17074491319635672278815991 25611736979453508418223987)
        ·
          refine ⟨38417605469180262627335981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25611736979453508418223987 38417605469180262627335981)
          ·
            refine ⟨14406602050942598485250993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38417605469180262627335981 14406602050942598485250993)
            ·
              refine ⟨10804951538206948863938245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14406602050942598485250993 10804951538206948863938245)
              ·
                refine ⟨2025928413413802911988421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10804951538206948863938245 2025928413413802911988421)
                ·
                  refine ⟨379861577515088045997829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2025928413413802911988421 379861577515088045997829)
                  ·
                    rfl

theorem cell20_832250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_832250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832250 prefixEnd_832250 := by exact prefixLift 832250
  have htrace : WordTrace (prefixWord ++ tailWord_832250) baseStart_832250 baseEnd_832250 := by
    simpa [prefixWord, tailWord_832250, baseEnd_832250] using wordTrace_append hprefix tailTrace_832250
  have hstable : (prefixWord ++ tailWord_832250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832250).length < 2 ^ (prefixWord ++ tailWord_832250).sum := by decide
  have hdescent : baseEnd_832250 < baseStart_832250 := by decide
  rcases family_descends (prefixWord ++ tailWord_832250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832267 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 2]
def baseStart_832267 : Nat := 118140960795 + 832267 * 2 ^ 59
def prefixEnd_832267 : Nat := 4983230072969 + 3 ^ 40 * 832267 * 2
def baseEnd_832267 : Nat := 379869336778311542431093

theorem tailTrace_832267 : CollatzResearch.WordTrace tailWord_832267 prefixEnd_832267 379869336778311542431093 := by
  unfold tailWord_832267
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355271275846273732375055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20236847517230849154916703 30355271275846273732375055)
  ·
    refine ⟨45532906913769410598562583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30355271275846273732375055 45532906913769410598562583)
    ·
      refine ⟨68299360370654115897843875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45532906913769410598562583 68299360370654115897843875)
      ·
        refine ⟨102449040555981173846765813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68299360370654115897843875 102449040555981173846765813)
        ·
          refine ⟨9604597552123235048134295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102449040555981173846765813 9604597552123235048134295)
          ·
            refine ⟨14406896328184852572201443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9604597552123235048134295 14406896328184852572201443)
            ·
              refine ⟨21610344492277278858302165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14406896328184852572201443 21610344492277278858302165)
              ·
                refine ⟨506492449037748723241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21610344492277278858302165 506492449037748723241457)
                ·
                  refine ⟨379869336778311542431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506492449037748723241457 379869336778311542431093)
                  ·
                    rfl

theorem cell20_832267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2].length) (baseStart_832267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832267 prefixEnd_832267 := by exact prefixLift 832267
  have htrace : WordTrace (prefixWord ++ tailWord_832267) baseStart_832267 baseEnd_832267 := by
    simpa [prefixWord, tailWord_832267, baseEnd_832267] using wordTrace_append hprefix tailTrace_832267
  have hstable : (prefixWord ++ tailWord_832267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832267).length < 2 ^ (prefixWord ++ tailWord_832267).sum := by decide
  have hdescent : baseEnd_832267 < baseStart_832267 := by decide
  rcases family_descends (prefixWord ++ tailWord_832267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832274 : List Nat := [3, 2, 4, 1, 10]
def baseStart_832274 : Nat := 118140960795 + 832274 * 2 ^ 59
def prefixEnd_832274 : Nat := 4983230072969 + 3 ^ 40 * 832274 * 2
def baseEnd_832274 : Nat := 4689784342827785545651

theorem tailTrace_832274 : CollatzResearch.WordTrace tailWord_832274 prefixEnd_832274 4689784342827785545651 := by
  unfold tailWord_832274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588881646705228481969969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20237017724547275951919917 7588881646705228481969969)
  ·
    refine ⟨5691661235028921361477477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7588881646705228481969969 5691661235028921361477477)
    ·
      refine ⟨1067186481567922755277027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5691661235028921361477477 1067186481567922755277027)
      ·
        refine ⟨1600779722351884132915541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067186481567922755277027 1600779722351884132915541)
        ·
          refine ⟨4689784342827785545651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1600779722351884132915541 4689784342827785545651)
          ·
            rfl

theorem cell20_832274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 10].length) (baseStart_832274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_832274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_832274 prefixEnd_832274 := by exact prefixLift 832274
  have htrace : WordTrace (prefixWord ++ tailWord_832274) baseStart_832274 baseEnd_832274 := by
    simpa [prefixWord, tailWord_832274, baseEnd_832274] using wordTrace_append hprefix tailTrace_832274
  have hstable : (prefixWord ++ tailWord_832274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832274).length < 2 ^ (prefixWord ++ tailWord_832274).sum := by decide
  have hdescent : baseEnd_832274 < baseStart_832274 := by decide
  rcases family_descends (prefixWord ++ tailWord_832274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
