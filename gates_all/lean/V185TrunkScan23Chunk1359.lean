import V185TrunkScan23Chunk1358

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8048903 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_8048903 : Nat := 118140960795 + 8048903 * 2 ^ 59
def prefixEnd_8048903 : Nat := 4983230072969 + 3 ^ 40 * 8048903 * 2
def baseEnd_8048903 : Nat := 4132955980415627363696275

theorem tailTrace_8048903 : CollatzResearch.WordTrace tailWord_8048903 prefixEnd_8048903 4132955980415627363696275 := by
  unfold tailWord_8048903
  simp only [CollatzResearch.WordTrace]
  refine ⟨293567609959206549036575363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195711739972804366024383575 293567609959206549036575363)
  ·
    refine ⟨440351414938809823554863045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293567609959206549036575363 440351414938809823554863045)
    ·
      refine ⟨82565890301026841916536821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440351414938809823554863045 82565890301026841916536821)
      ·
        refine ⟨7740552215721266429675327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82565890301026841916536821 7740552215721266429675327)
        ·
          refine ⟨11610828323581899644512991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740552215721266429675327 11610828323581899644512991)
          ·
            refine ⟨17416242485372849466769487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610828323581899644512991 17416242485372849466769487)
            ·
              refine ⟨26124363728059274200154231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17416242485372849466769487 26124363728059274200154231)
              ·
                refine ⟨39186545592088911300231347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26124363728059274200154231 39186545592088911300231347)
                ·
                  refine ⟨58779818388133366950347021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39186545592088911300231347 58779818388133366950347021)
                  ·
                    refine ⟨22042431895550012606380133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58779818388133366950347021 22042431895550012606380133)
                    ·
                      refine ⟨4132955980415627363696275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22042431895550012606380133 4132955980415627363696275)
                      ·
                        rfl

theorem cell23_8048903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_8048903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048903 prefixEnd_8048903 := by exact prefixLift 8048903
  have htrace : WordTrace (prefixWord ++ tailWord_8048903) baseStart_8048903 baseEnd_8048903 := by
    simpa [prefixWord, tailWord_8048903, baseEnd_8048903] using wordTrace_append hprefix tailTrace_8048903
  have hstable : (prefixWord ++ tailWord_8048903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048903).length < 2 ^ (prefixWord ++ tailWord_8048903).sum := by decide
  have hdescent : baseEnd_8048903 < baseStart_8048903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048913 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 1, 4]
def baseStart_8048913 : Nat := 118140960795 + 8048913 * 2 ^ 59
def prefixEnd_8048913 : Nat := 4983230072969 + 3 ^ 40 * 8048913 * 2
def baseEnd_8048913 : Nat := 1377653705074057441523743

theorem tailTrace_8048913 : CollatzResearch.WordTrace tailWord_8048913 prefixEnd_8048913 1377653705074057441523743 := by
  unfold tailWord_8048913
  simp only [CollatzResearch.WordTrace]
  refine ⟨293567974689170320744439393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195711983126113547162959595 293567974689170320744439393)
  ·
    refine ⟨220175981016877740558329545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293567974689170320744439393 220175981016877740558329545)
    ·
      refine ⟨165131985762658305418747159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220175981016877740558329545 165131985762658305418747159)
      ·
        refine ⟨247697978643987458128120739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165131985762658305418747159 247697978643987458128120739)
        ·
          refine ⟨371546967965981187192181109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247697978643987458128120739 371546967965981187192181109)
          ·
            refine ⟨34832528246810736299266979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371546967965981187192181109 34832528246810736299266979)
            ·
              refine ⟨52248792370216104448900469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34832528246810736299266979 52248792370216104448900469)
              ·
                refine ⟨4898324284707759792084419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52248792370216104448900469 4898324284707759792084419)
                ·
                  refine ⟨7347486427061639688126629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898324284707759792084419 7347486427061639688126629)
                  ·
                    refine ⟨1377653705074057441523743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347486427061639688126629 1377653705074057441523743)
                    ·
                      rfl

theorem cell23_8048913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_8048913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048913 prefixEnd_8048913 := by exact prefixLift 8048913
  have htrace : WordTrace (prefixWord ++ tailWord_8048913) baseStart_8048913 baseEnd_8048913 := by
    simpa [prefixWord, tailWord_8048913, baseEnd_8048913] using wordTrace_append hprefix tailTrace_8048913
  have hstable : (prefixWord ++ tailWord_8048913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048913).length < 2 ^ (prefixWord ++ tailWord_8048913).sum := by decide
  have hdescent : baseEnd_8048913 < baseStart_8048913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048929 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8048929 : Nat := 118140960795 + 8048929 * 2 ^ 59
def prefixEnd_8048929 : Nat := 4983230072969 + 3 ^ 40 * 8048929 * 2
def baseEnd_8048929 : Nat := 4132969330912644261971155

theorem tailTrace_8048929 : CollatzResearch.WordTrace tailWord_8048929 prefixEnd_8048929 4132969330912644261971155 := by
  unfold tailWord_8048929
  simp only [CollatzResearch.WordTrace]
  refine ⟨293568558257112355477021841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195712372171408236984681227 293568558257112355477021841)
  ·
    refine ⟨220176418692834266607766381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293568558257112355477021841 220176418692834266607766381)
    ·
      refine ⟨82566157009812849977912393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220176418692834266607766381 82566157009812849977912393)
      ·
        refine ⟨61924617757359637483434295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82566157009812849977912393 61924617757359637483434295)
        ·
          refine ⟨92886926636039456225151443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61924617757359637483434295 92886926636039456225151443)
          ·
            refine ⟨139330389954059184337727165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92886926636039456225151443 139330389954059184337727165)
            ·
              refine ⟨52248896232772194126647687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139330389954059184337727165 52248896232772194126647687)
              ·
                refine ⟨78373344349158291189971531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52248896232772194126647687 78373344349158291189971531)
                ·
                  refine ⟨117560016523737436784957297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78373344349158291189971531 117560016523737436784957297)
                  ·
                    refine ⟨88170012392803077588717973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117560016523737436784957297 88170012392803077588717973)
                    ·
                      refine ⟨4132969330912644261971155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88170012392803077588717973 4132969330912644261971155)
                      ·
                        rfl

theorem cell23_8048929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8048929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048929 prefixEnd_8048929 := by exact prefixLift 8048929
  have htrace : WordTrace (prefixWord ++ tailWord_8048929) baseStart_8048929 baseEnd_8048929 := by
    simpa [prefixWord, tailWord_8048929, baseEnd_8048929] using wordTrace_append hprefix tailTrace_8048929
  have hstable : (prefixWord ++ tailWord_8048929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048929).length < 2 ^ (prefixWord ++ tailWord_8048929).sum := by decide
  have hdescent : baseEnd_8048929 < baseStart_8048929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048930 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_8048930 : Nat := 118140960795 + 8048930 * 2 ^ 59
def prefixEnd_8048930 : Nat := 4983230072969 + 3 ^ 40 * 8048930 * 2
def baseEnd_8048930 : Nat := 1377656614797766252686217

theorem tailTrace_8048930 : CollatzResearch.WordTrace tailWord_8048930 prefixEnd_8048930 1377656614797766252686217 := by
  unfold tailWord_8048930
  simp only [CollatzResearch.WordTrace]
  refine ⟨73392148682527183161952061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195712396486739155098538829 73392148682527183161952061)
  ·
    refine ⟨27522055755947693685732023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73392148682527183161952061 27522055755947693685732023)
    ·
      refine ⟨41283083633921540528598035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27522055755947693685732023 41283083633921540528598035)
      ·
        refine ⟨61924625450882310792897053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41283083633921540528598035 61924625450882310792897053)
        ·
          refine ⟨23221734544080866547336395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61924625450882310792897053 23221734544080866547336395)
          ·
            refine ⟨34832601816121299821004593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23221734544080866547336395 34832601816121299821004593)
            ·
              refine ⟨26124451362090974865753445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34832601816121299821004593 26124451362090974865753445)
              ·
                refine ⟨4898334630392057787328771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26124451362090974865753445 4898334630392057787328771)
                ·
                  refine ⟨7347501945588086680993157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898334630392057787328771 7347501945588086680993157)
                  ·
                    refine ⟨1377656614797766252686217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347501945588086680993157 1377656614797766252686217)
                    ·
                      rfl

theorem cell23_8048930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_8048930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048930 prefixEnd_8048930 := by exact prefixLift 8048930
  have htrace : WordTrace (prefixWord ++ tailWord_8048930) baseStart_8048930 baseEnd_8048930 := by
    simpa [prefixWord, tailWord_8048930, baseEnd_8048930] using wordTrace_append hprefix tailTrace_8048930
  have hstable : (prefixWord ++ tailWord_8048930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048930).length < 2 ^ (prefixWord ++ tailWord_8048930).sum := by decide
  have hdescent : baseEnd_8048930 < baseStart_8048930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048964 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_8048964 : Nat := 118140960795 + 8048964 * 2 ^ 59
def prefixEnd_8048964 : Nat := 4983230072969 + 3 ^ 40 * 8048964 * 2
def baseEnd_8048964 : Nat := 1377662434245183875011165

theorem tailTrace_8048964 : CollatzResearch.WordTrace tailWord_8048964 prefixEnd_8048964 1377662434245183875011165 := by
  unfold tailWord_8048964
  simp only [CollatzResearch.WordTrace]
  refine ⟨146784917405992778227272973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195713223207990370969697297 146784917405992778227272973)
  ·
    refine ⟨55044344027247291835227365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146784917405992778227272973 55044344027247291835227365)
    ·
      refine ⟨10320814505108867219105131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55044344027247291835227365 10320814505108867219105131)
      ·
        refine ⟨15481221757663300828657697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10320814505108867219105131 15481221757663300828657697)
        ·
          refine ⟨11610916318247475621493273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15481221757663300828657697 11610916318247475621493273)
          ·
            refine ⟨8708187238685606716119955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11610916318247475621493273 8708187238685606716119955)
            ·
              refine ⟨13062280858028410074179933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708187238685606716119955 13062280858028410074179933)
              ·
                refine ⟨4898355321760653777817475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13062280858028410074179933 4898355321760653777817475)
                ·
                  refine ⟨7347532982640980666726213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898355321760653777817475 7347532982640980666726213)
                  ·
                    refine ⟨1377662434245183875011165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347532982640980666726213 1377662434245183875011165)
                    ·
                      rfl

theorem cell23_8048964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_8048964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048964 prefixEnd_8048964 := by exact prefixLift 8048964
  have htrace : WordTrace (prefixWord ++ tailWord_8048964) baseStart_8048964 baseEnd_8048964 := by
    simpa [prefixWord, tailWord_8048964, baseEnd_8048964] using wordTrace_append hprefix tailTrace_8048964
  have hstable : (prefixWord ++ tailWord_8048964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048964).length < 2 ^ (prefixWord ++ tailWord_8048964).sum := by decide
  have hdescent : baseEnd_8048964 < baseStart_8048964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048969 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_8048969 : Nat := 118140960795 + 8048969 * 2 ^ 59
def prefixEnd_8048969 : Nat := 4983230072969 + 3 ^ 40 * 8048969 * 2
def baseEnd_8048969 : Nat := 1377663290046274701823657

theorem tailTrace_8048969 : CollatzResearch.WordTrace tailWord_8048969 prefixEnd_8048969 1377663290046274701823657 := by
  unfold tailWord_8048969
  simp only [CollatzResearch.WordTrace]
  refine ⟨293570017176967442308477961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195713344784644961538985307 293570017176967442308477961)
  ·
    refine ⟨220177512882725581731358471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293570017176967442308477961 220177512882725581731358471)
    ·
      refine ⟨330266269324088372597037707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220177512882725581731358471 330266269324088372597037707)
      ·
        refine ⟨495399403986132558895556561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330266269324088372597037707 495399403986132558895556561)
        ·
          refine ⟨371549552989599419171667421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495399403986132558895556561 371549552989599419171667421)
          ·
            refine ⟨139331082371099782189375283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371549552989599419171667421 139331082371099782189375283)
            ·
              refine ⟨208996623556649673284062925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139331082371099782189375283 208996623556649673284062925)
              ·
                refine ⟨78373733833743627481523597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208996623556649673284062925 78373733833743627481523597)
                ·
                  refine ⟨29390150187653860305571349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78373733833743627481523597 29390150187653860305571349)
                  ·
                    refine ⟨1377663290046274701823657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29390150187653860305571349 1377663290046274701823657)
                    ·
                      rfl

theorem cell23_8048969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_8048969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048969 prefixEnd_8048969 := by exact prefixLift 8048969
  have htrace : WordTrace (prefixWord ++ tailWord_8048969) baseStart_8048969 baseEnd_8048969 := by
    simpa [prefixWord, tailWord_8048969, baseEnd_8048969] using wordTrace_append hprefix tailTrace_8048969
  have hstable : (prefixWord ++ tailWord_8048969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048969).length < 2 ^ (prefixWord ++ tailWord_8048969).sum := by decide
  have hdescent : baseEnd_8048969 < baseStart_8048969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048980 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_8048980 : Nat := 118140960795 + 8048980 * 2 ^ 59
def prefixEnd_8048980 : Nat := 4983230072969 + 3 ^ 40 * 8048980 * 2
def baseEnd_8048980 : Nat := 4132995518426023562433421

theorem tailTrace_8048980 : CollatzResearch.WordTrace tailWord_8048980 prefixEnd_8048980 4132995518426023562433421 := by
  unfold tailWord_8048980
  simp only [CollatzResearch.WordTrace]
  refine ⟨146785209189963795593564197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195713612253285060791418929 146785209189963795593564197)
  ·
    refine ⟨27522226723118211673793287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146785209189963795593564197 27522226723118211673793287)
    ·
      refine ⟨41283340084677317510689931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27522226723118211673793287 41283340084677317510689931)
      ·
        refine ⟨61925010127015976266034897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41283340084677317510689931 61925010127015976266034897)
        ·
          refine ⟨46443757595261982199526173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61925010127015976266034897 46443757595261982199526173)
          ·
            refine ⟨17416409098223243324822315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46443757595261982199526173 17416409098223243324822315)
            ·
              refine ⟨26124613647334864987233473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17416409098223243324822315 26124613647334864987233473)
              ·
                refine ⟨19593460235501148740425105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26124613647334864987233473 19593460235501148740425105)
                ·
                  refine ⟨14695095176625861555318829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593460235501148740425105 14695095176625861555318829)
                  ·
                    refine ⟨5510660691234698083244561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14695095176625861555318829 5510660691234698083244561)
                    ·
                      refine ⟨4132995518426023562433421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510660691234698083244561 4132995518426023562433421)
                      ·
                        rfl

theorem cell23_8048980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_8048980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048980 prefixEnd_8048980 := by exact prefixLift 8048980
  have htrace : WordTrace (prefixWord ++ tailWord_8048980) baseStart_8048980 baseEnd_8048980 := by
    simpa [prefixWord, tailWord_8048980, baseEnd_8048980] using wordTrace_append hprefix tailTrace_8048980
  have hstable : (prefixWord ++ tailWord_8048980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048980).length < 2 ^ (prefixWord ++ tailWord_8048980).sum := by decide
  have hdescent : baseEnd_8048980 < baseStart_8048980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048996 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_8048996 : Nat := 118140960795 + 8048996 * 2 ^ 59
def prefixEnd_8048996 : Nat := 4983230072969 + 3 ^ 40 * 8048996 * 2
def baseEnd_8048996 : Nat := 4133003734116495499833347

theorem tailTrace_8048996 : CollatzResearch.WordTrace tailWord_8048996 prefixEnd_8048996 4133003734116495499833347 := by
  unfold tailWord_8048996
  simp only [CollatzResearch.WordTrace]
  refine ⟨146785500973934812959855421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195714001298579750613140561 146785500973934812959855421)
  ·
    refine ⟨55044562865225554859945783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146785500973934812959855421 55044562865225554859945783)
    ·
      refine ⟨82566844297838332289918675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55044562865225554859945783 82566844297838332289918675)
      ·
        refine ⟨123850266446757498434878013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82566844297838332289918675 123850266446757498434878013)
        ·
          refine ⟨46443849917534061913079255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123850266446757498434878013 46443849917534061913079255)
          ·
            refine ⟨69665774876301092869618883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46443849917534061913079255 69665774876301092869618883)
            ·
              refine ⟨104498662314451639304428325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69665774876301092869618883 104498662314451639304428325)
              ·
                refine ⟨19593499183959682369580311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104498662314451639304428325 19593499183959682369580311)
                ·
                  refine ⟨29390248775939523554370467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19593499183959682369580311 29390248775939523554370467)
                  ·
                    refine ⟨44085373163909285331555701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29390248775939523554370467 44085373163909285331555701)
                    ·
                      refine ⟨4133003734116495499833347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44085373163909285331555701 4133003734116495499833347)
                      ·
                        rfl

theorem cell23_8048996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_8048996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048996 prefixEnd_8048996 := by exact prefixLift 8048996
  have htrace : WordTrace (prefixWord ++ tailWord_8048996) baseStart_8048996 baseEnd_8048996 := by
    simpa [prefixWord, tailWord_8048996, baseEnd_8048996] using wordTrace_append hprefix tailTrace_8048996
  have hstable : (prefixWord ++ tailWord_8048996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048996).length < 2 ^ (prefixWord ++ tailWord_8048996).sum := by decide
  have hdescent : baseEnd_8048996 < baseStart_8048996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049010 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_8049010 : Nat := 118140960795 + 8049010 * 2 ^ 59
def prefixEnd_8049010 : Nat := 4983230072969 + 3 ^ 40 * 8049010 * 2
def baseEnd_8049010 : Nat := 4133010922845658445058283

theorem tailTrace_8049010 : CollatzResearch.WordTrace tailWord_8049010 prefixEnd_8049010 4133010922845658445058283 := by
  unfold tailWord_8049010
  simp only [CollatzResearch.WordTrace]
  refine ⟨73392878142454726577680121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195714341713212604207146989 73392878142454726577680121)
  ·
    refine ⟨55044658606841044933260091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73392878142454726577680121 55044658606841044933260091)
    ·
      refine ⟨82566987910261567399890137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55044658606841044933260091 82566987910261567399890137)
      ·
        refine ⟨61925240932696175549917603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82566987910261567399890137 61925240932696175549917603)
        ·
          refine ⟨92887861399044263324876405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61925240932696175549917603 92887861399044263324876405)
          ·
            refine ⟨8708237006160399686707163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92887861399044263324876405 8708237006160399686707163)
            ·
              refine ⟨13062355509240599530060745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708237006160399686707163 13062355509240599530060745)
              ·
                refine ⟨9796766631930449647545559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13062355509240599530060745 9796766631930449647545559)
                ·
                  refine ⟨14695149947895674471318339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9796766631930449647545559 14695149947895674471318339)
                  ·
                    refine ⟨22042724921843511706977509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14695149947895674471318339 22042724921843511706977509)
                    ·
                      refine ⟨4133010922845658445058283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22042724921843511706977509 4133010922845658445058283)
                      ·
                        rfl

theorem cell23_8049010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_8049010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049010 prefixEnd_8049010 := by exact prefixLift 8049010
  have htrace : WordTrace (prefixWord ++ tailWord_8049010) baseStart_8049010 baseEnd_8049010 := by
    simpa [prefixWord, tailWord_8049010, baseEnd_8049010] using wordTrace_append hprefix tailTrace_8049010
  have hstable : (prefixWord ++ tailWord_8049010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049010).length < 2 ^ (prefixWord ++ tailWord_8049010).sum := by decide
  have hdescent : baseEnd_8049010 < baseStart_8049010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049014 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_8049014 : Nat := 118140960795 + 8049014 * 2 ^ 59
def prefixEnd_8049014 : Nat := 4983230072969 + 3 ^ 40 * 8049014 * 2
def baseEnd_8049014 : Nat := 4133012976768276429408265

theorem tailTrace_8049014 : CollatzResearch.WordTrace tailWord_8049014 prefixEnd_8049014 4133012976768276429408265 := by
  unfold tailWord_8049014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18348228653862775937116631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195714438974536276662577397 18348228653862775937116631)
  ·
    refine ⟨27522342980794163905674947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18348228653862775937116631 27522342980794163905674947)
    ·
      refine ⟨41283514471191245858512421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27522342980794163905674947 41283514471191245858512421)
      ·
        refine ⟨7740658963348358598471079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41283514471191245858512421 7740658963348358598471079)
        ·
          refine ⟨11610988445022537897706619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740658963348358598471079 11610988445022537897706619)
          ·
            refine ⟨17416482667533806846559929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610988445022537897706619 17416482667533806846559929)
            ·
              refine ⟨13062362000650355134919947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17416482667533806846559929 13062362000650355134919947)
              ·
                refine ⟨19593543000975532702379921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13062362000650355134919947 19593543000975532702379921)
                ·
                  refine ⟨14695157250731649526784941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593543000975532702379921 14695157250731649526784941)
                  ·
                    refine ⟨5510683969024368572544353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14695157250731649526784941 5510683969024368572544353)
                    ·
                      refine ⟨4133012976768276429408265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510683969024368572544353 4133012976768276429408265)
                      ·
                        rfl

theorem cell23_8049014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_8049014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049014 prefixEnd_8049014 := by exact prefixLift 8049014
  have htrace : WordTrace (prefixWord ++ tailWord_8049014) baseStart_8049014 baseEnd_8049014 := by
    simpa [prefixWord, tailWord_8049014, baseEnd_8049014] using wordTrace_append hprefix tailTrace_8049014
  have hstable : (prefixWord ++ tailWord_8049014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049014).length < 2 ^ (prefixWord ++ tailWord_8049014).sum := by decide
  have hdescent : baseEnd_8049014 < baseStart_8049014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049060 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_8049060 : Nat := 118140960795 + 8049060 * 2 ^ 59
def prefixEnd_8049060 : Nat := 4983230072969 + 3 ^ 40 * 8049060 * 2
def baseEnd_8049060 : Nat := 4133036596878383249433053

theorem tailTrace_8049060 : CollatzResearch.WordTrace tailWord_8049060 prefixEnd_8049060 4133036596878383249433053 := by
  unfold tailWord_8049060
  simp only [CollatzResearch.WordTrace]
  refine ⟨146786668109818882425020317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195715557479758509900027089 146786668109818882425020317)
  ·
    refine ⟨55045000541182080909382619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146786668109818882425020317 55045000541182080909382619)
    ·
      refine ⟨82567500811773121364073929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55045000541182080909382619 82567500811773121364073929)
      ·
        refine ⟨61925625608829841023055447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82567500811773121364073929 61925625608829841023055447)
        ·
          refine ⟨92888438413244761534583171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61925625608829841023055447 92888438413244761534583171)
          ·
            refine ⟨139332657619867142301874757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92888438413244761534583171 139332657619867142301874757)
            ·
              refine ⟨26124873303725089181601517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139332657619867142301874757 26124873303725089181601517)
              ·
                refine ⟨9796827488896908443100569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26124873303725089181601517 9796827488896908443100569)
                ·
                  refine ⟨7347620616672681332325427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9796827488896908443100569 7347620616672681332325427)
                  ·
                    refine ⟨11021430925009021998488141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7347620616672681332325427 11021430925009021998488141)
                    ·
                      refine ⟨4133036596878383249433053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021430925009021998488141 4133036596878383249433053)
                      ·
                        rfl

theorem cell23_8049060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_8049060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049060 prefixEnd_8049060 := by exact prefixLift 8049060
  have htrace : WordTrace (prefixWord ++ tailWord_8049060) baseStart_8049060 baseEnd_8049060 := by
    simpa [prefixWord, tailWord_8049060, baseEnd_8049060] using wordTrace_append hprefix tailTrace_8049060
  have hstable : (prefixWord ++ tailWord_8049060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049060).length < 2 ^ (prefixWord ++ tailWord_8049060).sum := by decide
  have hdescent : baseEnd_8049060 < baseStart_8049060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049136 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_8049136 : Nat := 118140960795 + 8049136 * 2 ^ 59
def prefixEnd_8049136 : Nat := 4983230072969 + 3 ^ 40 * 8049136 * 2
def baseEnd_8049136 : Nat := 1377691873802708317360901

theorem tailTrace_8049136 : CollatzResearch.WordTrace tailWord_8049136 prefixEnd_8049136 1377691873802708317360901 := by
  unfold tailWord_8049136
  simp only [CollatzResearch.WordTrace]
  refine ⟨146788054083681214914903631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195717405444908286553204841 146788054083681214914903631)
  ·
    refine ⟨220182081125521822372355447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146788054083681214914903631 220182081125521822372355447)
    ·
      refine ⟨330273121688282733558533171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220182081125521822372355447 330273121688282733558533171)
      ·
        refine ⟨495409682532424100337799757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330273121688282733558533171 495409682532424100337799757)
        ·
          refine ⟨185778630949659037626674909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495409682532424100337799757 185778630949659037626674909)
          ·
            refine ⟨69666986606122139110003091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185778630949659037626674909 69666986606122139110003091)
            ·
              refine ⟨104500479909183208665004637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69666986606122139110003091 104500479909183208665004637)
              ·
                refine ⟨39187679965943703249376739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104500479909183208665004637 39187679965943703249376739)
                ·
                  refine ⟨58781519948915554874065109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39187679965943703249376739 58781519948915554874065109)
                  ·
                    refine ⟨1377691873802708317360901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58781519948915554874065109 1377691873802708317360901)
                    ·
                      rfl

theorem cell23_8049136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_8049136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049136 prefixEnd_8049136 := by exact prefixLift 8049136
  have htrace : WordTrace (prefixWord ++ tailWord_8049136) baseStart_8049136 baseEnd_8049136 := by
    simpa [prefixWord, tailWord_8049136, baseEnd_8049136] using wordTrace_append hprefix tailTrace_8049136
  have hstable : (prefixWord ++ tailWord_8049136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049136).length < 2 ^ (prefixWord ++ tailWord_8049136).sum := by decide
  have hdescent : baseEnd_8049136 < baseStart_8049136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049153 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_8049153 : Nat := 118140960795 + 8049153 * 2 ^ 59
def prefixEnd_8049153 : Nat := 4983230072969 + 3 ^ 40 * 8049153 * 2
def baseEnd_8049153 : Nat := 1377694783526417128523375

theorem tailTrace_8049153 : CollatzResearch.WordTrace tailWord_8049153 prefixEnd_8049153 1377694783526417128523375 := by
  unfold tailWord_8049153
  simp only [CollatzResearch.WordTrace]
  refine ⟨293576728208300841733176113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195717818805533894488784075 293576728208300841733176113)
  ·
    refine ⟨220182546156225631299882085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293576728208300841733176113 220182546156225631299882085)
    ·
      refine ⟨41284227404292305868727891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220182546156225631299882085 41284227404292305868727891)
      ·
        refine ⟨61926341106438458803091837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41284227404292305868727891 61926341106438458803091837)
        ·
          refine ⟨23222377914914422051159439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61926341106438458803091837 23222377914914422051159439)
          ·
            refine ⟨34833566872371633076739159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23222377914914422051159439 34833566872371633076739159)
            ·
              refine ⟨52250350308557449615108739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34833566872371633076739159 52250350308557449615108739)
              ·
                refine ⟨78375525462836174422663109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52250350308557449615108739 78375525462836174422663109)
                ·
                  refine ⟨14695411024281782704249333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78375525462836174422663109 14695411024281782704249333)
                  ·
                    refine ⟨1377694783526417128523375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14695411024281782704249333 1377694783526417128523375)
                    ·
                      rfl

theorem cell23_8049153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_8049153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049153 prefixEnd_8049153 := by exact prefixLift 8049153
  have htrace : WordTrace (prefixWord ++ tailWord_8049153) baseStart_8049153 baseEnd_8049153 := by
    simpa [prefixWord, tailWord_8049153, baseEnd_8049153] using wordTrace_append hprefix tailTrace_8049153
  have hstable : (prefixWord ++ tailWord_8049153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049153).length < 2 ^ (prefixWord ++ tailWord_8049153).sum := by decide
  have hdescent : baseEnd_8049153 < baseStart_8049153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049163 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5]
def baseStart_8049163 : Nat := 118140960795 + 8049163 * 2 ^ 59
def prefixEnd_8049163 : Nat := 4983230072969 + 3 ^ 40 * 8049163 * 2
def baseEnd_8049163 : Nat := 4133089485385796346445079

theorem tailTrace_8049163 : CollatzResearch.WordTrace tailWord_8049163 prefixEnd_8049163 4133089485385796346445079 := by
  unfold tailWord_8049163
  simp only [CollatzResearch.WordTrace]
  refine ⟨293577092938264613441040143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195718061958843075627360095 293577092938264613441040143)
  ·
    refine ⟨440365639407396920161560215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293577092938264613441040143 440365639407396920161560215)
    ·
      refine ⟨660548459111095380242340323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440365639407396920161560215 660548459111095380242340323)
      ·
        refine ⟨990822688666643070363510485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660548459111095380242340323 990822688666643070363510485)
        ·
          refine ⟨23222406765624446961644777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 990822688666643070363510485 23222406765624446961644777)
          ·
            refine ⟨17416805074218335221233583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23222406765624446961644777 17416805074218335221233583)
            ·
              refine ⟨26125207611327502831850375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17416805074218335221233583 26125207611327502831850375)
              ·
                refine ⟨39187811416991254247775563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26125207611327502831850375 39187811416991254247775563)
                ·
                  refine ⟨58781717125486881371663345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39187811416991254247775563 58781717125486881371663345)
                  ·
                    refine ⟨44086287844115161028747509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58781717125486881371663345 44086287844115161028747509)
                    ·
                      refine ⟨4133089485385796346445079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44086287844115161028747509 4133089485385796346445079)
                      ·
                        rfl

theorem cell23_8049163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_8049163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049163 prefixEnd_8049163 := by exact prefixLift 8049163
  have htrace : WordTrace (prefixWord ++ tailWord_8049163) baseStart_8049163 baseEnd_8049163 := by
    simpa [prefixWord, tailWord_8049163, baseEnd_8049163] using wordTrace_append hprefix tailTrace_8049163
  have hstable : (prefixWord ++ tailWord_8049163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049163).length < 2 ^ (prefixWord ++ tailWord_8049163).sum := by decide
  have hdescent : baseEnd_8049163 < baseStart_8049163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049173 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_8049173 : Nat := 118140960795 + 8049173 * 2 ^ 59
def prefixEnd_8049173 : Nat := 4983230072969 + 3 ^ 40 * 8049173 * 2
def baseEnd_8049173 : Nat := 4133094620192341307320033

theorem tailTrace_8049173 : CollatzResearch.WordTrace tailWord_8049173 prefixEnd_8049173 4133094620192341307320033 := by
  unfold tailWord_8049173
  simp only [CollatzResearch.WordTrace]
  refine ⟨293577457668228385148904173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195718305112152256765936115 293577457668228385148904173)
  ·
    refine ⟨110091546625585644430839065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293577457668228385148904173 110091546625585644430839065)
    ·
      refine ⟨82568659969189233323129299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110091546625585644430839065 82568659969189233323129299)
      ·
        refine ⟨123852989953783849984693949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82568659969189233323129299 123852989953783849984693949)
        ·
          refine ⟨46444871232668943744260231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123852989953783849984693949 46444871232668943744260231)
          ·
            refine ⟨69667306849003415616390347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46444871232668943744260231 69667306849003415616390347)
            ·
              refine ⟨104500960273505123424585521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69667306849003415616390347 104500960273505123424585521)
              ·
                refine ⟨78375720205128842568439141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104500960273505123424585521 78375720205128842568439141)
                ·
                  refine ⟨14695447538461657981582339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78375720205128842568439141 14695447538461657981582339)
                  ·
                    refine ⟨22043171307692486972373509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14695447538461657981582339 22043171307692486972373509)
                    ·
                      refine ⟨4133094620192341307320033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22043171307692486972373509 4133094620192341307320033)
                      ·
                        rfl

theorem cell23_8049173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_8049173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049173 prefixEnd_8049173 := by exact prefixLift 8049173
  have htrace : WordTrace (prefixWord ++ tailWord_8049173) baseStart_8049173 baseEnd_8049173 := by
    simpa [prefixWord, tailWord_8049173, baseEnd_8049173] using wordTrace_append hprefix tailTrace_8049173
  have hstable : (prefixWord ++ tailWord_8049173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049173).length < 2 ^ (prefixWord ++ tailWord_8049173).sum := by decide
  have hdescent : baseEnd_8049173 < baseStart_8049173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049183 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 5, 4]
def baseStart_8049183 : Nat := 118140960795 + 8049183 * 2 ^ 59
def prefixEnd_8049183 : Nat := 4983230072969 + 3 ^ 40 * 8049183 * 2
def baseEnd_8049183 : Nat := 1377699918332962089398329

theorem tailTrace_8049183 : CollatzResearch.WordTrace tailWord_8049183 prefixEnd_8049183 1377699918332962089398329 := by
  unfold tailWord_8049183
  simp only [CollatzResearch.WordTrace]
  refine ⟨293577822398192156856768203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195718548265461437904512135 293577822398192156856768203)
  ·
    refine ⟨440366733597288235285152305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293577822398192156856768203 440366733597288235285152305)
    ·
      refine ⟨330275050197966176463864229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440366733597288235285152305 330275050197966176463864229)
      ·
        refine ⟨61926571912118658086974543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330275050197966176463864229 61926571912118658086974543)
        ·
          refine ⟨92889857868177987130461815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61926571912118658086974543 92889857868177987130461815)
          ·
            refine ⟨139334786802266980695692723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92889857868177987130461815 139334786802266980695692723)
            ·
              refine ⟨209002180203400471043539085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139334786802266980695692723 209002180203400471043539085)
              ·
                refine ⟨78375817576275176641327157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209002180203400471043539085 78375817576275176641327157)
                ·
                  refine ⟨7347732897775797810124421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78375817576275176641327157 7347732897775797810124421)
                  ·
                    refine ⟨1377699918332962089398329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347732897775797810124421 1377699918332962089398329)
                    ·
                      rfl

theorem cell23_8049183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_8049183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049183 prefixEnd_8049183 := by exact prefixLift 8049183
  have htrace : WordTrace (prefixWord ++ tailWord_8049183) baseStart_8049183 baseEnd_8049183 := by
    simpa [prefixWord, tailWord_8049183, baseEnd_8049183] using wordTrace_append hprefix tailTrace_8049183
  have hstable : (prefixWord ++ tailWord_8049183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049183).length < 2 ^ (prefixWord ++ tailWord_8049183).sum := by decide
  have hdescent : baseEnd_8049183 < baseStart_8049183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049196 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 10]
def baseStart_8049196 : Nat := 118140960795 + 8049196 * 2 ^ 59
def prefixEnd_8049196 : Nat := 4983230072969 + 3 ^ 40 * 8049196 * 2
def baseEnd_8049196 : Nat := 459234047805266079703603

theorem tailTrace_8049196 : CollatzResearch.WordTrace tailWord_8049196 prefixEnd_8049196 459234047805266079703603 := by
  unfold tailWord_8049196
  simp only [CollatzResearch.WordTrace]
  refine ⟨146789148273572530038495721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195718864364763373384660961 146789148273572530038495721)
  ·
    refine ⟨110091861205179397528871791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146789148273572530038495721 110091861205179397528871791)
    ·
      refine ⟨165137791807769096293307687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110091861205179397528871791 165137791807769096293307687)
      ·
        refine ⟨247706687711653644439961531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165137791807769096293307687 247706687711653644439961531)
        ·
          refine ⟨371560031567480466659942297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247706687711653644439961531 371560031567480466659942297)
          ·
            refine ⟨278670023675610349994956723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371560031567480466659942297 278670023675610349994956723)
            ·
              refine ⟨418005035513415524992435085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278670023675610349994956723 418005035513415524992435085)
              ·
                refine ⟨156751888317530821872163157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418005035513415524992435085 156751888317530821872163157)
                ·
                  refine ⟨459234047805266079703603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156751888317530821872163157 459234047805266079703603)
                  ·
                    rfl

theorem cell23_8049196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_8049196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049196 prefixEnd_8049196 := by exact prefixLift 8049196
  have htrace : WordTrace (prefixWord ++ tailWord_8049196) baseStart_8049196 baseEnd_8049196 := by
    simpa [prefixWord, tailWord_8049196, baseEnd_8049196] using wordTrace_append hprefix tailTrace_8049196
  have hstable : (prefixWord ++ tailWord_8049196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049196).length < 2 ^ (prefixWord ++ tailWord_8049196).sum := by decide
  have hdescent : baseEnd_8049196 < baseStart_8049196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049210 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_8049210 : Nat := 118140960795 + 8049210 * 2 ^ 59
def prefixEnd_8049210 : Nat := 4983230072969 + 3 ^ 40 * 8049210 * 2
def baseEnd_8049210 : Nat := 4133113618976557662557363

theorem tailTrace_8049210 : CollatzResearch.WordTrace tailWord_8049210 prefixEnd_8049210 4133113618976557662557363 := by
  unfold tailWord_8049210
  simp only [CollatzResearch.WordTrace]
  refine ⟨73394701792273585117000271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195719204779396226978667389 73394701792273585117000271)
  ·
    refine ⟨110092052688410377675500407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73394701792273585117000271 110092052688410377675500407)
    ·
      refine ⟨165138079032615566513250611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110092052688410377675500407 165138079032615566513250611)
      ·
        refine ⟨247707118548923349769875917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165138079032615566513250611 247707118548923349769875917)
        ·
          refine ⟨92890169455846256163703469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247707118548923349769875917 92890169455846256163703469)
          ·
            refine ⟨34833813545942346061388801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92890169455846256163703469 34833813545942346061388801)
            ·
              refine ⟨26125360159456759546041601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34833813545942346061388801 26125360159456759546041601)
              ·
                refine ⟨19594020119592569659531201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26125360159456759546041601 19594020119592569659531201)
                ·
                  refine ⟨14695515089694427244648401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19594020119592569659531201 14695515089694427244648401)
                  ·
                    refine ⟨11021636317270820433486301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14695515089694427244648401 11021636317270820433486301)
                    ·
                      refine ⟨4133113618976557662557363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021636317270820433486301 4133113618976557662557363)
                      ·
                        rfl

theorem cell23_8049210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_8049210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049210 prefixEnd_8049210 := by exact prefixLift 8049210
  have htrace : WordTrace (prefixWord ++ tailWord_8049210) baseStart_8049210 baseEnd_8049210 := by
    simpa [prefixWord, tailWord_8049210, baseEnd_8049210] using wordTrace_append hprefix tailTrace_8049210
  have hstable : (prefixWord ++ tailWord_8049210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049210).length < 2 ^ (prefixWord ++ tailWord_8049210).sum := by decide
  have hdescent : baseEnd_8049210 < baseStart_8049210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049240 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_8049240 : Nat := 118140960795 + 8049240 * 2 ^ 59
def prefixEnd_8049240 : Nat := 4983230072969 + 3 ^ 40 * 8049240 * 2
def baseEnd_8049240 : Nat := 4133129023396192545182225

theorem tailTrace_8049240 : CollatzResearch.WordTrace tailWord_8049240 prefixEnd_8049240 4133129023396192545182225 := by
  unfold tailWord_8049240
  simp only [CollatzResearch.WordTrace]
  refine ⟨146789950679492827795796587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195719934239323770394395449 146789950679492827795796587)
  ·
    refine ⟨220184926019239241693694881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146789950679492827795796587 220184926019239241693694881)
    ·
      refine ⟨165138694514429431270271161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220184926019239241693694881 165138694514429431270271161)
      ·
        refine ⟨123854020885822073452703371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165138694514429431270271161 123854020885822073452703371)
        ·
          refine ⟨185781031328733110179055057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123854020885822073452703371 185781031328733110179055057)
          ·
            refine ⟨139335773496549832634291293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185781031328733110179055057 139335773496549832634291293)
            ·
              refine ⟨52250915061206187237859235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139335773496549832634291293 52250915061206187237859235)
              ·
                refine ⟨78376372591809280856788853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52250915061206187237859235 78376372591809280856788853)
                ·
                  refine ⟨7347784930482120080323955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78376372591809280856788853 7347784930482120080323955)
                  ·
                    refine ⟨11021677395723180120485933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7347784930482120080323955 11021677395723180120485933)
                    ·
                      refine ⟨4133129023396192545182225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021677395723180120485933 4133129023396192545182225)
                      ·
                        rfl

theorem cell23_8049240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_8049240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049240 prefixEnd_8049240 := by exact prefixLift 8049240
  have htrace : WordTrace (prefixWord ++ tailWord_8049240) baseStart_8049240 baseEnd_8049240 := by
    simpa [prefixWord, tailWord_8049240, baseEnd_8049240] using wordTrace_append hprefix tailTrace_8049240
  have hstable : (prefixWord ++ tailWord_8049240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049240).length < 2 ^ (prefixWord ++ tailWord_8049240).sum := by decide
  have hdescent : baseEnd_8049240 < baseStart_8049240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049244 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_8049244 : Nat := 118140960795 + 8049244 * 2 ^ 59
def prefixEnd_8049244 : Nat := 4983230072969 + 3 ^ 40 * 8049244 * 2
def baseEnd_8049244 : Nat := 4133131077318810529532207

theorem tailTrace_8049244 : CollatzResearch.WordTrace tailWord_8049244 prefixEnd_8049244 4133131077318810529532207 := by
  unfold tailWord_8049244
  simp only [CollatzResearch.WordTrace]
  refine ⟨146790023625485582137369393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195720031500647442849825857 146790023625485582137369393)
  ·
    refine ⟨110092517719114186603027045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146790023625485582137369393 110092517719114186603027045)
    ·
      refine ⟨20642347072333909988067571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110092517719114186603027045 20642347072333909988067571)
      ·
        refine ⟨30963520608500864982101357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20642347072333909988067571 30963520608500864982101357)
        ·
          refine ⟨11611320228187824368288009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30963520608500864982101357 11611320228187824368288009)
          ·
            refine ⟨8708490171140868276216007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611320228187824368288009 8708490171140868276216007)
            ·
              refine ⟨13062735256711302414324011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708490171140868276216007 13062735256711302414324011)
              ·
                refine ⟨19594102885066953621486017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13062735256711302414324011 19594102885066953621486017)
                ·
                  refine ⟨14695577163800215216114513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19594102885066953621486017 14695577163800215216114513)
                  ·
                    refine ⟨11021682872850161412085885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14695577163800215216114513 11021682872850161412085885)
                    ·
                      refine ⟨4133131077318810529532207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021682872850161412085885 4133131077318810529532207)
                      ·
                        rfl

theorem cell23_8049244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_8049244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049244 prefixEnd_8049244 := by exact prefixLift 8049244
  have htrace : WordTrace (prefixWord ++ tailWord_8049244) baseStart_8049244 baseEnd_8049244 := by
    simpa [prefixWord, tailWord_8049244, baseEnd_8049244] using wordTrace_append hprefix tailTrace_8049244
  have hstable : (prefixWord ++ tailWord_8049244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049244).length < 2 ^ (prefixWord ++ tailWord_8049244).sum := by decide
  have hdescent : baseEnd_8049244 < baseStart_8049244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049283 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_8049283 : Nat := 118140960795 + 8049283 * 2 ^ 59
def prefixEnd_8049283 : Nat := 4983230072969 + 3 ^ 40 * 8049283 * 2
def baseEnd_8049283 : Nat := 4133151103064335876944527

theorem tailTrace_8049283 : CollatzResearch.WordTrace tailWord_8049283 prefixEnd_8049283 4133151103064335876944527 := by
  unfold tailWord_8049283
  simp only [CollatzResearch.WordTrace]
  refine ⟨293581469697829873935408503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195720979798553249290272335 293581469697829873935408503)
  ·
    refine ⟨440372204546744810903112755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293581469697829873935408503 440372204546744810903112755)
    ·
      refine ⟨660558306820117216354669133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440372204546744810903112755 660558306820117216354669133)
      ·
        refine ⟨247709365057543956133000925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 660558306820117216354669133 247709365057543956133000925)
        ·
          refine ⟨92891011896578983549875347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247709365057543956133000925 92891011896578983549875347)
          ·
            refine ⟨139336517844868475324813021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92891011896578983549875347 139336517844868475324813021)
            ·
              refine ⟨52251194191825678246804883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139336517844868475324813021 52251194191825678246804883)
              ·
                refine ⟨78376791287738517370207325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52251194191825678246804883 78376791287738517370207325)
                ·
                  refine ⟨29391296732901944013827747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78376791287738517370207325 29391296732901944013827747)
                  ·
                    refine ⟨44086945099352916020741621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29391296732901944013827747 44086945099352916020741621)
                    ·
                      refine ⟨4133151103064335876944527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44086945099352916020741621 4133151103064335876944527)
                      ·
                        rfl

theorem cell23_8049283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_8049283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049283 prefixEnd_8049283 := by exact prefixLift 8049283
  have htrace : WordTrace (prefixWord ++ tailWord_8049283) baseStart_8049283 baseEnd_8049283 := by
    simpa [prefixWord, tailWord_8049283, baseEnd_8049283] using wordTrace_append hprefix tailTrace_8049283
  have hstable : (prefixWord ++ tailWord_8049283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049283).length < 2 ^ (prefixWord ++ tailWord_8049283).sum := by decide
  have hdescent : baseEnd_8049283 < baseStart_8049283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049303 : List Nat := [1, 1, 3, 3, 2, 1, 3, 9]
def baseStart_8049303 : Nat := 118140960795 + 8049303 * 2 ^ 59
def prefixEnd_8049303 : Nat := 4983230072969 + 3 ^ 40 * 8049303 * 2
def baseEnd_8049303 : Nat := 153080050839904659210905

theorem tailTrace_8049303 : CollatzResearch.WordTrace tailWord_8049303 prefixEnd_8049303 153080050839904659210905 := by
  unfold tailWord_8049303
  simp only [CollatzResearch.WordTrace]
  refine ⟨293582199157757417351136563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195721466105171611567424375 293582199157757417351136563)
  ·
    refine ⟨440373298736636126026704845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293582199157757417351136563 440373298736636126026704845)
    ·
      refine ⟨165139987026238547260014317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440373298736636126026704845 165139987026238547260014317)
      ·
        refine ⟨61927495134839455222505369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165139987026238547260014317 61927495134839455222505369)
        ·
          refine ⟨46445621351129591416879027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61927495134839455222505369 46445621351129591416879027)
          ·
            refine ⟨69668432026694387125318541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46445621351129591416879027 69668432026694387125318541)
            ·
              refine ⟨26125662010010395171994453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69668432026694387125318541 26125662010010395171994453)
              ·
                refine ⟨153080050839904659210905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26125662010010395171994453 153080050839904659210905)
                ·
                  rfl

theorem cell23_8049303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 9].length) (baseStart_8049303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049303 prefixEnd_8049303 := by exact prefixLift 8049303
  have htrace : WordTrace (prefixWord ++ tailWord_8049303) baseStart_8049303 baseEnd_8049303 := by
    simpa [prefixWord, tailWord_8049303, baseEnd_8049303] using wordTrace_append hprefix tailTrace_8049303
  have hstable : (prefixWord ++ tailWord_8049303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049303).length < 2 ^ (prefixWord ++ tailWord_8049303).sum := by decide
  have hdescent : baseEnd_8049303 < baseStart_8049303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049364 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8049364 : Nat := 118140960795 + 8049364 * 2 ^ 59
def prefixEnd_8049364 : Nat := 4983230072969 + 3 ^ 40 * 8049364 * 2
def baseEnd_8049364 : Nat := 4133192694997350060031655

theorem tailTrace_8049364 : CollatzResearch.WordTrace tailWord_8049364 prefixEnd_8049364 4133192694997350060031655 := by
  unfold tailWord_8049364
  simp only [CollatzResearch.WordTrace]
  refine ⟨146792212005268212384553573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195722949340357616512738097 146792212005268212384553573)
  ·
    refine ⟨27523539750987789822103795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146792212005268212384553573 27523539750987789822103795)
    ·
      refine ⟨41285309626481684733155693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27523539750987789822103795 41285309626481684733155693)
      ·
        refine ⟨15481991109930631774933385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41285309626481684733155693 15481991109930631774933385)
        ·
          refine ⟨11611493332447973831200039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15481991109930631774933385 11611493332447973831200039)
          ·
            refine ⟨17417239998671960746800059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11611493332447973831200039 17417239998671960746800059)
            ·
              refine ⟨26125859998007941120200089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17417239998671960746800059 26125859998007941120200089)
              ·
                refine ⟨19594394998505955840150067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26125859998007941120200089 19594394998505955840150067)
                ·
                  refine ⟨29391592497758933760225101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19594394998505955840150067 29391592497758933760225101)
                  ·
                    refine ⟨11021847186659600160084413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29391592497758933760225101 11021847186659600160084413)
                    ·
                      refine ⟨4133192694997350060031655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021847186659600160084413 4133192694997350060031655)
                      ·
                        rfl

theorem cell23_8049364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8049364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049364 prefixEnd_8049364 := by exact prefixLift 8049364
  have htrace : WordTrace (prefixWord ++ tailWord_8049364) baseStart_8049364 baseEnd_8049364 := by
    simpa [prefixWord, tailWord_8049364, baseEnd_8049364] using wordTrace_append hprefix tailTrace_8049364
  have hstable : (prefixWord ++ tailWord_8049364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049364).length < 2 ^ (prefixWord ++ tailWord_8049364).sum := by decide
  have hdescent : baseEnd_8049364 < baseStart_8049364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049400 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_8049400 : Nat := 118140960795 + 8049400 * 2 ^ 59
def prefixEnd_8049400 : Nat := 4983230072969 + 3 ^ 40 * 8049400 * 2
def baseEnd_8049400 : Nat := 4133211180300911919181489

theorem tailTrace_8049400 : CollatzResearch.WordTrace tailWord_8049400 prefixEnd_8049400 4133211180300911919181489 := by
  unfold tailWord_8049400
  simp only [CollatzResearch.WordTrace]
  refine ⟨146792868519203001458708827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195723824692270668611611769 146792868519203001458708827)
  ·
    refine ⟨220189302778804502188063241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146792868519203001458708827 220189302778804502188063241)
    ·
      refine ⟨165141977084103376641047431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220189302778804502188063241 165141977084103376641047431)
      ·
        refine ⟨247712965626155064961571147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165141977084103376641047431 247712965626155064961571147)
        ·
          refine ⟨371569448439232597442356721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247712965626155064961571147 371569448439232597442356721)
          ·
            refine ⟨278677086329424448081767541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371569448439232597442356721 278677086329424448081767541)
            ·
              refine ⟨26125976843383542007665707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278677086329424448081767541 26125976843383542007665707)
              ·
                refine ⟨39188965265075313011498561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26125976843383542007665707 39188965265075313011498561)
                ·
                  refine ⟨29391723948806484758623921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39188965265075313011498561 29391723948806484758623921)
                  ·
                    refine ⟨22043792961604863568967941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29391723948806484758623921 22043792961604863568967941)
                    ·
                      refine ⟨4133211180300911919181489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22043792961604863568967941 4133211180300911919181489)
                      ·
                        rfl

theorem cell23_8049400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_8049400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049400 prefixEnd_8049400 := by exact prefixLift 8049400
  have htrace : WordTrace (prefixWord ++ tailWord_8049400) baseStart_8049400 baseEnd_8049400 := by
    simpa [prefixWord, tailWord_8049400, baseEnd_8049400] using wordTrace_append hprefix tailTrace_8049400
  have hstable : (prefixWord ++ tailWord_8049400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049400).length < 2 ^ (prefixWord ++ tailWord_8049400).sum := by decide
  have hdescent : baseEnd_8049400 < baseStart_8049400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049403 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_8049403 : Nat := 118140960795 + 8049403 * 2 ^ 59
def prefixEnd_8049403 : Nat := 4983230072969 + 3 ^ 40 * 8049403 * 2
def baseEnd_8049403 : Nat := 4133212720742875407443975

theorem tailTrace_8049403 : CollatzResearch.WordTrace tailWord_8049403 prefixEnd_8049403 4133212720742875407443975 := by
  unfold tailWord_8049403
  simp only [CollatzResearch.WordTrace]
  refine ⟨293585846457395134429776863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195723897638263422953184575 293585846457395134429776863)
  ·
    refine ⟨440378769686092701644665295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293585846457395134429776863 440378769686092701644665295)
    ·
      refine ⟨660568154529139052466997943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440378769686092701644665295 660568154529139052466997943)
      ·
        refine ⟨990852231793708578700496915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660568154529139052466997943 990852231793708578700496915)
        ·
          refine ⟨1486278347690562868050745373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990852231793708578700496915 1486278347690562868050745373)
          ·
            refine ⟨557354380383961075519029515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1486278347690562868050745373 557354380383961075519029515)
            ·
              refine ⟨836031570575941613278544273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557354380383961075519029515 836031570575941613278544273)
              ·
                refine ⟨627023677931956209958908205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836031570575941613278544273 627023677931956209958908205)
                ·
                  refine ⟨235133879224483578734590577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627023677931956209958908205 235133879224483578734590577)
                  ·
                    refine ⟨176350409418362684050942933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235133879224483578734590577 176350409418362684050942933)
                    ·
                      refine ⟨4133212720742875407443975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176350409418362684050942933 4133212720742875407443975)
                      ·
                        rfl

theorem cell23_8049403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_8049403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049403 prefixEnd_8049403 := by exact prefixLift 8049403
  have htrace : WordTrace (prefixWord ++ tailWord_8049403) baseStart_8049403 baseEnd_8049403 := by
    simpa [prefixWord, tailWord_8049403, baseEnd_8049403] using wordTrace_append hprefix tailTrace_8049403
  have hstable : (prefixWord ++ tailWord_8049403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049403).length < 2 ^ (prefixWord ++ tailWord_8049403).sum := by decide
  have hdescent : baseEnd_8049403 < baseStart_8049403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049404 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_8049404 : Nat := 118140960795 + 8049404 * 2 ^ 59
def prefixEnd_8049404 : Nat := 4983230072969 + 3 ^ 40 * 8049404 * 2
def baseEnd_8049404 : Nat := 4133213234223529903531471

theorem tailTrace_8049404 : CollatzResearch.WordTrace tailWord_8049404 prefixEnd_8049404 4133213234223529903531471 := by
  unfold tailWord_8049404
  simp only [CollatzResearch.WordTrace]
  refine ⟨146792941465195755800281633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195723921953594341067042177 146792941465195755800281633)
  ·
    refine ⟨110094706098896816850211225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146792941465195755800281633 110094706098896816850211225)
    ·
      refine ⟨82571029574172612637658419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110094706098896816850211225 82571029574172612637658419)
      ·
        refine ⟨123856544361258918956487629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82571029574172612637658419 123856544361258918956487629)
        ·
          refine ⟨46446204135472094608682861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123856544361258918956487629 46446204135472094608682861)
          ·
            refine ⟨17417326550802035478256073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46446204135472094608682861 17417326550802035478256073)
            ·
              refine ⟨13062994913101526608692055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17417326550802035478256073 13062994913101526608692055)
              ·
                refine ⟨19594492369652289913038083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13062994913101526608692055 19594492369652289913038083)
                ·
                  refine ⟨29391738554478434869557125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19594492369652289913038083 29391738554478434869557125)
                  ·
                    refine ⟨5510950978964706538041961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29391738554478434869557125 5510950978964706538041961)
                    ·
                      refine ⟨4133213234223529903531471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510950978964706538041961 4133213234223529903531471)
                      ·
                        rfl

theorem cell23_8049404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_8049404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049404 prefixEnd_8049404 := by exact prefixLift 8049404
  have htrace : WordTrace (prefixWord ++ tailWord_8049404) baseStart_8049404 baseEnd_8049404 := by
    simpa [prefixWord, tailWord_8049404, baseEnd_8049404] using wordTrace_append hprefix tailTrace_8049404
  have hstable : (prefixWord ++ tailWord_8049404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049404).length < 2 ^ (prefixWord ++ tailWord_8049404).sum := by decide
  have hdescent : baseEnd_8049404 < baseStart_8049404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049420 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_8049420 : Nat := 118140960795 + 8049420 * 2 ^ 59
def prefixEnd_8049420 : Nat := 4983230072969 + 3 ^ 40 * 8049420 * 2
def baseEnd_8049420 : Nat := 4133221449914001840931397

theorem tailTrace_8049420 : CollatzResearch.WordTrace tailWord_8049420 prefixEnd_8049420 4133221449914001840931397 := by
  unfold tailWord_8049420
  simp only [CollatzResearch.WordTrace]
  refine ⟨146793233249166773166572857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195724310998889030888763809 146793233249166773166572857)
  ·
    refine ⟨110094924936875079874929643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146793233249166773166572857 110094924936875079874929643)
    ·
      refine ⟨165142387405312619812394465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110094924936875079874929643 165142387405312619812394465)
      ·
        refine ⟨123856790553984464859295849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165142387405312619812394465 123856790553984464859295849)
        ·
          refine ⟨92892592915488348644471887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123856790553984464859295849 92892592915488348644471887)
          ·
            refine ⟨139338889373232522966707831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92892592915488348644471887 139338889373232522966707831)
            ·
              refine ⟨209008334059848784450061747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139338889373232522966707831 209008334059848784450061747)
              ·
                refine ⟨313512501089773176675092621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209008334059848784450061747 313512501089773176675092621)
                ·
                  refine ⟨117567187908664941253159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313512501089773176675092621 117567187908664941253159733)
                  ·
                    refine ⟨11021923866437338242483725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117567187908664941253159733 11021923866437338242483725)
                    ·
                      refine ⟨4133221449914001840931397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021923866437338242483725 4133221449914001840931397)
                      ·
                        rfl

theorem cell23_8049420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_8049420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049420 prefixEnd_8049420 := by exact prefixLift 8049420
  have htrace : WordTrace (prefixWord ++ tailWord_8049420) baseStart_8049420 baseEnd_8049420 := by
    simpa [prefixWord, tailWord_8049420, baseEnd_8049420] using wordTrace_append hprefix tailTrace_8049420
  have hstable : (prefixWord ++ tailWord_8049420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049420).length < 2 ^ (prefixWord ++ tailWord_8049420).sum := by decide
  have hdescent : baseEnd_8049420 < baseStart_8049420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049427 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 5]
def baseStart_8049427 : Nat := 118140960795 + 8049427 * 2 ^ 59
def prefixEnd_8049427 : Nat := 4983230072969 + 3 ^ 40 * 8049427 * 2
def baseEnd_8049427 : Nat := 459247227142064812615985

theorem tailTrace_8049427 : CollatzResearch.WordTrace tailWord_8049427 prefixEnd_8049427 459247227142064812615985 := by
  unfold tailWord_8049427
  simp only [CollatzResearch.WordTrace]
  refine ⟨293586721809308186528650535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195724481206205457685767023 293586721809308186528650535)
  ·
    refine ⟨440380082713962279792975803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293586721809308186528650535 440380082713962279792975803)
    ·
      refine ⟨660570124070943419689463705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440380082713962279792975803 660570124070943419689463705)
      ·
        refine ⟨495427593053207564767097779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660570124070943419689463705 495427593053207564767097779)
        ·
          refine ⟨743141389579811347150646669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495427593053207564767097779 743141389579811347150646669)
          ·
            refine ⟨278678021092429255181492501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743141389579811347150646669 278678021092429255181492501)
            ·
              refine ⟨13063032238707621336632461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278678021092429255181492501 13063032238707621336632461)
              ·
                refine ⟨4898637089515358001237173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13063032238707621336632461 4898637089515358001237173)
                ·
                  refine ⟨459247227142064812615985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4898637089515358001237173 459247227142064812615985)
                  ·
                    rfl

theorem cell23_8049427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 5].length) (baseStart_8049427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049427 prefixEnd_8049427 := by exact prefixLift 8049427
  have htrace : WordTrace (prefixWord ++ tailWord_8049427) baseStart_8049427 baseEnd_8049427 := by
    simpa [prefixWord, tailWord_8049427, baseEnd_8049427] using wordTrace_append hprefix tailTrace_8049427
  have hstable : (prefixWord ++ tailWord_8049427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049427).length < 2 ^ (prefixWord ++ tailWord_8049427).sum := by decide
  have hdescent : baseEnd_8049427 < baseStart_8049427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049454 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_8049454 : Nat := 118140960795 + 8049454 * 2 ^ 59
def prefixEnd_8049454 : Nat := 4983230072969 + 3 ^ 40 * 8049454 * 2
def baseEnd_8049454 : Nat := 4133238908256254707906241

theorem tailTrace_8049454 : CollatzResearch.WordTrace tailWord_8049454 prefixEnd_8049454 4133238908256254707906241 := by
  unfold tailWord_8049454
  simp only [CollatzResearch.WordTrace]
  refine ⟨36698463322526296267485427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195725137720140246759922277 36698463322526296267485427)
  ·
    refine ⟨55047694983789444401228141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36698463322526296267485427 55047694983789444401228141)
    ·
      refine ⟨20642885618921041650460553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55047694983789444401228141 20642885618921041650460553)
      ·
        refine ⟨15482164214190781237845415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20642885618921041650460553 15482164214190781237845415)
        ·
          refine ⟨23223246321286171856768123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482164214190781237845415 23223246321286171856768123)
          ·
            refine ⟨34834869481929257785152185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23223246321286171856768123 34834869481929257785152185)
            ·
              refine ⟨26126152111446943338864139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34834869481929257785152185 26126152111446943338864139)
              ·
                refine ⟨39189228167170415008296209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26126152111446943338864139 39189228167170415008296209)
                ·
                  refine ⟨29391921125377811256222157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39189228167170415008296209 29391921125377811256222157)
                  ·
                    refine ⟨11021970422016679221083309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29391921125377811256222157 11021970422016679221083309)
                    ·
                      refine ⟨4133238908256254707906241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021970422016679221083309 4133238908256254707906241)
                      ·
                        rfl

theorem cell23_8049454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_8049454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049454 prefixEnd_8049454 := by exact prefixLift 8049454
  have htrace : WordTrace (prefixWord ++ tailWord_8049454) baseStart_8049454 baseEnd_8049454 := by
    simpa [prefixWord, tailWord_8049454, baseEnd_8049454] using wordTrace_append hprefix tailTrace_8049454
  have hstable : (prefixWord ++ tailWord_8049454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049454).length < 2 ^ (prefixWord ++ tailWord_8049454).sum := by decide
  have hdescent : baseEnd_8049454 < baseStart_8049454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049477 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_8049477 : Nat := 118140960795 + 8049477 * 2 ^ 59
def prefixEnd_8049477 : Nat := 4983230072969 + 3 ^ 40 * 8049477 * 2
def baseEnd_8049477 : Nat := 4133250718311308117918635

theorem tailTrace_8049477 : CollatzResearch.WordTrace tailWord_8049477 prefixEnd_8049477 4133250718311308117918635 := by
  unfold tailWord_8049477
  simp only [CollatzResearch.WordTrace]
  refine ⟨293588545459127045067970685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195725696972751363378647123 293588545459127045067970685)
  ·
    refine ⟨110095704547172641900489007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293588545459127045067970685 110095704547172641900489007)
    ·
      refine ⟨165143556820758962850733511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110095704547172641900489007 165143556820758962850733511)
      ·
        refine ⟨247715335231138444276100267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165143556820758962850733511 247715335231138444276100267)
        ·
          refine ⟨371573002846707666414150401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247715335231138444276100267 371573002846707666414150401)
          ·
            refine ⟨278679752135030749810612801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371573002846707666414150401 278679752135030749810612801)
            ·
              refine ⟨209009814101273062357959601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278679752135030749810612801 209009814101273062357959601)
              ·
                refine ⟨156757360575954796768469701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209009814101273062357959601 156757360575954796768469701)
                ·
                  refine ⟨29392005107991524394088069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156757360575954796768469701 29392005107991524394088069)
                  ·
                    refine ⟨5511000957748410823891513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29392005107991524394088069 5511000957748410823891513)
                    ·
                      refine ⟨4133250718311308117918635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511000957748410823891513 4133250718311308117918635)
                      ·
                        rfl

theorem cell23_8049477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_8049477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049477 prefixEnd_8049477 := by exact prefixLift 8049477
  have htrace : WordTrace (prefixWord ++ tailWord_8049477) baseStart_8049477 baseEnd_8049477 := by
    simpa [prefixWord, tailWord_8049477, baseEnd_8049477] using wordTrace_append hprefix tailTrace_8049477
  have hstable : (prefixWord ++ tailWord_8049477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049477).length < 2 ^ (prefixWord ++ tailWord_8049477).sum := by decide
  have hdescent : baseEnd_8049477 < baseStart_8049477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049497 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_8049497 : Nat := 118140960795 + 8049497 * 2 ^ 59
def prefixEnd_8049497 : Nat := 4983230072969 + 3 ^ 40 * 8049497 * 2
def baseEnd_8049497 : Nat := 4133260987924398039668543

theorem tailTrace_8049497 : CollatzResearch.WordTrace tailWord_8049497 prefixEnd_8049497 4133260987924398039668543 := by
  unfold tailWord_8049497
  simp only [CollatzResearch.WordTrace]
  refine ⟨293589274919054588483698745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195726183279369725655799163 293589274919054588483698745)
  ·
    refine ⟨220191956189290941362774059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293589274919054588483698745 220191956189290941362774059)
    ·
      refine ⟨330287934283936412044161089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220191956189290941362774059 330287934283936412044161089)
      ·
        refine ⟨247715950712952309033120817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330287934283936412044161089 247715950712952309033120817)
        ·
          refine ⟨185786963034714231774840613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247715950712952309033120817 185786963034714231774840613)
          ·
            refine ⟨34835055569008918457782615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185786963034714231774840613 34835055569008918457782615)
            ·
              refine ⟨52252583353513377686673923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34835055569008918457782615 52252583353513377686673923)
              ·
                refine ⟨78378875030270066530010885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52252583353513377686673923 78378875030270066530010885)
                ·
                  refine ⟨14696039068175637474377041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78378875030270066530010885 14696039068175637474377041)
                  ·
                    refine ⟨11022029301131728105782781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14696039068175637474377041 11022029301131728105782781)
                    ·
                      refine ⟨4133260987924398039668543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11022029301131728105782781 4133260987924398039668543)
                      ·
                        rfl

theorem cell23_8049497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_8049497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049497 prefixEnd_8049497 := by exact prefixLift 8049497
  have htrace : WordTrace (prefixWord ++ tailWord_8049497) baseStart_8049497 baseEnd_8049497 := by
    simpa [prefixWord, tailWord_8049497, baseEnd_8049497] using wordTrace_append hprefix tailTrace_8049497
  have hstable : (prefixWord ++ tailWord_8049497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049497).length < 2 ^ (prefixWord ++ tailWord_8049497).sum := by decide
  have hdescent : baseEnd_8049497 < baseStart_8049497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049520 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_8049520 : Nat := 118140960795 + 8049520 * 2 ^ 59
def prefixEnd_8049520 : Nat := 4983230072969 + 3 ^ 40 * 8049520 * 2
def baseEnd_8049520 : Nat := 4133272797979451449680937

theorem tailTrace_8049520 : CollatzResearch.WordTrace tailWord_8049520 prefixEnd_8049520 4133272797979451449680937 := by
  unfold tailWord_8049520
  simp only [CollatzResearch.WordTrace]
  refine ⟨146795056898985631705893007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195726742531980842274524009 146795056898985631705893007)
  ·
    refine ⟨220192585348478447558839511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146795056898985631705893007 220192585348478447558839511)
    ·
      refine ⟨330288878022717671338259267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220192585348478447558839511 330288878022717671338259267)
      ·
        refine ⟨495433317034076507007388901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330288878022717671338259267 495433317034076507007388901)
        ·
          refine ⟨92893746943889345063885419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495433317034076507007388901 92893746943889345063885419)
          ·
            refine ⟨139340620415834017595828129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92893746943889345063885419 139340620415834017595828129)
            ·
              refine ⟨104505465311875513196871097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139340620415834017595828129 104505465311875513196871097)
              ·
                refine ⟨78379098983906634897653323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104505465311875513196871097 78379098983906634897653323)
                ·
                  refine ⟨117568648475859952346479985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78379098983906634897653323 117568648475859952346479985)
                  ·
                    refine ⟨88176486356894964259859989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117568648475859952346479985 88176486356894964259859989)
                    ·
                      refine ⟨4133272797979451449680937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88176486356894964259859989 4133272797979451449680937)
                      ·
                        rfl

theorem cell23_8049520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_8049520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049520 prefixEnd_8049520 := by exact prefixLift 8049520
  have htrace : WordTrace (prefixWord ++ tailWord_8049520) baseStart_8049520 baseEnd_8049520 := by
    simpa [prefixWord, tailWord_8049520, baseEnd_8049520] using wordTrace_append hprefix tailTrace_8049520
  have hstable : (prefixWord ++ tailWord_8049520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049520).length < 2 ^ (prefixWord ++ tailWord_8049520).sum := by decide
  have hdescent : baseEnd_8049520 < baseStart_8049520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049547 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 1, 5]
def baseStart_8049547 : Nat := 118140960795 + 8049547 * 2 ^ 59
def prefixEnd_8049547 : Nat := 4983230072969 + 3 ^ 40 * 8049547 * 2
def baseEnd_8049547 : Nat := 1377762220652374281347771

theorem tailTrace_8049547 : CollatzResearch.WordTrace tailWord_8049547 prefixEnd_8049547 1377762220652374281347771 := by
  unfold tailWord_8049547
  simp only [CollatzResearch.WordTrace]
  refine ⟨293591098568873447023018895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195727399045915631348679263 293591098568873447023018895)
  ·
    refine ⟨440386647853310170534528343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293591098568873447023018895 440386647853310170534528343)
    ·
      refine ⟨660579971779965255801792515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440386647853310170534528343 660579971779965255801792515)
      ·
        refine ⟨990869957669947883702688773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660579971779965255801792515 990869957669947883702688773)
        ·
          refine ⟨185788117063115228194254145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 990869957669947883702688773 185788117063115228194254145)
          ·
            refine ⟨139341087797336421145690609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185788117063115228194254145 139341087797336421145690609)
            ·
              refine ⟨104505815848002315859267957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139341087797336421145690609 104505815848002315859267957)
              ·
                refine ⟨9797420235750217111806371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104505815848002315859267957 9797420235750217111806371)
                ·
                  refine ⟨14696130353625325667709557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797420235750217111806371 14696130353625325667709557)
                  ·
                    refine ⟨1377762220652374281347771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14696130353625325667709557 1377762220652374281347771)
                    ·
                      rfl

theorem cell23_8049547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 5].length) (baseStart_8049547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049547 prefixEnd_8049547 := by exact prefixLift 8049547
  have htrace : WordTrace (prefixWord ++ tailWord_8049547) baseStart_8049547 baseEnd_8049547 := by
    simpa [prefixWord, tailWord_8049547, baseEnd_8049547] using wordTrace_append hprefix tailTrace_8049547
  have hstable : (prefixWord ++ tailWord_8049547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049547).length < 2 ^ (prefixWord ++ tailWord_8049547).sum := by decide
  have hdescent : baseEnd_8049547 < baseStart_8049547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049577 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_8049577 : Nat := 118140960795 + 8049577 * 2 ^ 59
def prefixEnd_8049577 : Nat := 4983230072969 + 3 ^ 40 * 8049577 * 2
def baseEnd_8049577 : Nat := 1377767355458919242222725

theorem tailTrace_8049577 : CollatzResearch.WordTrace tailWord_8049577 prefixEnd_8049577 1377767355458919242222725 := by
  unfold tailWord_8049577
  simp only [CollatzResearch.WordTrace]
  refine ⟨293592192758764762146610985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195728128505843174764407323 293592192758764762146610985)
  ·
    refine ⟨220194144569073571609958239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293592192758764762146610985 220194144569073571609958239)
    ·
      refine ⟨330291216853610357414937359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220194144569073571609958239 330291216853610357414937359)
      ·
        refine ⟨495436825280415536122406039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330291216853610357414937359 495436825280415536122406039)
        ·
          refine ⟨743155237920623304183609059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495436825280415536122406039 743155237920623304183609059)
          ·
            refine ⟨1114732856880934956275413589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743155237920623304183609059 1114732856880934956275413589)
            ·
              refine ⟨13063275666573456518852503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1114732856880934956275413589 13063275666573456518852503)
              ·
                refine ⟨19594913499860184778278755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13063275666573456518852503 19594913499860184778278755)
                ·
                  refine ⟨29392370249790277167418133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19594913499860184778278755 29392370249790277167418133)
                  ·
                    refine ⟨1377767355458919242222725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29392370249790277167418133 1377767355458919242222725)
                    ·
                      rfl

theorem cell23_8049577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_8049577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049577 prefixEnd_8049577 := by exact prefixLift 8049577
  have htrace : WordTrace (prefixWord ++ tailWord_8049577) baseStart_8049577 baseEnd_8049577 := by
    simpa [prefixWord, tailWord_8049577, baseEnd_8049577] using wordTrace_append hprefix tailTrace_8049577
  have hstable : (prefixWord ++ tailWord_8049577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049577).length < 2 ^ (prefixWord ++ tailWord_8049577).sum := by decide
  have hdescent : baseEnd_8049577 < baseStart_8049577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049588 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_8049588 : Nat := 118140960795 + 8049588 * 2 ^ 59
def prefixEnd_8049588 : Nat := 4983230072969 + 3 ^ 40 * 8049588 * 2
def baseEnd_8049588 : Nat := 4133307714663957183630625

theorem tailTrace_8049588 : CollatzResearch.WordTrace tailWord_8049588 prefixEnd_8049588 4133307714663957183630625 := by
  unfold tailWord_8049588
  simp only [CollatzResearch.WordTrace]
  refine ⟨146796296980862455512630709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195728395974483274016840945 146796296980862455512630709)
  ·
    refine ⟨13762152841955855204309129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146796296980862455512630709 13762152841955855204309129)
    ·
      refine ⟨10321614631466891403231847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13762152841955855204309129 10321614631466891403231847)
      ·
        refine ⟨15482421947200337104847771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10321614631466891403231847 15482421947200337104847771)
        ·
          refine ⟨23223632920800505657271657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482421947200337104847771 23223632920800505657271657)
          ·
            refine ⟨17417724690600379242953743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23223632920800505657271657 17417724690600379242953743)
            ·
              refine ⟨26126587035900568864430615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17417724690600379242953743 26126587035900568864430615)
              ·
                refine ⟨39189880553850853296645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26126587035900568864430615 39189880553850853296645923)
                ·
                  refine ⟨58784820830776279944968885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39189880553850853296645923 58784820830776279944968885)
                  ·
                    refine ⟨5511076952885276244840833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58784820830776279944968885 5511076952885276244840833)
                    ·
                      refine ⟨4133307714663957183630625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511076952885276244840833 4133307714663957183630625)
                      ·
                        rfl

theorem cell23_8049588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_8049588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049588 prefixEnd_8049588 := by exact prefixLift 8049588
  have htrace : WordTrace (prefixWord ++ tailWord_8049588) baseStart_8049588 baseEnd_8049588 := by
    simpa [prefixWord, tailWord_8049588, baseEnd_8049588] using wordTrace_append hprefix tailTrace_8049588
  have hstable : (prefixWord ++ tailWord_8049588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049588).length < 2 ^ (prefixWord ++ tailWord_8049588).sum := by decide
  have hdescent : baseEnd_8049588 < baseStart_8049588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049611 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 2, 4]
def baseStart_8049611 : Nat := 118140960795 + 8049611 * 2 ^ 59
def prefixEnd_8049611 : Nat := 4983230072969 + 3 ^ 40 * 8049611 * 2
def baseEnd_8049611 : Nat := 1377773174906336864547673

theorem tailTrace_8049611 : CollatzResearch.WordTrace tailWord_8049611 prefixEnd_8049611 1377773174906336864547673 := by
  unfold tailWord_8049611
  simp only [CollatzResearch.WordTrace]
  refine ⟨293593432840641585953348687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195728955227094390635565791 293593432840641585953348687)
  ·
    refine ⟨440390149260962378930023031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293593432840641585953348687 440390149260962378930023031)
    ·
      refine ⟨660585223891443568395034547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440390149260962378930023031 660585223891443568395034547)
      ·
        refine ⟨990877835837165352592551821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660585223891443568395034547 990877835837165352592551821)
        ·
          refine ⟨371579188438937007222206933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 990877835837165352592551821 371579188438937007222206933)
          ·
            refine ⟨8708887229037586106770475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 371579188438937007222206933 8708887229037586106770475)
            ·
              refine ⟨13063330843556379160155713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708887229037586106770475 13063330843556379160155713)
              ·
                refine ⟨9797498132667284370116785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13063330843556379160155713 9797498132667284370116785)
                ·
                  refine ⟨7348123599500463277587589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797498132667284370116785 7348123599500463277587589)
                  ·
                    refine ⟨1377773174906336864547673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348123599500463277587589 1377773174906336864547673)
                    ·
                      rfl

theorem cell23_8049611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 4].length) (baseStart_8049611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049611 prefixEnd_8049611 := by exact prefixLift 8049611
  have htrace : WordTrace (prefixWord ++ tailWord_8049611) baseStart_8049611 baseEnd_8049611 := by
    simpa [prefixWord, tailWord_8049611, baseEnd_8049611] using wordTrace_append hprefix tailTrace_8049611
  have hstable : (prefixWord ++ tailWord_8049611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049611).length < 2 ^ (prefixWord ++ tailWord_8049611).sum := by decide
  have hdescent : baseEnd_8049611 < baseStart_8049611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049618 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_8049618 : Nat := 118140960795 + 8049618 * 2 ^ 59
def prefixEnd_8049618 : Nat := 4983230072969 + 3 ^ 40 * 8049618 * 2
def baseEnd_8049618 : Nat := 4133323119083592066255487

theorem tailTrace_8049618 : CollatzResearch.WordTrace tailWord_8049618 prefixEnd_8049618 4133323119083592066255487 := by
  unfold tailWord_8049618
  simp only [CollatzResearch.WordTrace]
  refine ⟨73398422037904056537213377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195729125434410817432569005 73398422037904056537213377)
  ·
    refine ⟨55048816528428042402910033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73398422037904056537213377 55048816528428042402910033)
    ·
      refine ⟨41286612396321031802182525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55048816528428042402910033 41286612396321031802182525)
      ·
        refine ⟨15482479648620386925818447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41286612396321031802182525 15482479648620386925818447)
        ·
          refine ⟨23223719472930580388727671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482479648620386925818447 23223719472930580388727671)
          ·
            refine ⟨34835579209395870583091507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23223719472930580388727671 34835579209395870583091507)
            ·
              refine ⟨52253368814093805874637261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34835579209395870583091507 52253368814093805874637261)
              ·
                refine ⟨19595013305285177202988973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52253368814093805874637261 19595013305285177202988973)
                ·
                  refine ⟨7348129989481941451120865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19595013305285177202988973 7348129989481941451120865)
                  ·
                    refine ⟨5511097492111456088340649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348129989481941451120865 5511097492111456088340649)
                    ·
                      refine ⟨4133323119083592066255487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511097492111456088340649 4133323119083592066255487)
                      ·
                        rfl

theorem cell23_8049618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_8049618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049618 prefixEnd_8049618 := by exact prefixLift 8049618
  have htrace : WordTrace (prefixWord ++ tailWord_8049618) baseStart_8049618 baseEnd_8049618 := by
    simpa [prefixWord, tailWord_8049618, baseEnd_8049618] using wordTrace_append hprefix tailTrace_8049618
  have hstable : (prefixWord ++ tailWord_8049618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049618).length < 2 ^ (prefixWord ++ tailWord_8049618).sum := by decide
  have hdescent : baseEnd_8049618 < baseStart_8049618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049631 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_8049631 : Nat := 118140960795 + 8049631 * 2 ^ 59
def prefixEnd_8049631 : Nat := 4983230072969 + 3 ^ 40 * 8049631 * 2
def baseEnd_8049631 : Nat := 4133329794332100515392927

theorem tailTrace_8049631 : CollatzResearch.WordTrace tailWord_8049631 prefixEnd_8049631 4133329794332100515392927 := by
  unfold tailWord_8049631
  simp only [CollatzResearch.WordTrace]
  refine ⟨293594162300569129369076747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195729441533712752912717831 293594162300569129369076747)
  ·
    refine ⟨440391243450853694053615121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293594162300569129369076747 440391243450853694053615121)
    ·
      refine ⟨330293432588140270540211341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440391243450853694053615121 330293432588140270540211341)
      ·
        refine ⟨123860037220552601452579253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330293432588140270540211341 123860037220552601452579253)
        ·
          refine ⟨11611878489426806386179305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123860037220552601452579253 11611878489426806386179305)
          ·
            refine ⟨8708908867070104789634479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611878489426806386179305 8708908867070104789634479)
            ·
              refine ⟨13063363300605157184451719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708908867070104789634479 13063363300605157184451719)
              ·
                refine ⟨19595044950907735776677579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13063363300605157184451719 19595044950907735776677579)
                ·
                  refine ⟨29392567426361603665016369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19595044950907735776677579 29392567426361603665016369)
                  ·
                    refine ⟨22044425569771202748762277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29392567426361603665016369 22044425569771202748762277)
                    ·
                      refine ⟨4133329794332100515392927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22044425569771202748762277 4133329794332100515392927)
                      ·
                        rfl

theorem cell23_8049631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_8049631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049631 prefixEnd_8049631 := by exact prefixLift 8049631
  have htrace : WordTrace (prefixWord ++ tailWord_8049631) baseStart_8049631 baseEnd_8049631 := by
    simpa [prefixWord, tailWord_8049631, baseEnd_8049631] using wordTrace_append hprefix tailTrace_8049631
  have hstable : (prefixWord ++ tailWord_8049631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049631).length < 2 ^ (prefixWord ++ tailWord_8049631).sum := by decide
  have hdescent : baseEnd_8049631 < baseStart_8049631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049647 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_8049647 : Nat := 118140960795 + 8049647 * 2 ^ 59
def prefixEnd_8049647 : Nat := 4983230072969 + 3 ^ 40 * 8049647 * 2
def baseEnd_8049647 : Nat := 4133338010022572452792853

theorem tailTrace_8049647 : CollatzResearch.WordTrace tailWord_8049647 prefixEnd_8049647 4133338010022572452792853 := by
  unfold tailWord_8049647
  simp only [CollatzResearch.WordTrace]
  refine ⟨293594745868511164101659195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195729830579007442734439463 293594745868511164101659195)
  ·
    refine ⟨440392118802766746152488793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293594745868511164101659195 440392118802766746152488793)
    ·
      refine ⟨330294089102075059614366595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440392118802766746152488793 330294089102075059614366595)
      ·
        refine ⟨495441133653112589421549893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330294089102075059614366595 495441133653112589421549893)
        ·
          refine ⟨92895212559958610516540605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495441133653112589421549893 92895212559958610516540605)
          ·
            refine ⟨34835704709984478943702727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92895212559958610516540605 34835704709984478943702727)
            ·
              refine ⟨52253557064976718415554091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34835704709984478943702727 52253557064976718415554091)
              ·
                refine ⟨78380335597465077623331137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52253557064976718415554091 78380335597465077623331137)
                ·
                  refine ⟨58785251698098808217498353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78380335597465077623331137 58785251698098808217498353)
                  ·
                    refine ⟨44088938773574106163123765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58785251698098808217498353 44088938773574106163123765)
                    ·
                      refine ⟨4133338010022572452792853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44088938773574106163123765 4133338010022572452792853)
                      ·
                        rfl

theorem cell23_8049647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_8049647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049647 prefixEnd_8049647 := by exact prefixLift 8049647
  have htrace : WordTrace (prefixWord ++ tailWord_8049647) baseStart_8049647 baseEnd_8049647 := by
    simpa [prefixWord, tailWord_8049647, baseEnd_8049647] using wordTrace_append hprefix tailTrace_8049647
  have hstable : (prefixWord ++ tailWord_8049647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049647).length < 2 ^ (prefixWord ++ tailWord_8049647).sum := by decide
  have hdescent : baseEnd_8049647 < baseStart_8049647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049685 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_8049685 : Nat := 118140960795 + 8049685 * 2 ^ 59
def prefixEnd_8049685 : Nat := 4983230072969 + 3 ^ 40 * 8049685 * 2
def baseEnd_8049685 : Nat := 4133357522287443304117679

theorem tailTrace_8049685 : CollatzResearch.WordTrace tailWord_8049685 prefixEnd_8049685 4133357522287443304117679 := by
  unfold tailWord_8049685
  simp only [CollatzResearch.WordTrace]
  refine ⟨293596131842373496591542509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195730754561582331061028339 293596131842373496591542509)
  ·
    refine ⟨110098549440890061221828441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293596131842373496591542509 110098549440890061221828441)
    ·
      refine ⟨82573912080667545916371331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110098549440890061221828441 82573912080667545916371331)
      ·
        refine ⟨123860868121001318874556997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82573912080667545916371331 123860868121001318874556997)
        ·
          refine ⟨23223912772687747288979437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123860868121001318874556997 23223912772687747288979437)
          ·
            refine ⟨8708967289757905233367289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23223912772687747288979437 8708967289757905233367289)
            ·
              refine ⟨6531725467318428925025467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708967289757905233367289 6531725467318428925025467)
              ·
                refine ⟨9797588200977643387538201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531725467318428925025467 9797588200977643387538201)
                ·
                  refine ⟨7348191150733232540653651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797588200977643387538201 7348191150733232540653651)
                  ·
                    refine ⟨11022286726099848810980477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348191150733232540653651 11022286726099848810980477)
                    ·
                      refine ⟨4133357522287443304117679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11022286726099848810980477 4133357522287443304117679)
                      ·
                        rfl

theorem cell23_8049685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_8049685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049685 prefixEnd_8049685 := by exact prefixLift 8049685
  have htrace : WordTrace (prefixWord ++ tailWord_8049685) baseStart_8049685 baseEnd_8049685 := by
    simpa [prefixWord, tailWord_8049685, baseEnd_8049685] using wordTrace_append hprefix tailTrace_8049685
  have hstable : (prefixWord ++ tailWord_8049685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049685).length < 2 ^ (prefixWord ++ tailWord_8049685).sum := by decide
  have hdescent : baseEnd_8049685 < baseStart_8049685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049725 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_8049725 : Nat := 118140960795 + 8049725 * 2 ^ 59
def prefixEnd_8049725 : Nat := 4983230072969 + 3 ^ 40 * 8049725 * 2
def baseEnd_8049725 : Nat := 4133378061513623147617495

theorem tailTrace_8049725 : CollatzResearch.WordTrace tailWord_8049725 prefixEnd_8049725 4133378061513623147617495 := by
  unfold tailWord_8049725
  simp only [CollatzResearch.WordTrace]
  refine ⟨293597590762228583422998629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195731727174819055615332419 293597590762228583422998629)
  ·
    refine ⟨55049548267917859391812243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293597590762228583422998629 55049548267917859391812243)
    ·
      refine ⟨82574322401876789087718365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55049548267917859391812243 82574322401876789087718365)
      ·
        refine ⟨30965370900703795907894387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82574322401876789087718365 30965370900703795907894387)
        ·
          refine ⟨46448056351055693861841581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30965370900703795907894387 46448056351055693861841581)
          ·
            refine ⟨17418021131645885198190593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46448056351055693861841581 17418021131645885198190593)
            ·
              refine ⟨13063515848734413898642945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17418021131645885198190593 13063515848734413898642945)
              ·
                refine ⟨9797636886550810423982209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13063515848734413898642945 9797636886550810423982209)
                ·
                  refine ⟨7348227664913107817986657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797636886550810423982209 7348227664913107817986657)
                  ·
                    refine ⟨5511170748684830863489993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348227664913107817986657 5511170748684830863489993)
                    ·
                      refine ⟨4133378061513623147617495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511170748684830863489993 4133378061513623147617495)
                      ·
                        rfl

theorem cell23_8049725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_8049725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049725 prefixEnd_8049725 := by exact prefixLift 8049725
  have htrace : WordTrace (prefixWord ++ tailWord_8049725) baseStart_8049725 baseEnd_8049725 := by
    simpa [prefixWord, tailWord_8049725, baseEnd_8049725] using wordTrace_append hprefix tailTrace_8049725
  have hstable : (prefixWord ++ tailWord_8049725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049725).length < 2 ^ (prefixWord ++ tailWord_8049725).sum := by decide
  have hdescent : baseEnd_8049725 < baseStart_8049725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049727 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 7]
def baseStart_8049727 : Nat := 118140960795 + 8049727 * 2 ^ 59
def prefixEnd_8049727 : Nat := 4983230072969 + 3 ^ 40 * 8049727 * 2
def baseEnd_8049727 : Nat := 1377793029491644046597495

theorem tailTrace_8049727 : CollatzResearch.WordTrace tailWord_8049727 prefixEnd_8049727 1377793029491644046597495 := by
  unfold tailWord_8049727
  simp only [CollatzResearch.WordTrace]
  refine ⟨293597663708221337764571435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195731775805480891843047623 293597663708221337764571435)
  ·
    refine ⟨440396495562332006646857153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293597663708221337764571435 440396495562332006646857153)
    ·
      refine ⟨330297371671749004985142865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440396495562332006646857153 330297371671749004985142865)
      ·
        refine ⟨247723028753811753738857149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330297371671749004985142865 247723028753811753738857149)
        ·
          refine ⟨92896135782679407652071431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247723028753811753738857149 92896135782679407652071431)
          ·
            refine ⟨139344203674019111478107147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92896135782679407652071431 139344203674019111478107147)
            ·
              refine ⟨209016305511028667217160721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139344203674019111478107147 209016305511028667217160721)
              ·
                refine ⟨156762229133271500412870541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209016305511028667217160721 156762229133271500412870541)
                ·
                  refine ⟨58785835924976812654826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156762229133271500412870541 58785835924976812654826453)
                  ·
                    refine ⟨1377793029491644046597495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58785835924976812654826453 1377793029491644046597495)
                    ·
                      rfl

theorem cell23_8049727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_8049727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049727 prefixEnd_8049727 := by exact prefixLift 8049727
  have htrace : WordTrace (prefixWord ++ tailWord_8049727) baseStart_8049727 baseEnd_8049727 := by
    simpa [prefixWord, tailWord_8049727, baseEnd_8049727] using wordTrace_append hprefix tailTrace_8049727
  have hstable : (prefixWord ++ tailWord_8049727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049727).length < 2 ^ (prefixWord ++ tailWord_8049727).sum := by decide
  have hdescent : baseEnd_8049727 < baseStart_8049727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049737 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_8049737 : Nat := 118140960795 + 8049737 * 2 ^ 59
def prefixEnd_8049737 : Nat := 4983230072969 + 3 ^ 40 * 8049737 * 2
def baseEnd_8049737 : Nat := 4133384223281477100667439

theorem tailTrace_8049737 : CollatzResearch.WordTrace tailWord_8049737 prefixEnd_8049737 4133384223281477100667439 := by
  unfold tailWord_8049737
  simp only [CollatzResearch.WordTrace]
  refine ⟨293598028438185109472435465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195732018958790072981623643 293598028438185109472435465)
  ·
    refine ⟨220198521328638832104326599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293598028438185109472435465 220198521328638832104326599)
    ·
      refine ⟨330297781992958248156489899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220198521328638832104326599 330297781992958248156489899)
      ·
        refine ⟨495446672989437372234734849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330297781992958248156489899 495446672989437372234734849)
        ·
          refine ⟨371585004742078029176051137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495446672989437372234734849 371585004742078029176051137)
          ·
            refine ⟨278688753556558521882038353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371585004742078029176051137 278688753556558521882038353)
            ·
              refine ⟨209016565167418891411528765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278688753556558521882038353 209016565167418891411528765)
              ·
                refine ⟨78381211937782084279323287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209016565167418891411528765 78381211937782084279323287)
                ·
                  refine ⟨117571817906673126418984931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78381211937782084279323287 117571817906673126418984931)
                  ·
                    refine ⟨176357726860009689628477397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117571817906673126418984931 176357726860009689628477397)
                    ·
                      refine ⟨4133384223281477100667439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176357726860009689628477397 4133384223281477100667439)
                      ·
                        rfl

theorem cell23_8049737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_8049737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049737 prefixEnd_8049737 := by exact prefixLift 8049737
  have htrace : WordTrace (prefixWord ++ tailWord_8049737) baseStart_8049737 baseEnd_8049737 := by
    simpa [prefixWord, tailWord_8049737, baseEnd_8049737] using wordTrace_append hprefix tailTrace_8049737
  have hstable : (prefixWord ++ tailWord_8049737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049737).length < 2 ^ (prefixWord ++ tailWord_8049737).sum := by decide
  have hdescent : baseEnd_8049737 < baseStart_8049737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049741 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_8049741 : Nat := 118140960795 + 8049741 * 2 ^ 59
def prefixEnd_8049741 : Nat := 4983230072969 + 3 ^ 40 * 8049741 * 2
def baseEnd_8049741 : Nat := 4133386277204095085017421

theorem tailTrace_8049741 : CollatzResearch.WordTrace tailWord_8049741 prefixEnd_8049741 4133386277204095085017421 := by
  unfold tailWord_8049741
  simp only [CollatzResearch.WordTrace]
  refine ⟨293598174330170618155581077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195732116220113745437054051 293598174330170618155581077)
  ·
    refine ⟨13762414421726747726042863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293598174330170618155581077 13762414421726747726042863)
    ·
      refine ⟨20643621632590121589064295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762414421726747726042863 20643621632590121589064295)
      ·
        refine ⟨30965432448885182383596443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20643621632590121589064295 30965432448885182383596443)
        ·
          refine ⟨46448148673327773575394665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30965432448885182383596443 46448148673327773575394665)
          ·
            refine ⟨34836111504995830181545999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46448148673327773575394665 34836111504995830181545999)
            ·
              refine ⟨52254167257493745272318999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836111504995830181545999 52254167257493745272318999)
              ·
                refine ⟨78381250886240617908478499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52254167257493745272318999 78381250886240617908478499)
                ·
                  refine ⟨117571876329360926862717749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78381250886240617908478499 117571876329360926862717749)
                  ·
                    refine ⟨11022363405877586893379789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117571876329360926862717749 11022363405877586893379789)
                    ·
                      refine ⟨4133386277204095085017421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11022363405877586893379789 4133386277204095085017421)
                      ·
                        rfl

theorem cell23_8049741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_8049741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049741 prefixEnd_8049741 := by exact prefixLift 8049741
  have htrace : WordTrace (prefixWord ++ tailWord_8049741) baseStart_8049741 baseEnd_8049741 := by
    simpa [prefixWord, tailWord_8049741, baseEnd_8049741] using wordTrace_append hprefix tailTrace_8049741
  have hstable : (prefixWord ++ tailWord_8049741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049741).length < 2 ^ (prefixWord ++ tailWord_8049741).sum := by decide
  have hdescent : baseEnd_8049741 < baseStart_8049741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049804 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 6]
def baseStart_8049804 : Nat := 118140960795 + 8049804 * 2 ^ 59
def prefixEnd_8049804 : Nat := 4983230072969 + 3 ^ 40 * 8049804 * 2
def baseEnd_8049804 : Nat := 459268736276147593169959

theorem tailTrace_8049804 : CollatzResearch.WordTrace tailWord_8049804 prefixEnd_8049804 459268736276147593169959 := by
  unfold tailWord_8049804
  simp only [CollatzResearch.WordTrace]
  refine ⟨146800236064471189957562233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195733648085961586610082977 146800236064471189957562233)
  ·
    refine ⟨110100177048353392468171675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146800236064471189957562233 110100177048353392468171675)
    ·
      refine ⟨165150265572530088702257513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110100177048353392468171675 165150265572530088702257513)
      ·
        refine ⟨123862699179397566526693135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165150265572530088702257513 123862699179397566526693135)
        ·
          refine ⟨185794048769096349790039703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123862699179397566526693135 185794048769096349790039703)
          ·
            refine ⟨278691073153644524685059555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185794048769096349790039703 278691073153644524685059555)
            ·
              refine ⟨418036609730466787027589333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278691073153644524685059555 418036609730466787027589333)
              ·
                refine ⟨9797733040557815320959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 418036609730466787027589333 9797733040557815320959125)
                ·
                  refine ⟨459268736276147593169959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9797733040557815320959125 459268736276147593169959)
                  ·
                    rfl

theorem cell23_8049804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_8049804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049804 prefixEnd_8049804 := by exact prefixLift 8049804
  have htrace : WordTrace (prefixWord ++ tailWord_8049804) baseStart_8049804 baseEnd_8049804 := by
    simpa [prefixWord, tailWord_8049804, baseEnd_8049804] using wordTrace_append hprefix tailTrace_8049804
  have hstable : (prefixWord ++ tailWord_8049804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049804).length < 2 ^ (prefixWord ++ tailWord_8049804).sum := by decide
  have hdescent : baseEnd_8049804 < baseStart_8049804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049871 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_8049871 : Nat := 118140960795 + 8049871 * 2 ^ 59
def prefixEnd_8049871 : Nat := 4983230072969 + 3 ^ 40 * 8049871 * 2
def baseEnd_8049871 : Nat := 4133453029689179576391823

theorem tailTrace_8049871 : CollatzResearch.WordTrace tailWord_8049871 prefixEnd_8049871 4133453029689179576391823 := by
  unfold tailWord_8049871
  simp only [CollatzResearch.WordTrace]
  refine ⟨293602915819699650357813467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195735277213133100238542311 293602915819699650357813467)
  ·
    refine ⟨440404373729549475536720201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293602915819699650357813467 440404373729549475536720201)
    ·
      refine ⟨330303280297162106652540151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440404373729549475536720201 330303280297162106652540151)
      ·
        refine ⟨495454920445743159978810227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330303280297162106652540151 495454920445743159978810227)
        ·
          refine ⟨743182380668614739968215341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495454920445743159978810227 743182380668614739968215341)
          ·
            refine ⟨278693392750730527488080753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743182380668614739968215341 278693392750730527488080753)
            ·
              refine ⟨209020044563047895616060565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278693392750730527488080753 209020044563047895616060565)
              ·
                refine ⟨9797814588892870107002839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209020044563047895616060565 9797814588892870107002839)
                ·
                  refine ⟨14696721883339305160504259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797814588892870107002839 14696721883339305160504259)
                  ·
                    refine ⟨22045082825008957740756389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14696721883339305160504259 22045082825008957740756389)
                    ·
                      refine ⟨4133453029689179576391823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22045082825008957740756389 4133453029689179576391823)
                      ·
                        rfl

theorem cell23_8049871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_8049871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049871 prefixEnd_8049871 := by exact prefixLift 8049871
  have htrace : WordTrace (prefixWord ++ tailWord_8049871) baseStart_8049871 baseEnd_8049871 := by
    simpa [prefixWord, tailWord_8049871, baseEnd_8049871] using wordTrace_append hprefix tailTrace_8049871
  have hstable : (prefixWord ++ tailWord_8049871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049871).length < 2 ^ (prefixWord ++ tailWord_8049871).sum := by decide
  have hdescent : baseEnd_8049871 < baseStart_8049871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049898 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_8049898 : Nat := 118140960795 + 8049898 * 2 ^ 59
def prefixEnd_8049898 : Nat := 4983230072969 + 3 ^ 40 * 8049898 * 2
def baseEnd_8049898 : Nat := 1377822297888950323584733

theorem tailTrace_8049898 : CollatzResearch.WordTrace tailWord_8049898 prefixEnd_8049898 1377822297888950323584733 := by
  unfold tailWord_8049898
  simp only [CollatzResearch.WordTrace]
  refine ⟨73400975147650458492261587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195735933727067889312697565 73400975147650458492261587)
  ·
    refine ⟨110101462721475687738392381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73400975147650458492261587 110101462721475687738392381)
    ·
      refine ⟨41288048520553382901897143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110101462721475687738392381 41288048520553382901897143)
      ·
        refine ⟨61932072780830074352845715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41288048520553382901897143 61932072780830074352845715)
        ·
          refine ⟨92898109171245111529268573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61932072780830074352845715 92898109171245111529268573)
          ·
            refine ⟨34836790939216916823475715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92898109171245111529268573 34836790939216916823475715)
            ·
              refine ⟨52255186408825375235213573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836790939216916823475715 52255186408825375235213573)
              ·
                refine ⟨9797847451654757856602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52255186408825375235213573 9797847451654757856602545)
                ·
                  refine ⟨7348385588741068392451909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797847451654757856602545 7348385588741068392451909)
                  ·
                    refine ⟨1377822297888950323584733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348385588741068392451909 1377822297888950323584733)
                    ·
                      rfl

theorem cell23_8049898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_8049898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049898 prefixEnd_8049898 := by exact prefixLift 8049898
  have htrace : WordTrace (prefixWord ++ tailWord_8049898) baseStart_8049898 baseEnd_8049898 := by
    simpa [prefixWord, tailWord_8049898, baseEnd_8049898] using wordTrace_append hprefix tailTrace_8049898
  have hstable : (prefixWord ++ tailWord_8049898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049898).length < 2 ^ (prefixWord ++ tailWord_8049898).sum := by decide
  have hdescent : baseEnd_8049898 < baseStart_8049898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049918 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_8049918 : Nat := 118140960795 + 8049918 * 2 ^ 59
def prefixEnd_8049918 : Nat := 4983230072969 + 3 ^ 40 * 8049918 * 2
def baseEnd_8049918 : Nat := 4133477163279940892504107

theorem tailTrace_8049918 : CollatzResearch.WordTrace tailWord_8049918 prefixEnd_8049918 4133477163279940892504107 := by
  unfold tailWord_8049918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36700578756316172173096801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195736420033686251589849605 36700578756316172173096801)
  ·
    refine ⟨27525434067237129129822601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36700578756316172173096801 27525434067237129129822601)
    ·
      refine ⟨20644075550427846847366951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27525434067237129129822601 20644075550427846847366951)
      ·
        refine ⟨30966113325641770271050427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20644075550427846847366951 30966113325641770271050427)
        ·
          refine ⟨46449169988462655406575641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30966113325641770271050427 46449169988462655406575641)
          ·
            refine ⟨34836877491346991554931731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46449169988462655406575641 34836877491346991554931731)
            ·
              refine ⟨52255316237020487332397597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836877491346991554931731 52255316237020487332397597)
              ·
                refine ⟨19595743588882682749649099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52255316237020487332397597 19595743588882682749649099)
                ·
                  refine ⟨29393615383324024124473649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19595743588882682749649099 29393615383324024124473649)
                  ·
                    refine ⟨22045211537493018093355237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29393615383324024124473649 22045211537493018093355237)
                    ·
                      refine ⟨4133477163279940892504107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22045211537493018093355237 4133477163279940892504107)
                      ·
                        rfl

theorem cell23_8049918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_8049918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049918 prefixEnd_8049918 := by exact prefixLift 8049918
  have htrace : WordTrace (prefixWord ++ tailWord_8049918) baseStart_8049918 baseEnd_8049918 := by
    simpa [prefixWord, tailWord_8049918, baseEnd_8049918] using wordTrace_append hprefix tailTrace_8049918
  have hstable : (prefixWord ++ tailWord_8049918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049918).length < 2 ^ (prefixWord ++ tailWord_8049918).sum := by decide
  have hdescent : baseEnd_8049918 < baseStart_8049918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049928 : List Nat := [2, 1, 3, 2, 4, 1, 3, 7]
def baseStart_8049928 : Nat := 118140960795 + 8049928 * 2 ^ 59
def prefixEnd_8049928 : Nat := 4983230072969 + 3 ^ 40 * 8049928 * 2
def baseEnd_8049928 : Nat := 153091936966166142717743

theorem tailTrace_8049928 : CollatzResearch.WordTrace tailWord_8049928 prefixEnd_8049928 153091936966166142717743 := by
  unfold tailWord_8049928
  simp only [CollatzResearch.WordTrace]
  refine ⟨146802497390246574546319219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195736663186995432728425625 146802497390246574546319219)
  ·
    refine ⟨220203746085369861819478829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146802497390246574546319219 220203746085369861819478829)
    ·
      refine ⟨82576404782013698182304561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220203746085369861819478829 82576404782013698182304561)
      ·
        refine ⟨61932303586510273636728421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82576404782013698182304561 61932303586510273636728421)
        ·
          refine ⟨11612306922470676306886579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61932303586510273636728421 11612306922470676306886579)
          ·
            refine ⟨17418460383706014460329869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612306922470676306886579 17418460383706014460329869)
            ·
              refine ⟨6531922643889755422623701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17418460383706014460329869 6531922643889755422623701)
              ·
                refine ⟨153091936966166142717743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6531922643889755422623701 153091936966166142717743)
                ·
                  rfl

theorem cell23_8049928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 7].length) (baseStart_8049928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049928 prefixEnd_8049928 := by exact prefixLift 8049928
  have htrace : WordTrace (prefixWord ++ tailWord_8049928) baseStart_8049928 baseEnd_8049928 := by
    simpa [prefixWord, tailWord_8049928, baseEnd_8049928] using wordTrace_append hprefix tailTrace_8049928
  have hstable : (prefixWord ++ tailWord_8049928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049928).length < 2 ^ (prefixWord ++ tailWord_8049928).sum := by decide
  have hdescent : baseEnd_8049928 < baseStart_8049928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049955 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 3]
def baseStart_8049955 : Nat := 118140960795 + 8049955 * 2 ^ 59
def prefixEnd_8049955 : Nat := 4983230072969 + 3 ^ 40 * 8049955 * 2
def baseEnd_8049955 : Nat := 4133496162064157247741437

theorem tailTrace_8049955 : CollatzResearch.WordTrace tailWord_8049955 prefixEnd_8049955 4133496162064157247741437 := by
  unfold tailWord_8049955
  simp only [CollatzResearch.WordTrace]
  refine ⟨293605979551395332703871319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195737319700930221802580879 293605979551395332703871319)
  ·
    refine ⟨440408969327092999055806979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293605979551395332703871319 440408969327092999055806979)
    ·
      refine ⟨660613453990639498583710469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440408969327092999055806979 660613453990639498583710469)
      ·
        refine ⟨123865022623244905984445713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 660613453990639498583710469 123865022623244905984445713)
        ·
          refine ⟨92898766967433679488334285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123865022623244905984445713 92898766967433679488334285)
          ·
            refine ⟨34837037612787629808125357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92898766967433679488334285 34837037612787629808125357)
            ·
              refine ⟨13063889104795361178047009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34837037612787629808125357 13063889104795361178047009)
              ·
                refine ⟨9797916828596520883535257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13063889104795361178047009 9797916828596520883535257)
                ·
                  refine ⟨7348437621447390662651443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797916828596520883535257 7348437621447390662651443)
                  ·
                    refine ⟨11022656432171085993977165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348437621447390662651443 11022656432171085993977165)
                    ·
                      refine ⟨4133496162064157247741437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11022656432171085993977165 4133496162064157247741437)
                      ·
                        rfl

theorem cell23_8049955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_8049955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049955 prefixEnd_8049955 := by exact prefixLift 8049955
  have htrace : WordTrace (prefixWord ++ tailWord_8049955) baseStart_8049955 baseEnd_8049955 := by
    simpa [prefixWord, tailWord_8049955, baseEnd_8049955] using wordTrace_append hprefix tailTrace_8049955
  have hstable : (prefixWord ++ tailWord_8049955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049955).length < 2 ^ (prefixWord ++ tailWord_8049955).sum := by decide
  have hdescent : baseEnd_8049955 < baseStart_8049955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049971 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 2, 6]
def baseStart_8049971 : Nat := 118140960795 + 8049971 * 2 ^ 59
def prefixEnd_8049971 : Nat := 4983230072969 + 3 ^ 40 * 8049971 * 2
def baseEnd_8049971 : Nat := 1377834792584876395047121

theorem tailTrace_8049971 : CollatzResearch.WordTrace tailWord_8049971 prefixEnd_8049971 1377834792584876395047121 := by
  unfold tailWord_8049971
  simp only [CollatzResearch.WordTrace]
  refine ⟨293606563119337367436453767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195737708746224911624302511 293606563119337367436453767)
  ·
    refine ⟨440409844679006051154680651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293606563119337367436453767 440409844679006051154680651)
    ·
      refine ⟨660614767018509076732020977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440409844679006051154680651 660614767018509076732020977)
      ·
        refine ⟨495461075263881807549015733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660614767018509076732020977 495461075263881807549015733)
        ·
          refine ⟨46449475805988919457720225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 495461075263881807549015733 46449475805988919457720225)
          ·
            refine ⟨34837106854491689593290169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46449475805988919457720225 34837106854491689593290169)
            ·
              refine ⟨26127830140868767194967627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34837106854491689593290169 26127830140868767194967627)
              ·
                refine ⟨39191745211303150792451441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26127830140868767194967627 39191745211303150792451441)
                ·
                  refine ⟨29393808908477363094338581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39191745211303150792451441 29393808908477363094338581)
                  ·
                    refine ⟨1377834792584876395047121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29393808908477363094338581 1377834792584876395047121)
                    ·
                      rfl

theorem cell23_8049971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_8049971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049971 prefixEnd_8049971 := by exact prefixLift 8049971
  have htrace : WordTrace (prefixWord ++ tailWord_8049971) baseStart_8049971 baseEnd_8049971 := by
    simpa [prefixWord, tailWord_8049971, baseEnd_8049971] using wordTrace_append hprefix tailTrace_8049971
  have hstable : (prefixWord ++ tailWord_8049971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049971).length < 2 ^ (prefixWord ++ tailWord_8049971).sum := by decide
  have hdescent : baseEnd_8049971 < baseStart_8049971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049982 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_8049982 : Nat := 118140960795 + 8049982 * 2 ^ 59
def prefixEnd_8049982 : Nat := 4983230072969 + 3 ^ 40 * 8049982 * 2
def baseEnd_8049982 : Nat := 4133510026041828642103813

theorem tailTrace_8049982 : CollatzResearch.WordTrace tailWord_8049982 prefixEnd_8049982 4133510026041828642103813 := by
  unfold tailWord_8049982
  simp only [CollatzResearch.WordTrace]
  refine ⟨36700870540287189539388025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195737976214865010876736133 36700870540287189539388025)
  ·
    refine ⟨27525652905215392154541019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36700870540287189539388025 27525652905215392154541019)
    ·
      refine ⟨41288479357823088231811529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27525652905215392154541019 41288479357823088231811529)
      ·
        refine ⟨30966359518367316173858647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41288479357823088231811529 30966359518367316173858647)
        ·
          refine ⟨46449539277550974260787971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30966359518367316173858647 46449539277550974260787971)
          ·
            refine ⟨69674308916326461391181957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46449539277550974260787971 69674308916326461391181957)
            ·
              refine ⟨13063932921811211510846617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69674308916326461391181957 13063932921811211510846617)
              ·
                refine ⟨9797949691358408633134963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13063932921811211510846617 9797949691358408633134963)
                ·
                  refine ⟨14696924537037612949702445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9797949691358408633134963 14696924537037612949702445)
                  ·
                    refine ⟨5511346701389104856138417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14696924537037612949702445 5511346701389104856138417)
                    ·
                      refine ⟨4133510026041828642103813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511346701389104856138417 4133510026041828642103813)
                      ·
                        rfl

theorem cell23_8049982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_8049982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049982 prefixEnd_8049982 := by exact prefixLift 8049982
  have htrace : WordTrace (prefixWord ++ tailWord_8049982) baseStart_8049982 baseEnd_8049982 := by
    simpa [prefixWord, tailWord_8049982, baseEnd_8049982] using wordTrace_append hprefix tailTrace_8049982
  have hstable : (prefixWord ++ tailWord_8049982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049982).length < 2 ^ (prefixWord ++ tailWord_8049982).sum := by decide
  have hdescent : baseEnd_8049982 < baseStart_8049982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049990 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_8049990 : Nat := 118140960795 + 8049990 * 2 ^ 59
def prefixEnd_8049990 : Nat := 4983230072969 + 3 ^ 40 * 8049990 * 2
def baseEnd_8049990 : Nat := 4133514133887064610803777

theorem tailTrace_8049990 : CollatzResearch.WordTrace tailWord_8049990 prefixEnd_8049990 4133514133887064610803777 := by
  unfold tailWord_8049990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9175226753320891677543607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195738170737512355787596949 9175226753320891677543607)
  ·
    refine ⟨13762840129981337516315411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9175226753320891677543607 13762840129981337516315411)
    ·
      refine ⟨20644260194972006274473117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762840129981337516315411 20644260194972006274473117)
      ·
        refine ⟨7741597573114502352927419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20644260194972006274473117 7741597573114502352927419)
        ·
          refine ⟨11612396359671753529391129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7741597573114502352927419 11612396359671753529391129)
          ·
            refine ⟨8709297269753815147043347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11612396359671753529391129 8709297269753815147043347)
            ·
              refine ⟨13063945904630722720565021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709297269753815147043347 13063945904630722720565021)
              ·
                refine ⟨4898979714236521020211883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13063945904630722720565021 4898979714236521020211883)
                ·
                  refine ⟨7348469571354781530317825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898979714236521020211883 7348469571354781530317825)
                  ·
                    refine ⟨5511352178516086147738369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348469571354781530317825 5511352178516086147738369)
                    ·
                      refine ⟨4133514133887064610803777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511352178516086147738369 4133514133887064610803777)
                      ·
                        rfl

theorem cell23_8049990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_8049990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049990 prefixEnd_8049990 := by exact prefixLift 8049990
  have htrace : WordTrace (prefixWord ++ tailWord_8049990) baseStart_8049990 baseEnd_8049990 := by
    simpa [prefixWord, tailWord_8049990, baseEnd_8049990] using wordTrace_append hprefix tailTrace_8049990
  have hstable : (prefixWord ++ tailWord_8049990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049990).length < 2 ^ (prefixWord ++ tailWord_8049990).sum := by decide
  have hdescent : baseEnd_8049990 < baseStart_8049990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050029 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_8050029 : Nat := 118140960795 + 8050029 * 2 ^ 59
def prefixEnd_8050029 : Nat := 4983230072969 + 3 ^ 40 * 8050029 * 2
def baseEnd_8050029 : Nat := 4133534159632589958216097

theorem tailTrace_8050029 : CollatzResearch.WordTrace tailWord_8050029 prefixEnd_8050029 4133534159632589958216097 := by
  unfold tailWord_8050029
  simp only [CollatzResearch.WordTrace]
  refine ⟨293608678553127243342065141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195739119035418162228043427 293608678553127243342065141)
  ·
    refine ⟨27525813614355679063318607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293608678553127243342065141 27525813614355679063318607)
    ·
      refine ⟨41288720421533518594977911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27525813614355679063318607 41288720421533518594977911)
      ·
        refine ⟨61933080632300277892466867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41288720421533518594977911 61933080632300277892466867)
        ·
          refine ⟨92899620948450416838700301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61933080632300277892466867 92899620948450416838700301)
          ·
            refine ⟨34837357855668906314512613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92899620948450416838700301 34837357855668906314512613)
            ·
              refine ⟨6532004597937919933971115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34837357855668906314512613 6532004597937919933971115)
              ·
                refine ⟨9798006896906879900956673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532004597937919933971115 9798006896906879900956673)
                ·
                  refine ⟨7348505172680159925717505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798006896906879900956673 7348505172680159925717505)
                  ·
                    refine ⟨5511378879510119944288129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348505172680159925717505 5511378879510119944288129)
                    ·
                      refine ⟨4133534159632589958216097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511378879510119944288129 4133534159632589958216097)
                      ·
                        rfl

theorem cell23_8050029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_8050029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050029 prefixEnd_8050029 := by exact prefixLift 8050029
  have htrace : WordTrace (prefixWord ++ tailWord_8050029) baseStart_8050029 baseEnd_8050029 := by
    simpa [prefixWord, tailWord_8050029, baseEnd_8050029] using wordTrace_append hprefix tailTrace_8050029
  have hstable : (prefixWord ++ tailWord_8050029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050029).length < 2 ^ (prefixWord ++ tailWord_8050029).sum := by decide
  have hdescent : baseEnd_8050029 < baseStart_8050029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050031 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 4, 5]
def baseStart_8050031 : Nat := 118140960795 + 8050031 * 2 ^ 59
def prefixEnd_8050031 : Nat := 4983230072969 + 3 ^ 40 * 8050031 * 2
def baseEnd_8050031 : Nat := 1377845062197966316797029

theorem tailTrace_8050031 : CollatzResearch.WordTrace tailWord_8050031 prefixEnd_8050031 1377845062197966316797029 := by
  unfold tailWord_8050031
  simp only [CollatzResearch.WordTrace]
  refine ⟨293608751499119997683637947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195739167666079998455758631 293608751499119997683637947)
  ·
    refine ⟨440413127248679996525456921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293608751499119997683637947 440413127248679996525456921)
    ·
      refine ⟨330309845436509997394092691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440413127248679996525456921 330309845436509997394092691)
      ·
        refine ⟨495464768154764996091139037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330309845436509997394092691 495464768154764996091139037)
        ·
          refine ⟨185799288058036873534177139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495464768154764996091139037 185799288058036873534177139)
          ·
            refine ⟨278698932087055310301265709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185799288058036873534177139 278698932087055310301265709)
            ·
              refine ⟨104512099532645741362974641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278698932087055310301265709 104512099532645741362974641)
              ·
                refine ⟨78384074649484306022230981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104512099532645741362974641 78384074649484306022230981)
                ·
                  refine ⟨14697013996778307379168309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78384074649484306022230981 14697013996778307379168309)
                  ·
                    refine ⟨1377845062197966316797029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14697013996778307379168309 1377845062197966316797029)
                    ·
                      rfl

theorem cell23_8050031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_8050031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050031 prefixEnd_8050031 := by exact prefixLift 8050031
  have htrace : WordTrace (prefixWord ++ tailWord_8050031) baseStart_8050031 baseEnd_8050031 := by
    simpa [prefixWord, tailWord_8050031, baseEnd_8050031] using wordTrace_append hprefix tailTrace_8050031
  have hstable : (prefixWord ++ tailWord_8050031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050031).length < 2 ^ (prefixWord ++ tailWord_8050031).sum := by decide
  have hdescent : baseEnd_8050031 < baseStart_8050031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050071 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_8050071 : Nat := 118140960795 + 8050071 * 2 ^ 59
def prefixEnd_8050071 : Nat := 4983230072969 + 3 ^ 40 * 8050071 * 2
def baseEnd_8050071 : Nat := 4133555725820078793890903

theorem tailTrace_8050071 : CollatzResearch.WordTrace tailWord_8050071 prefixEnd_8050071 4133555725820078793890903 := by
  unfold tailWord_8050071
  simp only [CollatzResearch.WordTrace]
  refine ⟨293610210418975084515094067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195740140279316723010062711 293610210418975084515094067)
  ·
    refine ⟨440415315628462626772641101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293610210418975084515094067 440415315628462626772641101)
    ·
      refine ⟨165155743360673485039740413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440415315628462626772641101 165155743360673485039740413)
      ·
        refine ⟨61933403760252556889902655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165155743360673485039740413 61933403760252556889902655)
        ·
          refine ⟨92900105640378835334853983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61933403760252556889902655 92900105640378835334853983)
          ·
            refine ⟨139350158460568253002280975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92900105640378835334853983 139350158460568253002280975)
            ·
              refine ⟨209025237690852379503421463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139350158460568253002280975 209025237690852379503421463)
              ·
                refine ⟨313537856536278569255132195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209025237690852379503421463 313537856536278569255132195)
                ·
                  refine ⟨470306784804417853882698293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313537856536278569255132195 470306784804417853882698293)
                  ·
                    refine ⟨44091261075414173801502965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 470306784804417853882698293 44091261075414173801502965)
                    ·
                      refine ⟨4133555725820078793890903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44091261075414173801502965 4133555725820078793890903)
                      ·
                        rfl

theorem cell23_8050071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_8050071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050071 prefixEnd_8050071 := by exact prefixLift 8050071
  have htrace : WordTrace (prefixWord ++ tailWord_8050071) baseStart_8050071 baseEnd_8050071 := by
    simpa [prefixWord, tailWord_8050071, baseEnd_8050071] using wordTrace_append hprefix tailTrace_8050071
  have hstable : (prefixWord ++ tailWord_8050071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050071).length < 2 ^ (prefixWord ++ tailWord_8050071).sum := by decide
  have hdescent : baseEnd_8050071 < baseStart_8050071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050105 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_8050105 : Nat := 118140960795 + 8050105 * 2 ^ 59
def prefixEnd_8050105 : Nat := 4983230072969 + 3 ^ 40 * 8050105 * 2
def baseEnd_8050105 : Nat := 4133573184162331660865747

theorem tailTrace_8050105 : CollatzResearch.WordTrace tailWord_8050105 prefixEnd_8050105 4133573184162331660865747 := by
  unfold tailWord_8050105
  simp only [CollatzResearch.WordTrace]
  refine ⟨293611450500851908321831769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195740967000567938881221179 293611450500851908321831769)
  ·
    refine ⟨220208587875638931241373827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293611450500851908321831769 220208587875638931241373827)
    ·
      refine ⟨330312881813458396862060741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220208587875638931241373827 330312881813458396862060741)
      ·
        refine ⟨61933665340023449411636389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330312881813458396862060741 61933665340023449411636389)
        ·
          refine ⟨11612562251254396764681823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61933665340023449411636389 11612562251254396764681823)
          ·
            refine ⟨17418843376881595147022735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612562251254396764681823 17418843376881595147022735)
            ·
              refine ⟨26128265065322392720534103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17418843376881595147022735 26128265065322392720534103)
              ·
                refine ⟨39192397597983589080801155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26128265065322392720534103 39192397597983589080801155)
                ·
                  refine ⟨58788596396975383621201733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39192397597983589080801155 58788596396975383621201733)
                  ·
                    refine ⟨11022861824432884428975325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58788596396975383621201733 11022861824432884428975325)
                    ·
                      refine ⟨4133573184162331660865747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11022861824432884428975325 4133573184162331660865747)
                      ·
                        rfl

theorem cell23_8050105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_8050105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050105 prefixEnd_8050105 := by exact prefixLift 8050105
  have htrace : WordTrace (prefixWord ++ tailWord_8050105) baseStart_8050105 baseEnd_8050105 := by
    simpa [prefixWord, tailWord_8050105, baseEnd_8050105] using wordTrace_append hprefix tailTrace_8050105
  have hstable : (prefixWord ++ tailWord_8050105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050105).length < 2 ^ (prefixWord ++ tailWord_8050105).sum := by decide
  have hdescent : baseEnd_8050105 < baseStart_8050105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050111 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_8050111 : Nat := 118140960795 + 8050111 * 2 ^ 59
def prefixEnd_8050111 : Nat := 4983230072969 + 3 ^ 40 * 8050111 * 2
def baseEnd_8050111 : Nat := 4133576265046258637390719

theorem tailTrace_8050111 : CollatzResearch.WordTrace tailWord_8050111 prefixEnd_8050111 4133576265046258637390719 := by
  unfold tailWord_8050111
  simp only [CollatzResearch.WordTrace]
  refine ⟨293611669338830171346550187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195741112892553447564366791 293611669338830171346550187)
  ·
    refine ⟨440417504008245257019825281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293611669338830171346550187 440417504008245257019825281)
    ·
      refine ⟨330313128006183942764868961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440417504008245257019825281 330313128006183942764868961)
      ·
        refine ⟨247734846004637957073651721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330313128006183942764868961 247734846004637957073651721)
        ·
          refine ⟨185801134503478467805238791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247734846004637957073651721 185801134503478467805238791)
          ·
            refine ⟨278701701755217701707858187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185801134503478467805238791 278701701755217701707858187)
            ·
              refine ⟨418052552632826552561787281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278701701755217701707858187 418052552632826552561787281)
              ·
                refine ⟨313539414474619914421340461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418052552632826552561787281 313539414474619914421340461)
                ·
                  refine ⟨117577280427982467908002673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313539414474619914421340461 117577280427982467908002673)
                  ·
                    refine ⟨88182960320986850931002005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117577280427982467908002673 88182960320986850931002005)
                    ·
                      refine ⟨4133576265046258637390719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88182960320986850931002005 4133576265046258637390719)
                      ·
                        rfl

theorem cell23_8050111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_8050111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050111 prefixEnd_8050111 := by exact prefixLift 8050111
  have htrace : WordTrace (prefixWord ++ tailWord_8050111) baseStart_8050111 baseEnd_8050111 := by
    simpa [prefixWord, tailWord_8050111, baseEnd_8050111] using wordTrace_append hprefix tailTrace_8050111
  have hstable : (prefixWord ++ tailWord_8050111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050111).length < 2 ^ (prefixWord ++ tailWord_8050111).sum := by decide
  have hdescent : baseEnd_8050111 < baseStart_8050111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050145 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_8050145 : Nat := 118140960795 + 8050145 * 2 ^ 59
def prefixEnd_8050145 : Nat := 4983230072969 + 3 ^ 40 * 8050145 * 2
def baseEnd_8050145 : Nat := 4133593723388511504365563

theorem tailTrace_8050145 : CollatzResearch.WordTrace tailWord_8050145 prefixEnd_8050145 4133593723388511504365563 := by
  unfold tailWord_8050145
  simp only [CollatzResearch.WordTrace]
  refine ⟨293612909420706995153287889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195741939613804663435525259 293612909420706995153287889)
  ·
    refine ⟨220209682065530246364965917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293612909420706995153287889 220209682065530246364965917)
    ·
      refine ⟨82578630774573842386862219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220209682065530246364965917 82578630774573842386862219)
      ·
        refine ⟨123867946161860763580293329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82578630774573842386862219 123867946161860763580293329)
        ·
          refine ⟨92900959621395572685219997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123867946161860763580293329 92900959621395572685219997)
          ·
            refine ⟨34837859858023339756957499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92900959621395572685219997 34837859858023339756957499)
            ·
              refine ⟨52256789787035009635436249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34837859858023339756957499 52256789787035009635436249)
              ·
                refine ⟨39192592340276257226577187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52256789787035009635436249 39192592340276257226577187)
                ·
                  refine ⟨58788888510414385839865781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39192592340276257226577187 58788888510414385839865781)
                  ·
                    refine ⟨5511458297851348672487417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58788888510414385839865781 5511458297851348672487417)
                    ·
                      refine ⟨4133593723388511504365563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511458297851348672487417 4133593723388511504365563)
                      ·
                        rfl

theorem cell23_8050145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_8050145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050145 prefixEnd_8050145 := by exact prefixLift 8050145
  have htrace : WordTrace (prefixWord ++ tailWord_8050145) baseStart_8050145 baseEnd_8050145 := by
    simpa [prefixWord, tailWord_8050145, baseEnd_8050145] using wordTrace_append hprefix tailTrace_8050145
  have hstable : (prefixWord ++ tailWord_8050145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050145).length < 2 ^ (prefixWord ++ tailWord_8050145).sum := by decide
  have hdescent : baseEnd_8050145 < baseStart_8050145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050162 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_8050162 : Nat := 118140960795 + 8050162 * 2 ^ 59
def prefixEnd_8050162 : Nat := 4983230072969 + 3 ^ 40 * 8050162 * 2
def baseEnd_8050162 : Nat := 4133602452559637937852985

theorem tailTrace_8050162 : CollatzResearch.WordTrace tailWord_8050162 prefixEnd_8050162 4133602452559637937852985 := by
  unfold tailWord_8050162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73403382365411351764164185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195742352974430271371104493 73403382365411351764164185)
  ·
    refine ⟨55052536774058513823123139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73403382365411351764164185 55052536774058513823123139)
    ·
      refine ⟨82578805161087770734684709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55052536774058513823123139 82578805161087770734684709)
      ·
        refine ⟨15483525967703957012753383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82578805161087770734684709 15483525967703957012753383)
        ·
          refine ⟨23225288951555935519130075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483525967703957012753383 23225288951555935519130075)
          ·
            refine ⟨34837933427333903278695113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23225288951555935519130075 34837933427333903278695113)
            ·
              refine ⟨26128450070500427459021335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34837933427333903278695113 26128450070500427459021335)
              ·
                refine ⟨39192675105750641188532003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26128450070500427459021335 39192675105750641188532003)
                ·
                  refine ⟨58789012658625961782798005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39192675105750641188532003 58789012658625961782798005)
                  ·
                    refine ⟨5511469936746183917137313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58789012658625961782798005 5511469936746183917137313)
                    ·
                      refine ⟨4133602452559637937852985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511469936746183917137313 4133602452559637937852985)
                      ·
                        rfl

theorem cell23_8050162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_8050162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050162 prefixEnd_8050162 := by exact prefixLift 8050162
  have htrace : WordTrace (prefixWord ++ tailWord_8050162) baseStart_8050162 baseEnd_8050162 := by
    simpa [prefixWord, tailWord_8050162, baseEnd_8050162] using wordTrace_append hprefix tailTrace_8050162
  have hstable : (prefixWord ++ tailWord_8050162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050162).length < 2 ^ (prefixWord ++ tailWord_8050162).sum := by decide
  have hdescent : baseEnd_8050162 < baseStart_8050162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050185 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_8050185 : Nat := 118140960795 + 8050185 * 2 ^ 59
def prefixEnd_8050185 : Nat := 4983230072969 + 3 ^ 40 * 8050185 * 2
def baseEnd_8050185 : Nat := 1377871420871563782621793

theorem tailTrace_8050185 : CollatzResearch.WordTrace tailWord_8050185 prefixEnd_8050185 1377871420871563782621793 := by
  unfold tailWord_8050185
  simp only [CollatzResearch.WordTrace]
  refine ⟨293614368340562081984744009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195742912227041387989829339 293614368340562081984744009)
  ·
    refine ⟨220210776255421561488558007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293614368340562081984744009 220210776255421561488558007)
    ·
      refine ⟨330316164383132342232837011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220210776255421561488558007 330316164383132342232837011)
      ·
        refine ⟨495474246574698513349255517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330316164383132342232837011 495474246574698513349255517)
        ·
          refine ⟨185802842465511942505970819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495474246574698513349255517 185802842465511942505970819)
          ·
            refine ⟨278704263698267913758956229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185802842465511942505970819 278704263698267913758956229)
            ·
              refine ⟨52257049443425233829804293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278704263698267913758956229 52257049443425233829804293)
              ·
                refine ⟨9798196770642231343088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52257049443425233829804293 9798196770642231343088305)
                ·
                  refine ⟨7348647577981673507316229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798196770642231343088305 7348647577981673507316229)
                  ·
                    refine ⟨1377871420871563782621793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348647577981673507316229 1377871420871563782621793)
                    ·
                      rfl

theorem cell23_8050185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_8050185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050185 prefixEnd_8050185 := by exact prefixLift 8050185
  have htrace : WordTrace (prefixWord ++ tailWord_8050185) baseStart_8050185 baseEnd_8050185 := by
    simpa [prefixWord, tailWord_8050185, baseEnd_8050185] using wordTrace_append hprefix tailTrace_8050185
  have hstable : (prefixWord ++ tailWord_8050185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050185).length < 2 ^ (prefixWord ++ tailWord_8050185).sum := by decide
  have hdescent : baseEnd_8050185 < baseStart_8050185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050186 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_8050186 : Nat := 118140960795 + 8050186 * 2 ^ 59
def prefixEnd_8050186 : Nat := 4983230072969 + 3 ^ 40 * 8050186 * 2
def baseEnd_8050186 : Nat := 4133614776095345843952875

theorem tailTrace_8050186 : CollatzResearch.WordTrace tailWord_8050186 prefixEnd_8050186 4133614776095345843952875 := by
  unfold tailWord_8050186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73403601203389614788882603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195742936542372306103686941 73403601203389614788882603)
  ·
    refine ⟨110105401805084422183323905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73403601203389614788882603 110105401805084422183323905)
    ·
      refine ⟨82579051353813316637492929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110105401805084422183323905 82579051353813316637492929)
      ·
        refine ⟨61934288515359987478119697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82579051353813316637492929 61934288515359987478119697)
        ·
          refine ⟨46450716386519990608589773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61934288515359987478119697 46450716386519990608589773)
          ·
            refine ⟨17419018644944996478221165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46450716386519990608589773 17419018644944996478221165)
            ·
              refine ⟨6532131991854373679332937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17419018644944996478221165 6532131991854373679332937)
              ·
                refine ⟨4899098993890780259499703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6532131991854373679332937 4899098993890780259499703)
                ·
                  refine ⟨7348648490836170389249555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899098993890780259499703 7348648490836170389249555)
                  ·
                    refine ⟨11022972736254255583874333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348648490836170389249555 11022972736254255583874333)
                    ·
                      refine ⟨4133614776095345843952875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11022972736254255583874333 4133614776095345843952875)
                      ·
                        rfl

theorem cell23_8050186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_8050186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050186 prefixEnd_8050186 := by exact prefixLift 8050186
  have htrace : WordTrace (prefixWord ++ tailWord_8050186) baseStart_8050186 baseEnd_8050186 := by
    simpa [prefixWord, tailWord_8050186, baseEnd_8050186] using wordTrace_append hprefix tailTrace_8050186
  have hstable : (prefixWord ++ tailWord_8050186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050186).length < 2 ^ (prefixWord ++ tailWord_8050186).sum := by decide
  have hdescent : baseEnd_8050186 < baseStart_8050186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050205 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_8050205 : Nat := 118140960795 + 8050205 * 2 ^ 59
def prefixEnd_8050205 : Nat := 4983230072969 + 3 ^ 40 * 8050205 * 2
def baseEnd_8050205 : Nat := 4133624532227781269615287

theorem tailTrace_8050205 : CollatzResearch.WordTrace tailWord_8050205 prefixEnd_8050205 4133624532227781269615287 := by
  unfold tailWord_8050205
  simp only [CollatzResearch.WordTrace]
  refine ⟨293615097800489625400472069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195743398533659750266981379 293615097800489625400472069)
  ·
    refine ⟨55052830837591804762588513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293615097800489625400472069 55052830837591804762588513)
    ·
      refine ⟨41289623128193853571941385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55052830837591804762588513 41289623128193853571941385)
      ·
        refine ⟨30967217346145390178956039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41289623128193853571941385 30967217346145390178956039)
        ·
          refine ⟨46450826019218085268434059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967217346145390178956039 46450826019218085268434059)
          ·
            refine ⟨69676239028827127902651089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46450826019218085268434059 69676239028827127902651089)
            ·
              refine ⟨52257179271620345926988317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69676239028827127902651089 52257179271620345926988317)
              ·
                refine ⟨19596442226857629722620619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52257179271620345926988317 19596442226857629722620619)
                ·
                  refine ⟨29394663340286444583930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19596442226857629722620619 29394663340286444583930929)
                  ·
                    refine ⟨22045997505214833437948197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29394663340286444583930929 22045997505214833437948197)
                    ·
                      refine ⟨4133624532227781269615287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22045997505214833437948197 4133624532227781269615287)
                      ·
                        rfl

theorem cell23_8050205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_8050205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050205 prefixEnd_8050205 := by exact prefixLift 8050205
  have htrace : WordTrace (prefixWord ++ tailWord_8050205) baseStart_8050205 baseEnd_8050205 := by
    simpa [prefixWord, tailWord_8050205, baseEnd_8050205] using wordTrace_append hprefix tailTrace_8050205
  have hstable : (prefixWord ++ tailWord_8050205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050205).length < 2 ^ (prefixWord ++ tailWord_8050205).sum := by decide
  have hdescent : baseEnd_8050205 < baseStart_8050205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050206 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8050206 : Nat := 118140960795 + 8050206 * 2 ^ 59
def prefixEnd_8050206 : Nat := 4983230072969 + 3 ^ 40 * 8050206 * 2
def baseEnd_8050206 : Nat := 1377875015236145255234261

theorem tailTrace_8050206 : CollatzResearch.WordTrace tailWord_8050206 prefixEnd_8050206 1377875015236145255234261 := by
  unfold tailWord_8050206
  simp only [CollatzResearch.WordTrace]
  refine ⟨36701891784185750321407309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195743422848990668380838981 36701891784185750321407309)
  ·
    refine ⟨13763209419069656370527741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36701891784185750321407309 13763209419069656370527741)
    ·
      refine ⟨5161203532151121138947903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13763209419069656370527741 5161203532151121138947903)
      ·
        refine ⟨7741805298226681708421855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161203532151121138947903 7741805298226681708421855)
        ·
          refine ⟨11612707947340022562632783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7741805298226681708421855 11612707947340022562632783)
          ·
            refine ⟨17419061921010033843949175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612707947340022562632783 17419061921010033843949175)
            ·
              refine ⟨26128592881515050765923763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17419061921010033843949175 26128592881515050765923763)
              ·
                refine ⟨39192889322272576148885645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26128592881515050765923763 39192889322272576148885645)
                ·
                  refine ⟨14697333495852216055832117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39192889322272576148885645 14697333495852216055832117)
                  ·
                    refine ⟨1377875015236145255234261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14697333495852216055832117 1377875015236145255234261)
                    ·
                      rfl

theorem cell23_8050206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8050206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050206 prefixEnd_8050206 := by exact prefixLift 8050206
  have htrace : WordTrace (prefixWord ++ tailWord_8050206) baseStart_8050206 baseEnd_8050206 := by
    simpa [prefixWord, tailWord_8050206, baseEnd_8050206] using wordTrace_append hprefix tailTrace_8050206
  have hstable : (prefixWord ++ tailWord_8050206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050206).length < 2 ^ (prefixWord ++ tailWord_8050206).sum := by decide
  have hdescent : baseEnd_8050206 < baseStart_8050206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050222 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_8050222 : Nat := 118140960795 + 8050222 * 2 ^ 59
def prefixEnd_8050222 : Nat := 4983230072969 + 3 ^ 40 * 8050222 * 2
def baseEnd_8050222 : Nat := 4133633261398907703102709

theorem tailTrace_8050222 : CollatzResearch.WordTrace tailWord_8050222 prefixEnd_8050222 4133633261398907703102709 := by
  unfold tailWord_8050222
  simp only [CollatzResearch.WordTrace]
  refine ⟨36701964730178504662980115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195743811894285358202560613 36701964730178504662980115)
  ·
    refine ⟨55052947095267756994470173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36701964730178504662980115 55052947095267756994470173)
    ·
      refine ⟨20644855160725408872926315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55052947095267756994470173 20644855160725408872926315)
      ·
        refine ⟨30967282741088113309389473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20644855160725408872926315 30967282741088113309389473)
        ·
          refine ⟨23225462055816084982042105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30967282741088113309389473 23225462055816084982042105)
          ·
            refine ⟨17419096541862063736531579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23225462055816084982042105 17419096541862063736531579)
            ·
              refine ⟨26128644812793095604797369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17419096541862063736531579 26128644812793095604797369)
              ·
                refine ⟨19596483609594821703598027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26128644812793095604797369 19596483609594821703598027)
                ·
                  refine ⟨29394725414392232555397041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19596483609594821703598027 29394725414392232555397041)
                  ·
                    refine ⟨22046044060794174416547781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29394725414392232555397041 22046044060794174416547781)
                    ·
                      refine ⟨4133633261398907703102709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22046044060794174416547781 4133633261398907703102709)
                      ·
                        rfl

theorem cell23_8050222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_8050222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050222 prefixEnd_8050222 := by exact prefixLift 8050222
  have htrace : WordTrace (prefixWord ++ tailWord_8050222) baseStart_8050222 baseEnd_8050222 := by
    simpa [prefixWord, tailWord_8050222, baseEnd_8050222] using wordTrace_append hprefix tailTrace_8050222
  have hstable : (prefixWord ++ tailWord_8050222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050222).length < 2 ^ (prefixWord ++ tailWord_8050222).sum := by decide
  have hdescent : baseEnd_8050222 < baseStart_8050222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050229 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_8050229 : Nat := 118140960795 + 8050229 * 2 ^ 59
def prefixEnd_8050229 : Nat := 4983230072969 + 3 ^ 40 * 8050229 * 2
def baseEnd_8050229 : Nat := 4133636855763489175715177

theorem tailTrace_8050229 : CollatzResearch.WordTrace tailWord_8050229 prefixEnd_8050229 4133636855763489175715177 := by
  unfold tailWord_8050229
  simp only [CollatzResearch.WordTrace]
  refine ⟨293615973152402677499345741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195743982101601784999563827 293615973152402677499345741)
  ·
    refine ⟨110105989932151004062254653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293615973152402677499345741 110105989932151004062254653)
    ·
      refine ⟨41289746224556626523345495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110105989932151004062254653 41289746224556626523345495)
      ·
        refine ⟨61934619336834939785018243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41289746224556626523345495 61934619336834939785018243)
        ·
          refine ⟨92901929005252409677527365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61934619336834939785018243 92901929005252409677527365)
          ·
            refine ⟨17419111688484826814536381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92901929005252409677527365 17419111688484826814536381)
            ·
              refine ⟨6532166883181810055451143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17419111688484826814536381 6532166883181810055451143)
              ·
                refine ⟨9798250324772715083176715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532166883181810055451143 9798250324772715083176715)
                ·
                  refine ⟨14697375487159072624765073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798250324772715083176715 14697375487159072624765073)
                  ·
                    refine ⟨11023031615369304468573805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14697375487159072624765073 11023031615369304468573805)
                    ·
                      refine ⟨4133636855763489175715177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023031615369304468573805 4133636855763489175715177)
                      ·
                        rfl

theorem cell23_8050229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_8050229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050229 prefixEnd_8050229 := by exact prefixLift 8050229
  have htrace : WordTrace (prefixWord ++ tailWord_8050229) baseStart_8050229 baseEnd_8050229 := by
    simpa [prefixWord, tailWord_8050229, baseEnd_8050229] using wordTrace_append hprefix tailTrace_8050229
  have hstable : (prefixWord ++ tailWord_8050229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050229).length < 2 ^ (prefixWord ++ tailWord_8050229).sum := by decide
  have hdescent : baseEnd_8050229 < baseStart_8050229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050252 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_8050252 : Nat := 118140960795 + 8050252 * 2 ^ 59
def prefixEnd_8050252 : Nat := 4983230072969 + 3 ^ 40 * 8050252 * 2
def baseEnd_8050252 : Nat := 4133648665818542585727571

theorem tailTrace_8050252 : CollatzResearch.WordTrace tailWord_8050252 prefixEnd_8050252 4133648665818542585727571 := by
  unfold tailWord_8050252
  simp only [CollatzResearch.WordTrace]
  refine ⟨146808406015659676213716505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195744541354212901618288673 146808406015659676213716505)
  ·
    refine ⟨110106304511744757160287379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146808406015659676213716505 110106304511744757160287379)
    ·
      refine ⟨165159456767617135740431069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110106304511744757160287379 165159456767617135740431069)
      ·
        refine ⟨61934796287856425902661651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165159456767617135740431069 61934796287856425902661651)
        ·
          refine ⟨92902194431784638853992477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61934796287856425902661651 92902194431784638853992477)
          ·
            refine ⟨34838322911919239570247179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92902194431784638853992477 34838322911919239570247179)
            ·
              refine ⟨52257484367878859355370769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34838322911919239570247179 52257484367878859355370769)
              ·
                refine ⟨39193113275909144516528077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52257484367878859355370769 39193113275909144516528077)
                ·
                  refine ⟨14697417478465929193698029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39193113275909144516528077 14697417478465929193698029)
                  ·
                    refine ⟨5511531554424723447636761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14697417478465929193698029 5511531554424723447636761)
                    ·
                      refine ⟨4133648665818542585727571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511531554424723447636761 4133648665818542585727571)
                      ·
                        rfl

theorem cell23_8050252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_8050252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050252 prefixEnd_8050252 := by exact prefixLift 8050252
  have htrace : WordTrace (prefixWord ++ tailWord_8050252) baseStart_8050252 baseEnd_8050252 := by
    simpa [prefixWord, tailWord_8050252, baseEnd_8050252] using wordTrace_append hprefix tailTrace_8050252
  have hstable : (prefixWord ++ tailWord_8050252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050252).length < 2 ^ (prefixWord ++ tailWord_8050252).sum := by decide
  have hdescent : baseEnd_8050252 < baseStart_8050252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050286 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_8050286 : Nat := 118140960795 + 8050286 * 2 ^ 59
def prefixEnd_8050286 : Nat := 4983230072969 + 3 ^ 40 * 8050286 * 2
def baseEnd_8050286 : Nat := 4133666124160795452702415

theorem tailTrace_8050286 : CollatzResearch.WordTrace tailWord_8050286 prefixEnd_8050286 4133666124160795452702415 := by
  unfold tailWord_8050286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702256514149522029271339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195745368075464117489447141 36702256514149522029271339)
  ·
    refine ⟨55053384771224283043907009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36702256514149522029271339 55053384771224283043907009)
    ·
      refine ⟨41290038578418212282930257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55053384771224283043907009 41290038578418212282930257)
      ·
        refine ⟨30967528933813659212197693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41290038578418212282930257 30967528933813659212197693)
        ·
          refine ⟨11612823350180122204574135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30967528933813659212197693 11612823350180122204574135)
          ·
            refine ⟨17419235025270183306861203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612823350180122204574135 17419235025270183306861203)
            ·
              refine ⟨26128852537905274960291805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17419235025270183306861203 26128852537905274960291805)
              ·
                refine ⟨9798319701714478110109427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26128852537905274960291805 9798319701714478110109427)
                ·
                  refine ⟨14697479552571717165164141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798319701714478110109427 14697479552571717165164141)
                  ·
                    refine ⟨5511554832214393936936553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14697479552571717165164141 5511554832214393936936553)
                    ·
                      refine ⟨4133666124160795452702415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511554832214393936936553 4133666124160795452702415)
                      ·
                        rfl

theorem cell23_8050286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_8050286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050286 prefixEnd_8050286 := by exact prefixLift 8050286
  have htrace : WordTrace (prefixWord ++ tailWord_8050286) baseStart_8050286 baseEnd_8050286 := by
    simpa [prefixWord, tailWord_8050286, baseEnd_8050286] using wordTrace_append hprefix tailTrace_8050286
  have hstable : (prefixWord ++ tailWord_8050286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050286).length < 2 ^ (prefixWord ++ tailWord_8050286).sum := by decide
  have hdescent : baseEnd_8050286 < baseStart_8050286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_8050298 : Nat := 118140960795 + 8050298 * 2 ^ 59
def prefixEnd_8050298 : Nat := 4983230072969 + 3 ^ 40 * 8050298 * 2
def baseEnd_8050298 : Nat := 4133672285928649405752359

theorem tailTrace_8050298 : CollatzResearch.WordTrace tailWord_8050298 prefixEnd_8050298 4133672285928649405752359 := by
  unfold tailWord_8050298
  simp only [CollatzResearch.WordTrace]
  refine ⟨73404622447288175570901887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195745659859435134855738365 73404622447288175570901887)
  ·
    refine ⟨110106933670932263356352831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73404622447288175570901887 110106933670932263356352831)
    ·
      refine ⟨165160400506398395034529247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110106933670932263356352831 165160400506398395034529247)
      ·
        refine ⟨247740600759597592551793871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165160400506398395034529247 247740600759597592551793871)
        ·
          refine ⟨371610901139396388827690807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247740600759597592551793871 371610901139396388827690807)
          ·
            refine ⟨557416351709094583241536211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371610901139396388827690807 557416351709094583241536211)
            ·
              refine ⟨836124527563641874862304317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557416351709094583241536211 836124527563641874862304317)
              ·
                refine ⟨313546697836365703073364119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836124527563641874862304317 313546697836365703073364119)
                ·
                  refine ⟨470320046754548554610046179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313546697836365703073364119 470320046754548554610046179)
                  ·
                    refine ⟨705480070131822831915069269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470320046754548554610046179 705480070131822831915069269)
                    ·
                      refine ⟨4133672285928649405752359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 705480070131822831915069269 4133672285928649405752359)
                      ·
                        rfl

theorem cell23_8050298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_8050298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050298 prefixEnd_8050298 := by exact prefixLift 8050298
  have htrace : WordTrace (prefixWord ++ tailWord_8050298) baseStart_8050298 baseEnd_8050298 := by
    simpa [prefixWord, tailWord_8050298, baseEnd_8050298] using wordTrace_append hprefix tailTrace_8050298
  have hstable : (prefixWord ++ tailWord_8050298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050298).length < 2 ^ (prefixWord ++ tailWord_8050298).sum := by decide
  have hdescent : baseEnd_8050298 < baseStart_8050298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050305 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 7]
def baseStart_8050305 : Nat := 118140960795 + 8050305 * 2 ^ 59
def prefixEnd_8050305 : Nat := 4983230072969 + 3 ^ 40 * 8050305 * 2
def baseEnd_8050305 : Nat := 459297320032581208707203

theorem tailTrace_8050305 : CollatzResearch.WordTrace tailWord_8050305 prefixEnd_8050305 459297320032581208707203 := by
  unfold tailWord_8050305
  simp only [CollatzResearch.WordTrace]
  refine ⟨293618745100127342479112369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195745830066751561652741579 293618745100127342479112369)
  ·
    refine ⟨220214058825095506859334277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293618745100127342479112369 220214058825095506859334277)
    ·
      refine ⟨41290136029705407536125177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220214058825095506859334277 41290136029705407536125177)
      ·
        refine ⟨30967602022279055652093883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41290136029705407536125177 30967602022279055652093883)
        ·
          refine ⟨46451403033418583478140825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967602022279055652093883 46451403033418583478140825)
          ·
            refine ⟨34838552275063937608605619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46451403033418583478140825 34838552275063937608605619)
            ·
              refine ⟨52257828412595906412908429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34838552275063937608605619 52257828412595906412908429)
              ·
                refine ⟨19596685654723464904840661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52257828412595906412908429 19596685654723464904840661)
                ·
                  refine ⟨459297320032581208707203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19596685654723464904840661 459297320032581208707203)
                  ·
                    rfl

theorem cell23_8050305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_8050305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050305 prefixEnd_8050305 := by exact prefixLift 8050305
  have htrace : WordTrace (prefixWord ++ tailWord_8050305) baseStart_8050305 baseEnd_8050305 := by
    simpa [prefixWord, tailWord_8050305, baseEnd_8050305] using wordTrace_append hprefix tailTrace_8050305
  have hstable : (prefixWord ++ tailWord_8050305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050305).length < 2 ^ (prefixWord ++ tailWord_8050305).sum := by decide
  have hdescent : baseEnd_8050305 < baseStart_8050305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050315 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3]
def baseStart_8050315 : Nat := 118140960795 + 8050315 * 2 ^ 59
def prefixEnd_8050315 : Nat := 4983230072969 + 3 ^ 40 * 8050315 * 2
def baseEnd_8050315 : Nat := 4133681015099775839239781

theorem tailTrace_8050315 : CollatzResearch.WordTrace tailWord_8050315 prefixEnd_8050315 4133681015099775839239781 := by
  unfold tailWord_8050315
  simp only [CollatzResearch.WordTrace]
  refine ⟨293619109830091114186976399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195746073220060742791317599 293619109830091114186976399)
  ·
    refine ⟨440428664745136671280464599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293619109830091114186976399 440428664745136671280464599)
    ·
      refine ⟨660642997117705006920696899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440428664745136671280464599 660642997117705006920696899)
      ·
        refine ⟨990964495676557510381045349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660642997117705006920696899 990964495676557510381045349)
        ·
          refine ⟨185805842939354533196446003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 990964495676557510381045349 185805842939354533196446003)
          ·
            refine ⟨278708764409031799794669005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185805842939354533196446003 278708764409031799794669005)
            ·
              refine ⟨104515786653386924923000877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278708764409031799794669005 104515786653386924923000877)
              ·
                refine ⟨39193419995020096846125329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104515786653386924923000877 39193419995020096846125329)
                ·
                  refine ⟨29395064996265072634593997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39193419995020096846125329 29395064996265072634593997)
                  ·
                    refine ⟨11023149373599402237972749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29395064996265072634593997 11023149373599402237972749)
                    ·
                      refine ⟨4133681015099775839239781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023149373599402237972749 4133681015099775839239781)
                      ·
                        rfl

theorem cell23_8050315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3].length) (baseStart_8050315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050315 prefixEnd_8050315 := by exact prefixLift 8050315
  have htrace : WordTrace (prefixWord ++ tailWord_8050315) baseStart_8050315 baseEnd_8050315 := by
    simpa [prefixWord, tailWord_8050315, baseEnd_8050315] using wordTrace_append hprefix tailTrace_8050315
  have hstable : (prefixWord ++ tailWord_8050315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050315).length < 2 ^ (prefixWord ++ tailWord_8050315).sum := by decide
  have hdescent : baseEnd_8050315 < baseStart_8050315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050316 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_8050316 : Nat := 118140960795 + 8050316 * 2 ^ 59
def prefixEnd_8050316 : Nat := 4983230072969 + 3 ^ 40 * 8050316 * 2
def baseEnd_8050316 : Nat := 4133681528580430335327277

theorem tailTrace_8050316 : CollatzResearch.WordTrace tailWord_8050316 prefixEnd_8050316 4133681528580430335327277 := by
  unfold tailWord_8050316
  simp only [CollatzResearch.WordTrace]
  refine ⟨146809573151543745678881401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195746097535391660905175201 146809573151543745678881401)
  ·
    refine ⟨110107179863657809259161051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146809573151543745678881401 110107179863657809259161051)
    ·
      refine ⟨165160769795486713888741577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110107179863657809259161051 165160769795486713888741577)
      ·
        refine ⟨123870577346615035416556183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165160769795486713888741577 123870577346615035416556183)
        ·
          refine ⟨185805866019922553124834275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123870577346615035416556183 185805866019922553124834275)
          ·
            refine ⟨278708799029883829687251413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185805866019922553124834275 278708799029883829687251413)
            ·
              refine ⟨6532237477262902258294955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278708799029883829687251413 6532237477262902258294955)
              ·
                refine ⟨9798356215894353387442433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532237477262902258294955 9798356215894353387442433)
                ·
                  refine ⟨7348767161920765040581825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9798356215894353387442433 7348767161920765040581825)
                  ·
                    refine ⟨5511575371440573780436369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348767161920765040581825 5511575371440573780436369)
                    ·
                      refine ⟨4133681528580430335327277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511575371440573780436369 4133681528580430335327277)
                      ·
                        rfl

theorem cell23_8050316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_8050316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050316 prefixEnd_8050316 := by exact prefixLift 8050316
  have htrace : WordTrace (prefixWord ++ tailWord_8050316) baseStart_8050316 baseEnd_8050316 := by
    simpa [prefixWord, tailWord_8050316, baseEnd_8050316] using wordTrace_append hprefix tailTrace_8050316
  have hstable : (prefixWord ++ tailWord_8050316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050316).length < 2 ^ (prefixWord ++ tailWord_8050316).sum := by decide
  have hdescent : baseEnd_8050316 < baseStart_8050316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050372 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_8050372 : Nat := 118140960795 + 8050372 * 2 ^ 59
def prefixEnd_8050372 : Nat := 4983230072969 + 3 ^ 40 * 8050372 * 2
def baseEnd_8050372 : Nat := 4133710283497082116227019

theorem tailTrace_8050372 : CollatzResearch.WordTrace tailWord_8050372 prefixEnd_8050372 4133710283497082116227019 := by
  unfold tailWord_8050372
  simp only [CollatzResearch.WordTrace]
  refine ⟨146810594395442306460900685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195747459193923075281200913 146810594395442306460900685)
  ·
    refine ⟨55053972898290864922837757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146810594395442306460900685 55053972898290864922837757)
    ·
      refine ⟨20645239836859074346064159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55053972898290864922837757 20645239836859074346064159)
      ·
        refine ⟨30967859755288611519096239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20645239836859074346064159 30967859755288611519096239)
        ·
          refine ⟨46451789632932917278644359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967859755288611519096239 46451789632932917278644359)
          ·
            refine ⟨69677684449399375917966539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46451789632932917278644359 69677684449399375917966539)
            ·
              refine ⟨104516526674099063876949809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69677684449399375917966539 104516526674099063876949809)
              ·
                refine ⟨78387395005574297907712357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104516526674099063876949809 78387395005574297907712357)
                ·
                  refine ⟨14697636563545180857696067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78387395005574297907712357 14697636563545180857696067)
                  ·
                    refine ⟨22046454845317771286544101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14697636563545180857696067 22046454845317771286544101)
                    ·
                      refine ⟨4133710283497082116227019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22046454845317771286544101 4133710283497082116227019)
                      ·
                        rfl

theorem cell23_8050372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_8050372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050372 prefixEnd_8050372 := by exact prefixLift 8050372
  have htrace : WordTrace (prefixWord ++ tailWord_8050372) baseStart_8050372 baseEnd_8050372 := by
    simpa [prefixWord, tailWord_8050372, baseEnd_8050372] using wordTrace_append hprefix tailTrace_8050372
  have hstable : (prefixWord ++ tailWord_8050372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050372).length < 2 ^ (prefixWord ++ tailWord_8050372).sum := by decide
  have hdescent : baseEnd_8050372 < baseStart_8050372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050382 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_8050382 : Nat := 118140960795 + 8050382 * 2 ^ 59
def prefixEnd_8050382 : Nat := 4983230072969 + 3 ^ 40 * 8050382 * 2
def baseEnd_8050382 : Nat := 1377905139434542359033991

theorem tailTrace_8050382 : CollatzResearch.WordTrace tailWord_8050382 prefixEnd_8050382 1377905139434542359033991 := by
  unfold tailWord_8050382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702694190106048078708175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195747702347232256419776933 36702694190106048078708175)
  ·
    refine ⟨55054041285159072118062263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36702694190106048078708175 55054041285159072118062263)
    ·
      refine ⟨82581061927738608177093395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55054041285159072118062263 82581061927738608177093395)
      ·
        refine ⟨123871592891607912265640093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82581061927738608177093395 123871592891607912265640093)
        ·
          refine ⟨46451847334352967099615035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123871592891607912265640093 46451847334352967099615035)
          ·
            refine ⟨69677771001529450649422553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46451847334352967099615035 69677771001529450649422553)
            ·
              refine ⟨52258328251147087987066915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69677771001529450649422553 52258328251147087987066915)
              ·
                refine ⟨78387492376720631980600373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52258328251147087987066915 78387492376720631980600373)
                ·
                  refine ⟨7348827410317559248181285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78387492376720631980600373 7348827410317559248181285)
                  ·
                    refine ⟨1377905139434542359033991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348827410317559248181285 1377905139434542359033991)
                    ·
                      rfl

theorem cell23_8050382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_8050382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050382 prefixEnd_8050382 := by exact prefixLift 8050382
  have htrace : WordTrace (prefixWord ++ tailWord_8050382) baseStart_8050382 baseEnd_8050382 := by
    simpa [prefixWord, tailWord_8050382, baseEnd_8050382] using wordTrace_append hprefix tailTrace_8050382
  have hstable : (prefixWord ++ tailWord_8050382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050382).length < 2 ^ (prefixWord ++ tailWord_8050382).sum := by decide
  have hdescent : baseEnd_8050382 < baseStart_8050382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050399 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 1, 4]
def baseStart_8050399 : Nat := 118140960795 + 8050399 * 2 ^ 59
def prefixEnd_8050399 : Nat := 4983230072969 + 3 ^ 40 * 8050399 * 2
def baseEnd_8050399 : Nat := 1377908049158251170196465

theorem tailTrace_8050399 : CollatzResearch.WordTrace tailWord_8050399 prefixEnd_8050399 1377908049158251170196465 := by
  unfold tailWord_8050399
  simp only [CollatzResearch.WordTrace]
  refine ⟨293622173561786796533034251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195748115707857864355356167 293622173561786796533034251)
  ·
    refine ⟨440433260342680194799551377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293622173561786796533034251 440433260342680194799551377)
    ·
      refine ⟨330324945257010146099663533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440433260342680194799551377 330324945257010146099663533)
      ·
        refine ⟨123871854471378804787373825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330324945257010146099663533 123871854471378804787373825)
        ·
          refine ⟨92903890853534103590530369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123871854471378804787373825 92903890853534103590530369)
          ·
            refine ⟨69677918140150577692897777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92903890853534103590530369 69677918140150577692897777)
            ·
              refine ⟨52258438605112933269673333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69677918140150577692897777 52258438605112933269673333)
              ·
                refine ⟨4899228619229337494031875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52258438605112933269673333 4899228619229337494031875)
                ·
                  refine ⟨7348842928844006241047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899228619229337494031875 7348842928844006241047813)
                  ·
                    refine ⟨1377908049158251170196465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7348842928844006241047813 1377908049158251170196465)
                    ·
                      rfl

theorem cell23_8050399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 4].length) (baseStart_8050399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050399 prefixEnd_8050399 := by exact prefixLift 8050399
  have htrace : WordTrace (prefixWord ++ tailWord_8050399) baseStart_8050399 baseEnd_8050399 := by
    simpa [prefixWord, tailWord_8050399, baseEnd_8050399] using wordTrace_append hprefix tailTrace_8050399
  have hstable : (prefixWord ++ tailWord_8050399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050399).length < 2 ^ (prefixWord ++ tailWord_8050399).sum := by decide
  have hdescent : baseEnd_8050399 < baseStart_8050399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050415 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_8050415 : Nat := 118140960795 + 8050415 * 2 ^ 59
def prefixEnd_8050415 : Nat := 4983230072969 + 3 ^ 40 * 8050415 * 2
def baseEnd_8050415 : Nat := 4133732363165225447989321

theorem tailTrace_8050415 : CollatzResearch.WordTrace tailWord_8050415 prefixEnd_8050415 4133732363165225447989321 := by
  unfold tailWord_8050415
  simp only [CollatzResearch.WordTrace]
  refine ⟨293622757129728831265616699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195748504753152554177077799 293622757129728831265616699)
  ·
    refine ⟨440434135694593246898425049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293622757129728831265616699 440434135694593246898425049)
    ·
      refine ⟨330325601770944935173818787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440434135694593246898425049 330325601770944935173818787)
      ·
        refine ⟨495488402656417402760728181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330325601770944935173818787 495488402656417402760728181)
        ·
          refine ⟨46452037749039131508818267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 495488402656417402760728181 46452037749039131508818267)
          ·
            refine ⟨69678056623558697263227401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46452037749039131508818267 69678056623558697263227401)
            ·
              refine ⟨52258542467669022947420551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69678056623558697263227401 52258542467669022947420551)
              ·
                refine ⟨78387813701503534421130827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52258542467669022947420551 78387813701503534421130827)
                ·
                  refine ⟨117581720552255301631696241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78387813701503534421130827 117581720552255301631696241)
                  ·
                    refine ⟨88186290414191476223772181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117581720552255301631696241 88186290414191476223772181)
                    ·
                      refine ⟨4133732363165225447989321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88186290414191476223772181 4133732363165225447989321)
                      ·
                        rfl

theorem cell23_8050415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_8050415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050415 prefixEnd_8050415 := by exact prefixLift 8050415
  have htrace : WordTrace (prefixWord ++ tailWord_8050415) baseStart_8050415 baseEnd_8050415 := by
    simpa [prefixWord, tailWord_8050415, baseEnd_8050415] using wordTrace_append hprefix tailTrace_8050415
  have hstable : (prefixWord ++ tailWord_8050415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050415).length < 2 ^ (prefixWord ++ tailWord_8050415).sum := by decide
  have hdescent : baseEnd_8050415 < baseStart_8050415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050432 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2]
def baseStart_8050432 : Nat := 118140960795 + 8050432 * 2 ^ 59
def prefixEnd_8050432 : Nat := 4983230072969 + 3 ^ 40 * 8050432 * 2
def baseEnd_8050432 : Nat := 4133741092336351881476743

theorem tailTrace_8050432 : CollatzResearch.WordTrace tailWord_8050432 prefixEnd_8050432 4133741092336351881476743 := by
  unfold tailWord_8050432
  simp only [CollatzResearch.WordTrace]
  refine ⟨146811688585333621584492775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195748918113778162112657033 146811688585333621584492775)
  ·
    refine ⟨220217532878000432376739163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146811688585333621584492775 220217532878000432376739163)
    ·
      refine ⟨330326299317000648565108745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220217532878000432376739163 330326299317000648565108745)
      ·
        refine ⟨247744724487750486423831559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330326299317000648565108745 247744724487750486423831559)
        ·
          refine ⟨371617086731625729635747339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247744724487750486423831559 371617086731625729635747339)
          ·
            refine ⟨557425630097438594453621009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371617086731625729635747339 557425630097438594453621009)
            ·
              refine ⟨418069222573078945840215757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557425630097438594453621009 418069222573078945840215757)
              ·
                refine ⟨156775958464904604690080909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418069222573078945840215757 156775958464904604690080909)
                ·
                  refine ⟨58790984424339226758780341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156775958464904604690080909 58790984424339226758780341)
                  ·
                    refine ⟨5511654789781802508635657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58790984424339226758780341 5511654789781802508635657)
                    ·
                      refine ⟨4133741092336351881476743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511654789781802508635657 4133741092336351881476743)
                      ·
                        rfl

theorem cell23_8050432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_8050432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050432 prefixEnd_8050432 := by exact prefixLift 8050432
  have htrace : WordTrace (prefixWord ++ tailWord_8050432) baseStart_8050432 baseEnd_8050432 := by
    simpa [prefixWord, tailWord_8050432, baseEnd_8050432] using wordTrace_append hprefix tailTrace_8050432
  have hstable : (prefixWord ++ tailWord_8050432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050432).length < 2 ^ (prefixWord ++ tailWord_8050432).sum := by decide
  have hdescent : baseEnd_8050432 < baseStart_8050432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050442 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_8050442 : Nat := 118140960795 + 8050442 * 2 ^ 59
def prefixEnd_8050442 : Nat := 4983230072969 + 3 ^ 40 * 8050442 * 2
def baseEnd_8050442 : Nat := 1377915409047632280783899

theorem tailTrace_8050442 : CollatzResearch.WordTrace tailWord_8050442 prefixEnd_8050442 1377915409047632280783899 := by
  unfold tailWord_8050442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73405935475157753719212395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195749161267087343251233053 73405935475157753719212395)
  ·
    refine ⟨110108903212736630578818593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73405935475157753719212395 110108903212736630578818593)
    ·
      refine ⟨82581677409552472934113945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110108903212736630578818593 82581677409552472934113945)
      ·
        refine ⟨61936258057164354700585459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82581677409552472934113945 61936258057164354700585459)
        ·
          refine ⟨92904387085746532050878189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61936258057164354700585459 92904387085746532050878189)
          ·
            refine ⟨34839145157154949519079321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92904387085746532050878189 34839145157154949519079321)
            ·
              refine ⟨26129358867866212139309491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34839145157154949519079321 26129358867866212139309491)
              ·
                refine ⟨39194038301799318208964237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26129358867866212139309491 39194038301799318208964237)
                ·
                  refine ⟨14697764363174744328361589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39194038301799318208964237 14697764363174744328361589)
                  ·
                    refine ⟨1377915409047632280783899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14697764363174744328361589 1377915409047632280783899)
                    ·
                      rfl

theorem cell23_8050442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_8050442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050442 prefixEnd_8050442 := by exact prefixLift 8050442
  have htrace : WordTrace (prefixWord ++ tailWord_8050442) baseStart_8050442 baseEnd_8050442 := by
    simpa [prefixWord, tailWord_8050442, baseEnd_8050442] using wordTrace_append hprefix tailTrace_8050442
  have hstable : (prefixWord ++ tailWord_8050442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050442).length < 2 ^ (prefixWord ++ tailWord_8050442).sum := by decide
  have hdescent : baseEnd_8050442 < baseStart_8050442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050456 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 1, 1, 3]
def baseStart_8050456 : Nat := 118140960795 + 8050456 * 2 ^ 59
def prefixEnd_8050456 : Nat := 4983230072969 + 3 ^ 40 * 8050456 * 2
def baseEnd_8050456 : Nat := 4133753415872059787576633

theorem tailTrace_8050456 : CollatzResearch.WordTrace tailWord_8050456 prefixEnd_8050456 4133753415872059787576633 := by
  unfold tailWord_8050456
  simp only [CollatzResearch.WordTrace]
  refine ⟨146812126261290147633929611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195749501681720196845239481 146812126261290147633929611)
  ·
    refine ⟨220218189391935221450894417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146812126261290147633929611 220218189391935221450894417)
    ·
      refine ⟨165163642043951416088170813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220218189391935221450894417 165163642043951416088170813)
      ·
        refine ⟨61936365766481781033064055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165163642043951416088170813 61936365766481781033064055)
        ·
          refine ⟨92904548649722671549596083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61936365766481781033064055 92904548649722671549596083)
          ·
            refine ⟨139356822974584007324394125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92904548649722671549596083 139356822974584007324394125)
            ·
              refine ⟨52258808615469002746647797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139356822974584007324394125 52258808615469002746647797)
              ·
                refine ⟨4899263307700219007498231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52258808615469002746647797 4899263307700219007498231)
                ·
                  refine ⟨7348894961550328511247347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899263307700219007498231 7348894961550328511247347)
                  ·
                    refine ⟨11023342442325492766871021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348894961550328511247347 11023342442325492766871021)
                    ·
                      refine ⟨4133753415872059787576633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023342442325492766871021 4133753415872059787576633)
                      ·
                        rfl

theorem cell23_8050456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_8050456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050456 prefixEnd_8050456 := by exact prefixLift 8050456
  have htrace : WordTrace (prefixWord ++ tailWord_8050456) baseStart_8050456 baseEnd_8050456 := by
    simpa [prefixWord, tailWord_8050456, baseEnd_8050456] using wordTrace_append hprefix tailTrace_8050456
  have hstable : (prefixWord ++ tailWord_8050456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050456).length < 2 ^ (prefixWord ++ tailWord_8050456).sum := by decide
  have hdescent : baseEnd_8050456 < baseStart_8050456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050479 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 7, 2, 2]
def baseStart_8050479 : Nat := 118140960795 + 8050479 * 2 ^ 59
def prefixEnd_8050479 : Nat := 4983230072969 + 3 ^ 40 * 8050479 * 2
def baseEnd_8050479 : Nat := 4133765225927113197589027

theorem tailTrace_8050479 : CollatzResearch.WordTrace tailWord_8050479 prefixEnd_8050479 4133765225927113197589027 := by
  unfold tailWord_8050479
  simp only [CollatzResearch.WordTrace]
  refine ⟨293625091401496970195946491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195750060934331313463964327 293625091401496970195946491)
  ·
    refine ⟨440437637102245455293919737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293625091401496970195946491 440437637102245455293919737)
    ·
      refine ⟨330328227826684091470439803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440437637102245455293919737 330328227826684091470439803)
      ·
        refine ⟨495492341740026137205659705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330328227826684091470439803 495492341740026137205659705)
        ·
          refine ⟨371619256305019602904244779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495492341740026137205659705 371619256305019602904244779)
          ·
            refine ⟨557428884457529404356367169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371619256305019602904244779 557428884457529404356367169)
            ·
              refine ⟨418071663343147053267275377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557428884457529404356367169 418071663343147053267275377)
              ·
                refine ⟨313553747507360289950456533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418071663343147053267275377 313553747507360289950456533)
                ·
                  refine ⟨7348915957203756795713825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 313553747507360289950456533 7348915957203756795713825)
                  ·
                    refine ⟨5511686967902817596785369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348915957203756795713825 5511686967902817596785369)
                    ·
                      refine ⟨4133765225927113197589027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511686967902817596785369 4133765225927113197589027)
                      ·
                        rfl

theorem cell23_8050479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2, 2].length) (baseStart_8050479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050479 prefixEnd_8050479 := by exact prefixLift 8050479
  have htrace : WordTrace (prefixWord ++ tailWord_8050479) baseStart_8050479 baseEnd_8050479 := by
    simpa [prefixWord, tailWord_8050479, baseEnd_8050479] using wordTrace_append hprefix tailTrace_8050479
  have hstable : (prefixWord ++ tailWord_8050479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050479).length < 2 ^ (prefixWord ++ tailWord_8050479).sum := by decide
  have hdescent : baseEnd_8050479 < baseStart_8050479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050482 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_8050482 : Nat := 118140960795 + 8050482 * 2 ^ 59
def prefixEnd_8050482 : Nat := 4983230072969 + 3 ^ 40 * 8050482 * 2
def baseEnd_8050482 : Nat := 4133766766369076685851513

theorem tailTrace_8050482 : CollatzResearch.WordTrace tailWord_8050482 prefixEnd_8050482 4133766766369076685851513 := by
  unfold tailWord_8050482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73406300205121525427076425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195750133880324067805537133 73406300205121525427076425)
  ·
    refine ⟨55054725153841144070307319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73406300205121525427076425 55054725153841144070307319)
    ·
      refine ⟨82582087730761716105460979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55054725153841144070307319 82582087730761716105460979)
      ·
        refine ⟨123873131596142574158191469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82582087730761716105460979 123873131596142574158191469)
        ·
          refine ⟨46452424348553465309321801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123873131596142574158191469 46452424348553465309321801)
          ·
            refine ⟨34839318261415098981991351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46452424348553465309321801 34839318261415098981991351)
            ·
              refine ⟨52258977392122648472987027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34839318261415098981991351 52258977392122648472987027)
              ·
                refine ⟨78388466088183972709480541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52258977392122648472987027 78388466088183972709480541)
                ·
                  refine ⟨29395674783068989766055203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78388466088183972709480541 29395674783068989766055203)
                  ·
                    refine ⟨44093512174603484649082805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29395674783068989766055203 44093512174603484649082805)
                    ·
                      refine ⟨4133766766369076685851513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44093512174603484649082805 4133766766369076685851513)
                      ·
                        rfl

theorem cell23_8050482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_8050482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050482 prefixEnd_8050482 := by exact prefixLift 8050482
  have htrace : WordTrace (prefixWord ++ tailWord_8050482) baseStart_8050482 baseEnd_8050482 := by
    simpa [prefixWord, tailWord_8050482, baseEnd_8050482] using wordTrace_append hprefix tailTrace_8050482
  have hstable : (prefixWord ++ tailWord_8050482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050482).length < 2 ^ (prefixWord ++ tailWord_8050482).sum := by decide
  have hdescent : baseEnd_8050482 < baseStart_8050482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050499 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 3]
def baseStart_8050499 : Nat := 118140960795 + 8050499 * 2 ^ 59
def prefixEnd_8050499 : Nat := 4983230072969 + 3 ^ 40 * 8050499 * 2
def baseEnd_8050499 : Nat := 4133775495540203119338935

theorem tailTrace_8050499 : CollatzResearch.WordTrace tailWord_8050499 prefixEnd_8050499 4133775495540203119338935 := by
  unfold tailWord_8050499
  simp only [CollatzResearch.WordTrace]
  refine ⟨293625820861424513611674551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195750547240949675741116367 293625820861424513611674551)
  ·
    refine ⟨440438731292136770417511827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293625820861424513611674551 440438731292136770417511827)
    ·
      refine ⟨660658096938205155626267741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440438731292136770417511827 660658096938205155626267741)
      ·
        refine ⟨247746786351826933359850403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 660658096938205155626267741 247746786351826933359850403)
        ·
          refine ⟨371620179527740400039775605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247746786351826933359850403 371620179527740400039775605)
          ·
            refine ⟨34839391830725662503728963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371620179527740400039775605 34839391830725662503728963)
            ·
              refine ⟨52259087746088493755593445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34839391830725662503728963 52259087746088493755593445)
              ·
                refine ⟨9798578952391592579173771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52259087746088493755593445 9798578952391592579173771)
                ·
                  refine ⟨14697868428587388868760657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798578952391592579173771 14697868428587388868760657)
                  ·
                    refine ⟨11023401321440541651570493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14697868428587388868760657 11023401321440541651570493)
                    ·
                      refine ⟨4133775495540203119338935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023401321440541651570493 4133775495540203119338935)
                      ·
                        rfl

theorem cell23_8050499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_8050499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050499 prefixEnd_8050499 := by exact prefixLift 8050499
  have htrace : WordTrace (prefixWord ++ tailWord_8050499) baseStart_8050499 baseEnd_8050499 := by
    simpa [prefixWord, tailWord_8050499, baseEnd_8050499] using wordTrace_append hprefix tailTrace_8050499
  have hstable : (prefixWord ++ tailWord_8050499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050499).length < 2 ^ (prefixWord ++ tailWord_8050499).sum := by decide
  have hdescent : baseEnd_8050499 < baseStart_8050499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050512 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_8050512 : Nat := 118140960795 + 8050512 * 2 ^ 59
def prefixEnd_8050512 : Nat := 4983230072969 + 3 ^ 40 * 8050512 * 2
def baseEnd_8050512 : Nat := 4133782170788711568476375

theorem tailTrace_8050512 : CollatzResearch.WordTrace tailWord_8050512 prefixEnd_8050512 4133782170788711568476375 := by
  unfold tailWord_8050512
  simp only [CollatzResearch.WordTrace]
  refine ⟨146813147505188708415948895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195750863340251611221265193 146813147505188708415948895)
  ·
    refine ⟨220219721257783062623923343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146813147505188708415948895 220219721257783062623923343)
    ·
      refine ⟨330329581886674593935885015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220219721257783062623923343 330329581886674593935885015)
      ·
        refine ⟨495494372830011890903827523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330329581886674593935885015 495494372830011890903827523)
        ·
          refine ⟨743241559245017836355741285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495494372830011890903827523 743241559245017836355741285)
          ·
            refine ⟨139357792358440844316701491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 743241559245017836355741285 139357792358440844316701491)
            ·
              refine ⟨209036688537661266475052237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139357792358440844316701491 209036688537661266475052237)
              ·
                refine ⟨78388758201622974928144589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209036688537661266475052237 78388758201622974928144589)
                ·
                  refine ⟨29395784325608615598054221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78388758201622974928144589 29395784325608615598054221)
                  ·
                    refine ⟨11023419122103230849270333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29395784325608615598054221 11023419122103230849270333)
                    ·
                      refine ⟨4133782170788711568476375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023419122103230849270333 4133782170788711568476375)
                      ·
                        rfl

theorem cell23_8050512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_8050512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050512 prefixEnd_8050512 := by exact prefixLift 8050512
  have htrace : WordTrace (prefixWord ++ tailWord_8050512) baseStart_8050512 baseEnd_8050512 := by
    simpa [prefixWord, tailWord_8050512, baseEnd_8050512] using wordTrace_append hprefix tailTrace_8050512
  have hstable : (prefixWord ++ tailWord_8050512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050512).length < 2 ^ (prefixWord ++ tailWord_8050512).sum := by decide
  have hdescent : baseEnd_8050512 < baseStart_8050512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050515 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 9]
def baseStart_8050515 : Nat := 118140960795 + 8050515 * 2 ^ 59
def prefixEnd_8050515 : Nat := 4983230072969 + 3 ^ 40 * 8050515 * 2
def baseEnd_8050515 : Nat := 1377927903743558352246287

theorem tailTrace_8050515 : CollatzResearch.WordTrace tailWord_8050515 prefixEnd_8050515 1377927903743558352246287 := by
  unfold tailWord_8050515
  simp only [CollatzResearch.WordTrace]
  refine ⟨293626404429366548344256999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195750936286244365562837999 293626404429366548344256999)
  ·
    refine ⟨440439606644049822516385499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293626404429366548344256999 440439606644049822516385499)
    ·
      refine ⟨660659409966074733774578249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440439606644049822516385499 660659409966074733774578249)
      ·
        refine ⟨495494557474556050330933687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660659409966074733774578249 495494557474556050330933687)
        ·
          refine ⟨743241836211834075496400531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495494557474556050330933687 743241836211834075496400531)
          ·
            refine ⟨1114862754317751113244600797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743241836211834075496400531 1114862754317751113244600797)
            ·
              refine ⟨418073532869156667466725299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114862754317751113244600797 418073532869156667466725299)
              ·
                refine ⟨627110299303735001200087949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418073532869156667466725299 627110299303735001200087949)
                ·
                  refine ⟨235166362238900625450032981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627110299303735001200087949 235166362238900625450032981)
                  ·
                    refine ⟨1377927903743558352246287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235166362238900625450032981 1377927903743558352246287)
                    ·
                      rfl

theorem cell23_8050515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_8050515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050515 prefixEnd_8050515 := by exact prefixLift 8050515
  have htrace : WordTrace (prefixWord ++ tailWord_8050515) baseStart_8050515 baseEnd_8050515 := by
    simpa [prefixWord, tailWord_8050515, baseEnd_8050515] using wordTrace_append hprefix tailTrace_8050515
  have hstable : (prefixWord ++ tailWord_8050515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050515).length < 2 ^ (prefixWord ++ tailWord_8050515).sum := by decide
  have hdescent : baseEnd_8050515 < baseStart_8050515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050516 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_8050516 : Nat := 118140960795 + 8050516 * 2 ^ 59
def prefixEnd_8050516 : Nat := 4983230072969 + 3 ^ 40 * 8050516 * 2
def baseEnd_8050516 : Nat := 4133784224711329552826357

theorem tailTrace_8050516 : CollatzResearch.WordTrace tailWord_8050516 prefixEnd_8050516 4133784224711329552826357 := by
  unfold tailWord_8050516
  simp only [CollatzResearch.WordTrace]
  refine ⟨146813220451181462757521701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195750960601575283676695601 146813220451181462757521701)
  ·
    refine ⟨27527478834596524267035319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146813220451181462757521701 27527478834596524267035319)
    ·
      refine ⟨41291218251894786400552979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27527478834596524267035319 41291218251894786400552979)
      ·
        refine ⟨61936827377842179600829469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41291218251894786400552979 61936827377842179600829469)
        ·
          refine ⟨23226310266690817350311051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61936827377842179600829469 23226310266690817350311051)
          ·
            refine ⟨34839465400036226025466577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226310266690817350311051 34839465400036226025466577)
            ·
              refine ⟨26129599050027169519099933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34839465400036226025466577 26129599050027169519099933)
              ·
                refine ⟨9798599643760188569662475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26129599050027169519099933 9798599643760188569662475)
                ·
                  refine ⟨14697899465640282854493713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798599643760188569662475 14697899465640282854493713)
                  ·
                    refine ⟨11023424599230212140870285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14697899465640282854493713 11023424599230212140870285)
                    ·
                      refine ⟨4133784224711329552826357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023424599230212140870285 4133784224711329552826357)
                      ·
                        rfl

theorem cell23_8050516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_8050516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050516 prefixEnd_8050516 := by exact prefixLift 8050516
  have htrace : WordTrace (prefixWord ++ tailWord_8050516) baseStart_8050516 baseEnd_8050516 := by
    simpa [prefixWord, tailWord_8050516, baseEnd_8050516] using wordTrace_append hprefix tailTrace_8050516
  have hstable : (prefixWord ++ tailWord_8050516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050516).length < 2 ^ (prefixWord ++ tailWord_8050516).sum := by decide
  have hdescent : baseEnd_8050516 < baseStart_8050516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050519 : List Nat := [1, 1, 3, 2, 6, 1, 9]
def baseStart_8050519 : Nat := 118140960795 + 8050519 * 2 ^ 59
def prefixEnd_8050519 : Nat := 4983230072969 + 3 ^ 40 * 8050519 * 2
def baseEnd_8050519 : Nat := 51034392162386333840603

theorem tailTrace_8050519 : CollatzResearch.WordTrace tailWord_8050519 prefixEnd_8050519 51034392162386333840603 := by
  unfold tailWord_8050519
  simp only [CollatzResearch.WordTrace]
  refine ⟨293626550321352057027402611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195751033547568038018268407 293626550321352057027402611)
  ·
    refine ⟨440439825482028085541103917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293626550321352057027402611 440439825482028085541103917)
    ·
      refine ⟨165164934555760532077913969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440439825482028085541103917 165164934555760532077913969)
      ·
        refine ⟨123873700916820399058435477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165164934555760532077913969 123873700916820399058435477)
        ·
          refine ⟨5806579730475956205864163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123873700916820399058435477 5806579730475956205864163)
          ·
            refine ⟨8709869595713934308796245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806579730475956205864163 8709869595713934308796245)
            ·
              refine ⟨51034392162386333840603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8709869595713934308796245 51034392162386333840603)
              ·
                rfl

theorem cell23_8050519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 9].length) (baseStart_8050519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050519 prefixEnd_8050519 := by exact prefixLift 8050519
  have htrace : WordTrace (prefixWord ++ tailWord_8050519) baseStart_8050519 baseEnd_8050519 := by
    simpa [prefixWord, tailWord_8050519, baseEnd_8050519] using wordTrace_append hprefix tailTrace_8050519
  have hstable : (prefixWord ++ tailWord_8050519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050519).length < 2 ^ (prefixWord ++ tailWord_8050519).sum := by decide
  have hdescent : baseEnd_8050519 < baseStart_8050519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050529 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_8050529 : Nat := 118140960795 + 8050529 * 2 ^ 59
def prefixEnd_8050529 : Nat := 4983230072969 + 3 ^ 40 * 8050529 * 2
def baseEnd_8050529 : Nat := 4133790899959838001963797

theorem tailTrace_8050529 : CollatzResearch.WordTrace tailWord_8050529 prefixEnd_8050529 4133790899959838001963797 := by
  unfold tailWord_8050529
  simp only [CollatzResearch.WordTrace]
  refine ⟨293626915051315828735266641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195751276700877219156844427 293626915051315828735266641)
  ·
    refine ⟨220220186288486871551449981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293626915051315828735266641 220220186288486871551449981)
    ·
      refine ⟨82582569858182576831793743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220220186288486871551449981 82582569858182576831793743)
      ·
        refine ⟨123873854787273865247690615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82582569858182576831793743 123873854787273865247690615)
        ·
          refine ⟨185810782180910797871535923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123873854787273865247690615 185810782180910797871535923)
          ·
            refine ⟨278716173271366196807303885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185810782180910797871535923 278716173271366196807303885)
            ·
              refine ⟨104518564976762323802738957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278716173271366196807303885 104518564976762323802738957)
              ·
                refine ⟨39194461866285871426027109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104518564976762323802738957 39194461866285871426027109)
                ·
                  refine ⟨7348961599928600892380083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39194461866285871426027109 7348961599928600892380083)
                  ·
                    refine ⟨11023442399892901338570125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7348961599928600892380083 11023442399892901338570125)
                    ·
                      refine ⟨4133790899959838001963797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023442399892901338570125 4133790899959838001963797)
                      ·
                        rfl

theorem cell23_8050529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_8050529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050529 prefixEnd_8050529 := by exact prefixLift 8050529
  have htrace : WordTrace (prefixWord ++ tailWord_8050529) baseStart_8050529 baseEnd_8050529 := by
    simpa [prefixWord, tailWord_8050529, baseEnd_8050529] using wordTrace_append hprefix tailTrace_8050529
  have hstable : (prefixWord ++ tailWord_8050529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050529).length < 2 ^ (prefixWord ++ tailWord_8050529).sum := by decide
  have hdescent : baseEnd_8050529 < baseStart_8050529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050530 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_8050530 : Nat := 118140960795 + 8050530 * 2 ^ 59
def prefixEnd_8050530 : Nat := 4983230072969 + 3 ^ 40 * 8050530 * 2
def baseEnd_8050530 : Nat := 4133791413440492498051293

theorem tailTrace_8050530 : CollatzResearch.WordTrace tailWord_8050530 prefixEnd_8050530 4133791413440492498051293 := by
  unfold tailWord_8050530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73406737881078051476513261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195751301016208137270702029 73406737881078051476513261)
  ·
    refine ⟨27527526705404269303692473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73406737881078051476513261 27527526705404269303692473)
    ·
      refine ⟨20645645029053201977769355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27527526705404269303692473 20645645029053201977769355)
      ·
        refine ⟨30968467543579802966654033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20645645029053201977769355 30968467543579802966654033)
        ·
          refine ⟨23226350657684852224990525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30968467543579802966654033 23226350657684852224990525)
          ·
            refine ⟨8709881496631819584371447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23226350657684852224990525 8709881496631819584371447)
            ·
              refine ⟨13064822244947729376557171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709881496631819584371447 13064822244947729376557171)
              ·
                refine ⟨19597233367421594064835757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13064822244947729376557171 19597233367421594064835757)
                ·
                  refine ⟨7348962512783097774313409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19597233367421594064835757 7348962512783097774313409)
                  ·
                    refine ⟨5511721884587323330735057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7348962512783097774313409 5511721884587323330735057)
                    ·
                      refine ⟨4133791413440492498051293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511721884587323330735057 4133791413440492498051293)
                      ·
                        rfl

theorem cell23_8050530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_8050530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050530 prefixEnd_8050530 := by exact prefixLift 8050530
  have htrace : WordTrace (prefixWord ++ tailWord_8050530) baseStart_8050530 baseEnd_8050530 := by
    simpa [prefixWord, tailWord_8050530, baseEnd_8050530] using wordTrace_append hprefix tailTrace_8050530
  have hstable : (prefixWord ++ tailWord_8050530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050530).length < 2 ^ (prefixWord ++ tailWord_8050530).sum := by decide
  have hdescent : baseEnd_8050530 < baseStart_8050530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050539 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 3, 3, 2]
def baseStart_8050539 : Nat := 118140960795 + 8050539 * 2 ^ 59
def prefixEnd_8050539 : Nat := 4983230072969 + 3 ^ 40 * 8050539 * 2
def baseEnd_8050539 : Nat := 4133796034766382962838751

theorem tailTrace_8050539 : CollatzResearch.WordTrace tailWord_8050539 prefixEnd_8050539 4133796034766382962838751 := by
  unfold tailWord_8050539
  simp only [CollatzResearch.WordTrace]
  refine ⟨293627279781279600443130671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195751519854186400295420447 293627279781279600443130671)
  ·
    refine ⟨440440919671919400664696007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293627279781279600443130671 440440919671919400664696007)
    ·
      refine ⟨660661379507879100997044011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440440919671919400664696007 660661379507879100997044011)
      ·
        refine ⟨990992069261818651495566017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660661379507879100997044011 990992069261818651495566017)
        ·
          refine ⟨743244051946363988621674513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990992069261818651495566017 743244051946363988621674513)
          ·
            refine ⟨557433038959772991466255885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743244051946363988621674513 557433038959772991466255885)
            ·
              refine ⟨209037389609914871799845957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557433038959772991466255885 209037389609914871799845957)
              ·
                refine ⟨39194510551859038462471117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209037389609914871799845957 39194510551859038462471117)
                ·
                  refine ⟨14697941456947139423426669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39194510551859038462471117 14697941456947139423426669)
                  ·
                    refine ⟨5511728046355177283785001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14697941456947139423426669 5511728046355177283785001)
                    ·
                      refine ⟨4133796034766382962838751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511728046355177283785001 4133796034766382962838751)
                      ·
                        rfl

theorem cell23_8050539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3, 2].length) (baseStart_8050539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050539 prefixEnd_8050539 := by exact prefixLift 8050539
  have htrace : WordTrace (prefixWord ++ tailWord_8050539) baseStart_8050539 baseEnd_8050539 := by
    simpa [prefixWord, tailWord_8050539, baseEnd_8050539] using wordTrace_append hprefix tailTrace_8050539
  have hstable : (prefixWord ++ tailWord_8050539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050539).length < 2 ^ (prefixWord ++ tailWord_8050539).sum := by decide
  have hdescent : baseEnd_8050539 < baseStart_8050539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050550 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_8050550 : Nat := 118140960795 + 8050550 * 2 ^ 59
def prefixEnd_8050550 : Nat := 4983230072969 + 3 ^ 40 * 8050550 * 2
def baseEnd_8050550 : Nat := 4133801683053582419801201

theorem tailTrace_8050550 : CollatzResearch.WordTrace tailWord_8050550 prefixEnd_8050550 4133801683053582419801201 := by
  unfold tailWord_8050550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18351730061514984332611319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195751787322826499547854069 18351730061514984332611319)
  ·
    refine ⟨27527595092272476498916979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18351730061514984332611319 27527595092272476498916979)
    ·
      refine ⟨41291392638408714748375469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27527595092272476498916979 41291392638408714748375469)
      ·
        refine ⟨15484272239403268030640801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41291392638408714748375469 15484272239403268030640801)
        ·
          refine ⟨11613204179552451022980601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15484272239403268030640801 11613204179552451022980601)
          ·
            refine ⟨8709903134664338267235451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613204179552451022980601 8709903134664338267235451)
            ·
              refine ⟨13064854701996507400853177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8709903134664338267235451 13064854701996507400853177)
              ·
                refine ⟨9798641026497380550639883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13064854701996507400853177 9798641026497380550639883)
                ·
                  refine ⟨14697961539746070825959825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798641026497380550639883 14697961539746070825959825)
                  ·
                    refine ⟨11023471154809553119469869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14697961539746070825959825 11023471154809553119469869)
                    ·
                      refine ⟨4133801683053582419801201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023471154809553119469869 4133801683053582419801201)
                      ·
                        rfl

theorem cell23_8050550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_8050550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050550 prefixEnd_8050550 := by exact prefixLift 8050550
  have htrace : WordTrace (prefixWord ++ tailWord_8050550) baseStart_8050550 baseEnd_8050550 := by
    simpa [prefixWord, tailWord_8050550, baseEnd_8050550] using wordTrace_append hprefix tailTrace_8050550
  have hstable : (prefixWord ++ tailWord_8050550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050550).length < 2 ^ (prefixWord ++ tailWord_8050550).sum := by decide
  have hdescent : baseEnd_8050550 < baseStart_8050550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050589 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_8050589 : Nat := 118140960795 + 8050589 * 2 ^ 59
def prefixEnd_8050589 : Nat := 4983230072969 + 3 ^ 40 * 8050589 * 2
def baseEnd_8050589 : Nat := 4133821708799107767213521

theorem tailTrace_8050589 : CollatzResearch.WordTrace tailWord_8050589 prefixEnd_8050589 4133821708799107767213521 := by
  unfold tailWord_8050589
  simp only [CollatzResearch.WordTrace]
  refine ⟨293629103431098458982450821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195752735620732305988300547 293629103431098458982450821)
  ·
    refine ⟨55055456893330961059209529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293629103431098458982450821 55055456893330961059209529)
    ·
      refine ⟨41291592669998220794407147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55055456893330961059209529 41291592669998220794407147)
      ·
        refine ⟨61937389004997331191610721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41291592669998220794407147 61937389004997331191610721)
        ·
          refine ⟨46453041753747998393708041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61937389004997331191610721 46453041753747998393708041)
          ·
            refine ⟨34839781315310998795281031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46453041753747998393708041 34839781315310998795281031)
            ·
              refine ⟨52259671972966498192921547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34839781315310998795281031 52259671972966498192921547)
              ·
                refine ⟨78389507959449747289382321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52259671972966498192921547 78389507959449747289382321)
                ·
                  refine ⟨58792130969587310467036741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78389507959449747289382321 58792130969587310467036741)
                  ·
                    refine ⟨11023524556797620712569389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58792130969587310467036741 11023524556797620712569389)
                    ·
                      refine ⟨4133821708799107767213521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023524556797620712569389 4133821708799107767213521)
                      ·
                        rfl

theorem cell23_8050589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_8050589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050589 prefixEnd_8050589 := by exact prefixLift 8050589
  have htrace : WordTrace (prefixWord ++ tailWord_8050589) baseStart_8050589 baseEnd_8050589 := by
    simpa [prefixWord, tailWord_8050589, baseEnd_8050589] using wordTrace_append hprefix tailTrace_8050589
  have hstable : (prefixWord ++ tailWord_8050589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050589).length < 2 ^ (prefixWord ++ tailWord_8050589).sum := by decide
  have hdescent : baseEnd_8050589 < baseStart_8050589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050592 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 7]
def baseStart_8050592 : Nat := 118140960795 + 8050592 * 2 ^ 59
def prefixEnd_8050592 : Nat := 4983230072969 + 3 ^ 40 * 8050592 * 2
def baseEnd_8050592 : Nat := 459313694360119028386223

theorem tailTrace_8050592 : CollatzResearch.WordTrace tailWord_8050592 prefixEnd_8050592 459313694360119028386223 := by
  unfold tailWord_8050592
  simp only [CollatzResearch.WordTrace]
  refine ⟨146814606425043795247405015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195752808566725060329873353 146814606425043795247405015)
  ·
    refine ⟨220221909637565692871107523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146814606425043795247405015 220221909637565692871107523)
    ·
      refine ⟨330332864456348539306661285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220221909637565692871107523 330332864456348539306661285)
      ·
        refine ⟨61937412085565351119998991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330332864456348539306661285 61937412085565351119998991)
        ·
          refine ⟨92906118128348026679998487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61937412085565351119998991 92906118128348026679998487)
          ·
            refine ⟨139359177192522040019997731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92906118128348026679998487 139359177192522040019997731)
            ·
              refine ⟨209038765788783060029996597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139359177192522040019997731 209038765788783060029996597)
              ·
                refine ⟨19597384292698411877812181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209038765788783060029996597 19597384292698411877812181)
                ·
                  refine ⟨459313694360119028386223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19597384292698411877812181 459313694360119028386223)
                  ·
                    rfl

theorem cell23_8050592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_8050592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050592 prefixEnd_8050592 := by exact prefixLift 8050592
  have htrace : WordTrace (prefixWord ++ tailWord_8050592) baseStart_8050592 baseEnd_8050592 := by
    simpa [prefixWord, tailWord_8050592, baseEnd_8050592] using wordTrace_append hprefix tailTrace_8050592
  have hstable : (prefixWord ++ tailWord_8050592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050592).length < 2 ^ (prefixWord ++ tailWord_8050592).sum := by decide
  have hdescent : baseEnd_8050592 < baseStart_8050592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050599 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_8050599 : Nat := 118140960795 + 8050599 * 2 ^ 59
def prefixEnd_8050599 : Nat := 4983230072969 + 3 ^ 40 * 8050599 * 2
def baseEnd_8050599 : Nat := 4133826843605652728088475

theorem tailTrace_8050599 : CollatzResearch.WordTrace tailWord_8050599 prefixEnd_8050599 4133826843605652728088475 := by
  unfold tailWord_8050599
  simp only [CollatzResearch.WordTrace]
  refine ⟨293629468161062230690314851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195752978774041487126876567 293629468161062230690314851)
  ·
    refine ⟨440444202241593346035472277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293629468161062230690314851 440444202241593346035472277)
    ·
      refine ⟨20645821980074688095412763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440444202241593346035472277 20645821980074688095412763)
      ·
        refine ⟨30968732970112032143119145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20645821980074688095412763 30968732970112032143119145)
        ·
          refine ⟨23226549727584024107339359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30968732970112032143119145 23226549727584024107339359)
          ·
            refine ⟨34839824591376036161009039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226549727584024107339359 34839824591376036161009039)
            ·
              refine ⟨52259736887064054241513559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34839824591376036161009039 52259736887064054241513559)
              ·
                refine ⟨78389605330596081362270339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52259736887064054241513559 78389605330596081362270339)
                ·
                  refine ⟨117584407995894122043405509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78389605330596081362270339 117584407995894122043405509)
                  ·
                    refine ⟨22047076499230147883138533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117584407995894122043405509 22047076499230147883138533)
                    ·
                      refine ⟨4133826843605652728088475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22047076499230147883138533 4133826843605652728088475)
                      ·
                        rfl

theorem cell23_8050599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_8050599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050599 prefixEnd_8050599 := by exact prefixLift 8050599
  have htrace : WordTrace (prefixWord ++ tailWord_8050599) baseStart_8050599 baseEnd_8050599 := by
    simpa [prefixWord, tailWord_8050599, baseEnd_8050599] using wordTrace_append hprefix tailTrace_8050599
  have hstable : (prefixWord ++ tailWord_8050599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050599).length < 2 ^ (prefixWord ++ tailWord_8050599).sum := by decide
  have hdescent : baseEnd_8050599 < baseStart_8050599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050609 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 7]
def baseStart_8050609 : Nat := 118140960795 + 8050609 * 2 ^ 59
def prefixEnd_8050609 : Nat := 4983230072969 + 3 ^ 40 * 8050609 * 2
def baseEnd_8050609 : Nat := 459314664268021965440381

theorem tailTrace_8050609 : CollatzResearch.WordTrace tailWord_8050609 prefixEnd_8050609 459314664268021965440381 := by
  unfold tailWord_8050609
  simp only [CollatzResearch.WordTrace]
  refine ⟨293629832891026002398178881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195753221927350668265452587 293629832891026002398178881)
  ·
    refine ⟨220222374668269501798634161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293629832891026002398178881 220222374668269501798634161)
    ·
      refine ⟨165166781001202126348975621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220222374668269501798634161 165166781001202126348975621)
      ·
        refine ⟨30968771437725398690432929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165166781001202126348975621 30968771437725398690432929)
        ·
          refine ⟨23226578578294049017824697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30968771437725398690432929 23226578578294049017824697)
          ·
            refine ⟨17419933933720536763368523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23226578578294049017824697 17419933933720536763368523)
            ·
              refine ⟨26129900900580805145052785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17419933933720536763368523 26129900900580805145052785)
              ·
                refine ⟨19597425675435603858789589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26129900900580805145052785 19597425675435603858789589)
                ·
                  refine ⟨459314664268021965440381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19597425675435603858789589 459314664268021965440381)
                  ·
                    rfl

theorem cell23_8050609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_8050609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050609 prefixEnd_8050609 := by exact prefixLift 8050609
  have htrace : WordTrace (prefixWord ++ tailWord_8050609) baseStart_8050609 baseEnd_8050609 := by
    simpa [prefixWord, tailWord_8050609, baseEnd_8050609] using wordTrace_append hprefix tailTrace_8050609
  have hstable : (prefixWord ++ tailWord_8050609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050609).length < 2 ^ (prefixWord ++ tailWord_8050609).sum := by decide
  have hdescent : baseEnd_8050609 < baseStart_8050609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050629 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_8050629 : Nat := 118140960795 + 8050629 * 2 ^ 59
def prefixEnd_8050629 : Nat := 4983230072969 + 3 ^ 40 * 8050629 * 2
def baseEnd_8050629 : Nat := 4133842248025287610713337

theorem tailTrace_8050629 : CollatzResearch.WordTrace tailWord_8050629 prefixEnd_8050629 4133842248025287610713337 := by
  unfold tailWord_8050629
  simp only [CollatzResearch.WordTrace]
  refine ⟨293630562350953545813906941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195753708233969030542604627 293630562350953545813906941)
  ·
    refine ⟨110111460881607579680215103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293630562350953545813906941 110111460881607579680215103)
    ·
      refine ⟨165167191322411369520322655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110111460881607579680215103 165167191322411369520322655)
      ·
        refine ⟨247750786983617054280483983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165167191322411369520322655 247750786983617054280483983)
        ·
          refine ⟨371626180475425581420725975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247750786983617054280483983 371626180475425581420725975)
          ·
            refine ⟨557439270713138372131088963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371626180475425581420725975 557439270713138372131088963)
            ·
              refine ⟨836158906069707558196633445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557439270713138372131088963 836158906069707558196633445)
              ·
                refine ⟨156779794888070167161868771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836158906069707558196633445 156779794888070167161868771)
                ·
                  refine ⟨235169692332105250742803157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156779794888070167161868771 235169692332105250742803157)
                  ·
                    refine ⟨5511789664033716814284449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235169692332105250742803157 5511789664033716814284449)
                    ·
                      refine ⟨4133842248025287610713337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511789664033716814284449 4133842248025287610713337)
                      ·
                        rfl

theorem cell23_8050629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_8050629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050629 prefixEnd_8050629 := by exact prefixLift 8050629
  have htrace : WordTrace (prefixWord ++ tailWord_8050629) baseStart_8050629 baseEnd_8050629 := by
    simpa [prefixWord, tailWord_8050629, baseEnd_8050629] using wordTrace_append hprefix tailTrace_8050629
  have hstable : (prefixWord ++ tailWord_8050629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050629).length < 2 ^ (prefixWord ++ tailWord_8050629).sum := by decide
  have hdescent : baseEnd_8050629 < baseStart_8050629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050659 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_8050659 : Nat := 118140960795 + 8050659 * 2 ^ 59
def prefixEnd_8050659 : Nat := 4983230072969 + 3 ^ 40 * 8050659 * 2
def baseEnd_8050659 : Nat := 4133857652444922493338199

theorem tailTrace_8050659 : CollatzResearch.WordTrace tailWord_8050659 prefixEnd_8050659 4133857652444922493338199 := by
  unfold tailWord_8050659
  simp only [CollatzResearch.WordTrace]
  refine ⟨293631656540844860937499031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195754437693896573958332687 293631656540844860937499031)
  ·
    refine ⟨440447484811267291406248547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293631656540844860937499031 440447484811267291406248547)
    ·
      refine ⟨660671227216900937109372821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440447484811267291406248547 660671227216900937109372821)
      ·
        refine ⟨30968963775792231427001851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 660671227216900937109372821 30968963775792231427001851)
        ·
          refine ⟨46453445663688347140502777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30968963775792231427001851 46453445663688347140502777)
          ·
            refine ⟨34840084247766260355377083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46453445663688347140502777 34840084247766260355377083)
            ·
              refine ⟨52260126371649390533065625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34840084247766260355377083 52260126371649390533065625)
              ·
                refine ⟨39195094778737042899799219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52260126371649390533065625 39195094778737042899799219)
                ·
                  refine ⟨58792642168105564349698829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39195094778737042899799219 58792642168105564349698829)
                  ·
                    refine ⟨22047240813039586631137061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58792642168105564349698829 22047240813039586631137061)
                    ·
                      refine ⟨4133857652444922493338199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22047240813039586631137061 4133857652444922493338199)
                      ·
                        rfl

theorem cell23_8050659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_8050659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050659 prefixEnd_8050659 := by exact prefixLift 8050659
  have htrace : WordTrace (prefixWord ++ tailWord_8050659) baseStart_8050659 baseEnd_8050659 := by
    simpa [prefixWord, tailWord_8050659, baseEnd_8050659] using wordTrace_append hprefix tailTrace_8050659
  have hstable : (prefixWord ++ tailWord_8050659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050659).length < 2 ^ (prefixWord ++ tailWord_8050659).sum := by decide
  have hdescent : baseEnd_8050659 < baseStart_8050659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050679 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_8050679 : Nat := 118140960795 + 8050679 * 2 ^ 59
def prefixEnd_8050679 : Nat := 4983230072969 + 3 ^ 40 * 8050679 * 2
def baseEnd_8050679 : Nat := 4133867922058012415088107

theorem tailTrace_8050679 : CollatzResearch.WordTrace tailWord_8050679 prefixEnd_8050679 4133867922058012415088107 := by
  unfold tailWord_8050679
  simp only [CollatzResearch.WordTrace]
  refine ⟨293632386000772404353227091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195754924000514936235484727 293632386000772404353227091)
  ·
    refine ⟨440448579001158606529840637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293632386000772404353227091 440448579001158606529840637)
    ·
      refine ⟨165168217125434477448690239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440448579001158606529840637 165168217125434477448690239)
      ·
        refine ⟨247752325688151716173035359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165168217125434477448690239 247752325688151716173035359)
        ·
          refine ⟨371628488532227574259553039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247752325688151716173035359 371628488532227574259553039)
          ·
            refine ⟨557442732798341361389329559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371628488532227574259553039 557442732798341361389329559)
            ·
              refine ⟨836164099197512042083994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557442732798341361389329559 836164099197512042083994339)
              ·
                refine ⟨1254246148796268063125991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836164099197512042083994339 1254246148796268063125991509)
                ·
                  refine ⟨14698197056206266364757713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1254246148796268063125991509 14698197056206266364757713)
                  ·
                    refine ⟨11023647792154699773568285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14698197056206266364757713 11023647792154699773568285)
                    ·
                      refine ⟨4133867922058012415088107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023647792154699773568285 4133867922058012415088107)
                      ·
                        rfl

theorem cell23_8050679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_8050679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050679 prefixEnd_8050679 := by exact prefixLift 8050679
  have htrace : WordTrace (prefixWord ++ tailWord_8050679) baseStart_8050679 baseEnd_8050679 := by
    simpa [prefixWord, tailWord_8050679, baseEnd_8050679] using wordTrace_append hprefix tailTrace_8050679
  have hstable : (prefixWord ++ tailWord_8050679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050679).length < 2 ^ (prefixWord ++ tailWord_8050679).sum := by decide
  have hdescent : baseEnd_8050679 < baseStart_8050679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050694 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_8050694 : Nat := 118140960795 + 8050694 * 2 ^ 59
def prefixEnd_8050694 : Nat := 4983230072969 + 3 ^ 40 * 8050694 * 2
def baseEnd_8050694 : Nat := 459319513807536650711171

theorem tailTrace_8050694 : CollatzResearch.WordTrace tailWord_8050694 prefixEnd_8050694 459319513807536650711171 := by
  unfold tailWord_8050694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176029159241189434844473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195755288730478707943348757 9176029159241189434844473)
  ·
    refine ⟨6882021869430892076133355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9176029159241189434844473 6882021869430892076133355)
    ·
      refine ⟨10323032804146338114200033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6882021869430892076133355 10323032804146338114200033)
      ·
        refine ⟨7742274603109753585650025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10323032804146338114200033 7742274603109753585650025)
        ·
          refine ⟨5806705952332315189237519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7742274603109753585650025 5806705952332315189237519)
          ·
            refine ⟨8710058928498472783856279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806705952332315189237519 8710058928498472783856279)
            ·
              refine ⟨13065088392747709175784419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710058928498472783856279 13065088392747709175784419)
              ·
                refine ⟨19597632589121563763676629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065088392747709175784419 19597632589121563763676629)
                ·
                  refine ⟨459319513807536650711171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19597632589121563763676629 459319513807536650711171)
                  ·
                    rfl

theorem cell23_8050694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_8050694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050694 prefixEnd_8050694 := by exact prefixLift 8050694
  have htrace : WordTrace (prefixWord ++ tailWord_8050694) baseStart_8050694 baseEnd_8050694 := by
    simpa [prefixWord, tailWord_8050694, baseEnd_8050694] using wordTrace_append hprefix tailTrace_8050694
  have hstable : (prefixWord ++ tailWord_8050694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050694).length < 2 ^ (prefixWord ++ tailWord_8050694).sum := by decide
  have hdescent : baseEnd_8050694 < baseStart_8050694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050696 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_8050696 : Nat := 118140960795 + 8050696 * 2 ^ 59
def prefixEnd_8050696 : Nat := 4983230072969 + 3 ^ 40 * 8050696 * 2
def baseEnd_8050696 : Nat := 4133876651229138848575529

theorem tailTrace_8050696 : CollatzResearch.WordTrace tailWord_8050696 prefixEnd_8050696 4133876651229138848575529 := by
  unfold tailWord_8050696
  simp only [CollatzResearch.WordTrace]
  refine ⟨146816503020855408128297971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195755337361140544171063961 146816503020855408128297971)
  ·
    refine ⟨220224754531283112192446957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146816503020855408128297971 220224754531283112192446957)
    ·
      refine ⟨82584282949231167072167609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220224754531283112192446957 82584282949231167072167609)
      ·
        refine ⟨61938212211923375304125707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82584282949231167072167609 61938212211923375304125707)
        ·
          refine ⟨92907318317885062956188561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61938212211923375304125707 92907318317885062956188561)
          ·
            refine ⟨69680488738413797217141421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92907318317885062956188561 69680488738413797217141421)
            ·
              refine ⟨26130183276905173956428033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69680488738413797217141421 26130183276905173956428033)
              ·
                refine ⟨19597637457678880467321025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26130183276905173956428033 19597637457678880467321025)
                ·
                  refine ⟨14698228093259160350490769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19597637457678880467321025 14698228093259160350490769)
                  ·
                    refine ⟨11023671069944370262868077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14698228093259160350490769 11023671069944370262868077)
                    ·
                      refine ⟨4133876651229138848575529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023671069944370262868077 4133876651229138848575529)
                      ·
                        rfl

theorem cell23_8050696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_8050696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050696 prefixEnd_8050696 := by exact prefixLift 8050696
  have htrace : WordTrace (prefixWord ++ tailWord_8050696) baseStart_8050696 baseEnd_8050696 := by
    simpa [prefixWord, tailWord_8050696, baseEnd_8050696] using wordTrace_append hprefix tailTrace_8050696
  have hstable : (prefixWord ++ tailWord_8050696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050696).length < 2 ^ (prefixWord ++ tailWord_8050696).sum := by decide
  have hdescent : baseEnd_8050696 < baseStart_8050696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050699 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 6]
def baseStart_8050699 : Nat := 118140960795 + 8050699 * 2 ^ 59
def prefixEnd_8050699 : Nat := 4983230072969 + 3 ^ 40 * 8050699 * 2
def baseEnd_8050699 : Nat := 459319799074566926315335

theorem tailTrace_8050699 : CollatzResearch.WordTrace tailWord_8050699 prefixEnd_8050699 459319799074566926315335 := by
  unfold tailWord_8050699
  simp only [CollatzResearch.WordTrace]
  refine ⟨293633115460699947768955151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195755410307133298512636767 293633115460699947768955151)
  ·
    refine ⟨440449673191049921653432727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293633115460699947768955151 440449673191049921653432727)
    ·
      refine ⟨660674509786574882480149091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440449673191049921653432727 660674509786574882480149091)
      ·
        refine ⟨991011764679862323720223637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660674509786574882480149091 991011764679862323720223637)
        ·
          refine ⟨46453676469368546424385483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 991011764679862323720223637 46453676469368546424385483)
          ·
            refine ⟨69680514704052819636578225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46453676469368546424385483 69680514704052819636578225)
            ·
              refine ⟨52260386028039614727433669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69680514704052819636578225 52260386028039614727433669)
              ·
                refine ⟨9798822380257427761393813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52260386028039614727433669 9798822380257427761393813)
                ·
                  refine ⟨459319799074566926315335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9798822380257427761393813 459319799074566926315335)
                  ·
                    rfl

theorem cell23_8050699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 6].length) (baseStart_8050699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050699 prefixEnd_8050699 := by exact prefixLift 8050699
  have htrace : WordTrace (prefixWord ++ tailWord_8050699) baseStart_8050699 baseEnd_8050699 := by
    simpa [prefixWord, tailWord_8050699, baseEnd_8050699] using wordTrace_append hprefix tailTrace_8050699
  have hstable : (prefixWord ++ tailWord_8050699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050699).length < 2 ^ (prefixWord ++ tailWord_8050699).sum := by decide
  have hdescent : baseEnd_8050699 < baseStart_8050699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050716 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 6]
def baseStart_8050716 : Nat := 118140960795 + 8050716 * 2 ^ 59
def prefixEnd_8050716 : Nat := 4983230072969 + 3 ^ 40 * 8050716 * 2
def baseEnd_8050716 : Nat := 459320768982469863369493

theorem tailTrace_8050716 : CollatzResearch.WordTrace tailWord_8050716 prefixEnd_8050716 459320768982469863369493 := by
  unfold tailWord_8050716
  simp only [CollatzResearch.WordTrace]
  refine ⟨146816867750819179836162001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195755823667758906448216001 146816867750819179836162001)
  ·
    refine ⟨110112650813114384877121501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146816867750819179836162001 110112650813114384877121501)
    ·
      refine ⟨41292244054917894328920563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110112650813114384877121501 41292244054917894328920563)
      ·
        refine ⟨61938366082376841493380845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41292244054917894328920563 61938366082376841493380845)
        ·
          refine ⟨23226887280891315560017817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61938366082376841493380845 23226887280891315560017817)
          ·
            refine ⟨17420165460668486670013363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23226887280891315560017817 17420165460668486670013363)
            ·
              refine ⟨26130248191002730005020045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17420165460668486670013363 26130248191002730005020045)
              ·
                refine ⟨9798843071626023751882517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26130248191002730005020045 9798843071626023751882517)
                ·
                  refine ⟨459320768982469863369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9798843071626023751882517 459320768982469863369493)
                  ·
                    rfl

theorem cell23_8050716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_8050716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050716 prefixEnd_8050716 := by exact prefixLift 8050716
  have htrace : WordTrace (prefixWord ++ tailWord_8050716) baseStart_8050716 baseEnd_8050716 := by
    simpa [prefixWord, tailWord_8050716, baseEnd_8050716] using wordTrace_append hprefix tailTrace_8050716
  have hstable : (prefixWord ++ tailWord_8050716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050716).length < 2 ^ (prefixWord ++ tailWord_8050716).sum := by decide
  have hdescent : baseEnd_8050716 < baseStart_8050716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050759 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 3, 6]
def baseStart_8050759 : Nat := 118140960795 + 8050759 * 2 ^ 59
def prefixEnd_8050759 : Nat := 4983230072969 + 3 ^ 40 * 8050759 * 2
def baseEnd_8050759 : Nat := 1377969666836790700695913

theorem tailTrace_8050759 : CollatzResearch.WordTrace tailWord_8050759 prefixEnd_8050759 1377969666836790700695913 := by
  unfold tailWord_8050759
  simp only [CollatzResearch.WordTrace]
  refine ⟨293635303840482578016139331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195756869226988385344092887 293635303840482578016139331)
  ·
    refine ⟨440452955760723867024208997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293635303840482578016139331 440452955760723867024208997)
    ·
      refine ⟨82584929205135725067039187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440452955760723867024208997 82584929205135725067039187)
      ·
        refine ⟨123877393807703587600558781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82584929205135725067039187 123877393807703587600558781)
        ·
          refine ⟨46454022677888845350209543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123877393807703587600558781 46454022677888845350209543)
          ·
            refine ⟨69681034016833268025314315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46454022677888845350209543 69681034016833268025314315)
            ·
              refine ⟨104521551025249902037971473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69681034016833268025314315 104521551025249902037971473)
              ·
                refine ⟨78391163268937426528478605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104521551025249902037971473 78391163268937426528478605)
                ·
                  refine ⟨29396686225851534948179477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78391163268937426528478605 29396686225851534948179477)
                  ·
                    refine ⟨1377969666836790700695913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29396686225851534948179477 1377969666836790700695913)
                    ·
                      rfl

theorem cell23_8050759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_8050759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050759 prefixEnd_8050759 := by exact prefixLift 8050759
  have htrace : WordTrace (prefixWord ++ tailWord_8050759) baseStart_8050759 baseEnd_8050759 := by
    simpa [prefixWord, tailWord_8050759, baseEnd_8050759] using wordTrace_append hprefix tailTrace_8050759
  have hstable : (prefixWord ++ tailWord_8050759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050759).length < 2 ^ (prefixWord ++ tailWord_8050759).sum := by decide
  have hdescent : baseEnd_8050759 < baseStart_8050759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050766 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_8050766 : Nat := 118140960795 + 8050766 * 2 ^ 59
def prefixEnd_8050766 : Nat := 4983230072969 + 3 ^ 40 * 8050766 * 2
def baseEnd_8050766 : Nat := 4133912594874953574700207

theorem tailTrace_8050766 : CollatzResearch.WordTrace tailWord_8050766 prefixEnd_8050766 4133912594874953574700207 := by
  unfold tailWord_8050766
  simp only [CollatzResearch.WordTrace]
  refine ⟨36704444893932152276455519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195757039434304812141096101 36704444893932152276455519)
  ·
    refine ⟨55056667340898228414683279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36704444893932152276455519 55056667340898228414683279)
    ·
      refine ⟨82585001011347342622024919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55056667340898228414683279 82585001011347342622024919)
      ·
        refine ⟨123877501517021013933037379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82585001011347342622024919 123877501517021013933037379)
        ·
          refine ⟨185816252275531520899556069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123877501517021013933037379 185816252275531520899556069)
          ·
            refine ⟨34840547301662160168666763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185816252275531520899556069 34840547301662160168666763)
            ·
              refine ⟨52260820952493240253000145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34840547301662160168666763 52260820952493240253000145)
              ·
                refine ⟨39195615714369930189750109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52260820952493240253000145 39195615714369930189750109)
                ·
                  refine ⟨14698355892888723821156291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39195615714369930189750109 14698355892888723821156291)
                  ·
                    refine ⟨22047533839333085731734437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14698355892888723821156291 22047533839333085731734437)
                    ·
                      refine ⟨4133912594874953574700207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22047533839333085731734437 4133912594874953574700207)
                      ·
                        rfl

theorem cell23_8050766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_8050766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050766 prefixEnd_8050766 := by exact prefixLift 8050766
  have htrace : WordTrace (prefixWord ++ tailWord_8050766) baseStart_8050766 baseEnd_8050766 := by
    simpa [prefixWord, tailWord_8050766, baseEnd_8050766] using wordTrace_append hprefix tailTrace_8050766
  have hstable : (prefixWord ++ tailWord_8050766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050766).length < 2 ^ (prefixWord ++ tailWord_8050766).sum := by decide
  have hdescent : baseEnd_8050766 < baseStart_8050766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050769 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_8050769 : Nat := 118140960795 + 8050769 * 2 ^ 59
def prefixEnd_8050769 : Nat := 4983230072969 + 3 ^ 40 * 8050769 * 2
def baseEnd_8050769 : Nat := 4133914135316917062962693

theorem tailTrace_8050769 : CollatzResearch.WordTrace tailWord_8050769 prefixEnd_8050769 4133914135316917062962693 := by
  unfold tailWord_8050769
  simp only [CollatzResearch.WordTrace]
  refine ⟨293635668570446349724003361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195757112380297566482668907 293635668570446349724003361)
  ·
    refine ⟨220226751427834762293002521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293635668570446349724003361 220226751427834762293002521)
    ·
      refine ⟨165170063570876071719751891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220226751427834762293002521 165170063570876071719751891)
      ·
        refine ⟨247755095356314107579627837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165170063570876071719751891 247755095356314107579627837)
        ·
          refine ⟨92908160758617790342360439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247755095356314107579627837 92908160758617790342360439)
          ·
            refine ⟨139362241137926685513540659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92908160758617790342360439 139362241137926685513540659)
            ·
              refine ⟨209043361706890028270310989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139362241137926685513540659 209043361706890028270310989)
              ·
                refine ⟨78391260640083760601366621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209043361706890028270310989 78391260640083760601366621)
                ·
                  refine ⟨29396722740031410225512483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78391260640083760601366621 29396722740031410225512483)
                  ·
                    refine ⟨44095084110047115338268725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29396722740031410225512483 44095084110047115338268725)
                    ·
                      refine ⟨4133914135316917062962693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44095084110047115338268725 4133914135316917062962693)
                      ·
                        rfl

theorem cell23_8050769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_8050769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050769 prefixEnd_8050769 := by exact prefixLift 8050769
  have htrace : WordTrace (prefixWord ++ tailWord_8050769) baseStart_8050769 baseEnd_8050769 := by
    simpa [prefixWord, tailWord_8050769, baseEnd_8050769] using wordTrace_append hprefix tailTrace_8050769
  have hstable : (prefixWord ++ tailWord_8050769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050769).length < 2 ^ (prefixWord ++ tailWord_8050769).sum := by decide
  have hdescent : baseEnd_8050769 < baseStart_8050769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050776 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_8050776 : Nat := 118140960795 + 8050776 * 2 ^ 59
def prefixEnd_8050776 : Nat := 4983230072969 + 3 ^ 40 * 8050776 * 2
def baseEnd_8050776 : Nat := 1377972576560499511858387

theorem tailTrace_8050776 : CollatzResearch.WordTrace tailWord_8050776 prefixEnd_8050776 1377972576560499511858387 := by
  unfold tailWord_8050776
  simp only [CollatzResearch.WordTrace]
  refine ⟨146817961940710494959754091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195757282587613993279672121 146817961940710494959754091)
  ·
    refine ⟨220226942911065742439631137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146817961940710494959754091 220226942911065742439631137)
    ·
      refine ⟨165170207183299306829723353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220226942911065742439631137 165170207183299306829723353)
      ·
        refine ⟨123877655387474480122292515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165170207183299306829723353 123877655387474480122292515)
        ·
          refine ⟨185816483081211720183438773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123877655387474480122292515 185816483081211720183438773)
          ·
            refine ⟨17420295288863598767197385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185816483081211720183438773 17420295288863598767197385)
            ·
              refine ⟨13065221466647699075398039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17420295288863598767197385 13065221466647699075398039)
              ·
                refine ⟨19597832199971548613097059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065221466647699075398039 19597832199971548613097059)
                ·
                  refine ⟨29396748299957322919645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19597832199971548613097059 29396748299957322919645589)
                  ·
                    refine ⟨1377972576560499511858387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29396748299957322919645589 1377972576560499511858387)
                    ·
                      rfl

theorem cell23_8050776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_8050776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050776 prefixEnd_8050776 := by exact prefixLift 8050776
  have htrace : WordTrace (prefixWord ++ tailWord_8050776) baseStart_8050776 baseEnd_8050776 := by
    simpa [prefixWord, tailWord_8050776, baseEnd_8050776] using wordTrace_append hprefix tailTrace_8050776
  have hstable : (prefixWord ++ tailWord_8050776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050776).length < 2 ^ (prefixWord ++ tailWord_8050776).sum := by decide
  have hdescent : baseEnd_8050776 < baseStart_8050776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050796 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_8050796 : Nat := 118140960795 + 8050796 * 2 ^ 59
def prefixEnd_8050796 : Nat := 4983230072969 + 3 ^ 40 * 8050796 * 2
def baseEnd_8050796 : Nat := 4133927999294588457325069

theorem tailTrace_8050796 : CollatzResearch.WordTrace tailWord_8050796 prefixEnd_8050796 4133927999294588457325069 := by
  unfold tailWord_8050796
  simp only [CollatzResearch.WordTrace]
  refine ⟨146818326670674266667618121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195757768894232355556824161 146818326670674266667618121)
  ·
    refine ⟨110113745003005700000713591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146818326670674266667618121 110113745003005700000713591)
    ·
      refine ⟨165170617504508550001070387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110113745003005700000713591 165170617504508550001070387)
      ·
        refine ⟨247755926256762825001605581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165170617504508550001070387 247755926256762825001605581)
        ·
          refine ⟨92908472346286059375602093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247755926256762825001605581 92908472346286059375602093)
          ·
            refine ⟨34840677129857272265850785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92908472346286059375602093 34840677129857272265850785)
            ·
              refine ⟨26130507847392954199388089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34840677129857272265850785 26130507847392954199388089)
              ·
                refine ⟨19597880885544715649541067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26130507847392954199388089 19597880885544715649541067)
                ·
                  refine ⟨29396821328317073474311601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19597880885544715649541067 29396821328317073474311601)
                  ·
                    refine ⟨22047615996237805105733701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29396821328317073474311601 22047615996237805105733701)
                    ·
                      refine ⟨4133927999294588457325069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22047615996237805105733701 4133927999294588457325069)
                      ·
                        rfl

theorem cell23_8050796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_8050796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050796 prefixEnd_8050796 := by exact prefixLift 8050796
  have htrace : WordTrace (prefixWord ++ tailWord_8050796) baseStart_8050796 baseEnd_8050796 := by
    simpa [prefixWord, tailWord_8050796, baseEnd_8050796] using wordTrace_append hprefix tailTrace_8050796
  have hstable : (prefixWord ++ tailWord_8050796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050796).length < 2 ^ (prefixWord ++ tailWord_8050796).sum := by decide
  have hdescent : baseEnd_8050796 < baseStart_8050796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050800 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4]
def baseStart_8050800 : Nat := 118140960795 + 8050800 * 2 ^ 59
def prefixEnd_8050800 : Nat := 4983230072969 + 3 ^ 40 * 8050800 * 2
def baseEnd_8050800 : Nat := 4133930053217206441675051

theorem tailTrace_8050800 : CollatzResearch.WordTrace tailWord_8050800 prefixEnd_8050800 4133930053217206441675051 := by
  unfold tailWord_8050800
  simp only [CollatzResearch.WordTrace]
  refine ⟨146818399616667021009190927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195757866155556028012254569 146818399616667021009190927)
  ·
    refine ⟨220227599425000531513786391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146818399616667021009190927 220227599425000531513786391)
    ·
      refine ⟨330341399137500797270679587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220227599425000531513786391 330341399137500797270679587)
      ·
        refine ⟨495512098706251195906019381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330341399137500797270679587 495512098706251195906019381)
        ·
          refine ⟨46454259253711049616189317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 495512098706251195906019381 46454259253711049616189317)
          ·
            refine ⟨8710173610070821803035497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46454259253711049616189317 8710173610070821803035497)
            ·
              refine ⟨6532630207553116352276623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710173610070821803035497 6532630207553116352276623)
              ·
                refine ⟨9798945311329674528414935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532630207553116352276623 9798945311329674528414935)
                ·
                  refine ⟨14698417966994511792622403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798945311329674528414935 14698417966994511792622403)
                  ·
                    refine ⟨22047626950491767688933605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14698417966994511792622403 22047626950491767688933605)
                    ·
                      refine ⟨4133930053217206441675051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22047626950491767688933605 4133930053217206441675051)
                      ·
                        rfl

theorem cell23_8050800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 1, 4].length) (baseStart_8050800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050800 prefixEnd_8050800 := by exact prefixLift 8050800
  have htrace : WordTrace (prefixWord ++ tailWord_8050800) baseStart_8050800 baseEnd_8050800 := by
    simpa [prefixWord, tailWord_8050800, baseEnd_8050800] using wordTrace_append hprefix tailTrace_8050800
  have hstable : (prefixWord ++ tailWord_8050800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050800).length < 2 ^ (prefixWord ++ tailWord_8050800).sum := by decide
  have hdescent : baseEnd_8050800 < baseStart_8050800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050806 : List Nat := [5, 1, 1, 2, 1, 3, 10]
def baseStart_8050806 : Nat := 118140960795 + 8050806 * 2 ^ 59
def prefixEnd_8050806 : Nat := 4983230072969 + 3 ^ 40 * 8050806 * 2
def baseEnd_8050806 : Nat := 51036211532112758249383

theorem tailTrace_8050806 : CollatzResearch.WordTrace tailWord_8050806 prefixEnd_8050806 51036211532112758249383 := by
  unfold tailWord_8050806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352313629457019065193767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195758012047541536695400181 18352313629457019065193767)
  ·
    refine ⟨27528470444185528597790651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18352313629457019065193767 27528470444185528597790651)
    ·
      refine ⟨41292705666278292896685977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27528470444185528597790651 41292705666278292896685977)
      ·
        refine ⟨30969529249708719672514483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41292705666278292896685977 30969529249708719672514483)
        ·
          refine ⟨46454293874563079508771725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30969529249708719672514483 46454293874563079508771725)
          ·
            refine ⟨17420360202961154815789397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46454293874563079508771725 17420360202961154815789397)
            ·
              refine ⟨51036211532112758249383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17420360202961154815789397 51036211532112758249383)
              ·
                rfl

theorem cell23_8050806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 10].length) (baseStart_8050806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050806 prefixEnd_8050806 := by exact prefixLift 8050806
  have htrace : WordTrace (prefixWord ++ tailWord_8050806) baseStart_8050806 baseEnd_8050806 := by
    simpa [prefixWord, tailWord_8050806, baseEnd_8050806] using wordTrace_append hprefix tailTrace_8050806
  have hstable : (prefixWord ++ tailWord_8050806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050806).length < 2 ^ (prefixWord ++ tailWord_8050806).sum := by decide
  have hdescent : baseEnd_8050806 < baseStart_8050806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050817 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_8050817 : Nat := 118140960795 + 8050817 * 2 ^ 59
def prefixEnd_8050817 : Nat := 4983230072969 + 3 ^ 40 * 8050817 * 2
def baseEnd_8050817 : Nat := 4133938782388332875162473

theorem tailTrace_8050817 : CollatzResearch.WordTrace tailWord_8050817 prefixEnd_8050817 4133938782388332875162473 := by
  unfold tailWord_8050817
  simp only [CollatzResearch.WordTrace]
  refine ⟨293637419274272453921750705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195758279516181635947833803 293637419274272453921750705)
  ·
    refine ⟨220228064455704340441313029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293637419274272453921750705 220228064455704340441313029)
    ·
      refine ⟨41292762085444563832746193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220228064455704340441313029 41292762085444563832746193)
      ·
        refine ⟨30969571564083422874559645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41292762085444563832746193 30969571564083422874559645)
        ·
          refine ⟨11613589336531283577959867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30969571564083422874559645 11613589336531283577959867)
          ·
            refine ⟨17420384004796925366939801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11613589336531283577959867 17420384004796925366939801)
            ·
              refine ⟨13065288003597694025204851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17420384004796925366939801 13065288003597694025204851)
              ·
                refine ⟨19597932005396541037807277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065288003597694025204851 19597932005396541037807277)
                ·
                  refine ⟨7349224502023702889177729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19597932005396541037807277 7349224502023702889177729)
                  ·
                    refine ⟨5511918376517777166883297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349224502023702889177729 5511918376517777166883297)
                    ·
                      refine ⟨4133938782388332875162473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511918376517777166883297 4133938782388332875162473)
                      ·
                        rfl

theorem cell23_8050817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_8050817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050817 prefixEnd_8050817 := by exact prefixLift 8050817
  have htrace : WordTrace (prefixWord ++ tailWord_8050817) baseStart_8050817 baseEnd_8050817 := by
    simpa [prefixWord, tailWord_8050817, baseEnd_8050817] using wordTrace_append hprefix tailTrace_8050817
  have hstable : (prefixWord ++ tailWord_8050817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050817).length < 2 ^ (prefixWord ++ tailWord_8050817).sum := by decide
  have hdescent : baseEnd_8050817 < baseStart_8050817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050830 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_8050830 : Nat := 118140960795 + 8050830 * 2 ^ 59
def prefixEnd_8050830 : Nat := 4983230072969 + 3 ^ 40 * 8050830 * 2
def baseEnd_8050830 : Nat := 4133945457636841324299913

theorem tailTrace_8050830 : CollatzResearch.WordTrace tailWord_8050830 prefixEnd_8050830 4133945457636841324299913 := by
  unfold tailWord_8050830
  simp only [CollatzResearch.WordTrace]
  refine ⟨36704736677903169642746743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195758595615483571427982629 36704736677903169642746743)
  ·
    refine ⟨55057105016854754464120115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36704736677903169642746743 55057105016854754464120115)
    ·
      refine ⟨82585657525282131696180173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55057105016854754464120115 82585657525282131696180173)
      ·
        refine ⟨30969621571980799386067565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82585657525282131696180173 30969621571980799386067565)
        ·
          refine ⟨11613608089492799769775337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30969621571980799386067565 11613608089492799769775337)
          ·
            refine ⟨8710206067119599827331503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613608089492799769775337 8710206067119599827331503)
            ·
              refine ⟨13065309100679399740997255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710206067119599827331503 13065309100679399740997255)
              ·
                refine ⟨19597963651019099611495883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065309100679399740997255 19597963651019099611495883)
                ·
                  refine ⟨29396945476528649417243825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19597963651019099611495883 29396945476528649417243825)
                  ·
                    refine ⟨22047709107396487062932869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29396945476528649417243825 22047709107396487062932869)
                    ·
                      refine ⟨4133945457636841324299913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22047709107396487062932869 4133945457636841324299913)
                      ·
                        rfl

theorem cell23_8050830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_8050830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050830 prefixEnd_8050830 := by exact prefixLift 8050830
  have htrace : WordTrace (prefixWord ++ tailWord_8050830) baseStart_8050830 baseEnd_8050830 := by
    simpa [prefixWord, tailWord_8050830, baseEnd_8050830] using wordTrace_append hprefix tailTrace_8050830
  have hstable : (prefixWord ++ tailWord_8050830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050830).length < 2 ^ (prefixWord ++ tailWord_8050830).sum := by decide
  have hdescent : baseEnd_8050830 < baseStart_8050830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050840 : List Nat := [2, 1, 2, 4, 4, 1, 2, 7]
def baseStart_8050840 : Nat := 118140960795 + 8050840 * 2 ^ 59
def prefixEnd_8050840 : Nat := 4983230072969 + 3 ^ 40 * 8050840 * 2
def baseEnd_8050840 : Nat := 153109281201606899450921

theorem tailTrace_8050840 : CollatzResearch.WordTrace tailWord_8050840 prefixEnd_8050840 153109281201606899450921 := by
  unfold tailWord_8050840
  simp only [CollatzResearch.WordTrace]
  refine ⟨146819129076594564424918987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195758838768792752566558649 146819129076594564424918987)
  ·
    refine ⟨220228693614891846637378481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146819129076594564424918987 220228693614891846637378481)
    ·
      refine ⟨165171520211168884978033861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220228693614891846637378481 165171520211168884978033861)
      ·
        refine ⟨30969660039594165933381349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165171520211168884978033861 30969660039594165933381349)
        ·
          refine ⟨5806811257423906112509003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30969660039594165933381349 5806811257423906112509003)
          ·
            refine ⟨8710216886135859168763505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806811257423906112509003 8710216886135859168763505)
            ·
              refine ⟨6532662664601894376572629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710216886135859168763505 6532662664601894376572629)
              ·
                refine ⟨153109281201606899450921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6532662664601894376572629 153109281201606899450921)
                ·
                  rfl

theorem cell23_8050840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 7].length) (baseStart_8050840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050840 prefixEnd_8050840 := by exact prefixLift 8050840
  have htrace : WordTrace (prefixWord ++ tailWord_8050840) baseStart_8050840 baseEnd_8050840 := by
    simpa [prefixWord, tailWord_8050840, baseEnd_8050840] using wordTrace_append hprefix tailTrace_8050840
  have hstable : (prefixWord ++ tailWord_8050840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050840).length < 2 ^ (prefixWord ++ tailWord_8050840).sum := by decide
  have hdescent : baseEnd_8050840 < baseStart_8050840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050850 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_8050850 : Nat := 118140960795 + 8050850 * 2 ^ 59
def prefixEnd_8050850 : Nat := 4983230072969 + 3 ^ 40 * 8050850 * 2
def baseEnd_8050850 : Nat := 4133955727249931246049821

theorem tailTrace_8050850 : CollatzResearch.WordTrace tailWord_8050850 prefixEnd_8050850 4133955727249931246049821 := by
  unfold tailWord_8050850
  simp only [CollatzResearch.WordTrace]
  refine ⟨73409655720788225139425501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195759081922101933705134669 73409655720788225139425501)
  ·
    refine ⟨27528620895295584427284563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73409655720788225139425501 27528620895295584427284563)
    ·
      refine ⟨41292931342943376640926845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27528620895295584427284563 41292931342943376640926845)
      ·
        refine ⟨15484849253603766240347567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41292931342943376640926845 15484849253603766240347567)
        ·
          refine ⟨23227273880405649360521351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15484849253603766240347567 23227273880405649360521351)
          ·
            refine ⟨34840910820608474040782027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23227273880405649360521351 34840910820608474040782027)
            ·
              refine ⟨52261366230912711061173041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34840910820608474040782027 52261366230912711061173041)
              ·
                refine ⟨39196024673184533295879781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52261366230912711061173041 39196024673184533295879781)
                ·
                  refine ⟨7349254626222099992977459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39196024673184533295879781 7349254626222099992977459)
                  ·
                    refine ⟨11023881939333149989466189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349254626222099992977459 11023881939333149989466189)
                    ·
                      refine ⟨4133955727249931246049821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023881939333149989466189 4133955727249931246049821)
                      ·
                        rfl

theorem cell23_8050850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_8050850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050850 prefixEnd_8050850 := by exact prefixLift 8050850
  have htrace : WordTrace (prefixWord ++ tailWord_8050850) baseStart_8050850 baseEnd_8050850 := by
    simpa [prefixWord, tailWord_8050850, baseEnd_8050850] using wordTrace_append hprefix tailTrace_8050850
  have hstable : (prefixWord ++ tailWord_8050850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050850).length < 2 ^ (prefixWord ++ tailWord_8050850).sum := by decide
  have hdescent : baseEnd_8050850 < baseStart_8050850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050868 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_8050868 : Nat := 118140960795 + 8050868 * 2 ^ 59
def prefixEnd_8050868 : Nat := 4983230072969 + 3 ^ 40 * 8050868 * 2
def baseEnd_8050868 : Nat := 4133964969901712175624739

theorem tailTrace_8050868 : CollatzResearch.WordTrace tailWord_8050868 prefixEnd_8050868 4133964969901712175624739 := by
  unfold tailWord_8050868
  simp only [CollatzResearch.WordTrace]
  refine ⟨146819639698543844815928629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195759519598058459754571505 146819639698543844815928629)
  ·
    refine ⟨13764341221738485451493309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146819639698543844815928629 13764341221738485451493309)
    ·
      refine ⟨5161627958151932044309991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13764341221738485451493309 5161627958151932044309991)
      ·
        refine ⟨7742441937227898066464987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161627958151932044309991 7742441937227898066464987)
        ·
          refine ⟨11613662905841847099697481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742441937227898066464987 11613662905841847099697481)
          ·
            refine ⟨8710247179381385324773111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613662905841847099697481 8710247179381385324773111)
            ·
              refine ⟨13065370769072077987159667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710247179381385324773111 13065370769072077987159667)
              ·
                refine ⟨19598056153608116980739501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065370769072077987159667 19598056153608116980739501)
                ·
                  refine ⟨7349271057603043867777313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19598056153608116980739501 7349271057603043867777313)
                  ·
                    refine ⟨5511953293202282900832985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349271057603043867777313 5511953293202282900832985)
                    ·
                      refine ⟨4133964969901712175624739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5511953293202282900832985 4133964969901712175624739)
                      ·
                        rfl

theorem cell23_8050868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_8050868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050868 prefixEnd_8050868 := by exact prefixLift 8050868
  have htrace : WordTrace (prefixWord ++ tailWord_8050868) baseStart_8050868 baseEnd_8050868 := by
    simpa [prefixWord, tailWord_8050868, baseEnd_8050868] using wordTrace_append hprefix tailTrace_8050868
  have hstable : (prefixWord ++ tailWord_8050868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050868).length < 2 ^ (prefixWord ++ tailWord_8050868).sum := by decide
  have hdescent : baseEnd_8050868 < baseStart_8050868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050884 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_8050884 : Nat := 118140960795 + 8050884 * 2 ^ 59
def prefixEnd_8050884 : Nat := 4983230072969 + 3 ^ 40 * 8050884 * 2
def baseEnd_8050884 : Nat := 4133973185592184113024665

theorem tailTrace_8050884 : CollatzResearch.WordTrace tailWord_8050884 prefixEnd_8050884 4133973185592184113024665 := by
  unfold tailWord_8050884
  simp only [CollatzResearch.WordTrace]
  refine ⟨146819931482514862182219853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195759908643353149576293137 146819931482514862182219853)
  ·
    refine ⟨55057474305943073318332445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146819931482514862182219853 55057474305943073318332445)
    ·
      refine ⟨20646552864728652494374667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55057474305943073318332445 20646552864728652494374667)
      ·
        refine ⟨30969829297092978741562001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20646552864728652494374667 30969829297092978741562001)
        ·
          refine ⟨23227371972819734056171501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30969829297092978741562001 23227371972819734056171501)
          ·
            refine ⟨8710264489807400271064313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23227371972819734056171501 8710264489807400271064313)
            ·
              refine ⟨6532698367355550203298235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710264489807400271064313 6532698367355550203298235)
              ·
                refine ⟨9799047551033325304947353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532698367355550203298235 9799047551033325304947353)
                ·
                  refine ⟨7349285663274993978710515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799047551033325304947353 7349285663274993978710515)
                  ·
                    refine ⟨11023928494912490968065773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349285663274993978710515 11023928494912490968065773)
                    ·
                      refine ⟨4133973185592184113024665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11023928494912490968065773 4133973185592184113024665)
                      ·
                        rfl

theorem cell23_8050884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_8050884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050884 prefixEnd_8050884 := by exact prefixLift 8050884
  have htrace : WordTrace (prefixWord ++ tailWord_8050884) baseStart_8050884 baseEnd_8050884 := by
    simpa [prefixWord, tailWord_8050884, baseEnd_8050884] using wordTrace_append hprefix tailTrace_8050884
  have hstable : (prefixWord ++ tailWord_8050884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050884).length < 2 ^ (prefixWord ++ tailWord_8050884).sum := by decide
  have hdescent : baseEnd_8050884 < baseStart_8050884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050913 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 5]
def baseStart_8050913 : Nat := 118140960795 + 8050913 * 2 ^ 59
def prefixEnd_8050913 : Nat := 4983230072969 + 3 ^ 40 * 8050913 * 2
def baseEnd_8050913 : Nat := 459332008503462722173559

theorem tailTrace_8050913 : CollatzResearch.WordTrace tailWord_8050913 prefixEnd_8050913 459332008503462722173559 := by
  unfold tailWord_8050913
  simp only [CollatzResearch.WordTrace]
  refine ⟨293640920681924662317245393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195760613787949774878163595 293640920681924662317245393)
  ·
    refine ⟨220230690511443496737934045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293640920681924662317245393 220230690511443496737934045)
    ·
      refine ⟨82586508941791311276725267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220230690511443496737934045 82586508941791311276725267)
      ·
        refine ⟨123879763412686966915087901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82586508941791311276725267 123879763412686966915087901)
        ·
          refine ⟨46454911279757612593157963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123879763412686966915087901 46454911279757612593157963)
          ·
            refine ⟨69682366919636418889736945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46454911279757612593157963 69682366919636418889736945)
            ·
              refine ⟨52261775189727314167302709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69682366919636418889736945 52261775189727314167302709)
              ·
                refine ⟨4899541424036935703184629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52261775189727314167302709 4899541424036935703184629)
                ·
                  refine ⟨459332008503462722173559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899541424036935703184629 459332008503462722173559)
                  ·
                    rfl

theorem cell23_8050913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 5].length) (baseStart_8050913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050913 prefixEnd_8050913 := by exact prefixLift 8050913
  have htrace : WordTrace (prefixWord ++ tailWord_8050913) baseStart_8050913 baseEnd_8050913 := by
    simpa [prefixWord, tailWord_8050913, baseEnd_8050913] using wordTrace_append hprefix tailTrace_8050913
  have hstable : (prefixWord ++ tailWord_8050913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050913).length < 2 ^ (prefixWord ++ tailWord_8050913).sum := by decide
  have hdescent : baseEnd_8050913 < baseStart_8050913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050926 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_8050926 : Nat := 118140960795 + 8050926 * 2 ^ 59
def prefixEnd_8050926 : Nat := 4983230072969 + 3 ^ 40 * 8050926 * 2
def baseEnd_8050926 : Nat := 1377998250593224316233157

theorem tailTrace_8050926 : CollatzResearch.WordTrace tailWord_8050926 prefixEnd_8050926 1377998250593224316233157 := by
  unfold tailWord_8050926
  simp only [CollatzResearch.WordTrace]
  refine ⟨36705174353859695692183579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195760929887251710358312421 36705174353859695692183579)
  ·
    refine ⟨55057761530789543538275369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36705174353859695692183579 55057761530789543538275369)
    ·
      refine ⟨41293321148092157653706527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55057761530789543538275369 41293321148092157653706527)
      ·
        refine ⟨61939981722138236480559791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41293321148092157653706527 61939981722138236480559791)
        ·
          refine ⟨92909972583207354720839687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61939981722138236480559791 92909972583207354720839687)
          ·
            refine ⟨139364958874811032081259531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92909972583207354720839687 139364958874811032081259531)
            ·
              refine ⟨209047438312216548121889297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139364958874811032081259531 209047438312216548121889297)
              ·
                refine ⟨156785578734162411091416973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209047438312216548121889297 156785578734162411091416973)
                ·
                  refine ⟨58794592025310904159281365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156785578734162411091416973 58794592025310904159281365)
                  ·
                    refine ⟨1377998250593224316233157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58794592025310904159281365 1377998250593224316233157)
                    ·
                      rfl

theorem cell23_8050926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_8050926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050926 prefixEnd_8050926 := by exact prefixLift 8050926
  have htrace : WordTrace (prefixWord ++ tailWord_8050926) baseStart_8050926 baseEnd_8050926 := by
    simpa [prefixWord, tailWord_8050926, baseEnd_8050926] using wordTrace_append hprefix tailTrace_8050926
  have hstable : (prefixWord ++ tailWord_8050926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050926).length < 2 ^ (prefixWord ++ tailWord_8050926).sum := by decide
  have hdescent : baseEnd_8050926 < baseStart_8050926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050930 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_8050930 : Nat := 118140960795 + 8050930 * 2 ^ 59
def prefixEnd_8050930 : Nat := 4983230072969 + 3 ^ 40 * 8050930 * 2
def baseEnd_8050930 : Nat := 459332978411365659227717

theorem tailTrace_8050930 : CollatzResearch.WordTrace tailWord_8050930 prefixEnd_8050930 459332978411365659227717 := by
  unfold tailWord_8050930
  simp only [CollatzResearch.WordTrace]
  refine ⟨73410385180715768555153561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195761027148575382813742829 73410385180715768555153561)
  ·
    refine ⟨55057788885536826416365171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73410385180715768555153561 55057788885536826416365171)
    ·
      refine ⟨82586683328305239624547757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55057788885536826416365171 82586683328305239624547757)
      ·
        refine ⟨30970006248114464859205409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82586683328305239624547757 30970006248114464859205409)
        ·
          refine ⟨23227504686085848644404057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30970006248114464859205409 23227504686085848644404057)
          ·
            refine ⟨17420628514564386483303043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23227504686085848644404057 17420628514564386483303043)
            ·
              refine ⟨26130942771846579724954565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17420628514564386483303043 26130942771846579724954565)
              ·
                refine ⟨4899551769721233698428981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26130942771846579724954565 4899551769721233698428981)
                ·
                  refine ⟨459332978411365659227717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899551769721233698428981 459332978411365659227717)
                  ·
                    rfl

theorem cell23_8050930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_8050930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050930 prefixEnd_8050930 := by exact prefixLift 8050930
  have htrace : WordTrace (prefixWord ++ tailWord_8050930) baseStart_8050930 baseEnd_8050930 := by
    simpa [prefixWord, tailWord_8050930, baseEnd_8050930] using wordTrace_append hprefix tailTrace_8050930
  have hstable : (prefixWord ++ tailWord_8050930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050930).length < 2 ^ (prefixWord ++ tailWord_8050930).sum := by decide
  have hdescent : baseEnd_8050930 < baseStart_8050930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8050980 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_8050980 : Nat := 118140960795 + 8050980 * 2 ^ 59
def prefixEnd_8050980 : Nat := 4983230072969 + 3 ^ 40 * 8050980 * 2
def baseEnd_8050980 : Nat := 4134022479735015737424223

theorem tailTrace_8050980 : CollatzResearch.WordTrace tailWord_8050980 prefixEnd_8050980 4134022479735015737424223 := by
  unfold tailWord_8050980
  simp only [CollatzResearch.WordTrace]
  refine ⟨146821682186340966379967197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195762242915121288506622929 146821682186340966379967197)
  ·
    refine ⟨55058130819877862392487699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146821682186340966379967197 55058130819877862392487699)
    ·
      refine ⟨82587196229816793588731549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55058130819877862392487699 82587196229816793588731549)
      ·
        refine ⟨30970198586181297595774331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82587196229816793588731549 30970198586181297595774331)
        ·
          refine ⟨46455297879271946393661497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30970198586181297595774331 46455297879271946393661497)
          ·
            refine ⟨34841473409453959795246123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46455297879271946393661497 34841473409453959795246123)
            ·
              refine ⟨52262210114180939692869185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34841473409453959795246123 52262210114180939692869185)
              ·
                refine ⟨39196657585635704769651889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52262210114180939692869185 39196657585635704769651889)
                ·
                  refine ⟨29397493189226778577238917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39196657585635704769651889 29397493189226778577238917)
                  ·
                    refine ⟨5512029972980020983232297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29397493189226778577238917 5512029972980020983232297)
                    ·
                      refine ⟨4134022479735015737424223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512029972980020983232297 4134022479735015737424223)
                      ·
                        rfl

theorem cell23_8050980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_8050980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8050980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8050980 prefixEnd_8050980 := by exact prefixLift 8050980
  have htrace : WordTrace (prefixWord ++ tailWord_8050980) baseStart_8050980 baseEnd_8050980 := by
    simpa [prefixWord, tailWord_8050980, baseEnd_8050980] using wordTrace_append hprefix tailTrace_8050980
  have hstable : (prefixWord ++ tailWord_8050980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8050980).length < 2 ^ (prefixWord ++ tailWord_8050980).sum := by decide
  have hdescent : baseEnd_8050980 < baseStart_8050980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8050980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051047 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_8051047 : Nat := 118140960795 + 8051047 * 2 ^ 59
def prefixEnd_8051047 : Nat := 4983230072969 + 3 ^ 40 * 8051047 * 2
def baseEnd_8051047 : Nat := 4134056882938866975286415

theorem tailTrace_8051047 : CollatzResearch.WordTrace tailWord_8051047 prefixEnd_8051047 4134056882938866975286415 := by
  unfold tailWord_8051047
  simp only [CollatzResearch.WordTrace]
  refine ⟨293645808063439203202623395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195763872042292802135082263 293645808063439203202623395)
  ·
    refine ⟨440468712095158804803935093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293645808063439203202623395 440468712095158804803935093)
    ·
      refine ⟨41293941758921137950368915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 440468712095158804803935093 41293941758921137950368915)
      ·
        refine ⟨61940912638381706925553373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41293941758921137950368915 61940912638381706925553373)
        ·
          refine ⟨23227842239393140097082515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61940912638381706925553373 23227842239393140097082515)
          ·
            refine ⟨34841763359089710145623773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23227842239393140097082515 34841763359089710145623773)
            ·
              refine ⟨13065661259658641304608915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34841763359089710145623773 13065661259658641304608915)
              ·
                refine ⟨19598491889487961956913373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065661259658641304608915 19598491889487961956913373)
                ·
                  refine ⟨7349434458557985733842515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19598491889487961956913373 7349434458557985733842515)
                  ·
                    refine ⟨11024151687836978600763773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349434458557985733842515 11024151687836978600763773)
                    ·
                      refine ⟨4134056882938866975286415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024151687836978600763773 4134056882938866975286415)
                      ·
                        rfl

theorem cell23_8051047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_8051047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051047 prefixEnd_8051047 := by exact prefixLift 8051047
  have htrace : WordTrace (prefixWord ++ tailWord_8051047) baseStart_8051047 baseEnd_8051047 := by
    simpa [prefixWord, tailWord_8051047, baseEnd_8051047] using wordTrace_append hprefix tailTrace_8051047
  have hstable : (prefixWord ++ tailWord_8051047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051047).length < 2 ^ (prefixWord ++ tailWord_8051047).sum := by decide
  have hdescent : baseEnd_8051047 < baseStart_8051047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051063 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 6, 4]
def baseStart_8051063 : Nat := 118140960795 + 8051063 * 2 ^ 59
def prefixEnd_8051063 : Nat := 4983230072969 + 3 ^ 40 * 8051063 * 2
def baseEnd_8051063 : Nat := 1378021699543112970895447

theorem tailTrace_8051063 : CollatzResearch.WordTrace tailWord_8051063 prefixEnd_8051063 1378021699543112970895447 := by
  unfold tailWord_8051063
  simp only [CollatzResearch.WordTrace]
  refine ⟨293646391631381237935205843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195764261087587491956803895 293646391631381237935205843)
  ·
    refine ⟨440469587447071856902808765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293646391631381237935205843 440469587447071856902808765)
    ·
      refine ⟨165176095292651946338553287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440469587447071856902808765 165176095292651946338553287)
      ·
        refine ⟨247764142938977919507829931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165176095292651946338553287 247764142938977919507829931)
        ·
          refine ⟨371646214408466879261744897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247764142938977919507829931 371646214408466879261744897)
          ·
            refine ⟨278734660806350159446308673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371646214408466879261744897 278734660806350159446308673)
            ·
              refine ⟨209050995604762619584731505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278734660806350159446308673 209050995604762619584731505)
              ·
                refine ⟨156788246703571964688548629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209050995604762619584731505 156788246703571964688548629)
                ·
                  refine ⟨7349449064229935844775717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156788246703571964688548629 7349449064229935844775717)
                  ·
                    refine ⟨1378021699543112970895447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7349449064229935844775717 1378021699543112970895447)
                    ·
                      rfl

theorem cell23_8051063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_8051063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051063 prefixEnd_8051063 := by exact prefixLift 8051063
  have htrace : WordTrace (prefixWord ++ tailWord_8051063) baseStart_8051063 baseEnd_8051063 := by
    simpa [prefixWord, tailWord_8051063, baseEnd_8051063] using wordTrace_append hprefix tailTrace_8051063
  have hstable : (prefixWord ++ tailWord_8051063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051063).length < 2 ^ (prefixWord ++ tailWord_8051063).sum := by decide
  have hdescent : baseEnd_8051063 < baseStart_8051063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051083 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_8051083 : Nat := 118140960795 + 8051083 * 2 ^ 59
def prefixEnd_8051083 : Nat := 4983230072969 + 3 ^ 40 * 8051083 * 2
def baseEnd_8051083 : Nat := 4134075368242428834436249

theorem tailTrace_8051083 : CollatzResearch.WordTrace tailWord_8051083 prefixEnd_8051083 4134075368242428834436249 := by
  unfold tailWord_8051083
  simp only [CollatzResearch.WordTrace]
  refine ⟨293647121091308781350933903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195764747394205854233955935 293647121091308781350933903)
  ·
    refine ⟨440470681636963172026400855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293647121091308781350933903 440470681636963172026400855)
    ·
      refine ⟨660706022455444758039601283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440470681636963172026400855 660706022455444758039601283)
      ·
        refine ⟨991059033683167137059401925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660706022455444758039601283 991059033683167137059401925)
        ·
          refine ⟨185823568815593838198637861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 991059033683167137059401925 185823568815593838198637861)
          ·
            refine ⟨34841919152923844662244599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185823568815593838198637861 34841919152923844662244599)
            ·
              refine ⟨52262878729385766993366899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34841919152923844662244599 52262878729385766993366899)
              ·
                refine ⟨78394318094078650490050349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52262878729385766993366899 78394318094078650490050349)
                ·
                  refine ⟨29397869285279493933768881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78394318094078650490050349 29397869285279493933768881)
                  ·
                    refine ⟨22048401963959620450326661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29397869285279493933768881 22048401963959620450326661)
                    ·
                      refine ⟨4134075368242428834436249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22048401963959620450326661 4134075368242428834436249)
                      ·
                        rfl

theorem cell23_8051083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_8051083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051083 prefixEnd_8051083 := by exact prefixLift 8051083
  have htrace : WordTrace (prefixWord ++ tailWord_8051083) baseStart_8051083 baseEnd_8051083 := by
    simpa [prefixWord, tailWord_8051083, baseEnd_8051083] using wordTrace_append hprefix tailTrace_8051083
  have hstable : (prefixWord ++ tailWord_8051083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051083).length < 2 ^ (prefixWord ++ tailWord_8051083).sum := by decide
  have hdescent : baseEnd_8051083 < baseStart_8051083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051171 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 2, 1, 3]
def baseStart_8051171 : Nat := 118140960795 + 8051171 * 2 ^ 59
def prefixEnd_8051171 : Nat := 4983230072969 + 3 ^ 40 * 8051171 * 2
def baseEnd_8051171 : Nat := 4134120554540024490135845

theorem tailTrace_8051171 : CollatzResearch.WordTrace tailWord_8051171 prefixEnd_8051171 4134120554540024490135845 := by
  unfold tailWord_8051171
  simp only [CollatzResearch.WordTrace]
  refine ⟨293650330714989972380137367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195766887143326648253424911 293650330714989972380137367)
  ·
    refine ⟨440475496072484958570206051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293650330714989972380137367 440475496072484958570206051)
    ·
      refine ⟨660713244108727437855309077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440475496072484958570206051 660713244108727437855309077)
      ·
        refine ⟨30970933317596598649467613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 660713244108727437855309077 30970933317596598649467613)
        ·
          refine ⟨11614099994098724493550355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30970933317596598649467613 11614099994098724493550355)
          ·
            refine ⟨17421149991148086740325533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614099994098724493550355 17421149991148086740325533)
            ·
              refine ⟨6532931246680532527622075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17421149991148086740325533 6532931246680532527622075)
              ·
                refine ⟨9799396870020798791433113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532931246680532527622075 9799396870020798791433113)
                ·
                  refine ⟨7349547652515599093574835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799396870020798791433113 7349547652515599093574835)
                  ·
                    refine ⟨11024321478773398640362253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349547652515599093574835 11024321478773398640362253)
                    ·
                      refine ⟨4134120554540024490135845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024321478773398640362253 4134120554540024490135845)
                      ·
                        rfl

theorem cell23_8051171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_8051171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051171 prefixEnd_8051171 := by exact prefixLift 8051171
  have htrace : WordTrace (prefixWord ++ tailWord_8051171) baseStart_8051171 baseEnd_8051171 := by
    simpa [prefixWord, tailWord_8051171, baseEnd_8051171] using wordTrace_append hprefix tailTrace_8051171
  have hstable : (prefixWord ++ tailWord_8051171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051171).length < 2 ^ (prefixWord ++ tailWord_8051171).sum := by decide
  have hdescent : baseEnd_8051171 < baseStart_8051171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051181 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_8051181 : Nat := 118140960795 + 8051181 * 2 ^ 59
def prefixEnd_8051181 : Nat := 4983230072969 + 3 ^ 40 * 8051181 * 2
def baseEnd_8051181 : Nat := 4134125689346569451010799

theorem tailTrace_8051181 : CollatzResearch.WordTrace tailWord_8051181 prefixEnd_8051181 4134125689346569451010799 := by
  unfold tailWord_8051181
  simp only [CollatzResearch.WordTrace]
  refine ⟨293650695444953744088001397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195767130296635829392000931 293650695444953744088001397)
  ·
    refine ⟨27529752697964413508250131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293650695444953744088001397 27529752697964413508250131)
    ·
      refine ⟨41294629046946620262375197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27529752697964413508250131 41294629046946620262375197)
      ·
        refine ⟨15485485892604982598390699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41294629046946620262375197 15485485892604982598390699)
        ·
          refine ⟨23228228838907473897586049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15485485892604982598390699 23228228838907473897586049)
          ·
            refine ⟨17421171629180605423189537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23228228838907473897586049 17421171629180605423189537)
            ·
              refine ⟨13065878721885454067392153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17421171629180605423189537 13065878721885454067392153)
              ·
                refine ⟨9799409041414090550544115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13065878721885454067392153 9799409041414090550544115)
                ·
                  refine ⟨14699113562121135825816173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9799409041414090550544115 14699113562121135825816173)
                  ·
                    refine ⟨5512167585795425934681065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14699113562121135825816173 5512167585795425934681065)
                    ·
                      refine ⟨4134125689346569451010799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512167585795425934681065 4134125689346569451010799)
                      ·
                        rfl

theorem cell23_8051181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_8051181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051181 prefixEnd_8051181 := by exact prefixLift 8051181
  have htrace : WordTrace (prefixWord ++ tailWord_8051181) baseStart_8051181 baseEnd_8051181 := by
    simpa [prefixWord, tailWord_8051181, baseEnd_8051181] using wordTrace_append hprefix tailTrace_8051181
  have hstable : (prefixWord ++ tailWord_8051181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051181).length < 2 ^ (prefixWord ++ tailWord_8051181).sum := by decide
  have hdescent : baseEnd_8051181 < baseStart_8051181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051228 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_8051228 : Nat := 118140960795 + 8051228 * 2 ^ 59
def prefixEnd_8051228 : Nat := 4983230072969 + 3 ^ 40 * 8051228 * 2
def baseEnd_8051228 : Nat := 4134149822937330767123083

theorem tailTrace_8051228 : CollatzResearch.WordTrace tailWord_8051228 prefixEnd_8051228 4134149822937330767123083 := by
  unfold tailWord_8051228
  simp only [CollatzResearch.WordTrace]
  refine ⟨146826204837891735557481169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195768273117188980743308225 146826204837891735557481169)
  ·
    refine ⟨110119653628418801668110877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146826204837891735557481169 110119653628418801668110877)
    ·
      refine ⟨41294870110657050625541579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110119653628418801668110877 41294870110657050625541579)
      ·
        refine ⟨61942305165985575938312369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41294870110657050625541579 61942305165985575938312369)
        ·
          refine ⟨46456728874489181953734277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61942305165985575938312369 46456728874489181953734277)
          ·
            refine ⟨8710636663966721616325177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46456728874489181953734277 8710636663966721616325177)
            ·
              refine ⟨6532977497975041212243883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710636663966721616325177 6532977497975041212243883)
              ·
                refine ⟨9799466246962561818365825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532977497975041212243883 9799466246962561818365825)
                ·
                  refine ⟨7349599685221921363774369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799466246962561818365825 7349599685221921363774369)
                  ·
                    refine ⟨5512199763916441022830777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349599685221921363774369 5512199763916441022830777)
                    ·
                      refine ⟨4134149822937330767123083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512199763916441022830777 4134149822937330767123083)
                      ·
                        rfl

theorem cell23_8051228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_8051228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051228 prefixEnd_8051228 := by exact prefixLift 8051228
  have htrace : WordTrace (prefixWord ++ tailWord_8051228) baseStart_8051228 baseEnd_8051228 := by
    simpa [prefixWord, tailWord_8051228, baseEnd_8051228] using wordTrace_append hprefix tailTrace_8051228
  have hstable : (prefixWord ++ tailWord_8051228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051228).length < 2 ^ (prefixWord ++ tailWord_8051228).sum := by decide
  have hdescent : baseEnd_8051228 < baseStart_8051228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051243 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 8]
def baseStart_8051243 : Nat := 118140960795 + 8051243 * 2 ^ 59
def prefixEnd_8051243 : Nat := 4983230072969 + 3 ^ 40 * 8051243 * 2
def baseEnd_8051243 : Nat := 1378052508382382736145171

theorem tailTrace_8051243 : CollatzResearch.WordTrace tailWord_8051243 prefixEnd_8051243 1378052508382382736145171 := by
  unfold tailWord_8051243
  simp only [CollatzResearch.WordTrace]
  refine ⟨293652956770729128676758383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195768637847152752451172255 293652956770729128676758383)
  ·
    refine ⟨440479435156093693015137575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293652956770729128676758383 440479435156093693015137575)
    ·
      refine ⟨660719152734140539522706363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440479435156093693015137575 660719152734140539522706363)
      ·
        refine ⟨991078729101210809284059545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660719152734140539522706363 991078729101210809284059545)
        ·
          refine ⟨743309046825908106963044659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991078729101210809284059545 743309046825908106963044659)
          ·
            refine ⟨1114963570238862160444566989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743309046825908106963044659 1114963570238862160444566989)
            ·
              refine ⟨418111338839573310166712621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114963570238862160444566989 418111338839573310166712621)
              ·
                refine ⟨156791752064839991312517233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418111338839573310166712621 156791752064839991312517233)
                ·
                  refine ⟨117593814048629993484387925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156791752064839991312517233 117593814048629993484387925)
                  ·
                    refine ⟨1378052508382382736145171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117593814048629993484387925 1378052508382382736145171)
                    ·
                      rfl

theorem cell23_8051243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_8051243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051243 prefixEnd_8051243 := by exact prefixLift 8051243
  have htrace : WordTrace (prefixWord ++ tailWord_8051243) baseStart_8051243 baseEnd_8051243 := by
    simpa [prefixWord, tailWord_8051243, baseEnd_8051243] using wordTrace_append hprefix tailTrace_8051243
  have hstable : (prefixWord ++ tailWord_8051243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051243).length < 2 ^ (prefixWord ++ tailWord_8051243).sum := by decide
  have hdescent : baseEnd_8051243 < baseStart_8051243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051250 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_8051250 : Nat := 118140960795 + 8051250 * 2 ^ 59
def prefixEnd_8051250 : Nat := 4983230072969 + 3 ^ 40 * 8051250 * 2
def baseEnd_8051250 : Nat := 4134161119511729681047981

theorem tailTrace_8051250 : CollatzResearch.WordTrace tailWord_8051250 prefixEnd_8051250 4134161119511729681047981 := by
  unfold tailWord_8051250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73413303020425942218065801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195768808054469179248175469 73413303020425942218065801)
  ·
    refine ⟨55059977265319456663549351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73413303020425942218065801 55059977265319456663549351)
    ·
      refine ⟨82589965897979184995324027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55059977265319456663549351 82589965897979184995324027)
      ·
        refine ⟨123884948846968777492986041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82589965897979184995324027 123884948846968777492986041)
        ·
          refine ⟨92913711635226583119739531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123884948846968777492986041 92913711635226583119739531)
          ·
            refine ⟨139370567452839874679609297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92913711635226583119739531 139370567452839874679609297)
            ·
              refine ⟨104527925589629906009706973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139370567452839874679609297 104527925589629906009706973)
              ·
                refine ⟨39197972096111214753640115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104527925589629906009706973 39197972096111214753640115)
                ·
                  refine ⟨58796958144166822130460173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39197972096111214753640115 58796958144166822130460173)
                  ·
                    refine ⟨22048859304062558298922565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58796958144166822130460173 22048859304062558298922565)
                    ·
                      refine ⟨4134161119511729681047981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22048859304062558298922565 4134161119511729681047981)
                      ·
                        rfl

theorem cell23_8051250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_8051250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051250 prefixEnd_8051250 := by exact prefixLift 8051250
  have htrace : WordTrace (prefixWord ++ tailWord_8051250) baseStart_8051250 baseEnd_8051250 := by
    simpa [prefixWord, tailWord_8051250, baseEnd_8051250] using wordTrace_append hprefix tailTrace_8051250
  have hstable : (prefixWord ++ tailWord_8051250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051250).length < 2 ^ (prefixWord ++ tailWord_8051250).sum := by decide
  have hdescent : baseEnd_8051250 < baseStart_8051250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051268 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 5]
def baseStart_8051268 : Nat := 118140960795 + 8051268 * 2 ^ 59
def prefixEnd_8051268 : Nat := 4983230072969 + 3 ^ 40 * 8051268 * 2
def baseEnd_8051268 : Nat := 459352262462612290069211

theorem tailTrace_8051268 : CollatzResearch.WordTrace tailWord_8051268 prefixEnd_8051268 459352262462612290069211 := by
  unfold tailWord_8051268
  simp only [CollatzResearch.WordTrace]
  refine ⟨146826934297819278973209229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195769245730425705297612305 146826934297819278973209229)
  ·
    refine ⟨55060100361682229614953461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146826934297819278973209229 55060100361682229614953461)
    ·
      refine ⟨5161884408907709026401887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55060100361682229614953461 5161884408907709026401887)
      ·
        refine ⟨7742826613361563539602831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161884408907709026401887 7742826613361563539602831)
        ·
          refine ⟨11614239920042345309404247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742826613361563539602831 11614239920042345309404247)
          ·
            refine ⟨17421359880063517964106371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614239920042345309404247 17421359880063517964106371)
            ·
              refine ⟨26132039820095276946159557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17421359880063517964106371 26132039820095276946159557)
              ·
                refine ⟨4899757466267864427404917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26132039820095276946159557 4899757466267864427404917)
                ·
                  refine ⟨459352262462612290069211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899757466267864427404917 459352262462612290069211)
                  ·
                    rfl

theorem cell23_8051268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_8051268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051268 prefixEnd_8051268 := by exact prefixLift 8051268
  have htrace : WordTrace (prefixWord ++ tailWord_8051268) baseStart_8051268 baseEnd_8051268 := by
    simpa [prefixWord, tailWord_8051268, baseEnd_8051268] using wordTrace_append hprefix tailTrace_8051268
  have hstable : (prefixWord ++ tailWord_8051268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051268).length < 2 ^ (prefixWord ++ tailWord_8051268).sum := by decide
  have hdescent : baseEnd_8051268 < baseStart_8051268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051284 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_8051284 : Nat := 118140960795 + 8051284 * 2 ^ 59
def prefixEnd_8051284 : Nat := 4983230072969 + 3 ^ 40 * 8051284 * 2
def baseEnd_8051284 : Nat := 4134178577853982548022825

theorem tailTrace_8051284 : CollatzResearch.WordTrace tailWord_8051284 prefixEnd_8051284 4134178577853982548022825 := by
  unfold tailWord_8051284
  simp only [CollatzResearch.WordTrace]
  refine ⟨146827226081790296339500453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195769634775720395119333937 146827226081790296339500453)
  ·
    refine ⟨27530104890335680563656335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146827226081790296339500453 27530104890335680563656335)
    ·
      refine ⟨41295157335503520845484503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27530104890335680563656335 41295157335503520845484503)
      ·
        refine ⟨61942736003255281268226755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41295157335503520845484503 61942736003255281268226755)
        ·
          refine ⟨92914104004882921902340133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61942736003255281268226755 92914104004882921902340133)
          ·
            refine ⟨17421394500915547856688775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92914104004882921902340133 17421394500915547856688775)
            ·
              refine ⟨26132091751373321785033163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17421394500915547856688775 26132091751373321785033163)
              ·
                refine ⟨39198137627059982677549745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26132091751373321785033163 39198137627059982677549745)
                ·
                  refine ⟨29398603220294987008162309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39198137627059982677549745 29398603220294987008162309)
                  ·
                    refine ⟨5512238103805310064030433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29398603220294987008162309 5512238103805310064030433)
                    ·
                      refine ⟨4134178577853982548022825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512238103805310064030433 4134178577853982548022825)
                      ·
                        rfl

theorem cell23_8051284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_8051284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051284 prefixEnd_8051284 := by exact prefixLift 8051284
  have htrace : WordTrace (prefixWord ++ tailWord_8051284) baseStart_8051284 baseEnd_8051284 := by
    simpa [prefixWord, tailWord_8051284, baseEnd_8051284] using wordTrace_append hprefix tailTrace_8051284
  have hstable : (prefixWord ++ tailWord_8051284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051284).length < 2 ^ (prefixWord ++ tailWord_8051284).sum := by decide
  have hdescent : baseEnd_8051284 < baseStart_8051284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051298 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_8051298 : Nat := 118140960795 + 8051298 * 2 ^ 59
def prefixEnd_8051298 : Nat := 4983230072969 + 3 ^ 40 * 8051298 * 2
def baseEnd_8051298 : Nat := 1378061922194381831082587

theorem tailTrace_8051298 : CollatzResearch.WordTrace tailWord_8051298 prefixEnd_8051298 1378061922194381831082587 := by
  unfold tailWord_8051298
  simp only [CollatzResearch.WordTrace]
  refine ⟨73413740696382468267502637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195769975190353248713340365 73413740696382468267502637)
  ·
    refine ⟨27530152761143425600313489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73413740696382468267502637 27530152761143425600313489)
    ·
      refine ⟨20647614570857569200235117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27530152761143425600313489 20647614570857569200235117)
      ·
        refine ⟨7742855464071588450088169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20647614570857569200235117 7742855464071588450088169)
        ·
          refine ⟨5807141598053691337566127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7742855464071588450088169 5807141598053691337566127)
          ·
            refine ⟨8710712397080537006349191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807141598053691337566127 8710712397080537006349191)
            ·
              refine ⟨13066068595620805509523787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710712397080537006349191 13066068595620805509523787)
              ·
                refine ⟨19599102893431208264285681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13066068595620805509523787 19599102893431208264285681)
                ·
                  refine ⟨14699327170073406198214261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19599102893431208264285681 14699327170073406198214261)
                  ·
                    refine ⟨1378061922194381831082587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14699327170073406198214261 1378061922194381831082587)
                    ·
                      rfl

theorem cell23_8051298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_8051298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051298 prefixEnd_8051298 := by exact prefixLift 8051298
  have htrace : WordTrace (prefixWord ++ tailWord_8051298) baseStart_8051298 baseEnd_8051298 := by
    simpa [prefixWord, tailWord_8051298, baseEnd_8051298] using wordTrace_append hprefix tailTrace_8051298
  have hstable : (prefixWord ++ tailWord_8051298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051298).length < 2 ^ (prefixWord ++ tailWord_8051298).sum := by decide
  have hdescent : baseEnd_8051298 < baseStart_8051298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051301 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_8051301 : Nat := 118140960795 + 8051301 * 2 ^ 59
def prefixEnd_8051301 : Nat := 4983230072969 + 3 ^ 40 * 8051301 * 2
def baseEnd_8051301 : Nat := 4134187307025108981510247

theorem tailTrace_8051301 : CollatzResearch.WordTrace tailWord_8051301 prefixEnd_8051301 4134187307025108981510247 := by
  unfold tailWord_8051301
  simp only [CollatzResearch.WordTrace]
  refine ⟨293655072204519004582369757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195770048136346003054913171 293655072204519004582369757)
  ·
    refine ⟨110120652076694626718388659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293655072204519004582369757 110120652076694626718388659)
    ·
      refine ⟨165180978115041940077582989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110120652076694626718388659 165180978115041940077582989)
      ·
        refine ⟨61942866793140727529093621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165180978115041940077582989 61942866793140727529093621)
        ·
          refine ⟨5807143761856943205852527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61942866793140727529093621 5807143761856943205852527)
          ·
            refine ⟨8710715642785414808778791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807143761856943205852527 8710715642785414808778791)
            ·
              refine ⟨13066073464178122213168187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710715642785414808778791 13066073464178122213168187)
              ·
                refine ⟨19599110196267183319752281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13066073464178122213168187 19599110196267183319752281)
                ·
                  refine ⟨14699332647200387489814211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19599110196267183319752281 14699332647200387489814211)
                  ·
                    refine ⟨22048998970800581234721317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14699332647200387489814211 22048998970800581234721317)
                    ·
                      refine ⟨4134187307025108981510247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22048998970800581234721317 4134187307025108981510247)
                      ·
                        rfl

theorem cell23_8051301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_8051301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051301 prefixEnd_8051301 := by exact prefixLift 8051301
  have htrace : WordTrace (prefixWord ++ tailWord_8051301) baseStart_8051301 baseEnd_8051301 := by
    simpa [prefixWord, tailWord_8051301, baseEnd_8051301] using wordTrace_append hprefix tailTrace_8051301
  have hstable : (prefixWord ++ tailWord_8051301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051301).length < 2 ^ (prefixWord ++ tailWord_8051301).sum := by decide
  have hdescent : baseEnd_8051301 < baseStart_8051301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051304 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_8051304 : Nat := 118140960795 + 8051304 * 2 ^ 59
def prefixEnd_8051304 : Nat := 4983230072969 + 3 ^ 40 * 8051304 * 2
def baseEnd_8051304 : Nat := 4134188847467072469772733

theorem tailTrace_8051304 : CollatzResearch.WordTrace tailWord_8051304 prefixEnd_8051304 4134188847467072469772733 := by
  unfold tailWord_8051304
  simp only [CollatzResearch.WordTrace]
  refine ⟨146827590811754068047364483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195770121082338757396485977 146827590811754068047364483)
  ·
    refine ⟨220241386217631102071046725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146827590811754068047364483 220241386217631102071046725)
    ·
      refine ⟨41295259915805831638321261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220241386217631102071046725 41295259915805831638321261)
      ·
        refine ⟨15485722468427186864370473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41295259915805831638321261 15485722468427186864370473)
        ·
          refine ⟨11614291851320390148277855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15485722468427186864370473 11614291851320390148277855)
          ·
            refine ⟨17421437776980585222416783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614291851320390148277855 17421437776980585222416783)
            ·
              refine ⟨26132156665470877833625175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17421437776980585222416783 26132156665470877833625175)
              ·
                refine ⟨39198234998206316750437763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26132156665470877833625175 39198234998206316750437763)
                ·
                  refine ⟨58797352497309475125656645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39198234998206316750437763 58797352497309475125656645)
                  ·
                    refine ⟨11024503593245526586060621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58797352497309475125656645 11024503593245526586060621)
                    ·
                      refine ⟨4134188847467072469772733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024503593245526586060621 4134188847467072469772733)
                      ·
                        rfl

theorem cell23_8051304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_8051304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051304 prefixEnd_8051304 := by exact prefixLift 8051304
  have htrace : WordTrace (prefixWord ++ tailWord_8051304) baseStart_8051304 baseEnd_8051304 := by
    simpa [prefixWord, tailWord_8051304, baseEnd_8051304] using wordTrace_append hprefix tailTrace_8051304
  have hstable : (prefixWord ++ tailWord_8051304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051304).length < 2 ^ (prefixWord ++ tailWord_8051304).sum := by decide
  have hdescent : baseEnd_8051304 < baseStart_8051304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051340 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_8051340 : Nat := 118140960795 + 8051340 * 2 ^ 59
def prefixEnd_8051340 : Nat := 4983230072969 + 3 ^ 40 * 8051340 * 2
def baseEnd_8051340 : Nat := 4134207332770634328922567

theorem tailTrace_8051340 : CollatzResearch.WordTrace tailWord_8051340 prefixEnd_8051340 4134207332770634328922567 := by
  unfold tailWord_8051340
  simp only [CollatzResearch.WordTrace]
  refine ⟨146828247325688857121519737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195770996434251809495359649 146828247325688857121519737)
  ·
    refine ⟨110121185494266642841139803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146828247325688857121519737 110121185494266642841139803)
    ·
      refine ⟨165181778241399964261709705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110121185494266642841139803 165181778241399964261709705)
      ·
        refine ⟨123886333681049973196282279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165181778241399964261709705 123886333681049973196282279)
        ·
          refine ⟨185829500521574959794423419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123886333681049973196282279 185829500521574959794423419)
          ·
            refine ⟨278744250782362439691635129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185829500521574959794423419 278744250782362439691635129)
            ·
              refine ⟨209058188086771829768726347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278744250782362439691635129 209058188086771829768726347)
              ·
                refine ⟨313587282130157744653089521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209058188086771829768726347 313587282130157744653089521)
                ·
                  refine ⟨235190461597618308489817141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313587282130157744653089521 235190461597618308489817141)
                  ·
                    refine ⟨22049105774776716420920357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235190461597618308489817141 22049105774776716420920357)
                    ·
                      refine ⟨4134207332770634328922567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22049105774776716420920357 4134207332770634328922567)
                      ·
                        rfl

theorem cell23_8051340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_8051340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051340 prefixEnd_8051340 := by exact prefixLift 8051340
  have htrace : WordTrace (prefixWord ++ tailWord_8051340) baseStart_8051340 baseEnd_8051340 := by
    simpa [prefixWord, tailWord_8051340, baseEnd_8051340] using wordTrace_append hprefix tailTrace_8051340
  have hstable : (prefixWord ++ tailWord_8051340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051340).length < 2 ^ (prefixWord ++ tailWord_8051340).sum := by decide
  have hdescent : baseEnd_8051340 < baseStart_8051340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051357 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_8051357 : Nat := 118140960795 + 8051357 * 2 ^ 59
def prefixEnd_8051357 : Nat := 4983230072969 + 3 ^ 40 * 8051357 * 2
def baseEnd_8051357 : Nat := 4134216061941760762409989

theorem tailTrace_8051357 : CollatzResearch.WordTrace tailWord_8051357 prefixEnd_8051357 4134216061941760762409989 := by
  unfold tailWord_8051357
  simp only [CollatzResearch.WordTrace]
  refine ⟨293657114692316126146408325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195771409794877417430938883 293657114692316126146408325)
  ·
    refine ⟨55060709004809273652451561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293657114692316126146408325 55060709004809273652451561)
    ·
      refine ⟨41295531753606955239338671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55060709004809273652451561 41295531753606955239338671)
      ·
        refine ⟨61943297630410432859008007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41295531753606955239338671 61943297630410432859008007)
        ·
          refine ⟨92914946445615649288512011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61943297630410432859008007 92914946445615649288512011)
          ·
            refine ⟨139372419668423473932768017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92914946445615649288512011 139372419668423473932768017)
            ·
              refine ⟨104529314751317605449576013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139372419668423473932768017 104529314751317605449576013)
              ·
                refine ⟨39198493031744102043591005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104529314751317605449576013 39198493031744102043591005)
                ·
                  refine ⟨14699434886904038266346627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39198493031744102043591005 14699434886904038266346627)
                  ·
                    refine ⟨22049152330356057399519941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14699434886904038266346627 22049152330356057399519941)
                    ·
                      refine ⟨4134216061941760762409989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22049152330356057399519941 4134216061941760762409989)
                      ·
                        rfl

theorem cell23_8051357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_8051357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051357 prefixEnd_8051357 := by exact prefixLift 8051357
  have htrace : WordTrace (prefixWord ++ tailWord_8051357) baseStart_8051357 baseEnd_8051357 := by
    simpa [prefixWord, tailWord_8051357, baseEnd_8051357] using wordTrace_append hprefix tailTrace_8051357
  have hstable : (prefixWord ++ tailWord_8051357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051357).length < 2 ^ (prefixWord ++ tailWord_8051357).sum := by decide
  have hdescent : baseEnd_8051357 < baseStart_8051357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051391 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 3, 2, 2]
def baseStart_8051391 : Nat := 118140960795 + 8051391 * 2 ^ 59
def prefixEnd_8051391 : Nat := 4983230072969 + 3 ^ 40 * 8051391 * 2
def baseEnd_8051391 : Nat := 4134233520284013629384833

theorem tailTrace_8051391 : CollatzResearch.WordTrace tailWord_8051391 prefixEnd_8051391 4134233520284013629384833 := by
  unfold tailWord_8051391
  simp only [CollatzResearch.WordTrace]
  refine ⟨293658354774192949953146027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195772236516128633302097351 293658354774192949953146027)
  ·
    refine ⟨440487532161289424929719041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293658354774192949953146027 440487532161289424929719041)
    ·
      refine ⟨330365649120967068697289281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440487532161289424929719041 330365649120967068697289281)
      ·
        refine ⟨247774236840725301522966961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330365649120967068697289281 247774236840725301522966961)
        ·
          refine ⟨185830677630543976142225221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247774236840725301522966961 185830677630543976142225221)
          ·
            refine ⟨34843252055726995526667229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185830677630543976142225221 34843252055726995526667229)
            ·
              refine ⟨13066219520897623322500211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34843252055726995526667229 13066219520897623322500211)
              ·
                refine ⟨19599329281346434983750317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13066219520897623322500211 19599329281346434983750317)
                ·
                  refine ⟨7349748480504913118906369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19599329281346434983750317 7349748480504913118906369)
                  ·
                    refine ⟨5512311360378684839179777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349748480504913118906369 5512311360378684839179777)
                    ·
                      refine ⟨4134233520284013629384833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512311360378684839179777 4134233520284013629384833)
                      ·
                        rfl

theorem cell23_8051391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_8051391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051391 prefixEnd_8051391 := by exact prefixLift 8051391
  have htrace : WordTrace (prefixWord ++ tailWord_8051391) baseStart_8051391 baseEnd_8051391 := by
    simpa [prefixWord, tailWord_8051391, baseEnd_8051391] using wordTrace_append hprefix tailTrace_8051391
  have hstable : (prefixWord ++ tailWord_8051391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051391).length < 2 ^ (prefixWord ++ tailWord_8051391).sum := by decide
  have hdescent : baseEnd_8051391 < baseStart_8051391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051405 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_8051405 : Nat := 118140960795 + 8051405 * 2 ^ 59
def prefixEnd_8051405 : Nat := 4983230072969 + 3 ^ 40 * 8051405 * 2
def baseEnd_8051405 : Nat := 1378080236337725524869923

theorem tailTrace_8051405 : CollatzResearch.WordTrace tailWord_8051405 prefixEnd_8051405 1378080236337725524869923 := by
  unfold tailWord_8051405
  simp only [CollatzResearch.WordTrace]
  refine ⟨293658865396142230344155669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195772576930761486896103779 293658865396142230344155669)
  ·
    refine ⟨13765259315444167047382297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293658865396142230344155669 13765259315444167047382297)
    ·
      refine ⟨10323944486583125285536723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13765259315444167047382297 10323944486583125285536723)
      ·
        refine ⟨15485916729874687928305085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10323944486583125285536723 15485916729874687928305085)
        ·
          refine ⟨5807218773703007973114407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15485916729874687928305085 5807218773703007973114407)
          ·
            refine ⟨8710828160554511959671611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807218773703007973114407 8710828160554511959671611)
            ·
              refine ⟨13066242240831767939507417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710828160554511959671611 13066242240831767939507417)
              ·
                refine ⟨9799681680623825954630563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13066242240831767939507417 9799681680623825954630563)
                ·
                  refine ⟨14699522520935738931945845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9799681680623825954630563 14699522520935738931945845)
                  ·
                    refine ⟨1378080236337725524869923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14699522520935738931945845 1378080236337725524869923)
                    ·
                      rfl

theorem cell23_8051405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_8051405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051405 prefixEnd_8051405 := by exact prefixLift 8051405
  have htrace : WordTrace (prefixWord ++ tailWord_8051405) baseStart_8051405 baseEnd_8051405 := by
    simpa [prefixWord, tailWord_8051405, baseEnd_8051405] using wordTrace_append hprefix tailTrace_8051405
  have hstable : (prefixWord ++ tailWord_8051405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051405).length < 2 ^ (prefixWord ++ tailWord_8051405).sum := by decide
  have hdescent : baseEnd_8051405 < baseStart_8051405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051441 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_8051441 : Nat := 118140960795 + 8051441 * 2 ^ 59
def prefixEnd_8051441 : Nat := 4983230072969 + 3 ^ 40 * 8051441 * 2
def baseEnd_8051441 : Nat := 4134259194316738433759603

theorem tailTrace_8051441 : CollatzResearch.WordTrace tailWord_8051441 prefixEnd_8051441 4134259194316738433759603 := by
  unfold tailWord_8051441
  simp only [CollatzResearch.WordTrace]
  refine ⟨293660178424011808492466177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195773452282674538994977451 293660178424011808492466177)
  ·
    refine ⟨220245133818008856369349633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293660178424011808492466177 220245133818008856369349633)
    ·
      refine ⟨165183850363506642277012225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220245133818008856369349633 165183850363506642277012225)
      ·
        refine ⟨123887887772629981707759169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165183850363506642277012225 123887887772629981707759169)
        ·
          refine ⟨92915915829472486280819377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123887887772629981707759169 92915915829472486280819377)
          ·
            refine ⟨69686936872104364710614533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92915915829472486280819377 69686936872104364710614533)
            ·
              refine ⟨13066300663519568383240225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69686936872104364710614533 13066300663519568383240225)
              ·
                refine ⟨9799725497639676287430169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13066300663519568383240225 9799725497639676287430169)
                ·
                  refine ⟨7349794123229757215572627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799725497639676287430169 7349794123229757215572627)
                  ·
                    refine ⟨11024691184844635823358941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349794123229757215572627 11024691184844635823358941)
                    ·
                      refine ⟨4134259194316738433759603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024691184844635823358941 4134259194316738433759603)
                      ·
                        rfl

theorem cell23_8051441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_8051441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051441 prefixEnd_8051441 := by exact prefixLift 8051441
  have htrace : WordTrace (prefixWord ++ tailWord_8051441) baseStart_8051441 baseEnd_8051441 := by
    simpa [prefixWord, tailWord_8051441, baseEnd_8051441] using wordTrace_append hprefix tailTrace_8051441
  have hstable : (prefixWord ++ tailWord_8051441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051441).length < 2 ^ (prefixWord ++ tailWord_8051441).sum := by decide
  have hdescent : baseEnd_8051441 < baseStart_8051441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051442 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_8051442 : Nat := 118140960795 + 8051442 * 2 ^ 59
def prefixEnd_8051442 : Nat := 4983230072969 + 3 ^ 40 * 8051442 * 2
def baseEnd_8051442 : Nat := 4134259707797392929847099

theorem tailTrace_8051442 : CollatzResearch.WordTrace tailWord_8051442 prefixEnd_8051442 4134259707797392929847099 := by
  unfold tailWord_8051442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73415053724252046415813145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195773476598005457108835053 73415053724252046415813145)
  ·
    refine ⟨55061290293189034811859859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73415053724252046415813145 55061290293189034811859859)
    ·
      refine ⟨82591935439783552217789789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55061290293189034811859859 82591935439783552217789789)
      ·
        refine ⟨30971975789918832081671171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82591935439783552217789789 30971975789918832081671171)
        ·
          refine ⟨46457963684878248122506757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30971975789918832081671171 46457963684878248122506757)
          ·
            refine ⟨8710868190914671522970017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46457963684878248122506757 8710868190914671522970017)
            ·
              refine ⟨6533151143186003642227513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710868190914671522970017 6533151143186003642227513)
              ·
                refine ⟨4899863357389502731670635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533151143186003642227513 4899863357389502731670635)
                ·
                  refine ⟨7349795036084254097505953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899863357389502731670635 7349795036084254097505953)
                  ·
                    refine ⟨5512346277063190573129465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349795036084254097505953 5512346277063190573129465)
                    ·
                      refine ⟨4134259707797392929847099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512346277063190573129465 4134259707797392929847099)
                      ·
                        rfl

theorem cell23_8051442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_8051442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051442 prefixEnd_8051442 := by exact prefixLift 8051442
  have htrace : WordTrace (prefixWord ++ tailWord_8051442) baseStart_8051442 baseEnd_8051442 := by
    simpa [prefixWord, tailWord_8051442, baseEnd_8051442] using wordTrace_append hprefix tailTrace_8051442
  have hstable : (prefixWord ++ tailWord_8051442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051442).length < 2 ^ (prefixWord ++ tailWord_8051442).sum := by decide
  have hdescent : baseEnd_8051442 < baseStart_8051442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051458 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_8051458 : Nat := 118140960795 + 8051458 * 2 ^ 59
def prefixEnd_8051458 : Nat := 4983230072969 + 3 ^ 40 * 8051458 * 2
def baseEnd_8051458 : Nat := 4134267923487864867247025

theorem tailTrace_8051458 : CollatzResearch.WordTrace tailWord_8051458 prefixEnd_8051458 4134267923487864867247025 := by
  unfold tailWord_8051458
  simp only [CollatzResearch.WordTrace]
  refine ⟨73415199616237555098958757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195773865643300146930556685 73415199616237555098958757)
  ·
    refine ⟨13765349928044541581054767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73415199616237555098958757 13765349928044541581054767)
    ·
      refine ⟨20648024892066812371582151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13765349928044541581054767 20648024892066812371582151)
      ·
        refine ⟨30972037338100218557373227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20648024892066812371582151 30972037338100218557373227)
        ·
          refine ⟨46458056007150327836059841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30972037338100218557373227 46458056007150327836059841)
          ·
            refine ⟨34843542005362745877044881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46458056007150327836059841 34843542005362745877044881)
            ·
              refine ⟨26132656504022059407783661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34843542005362745877044881 26132656504022059407783661)
              ·
                refine ⟨9799746189008272277918873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26132656504022059407783661 9799746189008272277918873)
                ·
                  refine ⟨7349809641756204208439155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799746189008272277918873 7349809641756204208439155)
                  ·
                    refine ⟨11024714462634306312658733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349809641756204208439155 11024714462634306312658733)
                    ·
                      refine ⟨4134267923487864867247025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024714462634306312658733 4134267923487864867247025)
                      ·
                        rfl

theorem cell23_8051458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_8051458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051458 prefixEnd_8051458 := by exact prefixLift 8051458
  have htrace : WordTrace (prefixWord ++ tailWord_8051458) baseStart_8051458 baseEnd_8051458 := by
    simpa [prefixWord, tailWord_8051458, baseEnd_8051458] using wordTrace_append hprefix tailTrace_8051458
  have hstable : (prefixWord ++ tailWord_8051458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051458).length < 2 ^ (prefixWord ++ tailWord_8051458).sum := by decide
  have hdescent : baseEnd_8051458 < baseStart_8051458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051467 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3]
def baseStart_8051467 : Nat := 118140960795 + 8051467 * 2 ^ 59
def prefixEnd_8051467 : Nat := 4983230072969 + 3 ^ 40 * 8051467 * 2
def baseEnd_8051467 : Nat := 4134272544813755332034483

theorem tailTrace_8051467 : CollatzResearch.WordTrace tailWord_8051467 prefixEnd_8051467 4134272544813755332034483 := by
  unfold tailWord_8051467
  simp only [CollatzResearch.WordTrace]
  refine ⟨293661126721917614932912655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195774084481278409955275103 293661126721917614932912655)
  ·
    refine ⟨440491690082876422399368983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293661126721917614932912655 440491690082876422399368983)
    ·
      refine ⟨660737535124314633599053475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440491690082876422399368983 660737535124314633599053475)
      ·
        refine ⟨991106302686471950398580213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660737535124314633599053475 991106302686471950398580213)
        ·
          refine ⟨92916215876856745349866895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 991106302686471950398580213 92916215876856745349866895)
          ·
            refine ⟨139374323815285118024800343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92916215876856745349866895 139374323815285118024800343)
            ·
              refine ⟨209061485722927677037200515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139374323815285118024800343 209061485722927677037200515)
              ·
                refine ⟨313592228584391515555800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209061485722927677037200515 313592228584391515555800773)
                ·
                  refine ⟨58798542859573409166712645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313592228584391515555800773 58798542859573409166712645)
                  ·
                    refine ⟨11024726786170014218758621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58798542859573409166712645 11024726786170014218758621)
                    ·
                      refine ⟨4134272544813755332034483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024726786170014218758621 4134272544813755332034483)
                      ·
                        rfl

theorem cell23_8051467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3].length) (baseStart_8051467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051467 prefixEnd_8051467 := by exact prefixLift 8051467
  have htrace : WordTrace (prefixWord ++ tailWord_8051467) baseStart_8051467 baseEnd_8051467 := by
    simpa [prefixWord, tailWord_8051467, baseEnd_8051467] using wordTrace_append hprefix tailTrace_8051467
  have hstable : (prefixWord ++ tailWord_8051467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051467).length < 2 ^ (prefixWord ++ tailWord_8051467).sum := by decide
  have hdescent : baseEnd_8051467 < baseStart_8051467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051477 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_8051477 : Nat := 118140960795 + 8051477 * 2 ^ 59
def prefixEnd_8051477 : Nat := 4983230072969 + 3 ^ 40 * 8051477 * 2
def baseEnd_8051477 : Nat := 4134277679620300292909437

theorem tailTrace_8051477 : CollatzResearch.WordTrace tailWord_8051477 prefixEnd_8051477 4134277679620300292909437 := by
  unfold tailWord_8051477
  simp only [CollatzResearch.WordTrace]
  refine ⟨293661491451881386640776685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195774327634587591093851123 293661491451881386640776685)
  ·
    refine ⟨110123059294455519990291257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293661491451881386640776685 110123059294455519990291257)
    ·
      refine ⟨82592294470841639992718443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110123059294455519990291257 82592294470841639992718443)
      ·
        refine ⟨123888441706262459989077665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82592294470841639992718443 123888441706262459989077665)
        ·
          refine ⟨92916331279696844991808249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123888441706262459989077665 92916331279696844991808249)
          ·
            refine ⟨69687248459772633743856187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92916331279696844991808249 69687248459772633743856187)
            ·
              refine ⟨104530872689658950615784281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69687248459772633743856187 104530872689658950615784281)
              ·
                refine ⟨78398154517244212961838211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104530872689658950615784281 78398154517244212961838211)
                ·
                  refine ⟨117597231775866319442757317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78398154517244212961838211 117597231775866319442757317)
                  ·
                    refine ⟨22049480957974934895516997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117597231775866319442757317 22049480957974934895516997)
                    ·
                      refine ⟨4134277679620300292909437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22049480957974934895516997 4134277679620300292909437)
                      ·
                        rfl

theorem cell23_8051477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_8051477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051477 prefixEnd_8051477 := by exact prefixLift 8051477
  have htrace : WordTrace (prefixWord ++ tailWord_8051477) baseStart_8051477 baseEnd_8051477 := by
    simpa [prefixWord, tailWord_8051477, baseEnd_8051477] using wordTrace_append hprefix tailTrace_8051477
  have hstable : (prefixWord ++ tailWord_8051477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051477).length < 2 ^ (prefixWord ++ tailWord_8051477).sum := by decide
  have hdescent : baseEnd_8051477 < baseStart_8051477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051485 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_8051485 : Nat := 118140960795 + 8051485 * 2 ^ 59
def prefixEnd_8051485 : Nat := 4983230072969 + 3 ^ 40 * 8051485 * 2
def baseEnd_8051485 : Nat := 4134281787465536261609401

theorem tailTrace_8051485 : CollatzResearch.WordTrace tailWord_8051485 prefixEnd_8051485 4134281787465536261609401 := by
  unfold tailWord_8051485
  simp only [CollatzResearch.WordTrace]
  refine ⟨293661783235852404007067909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195774522157234936004711939 293661783235852404007067909)
  ·
    refine ⟨55061584356722325751325233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293661783235852404007067909 55061584356722325751325233)
    ·
      refine ⟨41296188267541744313493925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55061584356722325751325233 41296188267541744313493925)
      ·
        refine ⟨7743035300164077058780111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41296188267541744313493925 7743035300164077058780111)
        ·
          refine ⟨11614552950246115588170167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7743035300164077058780111 11614552950246115588170167)
          ·
            refine ⟨17421829425369173382255251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11614552950246115588170167 17421829425369173382255251)
            ·
              refine ⟨26132744138053760073382877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17421829425369173382255251 26132744138053760073382877)
              ·
                refine ⟨9799779051770160027518579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26132744138053760073382877 9799779051770160027518579)
                ·
                  refine ⟨14699668577655240041277869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9799779051770160027518579 14699668577655240041277869)
                  ·
                    refine ⟨5512375716620715015479201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14699668577655240041277869 5512375716620715015479201)
                    ·
                      refine ⟨4134281787465536261609401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512375716620715015479201 4134281787465536261609401)
                      ·
                        rfl

theorem cell23_8051485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_8051485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051485 prefixEnd_8051485 := by exact prefixLift 8051485
  have htrace : WordTrace (prefixWord ++ tailWord_8051485) baseStart_8051485 baseEnd_8051485 := by
    simpa [prefixWord, tailWord_8051485, baseEnd_8051485] using wordTrace_append hprefix tailTrace_8051485
  have hstable : (prefixWord ++ tailWord_8051485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051485).length < 2 ^ (prefixWord ++ tailWord_8051485).sum := by decide
  have hdescent : baseEnd_8051485 < baseStart_8051485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_8051497 : Nat := 118140960795 + 8051497 * 2 ^ 59
def prefixEnd_8051497 : Nat := 4983230072969 + 3 ^ 40 * 8051497 * 2
def baseEnd_8051497 : Nat := 4134287949233390214659345

theorem tailTrace_8051497 : CollatzResearch.WordTrace tailWord_8051497 prefixEnd_8051497 4134287949233390214659345 := by
  unfold tailWord_8051497
  simp only [CollatzResearch.WordTrace]
  refine ⟨293662220911808930056504745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195774813941205953371003163 293662220911808930056504745)
  ·
    refine ⟨220246665683856697542378559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293662220911808930056504745 220246665683856697542378559)
    ·
      refine ⟨330369998525785046313567839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220246665683856697542378559 330369998525785046313567839)
      ·
        refine ⟨495554997788677569470351759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330369998525785046313567839 495554997788677569470351759)
        ·
          refine ⟨743332496683016354205527639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495554997788677569470351759 743332496683016354205527639)
          ·
            refine ⟨1114998745024524531308291459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743332496683016354205527639 1114998745024524531308291459)
            ·
              refine ⟨1672498117536786796962437189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114998745024524531308291459 1672498117536786796962437189)
              ·
                refine ⟨313593397038147524430456973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1672498117536786796962437189 313593397038147524430456973)
                ·
                  refine ⟨117597523889305321661421365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313593397038147524430456973 117597523889305321661421365)
                  ·
                    refine ⟨11024767864622373905758253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117597523889305321661421365 11024767864622373905758253)
                    ·
                      refine ⟨4134287949233390214659345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024767864622373905758253 4134287949233390214659345)
                      ·
                        rfl

theorem cell23_8051497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_8051497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051497 prefixEnd_8051497 := by exact prefixLift 8051497
  have htrace : WordTrace (prefixWord ++ tailWord_8051497) baseStart_8051497 baseEnd_8051497 := by
    simpa [prefixWord, tailWord_8051497, baseEnd_8051497] using wordTrace_append hprefix tailTrace_8051497
  have hstable : (prefixWord ++ tailWord_8051497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051497).length < 2 ^ (prefixWord ++ tailWord_8051497).sum := by decide
  have hdescent : baseEnd_8051497 < baseStart_8051497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051527 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_8051527 : Nat := 118140960795 + 8051527 * 2 ^ 59
def prefixEnd_8051527 : Nat := 4983230072969 + 3 ^ 40 * 8051527 * 2
def baseEnd_8051527 : Nat := 4134303353653025097284207

theorem tailTrace_8051527 : CollatzResearch.WordTrace tailWord_8051527 prefixEnd_8051527 4134303353653025097284207 := by
  unfold tailWord_8051527
  simp only [CollatzResearch.WordTrace]
  refine ⟨293663315101700245180096835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195775543401133496786731223 293663315101700245180096835)
  ·
    refine ⟨440494972652550367770145253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293663315101700245180096835 440494972652550367770145253)
    ·
      refine ⟨82592807372353193956902235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440494972652550367770145253 82592807372353193956902235)
      ·
        refine ⟨123889211058529790935353353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82592807372353193956902235 123889211058529790935353353)
        ·
          refine ⟨92916908293897343201515015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123889211058529790935353353 92916908293897343201515015)
          ·
            refine ⟨139375362440846014802272523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92916908293897343201515015 139375362440846014802272523)
            ·
              refine ⟨209063043661269022203408785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139375362440846014802272523 209063043661269022203408785)
              ·
                refine ⟨156797282745951766652556589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209063043661269022203408785 156797282745951766652556589)
                ·
                  refine ⟨58798981029731912494708721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156797282745951766652556589 58798981029731912494708721)
                  ·
                    refine ⟨44099235772298934371031541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58798981029731912494708721 44099235772298934371031541)
                    ·
                      refine ⟨4134303353653025097284207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44099235772298934371031541 4134303353653025097284207)
                      ·
                        rfl

theorem cell23_8051527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_8051527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051527 prefixEnd_8051527 := by exact prefixLift 8051527
  have htrace : WordTrace (prefixWord ++ tailWord_8051527) baseStart_8051527 baseEnd_8051527 := by
    simpa [prefixWord, tailWord_8051527, baseEnd_8051527] using wordTrace_append hprefix tailTrace_8051527
  have hstable : (prefixWord ++ tailWord_8051527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051527).length < 2 ^ (prefixWord ++ tailWord_8051527).sum := by decide
  have hdescent : baseEnd_8051527 < baseStart_8051527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051567 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_8051567 : Nat := 118140960795 + 8051567 * 2 ^ 59
def prefixEnd_8051567 : Nat := 4983230072969 + 3 ^ 40 * 8051567 * 2
def baseEnd_8051567 : Nat := 4134323892879204940784023

theorem tailTrace_8051567 : CollatzResearch.WordTrace tailWord_8051567 prefixEnd_8051567 4134323892879204940784023 := by
  unfold tailWord_8051567
  simp only [CollatzResearch.WordTrace]
  refine ⟨293664774021555332011552955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195776516014370221341035303 293664774021555332011552955)
  ·
    refine ⟨440497161032332998017329433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293664774021555332011552955 440497161032332998017329433)
    ·
      refine ⟨330372870774249748512997075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440497161032332998017329433 330372870774249748512997075)
      ·
        refine ⟨495559306161374622769495613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330372870774249748512997075 495559306161374622769495613)
        ·
          refine ⟨185834739810515483538560855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495559306161374622769495613 185834739810515483538560855)
          ·
            refine ⟨278752109715773225307841283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185834739810515483538560855 278752109715773225307841283)
            ·
              refine ⟨418128164573659837961761925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278752109715773225307841283 418128164573659837961761925)
              ·
                refine ⟨78399030857561219617830361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418128164573659837961761925 78399030857561219617830361)
                ·
                  refine ⟨58799273143170914713372771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78399030857561219617830361 58799273143170914713372771)
                  ·
                    refine ⟨88198909714756372070059157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58799273143170914713372771 88198909714756372070059157)
                    ·
                      refine ⟨4134323892879204940784023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88198909714756372070059157 4134323892879204940784023)
                      ·
                        rfl

theorem cell23_8051567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_8051567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051567 prefixEnd_8051567 := by exact prefixLift 8051567
  have htrace : WordTrace (prefixWord ++ tailWord_8051567) baseStart_8051567 baseEnd_8051567 := by
    simpa [prefixWord, tailWord_8051567, baseEnd_8051567] using wordTrace_append hprefix tailTrace_8051567
  have hstable : (prefixWord ++ tailWord_8051567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051567).length < 2 ^ (prefixWord ++ tailWord_8051567).sum := by decide
  have hdescent : baseEnd_8051567 < baseStart_8051567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051591 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_8051591 : Nat := 118140960795 + 8051591 * 2 ^ 59
def prefixEnd_8051591 : Nat := 4983230072969 + 3 ^ 40 * 8051591 * 2
def baseEnd_8051591 : Nat := 4134336216414912846883913

theorem tailTrace_8051591 : CollatzResearch.WordTrace tailWord_8051591 prefixEnd_8051591 4134336216414912846883913 := by
  unfold tailWord_8051591
  simp only [CollatzResearch.WordTrace]
  refine ⟨293665649373468384110426627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195777099582312256073617751 293665649373468384110426627)
  ·
    refine ⟨440498474060202576165639941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293665649373468384110426627 440498474060202576165639941)
    ·
      refine ⟨82593463886287983031057489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440498474060202576165639941 82593463886287983031057489)
      ·
        refine ⟨61945097914715987273293117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82593463886287983031057489 61945097914715987273293117)
        ·
          refine ⟨23229411718018495227484919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61945097914715987273293117 23229411718018495227484919)
          ·
            refine ⟨34844117577027742841227379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23229411718018495227484919 34844117577027742841227379)
            ·
              refine ⟨52266176365541614261841069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34844117577027742841227379 52266176365541614261841069)
              ·
                refine ⟨19599816137078105348190401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52266176365541614261841069 19599816137078105348190401)
                ·
                  refine ⟨14699862102808579011142801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19599816137078105348190401 14699862102808579011142801)
                  ·
                    refine ⟨11024896577106434258357101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14699862102808579011142801 11024896577106434258357101)
                    ·
                      refine ⟨4134336216414912846883913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11024896577106434258357101 4134336216414912846883913)
                      ·
                        rfl

theorem cell23_8051591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_8051591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051591 prefixEnd_8051591 := by exact prefixLift 8051591
  have htrace : WordTrace (prefixWord ++ tailWord_8051591) baseStart_8051591 baseEnd_8051591 := by
    simpa [prefixWord, tailWord_8051591, baseEnd_8051591] using wordTrace_append hprefix tailTrace_8051591
  have hstable : (prefixWord ++ tailWord_8051591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051591).length < 2 ^ (prefixWord ++ tailWord_8051591).sum := by decide
  have hdescent : baseEnd_8051591 < baseStart_8051591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051615 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 1, 4]
def baseStart_8051615 : Nat := 118140960795 + 8051615 * 2 ^ 59
def prefixEnd_8051615 : Nat := 4983230072969 + 3 ^ 40 * 8051615 * 2
def baseEnd_8051615 : Nat := 1378116179983540250994601

theorem tailTrace_8051615 : CollatzResearch.WordTrace tailWord_8051615 prefixEnd_8051615 1378116179983540250994601 := by
  unfold tailWord_8051615
  simp only [CollatzResearch.WordTrace]
  refine ⟨293666524725381436209300299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195777683150254290806200199 293666524725381436209300299)
  ·
    refine ⟨440499787088072154313950449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293666524725381436209300299 440499787088072154313950449)
    ·
      refine ⟨330374840316054115735462837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440499787088072154313950449 330374840316054115735462837)
      ·
        refine ⟨30972641279630073350199641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330374840316054115735462837 30972641279630073350199641)
        ·
          refine ⟨23229480959722555012649731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30972641279630073350199641 23229480959722555012649731)
          ·
            refine ⟨34844221439583832518974597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23229480959722555012649731 34844221439583832518974597)
            ·
              refine ⟨6533291519921968597307737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34844221439583832518974597 6533291519921968597307737)
              ·
                refine ⟨4899968639941476447980803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533291519921968597307737 4899968639941476447980803)
                ·
                  refine ⟨7349952959912214671971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899968639941476447980803 7349952959912214671971205)
                  ·
                    refine ⟨1378116179983540250994601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7349952959912214671971205 1378116179983540250994601)
                    ·
                      rfl

theorem cell23_8051615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 4].length) (baseStart_8051615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051615 prefixEnd_8051615 := by exact prefixLift 8051615
  have htrace : WordTrace (prefixWord ++ tailWord_8051615) baseStart_8051615 baseEnd_8051615 := by
    simpa [prefixWord, tailWord_8051615, baseEnd_8051615] using wordTrace_append hprefix tailTrace_8051615
  have hstable : (prefixWord ++ tailWord_8051615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051615).length < 2 ^ (prefixWord ++ tailWord_8051615).sum := by decide
  have hdescent : baseEnd_8051615 < baseStart_8051615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051648 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2]
def baseStart_8051648 : Nat := 118140960795 + 8051648 * 2 ^ 59
def prefixEnd_8051648 : Nat := 4983230072969 + 3 ^ 40 * 8051648 * 2
def baseEnd_8051648 : Nat := 4134365484812219123871151

theorem tailTrace_8051648 : CollatzResearch.WordTrace tailWord_8051648 prefixEnd_8051648 4134365484812219123871151 := by
  unfold tailWord_8051648
  simp only [CollatzResearch.WordTrace]
  refine ⟨146833864167130941422625799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195778485556174588563501065 146833864167130941422625799)
  ·
    refine ⟨220250796250696412133938699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146833864167130941422625799 220250796250696412133938699)
    ·
      refine ⟨330376194376044618200908049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220250796250696412133938699 330376194376044618200908049)
      ·
        refine ⟨247782145782033463650681037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330376194376044618200908049 247782145782033463650681037)
        ·
          refine ⟨92918304668262548869005389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247782145782033463650681037 92918304668262548869005389)
          ·
            refine ⟨34844364250598455825877021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92918304668262548869005389 34844364250598455825877021)
            ·
              refine ⟨13066636593974420934703883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34844364250598455825877021 13066636593974420934703883)
              ·
                refine ⟨19599954890961631402055825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13066636593974420934703883 19599954890961631402055825)
                ·
                  refine ⟨14699966168221223551541869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19599954890961631402055825 14699966168221223551541869)
                  ·
                    refine ⟨5512487313082958831828201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14699966168221223551541869 5512487313082958831828201)
                    ·
                      refine ⟨4134365484812219123871151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512487313082958831828201 4134365484812219123871151)
                      ·
                        rfl

theorem cell23_8051648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_8051648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051648 prefixEnd_8051648 := by exact prefixLift 8051648
  have htrace : WordTrace (prefixWord ++ tailWord_8051648) baseStart_8051648 baseEnd_8051648 := by
    simpa [prefixWord, tailWord_8051648, baseEnd_8051648] using wordTrace_append hprefix tailTrace_8051648
  have hstable : (prefixWord ++ tailWord_8051648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051648).length < 2 ^ (prefixWord ++ tailWord_8051648).sum := by decide
  have hdescent : baseEnd_8051648 < baseStart_8051648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051664 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_8051664 : Nat := 118140960795 + 8051664 * 2 ^ 59
def prefixEnd_8051664 : Nat := 4983230072969 + 3 ^ 40 * 8051664 * 2
def baseEnd_8051664 : Nat := 4134373700502691061271077

theorem tailTrace_8051664 : CollatzResearch.WordTrace tailWord_8051664 prefixEnd_8051664 4134373700502691061271077 := by
  unfold tailWord_8051664
  simp only [CollatzResearch.WordTrace]
  refine ⟨146834155951101958788917023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195778874601469278385222697 146834155951101958788917023)
  ·
    refine ⟨220251233926652938183375535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146834155951101958788917023 220251233926652938183375535)
    ·
      refine ⟨330376850889979407275063303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220251233926652938183375535 330376850889979407275063303)
      ·
        refine ⟨495565276334969110912594955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330376850889979407275063303 495565276334969110912594955)
        ·
          refine ⟨743347914502453666368892433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495565276334969110912594955 743347914502453666368892433)
          ·
            refine ⟨557510935876840249776669325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743347914502453666368892433 557510935876840249776669325)
            ·
              refine ⟨209066600953815093666250997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557510935876840249776669325 209066600953815093666250997)
              ·
                refine ⟨19599993839420165031211031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209066600953815093666250997 19599993839420165031211031)
                ·
                  refine ⟨29399990759130247546816547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19599993839420165031211031 29399990759130247546816547)
                  ·
                    refine ⟨44099986138695371320224821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29399990759130247546816547 44099986138695371320224821)
                    ·
                      refine ⟨4134373700502691061271077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44099986138695371320224821 4134373700502691061271077)
                      ·
                        rfl

theorem cell23_8051664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_8051664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051664 prefixEnd_8051664 := by exact prefixLift 8051664
  have htrace : WordTrace (prefixWord ++ tailWord_8051664) baseStart_8051664 baseEnd_8051664 := by
    simpa [prefixWord, tailWord_8051664, baseEnd_8051664] using wordTrace_append hprefix tailTrace_8051664
  have hstable : (prefixWord ++ tailWord_8051664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051664).length < 2 ^ (prefixWord ++ tailWord_8051664).sum := by decide
  have hdescent : baseEnd_8051664 < baseStart_8051664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051671 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 2, 4]
def baseStart_8051671 : Nat := 118140960795 + 8051671 * 2 ^ 59
def prefixEnd_8051671 : Nat := 4983230072969 + 3 ^ 40 * 8051671 * 2
def baseEnd_8051671 : Nat := 1378125764955757511294515

theorem tailTrace_8051671 : CollatzResearch.WordTrace tailWord_8051671 prefixEnd_8051671 1378125764955757511294515 := by
  unfold tailWord_8051671
  simp only [CollatzResearch.WordTrace]
  refine ⟨293668567213178557773338867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195779044808785705182225911 293668567213178557773338867)
  ·
    refine ⟨440502850819767836660008301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293668567213178557773338867 440502850819767836660008301)
    ·
      refine ⟨165188569057412938747503113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440502850819767836660008301 165188569057412938747503113)
      ·
        refine ⟨123891426793059704060627335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165188569057412938747503113 123891426793059704060627335)
        ·
          refine ⟨185837140189589556090941003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123891426793059704060627335 185837140189589556090941003)
          ·
            refine ⟨278755710284384334136411505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185837140189589556090941003 278755710284384334136411505)
            ·
              refine ⟨209066782713288250602308629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278755710284384334136411505 209066782713288250602308629)
              ·
                refine ⟨9800005439685386746983217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209066782713288250602308629 9800005439685386746983217)
                ·
                  refine ⟨7350004079764040060237413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9800005439685386746983217 7350004079764040060237413)
                  ·
                    refine ⟨1378125764955757511294515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7350004079764040060237413 1378125764955757511294515)
                    ·
                      rfl

theorem cell23_8051671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_8051671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051671 prefixEnd_8051671 := by exact prefixLift 8051671
  have htrace : WordTrace (prefixWord ++ tailWord_8051671) baseStart_8051671 baseEnd_8051671 := by
    simpa [prefixWord, tailWord_8051671, baseEnd_8051671] using wordTrace_append hprefix tailTrace_8051671
  have hstable : (prefixWord ++ tailWord_8051671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051671).length < 2 ^ (prefixWord ++ tailWord_8051671).sum := by decide
  have hdescent : baseEnd_8051671 < baseStart_8051671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051738 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_8051738 : Nat := 118140960795 + 8051738 * 2 ^ 59
def prefixEnd_8051738 : Nat := 4983230072969 + 3 ^ 40 * 8051738 * 2
def baseEnd_8051738 : Nat := 4134411698071123771745737

theorem tailTrace_8051738 : CollatzResearch.WordTrace tailWord_8051738 prefixEnd_8051738 4134411698071123771745737 := by
  unfold tailWord_8051738
  simp only [CollatzResearch.WordTrace]
  refine ⟨73417752725983957054006967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195780673935957218810685245 73417752725983957054006967)
  ·
    refine ⟨110126629088975935581010451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73417752725983957054006967 110126629088975935581010451)
    ·
      refine ⟨165189943633463903371515677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110126629088975935581010451 165189943633463903371515677)
      ·
        refine ⟨61946228862548963764318379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165189943633463903371515677 61946228862548963764318379)
        ·
          refine ⟨92919343293823445646477569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61946228862548963764318379 92919343293823445646477569)
          ·
            refine ⟨69689507470367584234858177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92919343293823445646477569 69689507470367584234858177)
            ·
              refine ⟨52267130602775688176143633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69689507470367584234858177 52267130602775688176143633)
              ·
                refine ⟨39200347952081766132107725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52267130602775688176143633 39200347952081766132107725)
                ·
                  refine ⟨14700130482030662299540397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39200347952081766132107725 14700130482030662299540397)
                  ·
                    refine ⟨5512548930761498362327649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14700130482030662299540397 5512548930761498362327649)
                    ·
                      refine ⟨4134411698071123771745737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512548930761498362327649 4134411698071123771745737)
                      ·
                        rfl

theorem cell23_8051738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_8051738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051738 prefixEnd_8051738 := by exact prefixLift 8051738
  have htrace : WordTrace (prefixWord ++ tailWord_8051738) baseStart_8051738 baseEnd_8051738 := by
    simpa [prefixWord, tailWord_8051738, baseEnd_8051738] using wordTrace_append hprefix tailTrace_8051738
  have hstable : (prefixWord ++ tailWord_8051738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051738).length < 2 ^ (prefixWord ++ tailWord_8051738).sum := by decide
  have hdescent : baseEnd_8051738 < baseStart_8051738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051745 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_8051745 : Nat := 118140960795 + 8051745 * 2 ^ 59
def prefixEnd_8051745 : Nat := 4983230072969 + 3 ^ 40 * 8051745 * 2
def baseEnd_8051745 : Nat := 4134415292435705244358205

theorem tailTrace_8051745 : CollatzResearch.WordTrace tailWord_8051745 prefixEnd_8051745 4134415292435705244358205 := by
  unfold tailWord_8051745
  simp only [CollatzResearch.WordTrace]
  refine ⟨293671266214910468411532689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195780844143273645607688459 293671266214910468411532689)
  ·
    refine ⟨220253449661182851308649517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293671266214910468411532689 220253449661182851308649517)
    ·
      refine ⟨82595043622943569240743569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220253449661182851308649517 82595043622943569240743569)
      ·
        refine ⟨61946282717207676930557677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82595043622943569240743569 61946282717207676930557677)
        ·
          refine ⟨23229856018952878848959129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61946282717207676930557677 23229856018952878848959129)
          ·
            refine ⟨17422392014214659136719347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23229856018952878848959129 17422392014214659136719347)
            ·
              refine ⟨26133588021321988705079021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17422392014214659136719347 26133588021321988705079021)
              ·
                refine ⟨9800095507995745764404633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26133588021321988705079021 9800095507995745764404633)
                ·
                  refine ⟨7350071630996809323303475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9800095507995745764404633 7350071630996809323303475)
                  ·
                    refine ⟨11025107446495213984955213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7350071630996809323303475 11025107446495213984955213)
                    ·
                      refine ⟨4134415292435705244358205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11025107446495213984955213 4134415292435705244358205)
                      ·
                        rfl

theorem cell23_8051745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_8051745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051745 prefixEnd_8051745 := by exact prefixLift 8051745
  have htrace : WordTrace (prefixWord ++ tailWord_8051745) baseStart_8051745 baseEnd_8051745 := by
    simpa [prefixWord, tailWord_8051745, baseEnd_8051745] using wordTrace_append hprefix tailTrace_8051745
  have hstable : (prefixWord ++ tailWord_8051745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051745).length < 2 ^ (prefixWord ++ tailWord_8051745).sum := by decide
  have hdescent : baseEnd_8051745 < baseStart_8051745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051768 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_8051768 : Nat := 118140960795 + 8051768 * 2 ^ 59
def prefixEnd_8051768 : Nat := 4983230072969 + 3 ^ 40 * 8051768 * 2
def baseEnd_8051768 : Nat := 4134427102490758654370599

theorem tailTrace_8051768 : CollatzResearch.WordTrace tailWord_8051768 prefixEnd_8051768 4134427102490758654370599 := by
  unfold tailWord_8051768
  simp only [CollatzResearch.WordTrace]
  refine ⟨146836052546913571669809979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195781403395884762226413305 146836052546913571669809979)
  ·
    refine ⟨220254078820370357504714969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146836052546913571669809979 220254078820370357504714969)
    ·
      refine ⟨165190559115277768128536227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220254078820370357504714969 165190559115277768128536227)
      ·
        refine ⟨247785838672916652192804341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165190559115277768128536227 247785838672916652192804341)
        ·
          refine ⟨23229922375585936143075407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247785838672916652192804341 23229922375585936143075407)
          ·
            refine ⟨34844883563378904214613111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23229922375585936143075407 34844883563378904214613111)
            ·
              refine ⟨52267325345068356321919667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34844883563378904214613111 52267325345068356321919667)
              ·
                refine ⟨78400988017602534482879501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52267325345068356321919667 78400988017602534482879501)
                ·
                  refine ⟨29400370506600950431079813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78400988017602534482879501 29400370506600950431079813)
                  ·
                    refine ⟨5512569469987678205827465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29400370506600950431079813 5512569469987678205827465)
                    ·
                      refine ⟨4134427102490758654370599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512569469987678205827465 4134427102490758654370599)
                      ·
                        rfl

theorem cell23_8051768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_8051768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051768 prefixEnd_8051768 := by exact prefixLift 8051768
  have htrace : WordTrace (prefixWord ++ tailWord_8051768) baseStart_8051768 baseEnd_8051768 := by
    simpa [prefixWord, tailWord_8051768, baseEnd_8051768] using wordTrace_append hprefix tailTrace_8051768
  have hstable : (prefixWord ++ tailWord_8051768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051768).length < 2 ^ (prefixWord ++ tailWord_8051768).sum := by decide
  have hdescent : baseEnd_8051768 < baseStart_8051768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051772 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_8051772 : Nat := 118140960795 + 8051772 * 2 ^ 59
def prefixEnd_8051772 : Nat := 4983230072969 + 3 ^ 40 * 8051772 * 2
def baseEnd_8051772 : Nat := 4134429156413376638720581

theorem tailTrace_8051772 : CollatzResearch.WordTrace tailWord_8051772 prefixEnd_8051772 4134429156413376638720581 := by
  unfold tailWord_8051772
  simp only [CollatzResearch.WordTrace]
  refine ⟨146836125492906326011382785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195781500657208434681843713 146836125492906326011382785)
  ·
    refine ⟨110127094119679744508537089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146836125492906326011382785 110127094119679744508537089)
    ·
      refine ⟨82595320589759808381402817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110127094119679744508537089 82595320589759808381402817)
      ·
        refine ⟨61946490442319856286052113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82595320589759808381402817 61946490442319856286052113)
        ·
          refine ⟨46459867831739892214539085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61946490442319856286052113 46459867831739892214539085)
          ·
            refine ⟨17422450436902459580452157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46459867831739892214539085 17422450436902459580452157)
            ·
              refine ⟨6533418913838422342669559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17422450436902459580452157 6533418913838422342669559)
              ·
                refine ⟨9800128370757633514004339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533418913838422342669559 9800128370757633514004339)
                ·
                  refine ⟨14700192556136450271006509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800128370757633514004339 14700192556136450271006509)
                  ·
                    refine ⟨5512572208551168851627441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14700192556136450271006509 5512572208551168851627441)
                    ·
                      refine ⟨4134429156413376638720581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512572208551168851627441 4134429156413376638720581)
                      ·
                        rfl

theorem cell23_8051772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_8051772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051772 prefixEnd_8051772 := by exact prefixLift 8051772
  have htrace : WordTrace (prefixWord ++ tailWord_8051772) baseStart_8051772 baseEnd_8051772 := by
    simpa [prefixWord, tailWord_8051772, baseEnd_8051772] using wordTrace_append hprefix tailTrace_8051772
  have hstable : (prefixWord ++ tailWord_8051772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051772).length < 2 ^ (prefixWord ++ tailWord_8051772).sum := by decide
  have hdescent : baseEnd_8051772 < baseStart_8051772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051858 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_8051858 : Nat := 118140960795 + 8051858 * 2 ^ 59
def prefixEnd_8051858 : Nat := 4983230072969 + 3 ^ 40 * 8051858 * 2
def baseEnd_8051858 : Nat := 4134473315749663302245185

theorem tailTrace_8051858 : CollatzResearch.WordTrace tailWord_8051858 prefixEnd_8051858 4134473315749663302245185 := by
  unfold tailWord_8051858
  simp only [CollatzResearch.WordTrace]
  refine ⟨73418846915875272177599057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195783591775667392473597485 73418846915875272177599057)
  ·
    refine ⟨55064135186906454133199293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73418846915875272177599057 55064135186906454133199293)
    ·
      refine ⟨20649050695089920299949735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55064135186906454133199293 20649050695089920299949735)
      ·
        refine ⟨30973576042634880449924603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20649050695089920299949735 30973576042634880449924603)
        ·
          refine ⟨46460364063952320674886905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30973576042634880449924603 46460364063952320674886905)
          ·
            refine ⟨34845273047964240506165179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46460364063952320674886905 34845273047964240506165179)
            ·
              refine ⟨52267909571946360759247769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34845273047964240506165179 52267909571946360759247769)
              ·
                refine ⟨39200932178959770569435827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52267909571946360759247769 39200932178959770569435827)
                ·
                  refine ⟨58801398268439655854153741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39200932178959770569435827 58801398268439655854153741)
                  ·
                    refine ⟨22050524350664870945307653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58801398268439655854153741 22050524350664870945307653)
                    ·
                      refine ⟨4134473315749663302245185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22050524350664870945307653 4134473315749663302245185)
                      ·
                        rfl

theorem cell23_8051858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_8051858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051858 prefixEnd_8051858 := by exact prefixLift 8051858
  have htrace : WordTrace (prefixWord ++ tailWord_8051858) baseStart_8051858 baseEnd_8051858 := by
    simpa [prefixWord, tailWord_8051858, baseEnd_8051858] using wordTrace_append hprefix tailTrace_8051858
  have hstable : (prefixWord ++ tailWord_8051858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051858).length < 2 ^ (prefixWord ++ tailWord_8051858).sum := by decide
  have hdescent : baseEnd_8051858 < baseStart_8051858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051901 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_8051901 : Nat := 118140960795 + 8051901 * 2 ^ 59
def prefixEnd_8051901 : Nat := 4983230072969 + 3 ^ 40 * 8051901 * 2
def baseEnd_8051901 : Nat := 4134495395417806634007487

theorem tailTrace_8051901 : CollatzResearch.WordTrace tailWord_8051901 prefixEnd_8051901 4134495395417806634007487 := by
  unfold tailWord_8051901
  simp only [CollatzResearch.WordTrace]
  refine ⟨293676956002345307054211557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195784637334896871369474371 293676956002345307054211557)
  ·
    refine ⟨55064429250439745072664667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293676956002345307054211557 55064429250439745072664667)
    ·
      refine ⟨82596643875659617608997001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55064429250439745072664667 82596643875659617608997001)
      ·
        refine ⟨61947482906744713206747751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82596643875659617608997001 61947482906744713206747751)
        ·
          refine ⟨92921224360117069810121627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61947482906744713206747751 92921224360117069810121627)
          ·
            refine ⟨139381836540175604715182441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92921224360117069810121627 139381836540175604715182441)
            ·
              refine ⟨104536377405131703536386831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139381836540175604715182441 104536377405131703536386831)
              ·
                refine ⟨156804566107697555304580247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104536377405131703536386831 156804566107697555304580247)
                ·
                  refine ⟨235206849161546332956870371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156804566107697555304580247 235206849161546332956870371)
                  ·
                    refine ⟨352810273742319499435305557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235206849161546332956870371 352810273742319499435305557)
                    ·
                      refine ⟨4134495395417806634007487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 352810273742319499435305557 4134495395417806634007487)
                      ·
                        rfl

theorem cell23_8051901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_8051901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051901 prefixEnd_8051901 := by exact prefixLift 8051901
  have htrace : WordTrace (prefixWord ++ tailWord_8051901) baseStart_8051901 baseEnd_8051901 := by
    simpa [prefixWord, tailWord_8051901, baseEnd_8051901] using wordTrace_append hprefix tailTrace_8051901
  have hstable : (prefixWord ++ tailWord_8051901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051901).length < 2 ^ (prefixWord ++ tailWord_8051901).sum := by decide
  have hdescent : baseEnd_8051901 < baseStart_8051901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051902 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_8051902 : Nat := 118140960795 + 8051902 * 2 ^ 59
def prefixEnd_8051902 : Nat := 4983230072969 + 3 ^ 40 * 8051902 * 2
def baseEnd_8051902 : Nat := 1378165302966153710031661

theorem tailTrace_8051902 : CollatzResearch.WordTrace tailWord_8051902 prefixEnd_8051902 1378165302966153710031661 := by
  unfold tailWord_8051902
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709624059417710528124745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195784661650227789483331973 36709624059417710528124745)
  ·
    refine ⟨27532218044563282896093559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36709624059417710528124745 27532218044563282896093559)
    ·
      refine ⟨41298327066844924344140339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27532218044563282896093559 41298327066844924344140339)
      ·
        refine ⟨61947490600267386516210509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41298327066844924344140339 61947490600267386516210509)
        ·
          refine ⟨23230308975100269943578941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61947490600267386516210509 23230308975100269943578941)
          ·
            refine ⟨8711365865662601228842103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23230308975100269943578941 8711365865662601228842103)
            ·
              refine ⟨13067048798493901843263155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711365865662601228842103 13067048798493901843263155)
              ·
                refine ⟨19600573197740852764894733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067048798493901843263155 19600573197740852764894733)
                ·
                  refine ⟨7350214949152819786835525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19600573197740852764894733 7350214949152819786835525)
                  ·
                    refine ⟨1378165302966153710031661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7350214949152819786835525 1378165302966153710031661)
                    ·
                      rfl

theorem cell23_8051902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_8051902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051902 prefixEnd_8051902 := by exact prefixLift 8051902
  have htrace : WordTrace (prefixWord ++ tailWord_8051902) baseStart_8051902 baseEnd_8051902 := by
    simpa [prefixWord, tailWord_8051902, baseEnd_8051902] using wordTrace_append hprefix tailTrace_8051902
  have hstable : (prefixWord ++ tailWord_8051902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051902).length < 2 ^ (prefixWord ++ tailWord_8051902).sum := by decide
  have hdescent : baseEnd_8051902 < baseStart_8051902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051935 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 2, 3, 2]
def baseStart_8051935 : Nat := 118140960795 + 8051935 * 2 ^ 59
def prefixEnd_8051935 : Nat := 4983230072969 + 3 ^ 40 * 8051935 * 2
def baseEnd_8051935 : Nat := 4134512853760059500982331

theorem tailTrace_8051935 : CollatzResearch.WordTrace tailWord_8051935 prefixEnd_8051935 4134512853760059500982331 := by
  unfold tailWord_8051935
  simp only [CollatzResearch.WordTrace]
  refine ⟨293678196084222130860949259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195785464056148087240632839 293678196084222130860949259)
  ·
    refine ⟨440517294126333196291423889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293678196084222130860949259 440517294126333196291423889)
    ·
      refine ⟨330387970594749897218567917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440517294126333196291423889 330387970594749897218567917)
      ·
        refine ⟨123895488973031211456962969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330387970594749897218567917 123895488973031211456962969)
        ·
          refine ⟨92921616729773408592722227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123895488973031211456962969 92921616729773408592722227)
          ·
            refine ⟨139382425094660112889083341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92921616729773408592722227 139382425094660112889083341)
            ·
              refine ⟨52268409410497542333406253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139382425094660112889083341 52268409410497542333406253)
              ·
                refine ⟨19600653528936578375027345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52268409410497542333406253 19600653528936578375027345)
                ·
                  refine ⟨14700490146702433781270509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19600653528936578375027345 14700490146702433781270509)
                  ·
                    refine ⟨5512683805013412667976441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14700490146702433781270509 5512683805013412667976441)
                    ·
                      refine ⟨4134512853760059500982331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512683805013412667976441 4134512853760059500982331)
                      ·
                        rfl

theorem cell23_8051935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_8051935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051935 prefixEnd_8051935 := by exact prefixLift 8051935
  have htrace : WordTrace (prefixWord ++ tailWord_8051935) baseStart_8051935 baseEnd_8051935 := by
    simpa [prefixWord, tailWord_8051935, baseEnd_8051935] using wordTrace_append hprefix tailTrace_8051935
  have hstable : (prefixWord ++ tailWord_8051935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051935).length < 2 ^ (prefixWord ++ tailWord_8051935).sum := by decide
  have hdescent : baseEnd_8051935 < baseStart_8051935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051958 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_8051958 : Nat := 118140960795 + 8051958 * 2 ^ 59
def prefixEnd_8051958 : Nat := 4983230072969 + 3 ^ 40 * 8051958 * 2
def baseEnd_8051958 : Nat := 1378174887938370970331575

theorem tailTrace_8051958 : CollatzResearch.WordTrace tailWord_8051958 prefixEnd_8051958 1378174887938370970331575 := by
  unfold tailWord_8051958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18354939685196175361814783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195786023308759203859357685 18354939685196175361814783)
  ·
    refine ⟨27532409527794263042722175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18354939685196175361814783 27532409527794263042722175)
    ·
      refine ⟨41298614291691394564083263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27532409527794263042722175 41298614291691394564083263)
      ·
        refine ⟨61947921437537091846124895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41298614291691394564083263 61947921437537091846124895)
        ·
          refine ⟨92921882156305637769187343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61947921437537091846124895 92921882156305637769187343)
          ·
            refine ⟨139382823234458456653781015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92921882156305637769187343 139382823234458456653781015)
            ·
              refine ⟨209074234851687684980671523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139382823234458456653781015 209074234851687684980671523)
              ·
                refine ⟨313611352277531527471007285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209074234851687684980671523 313611352277531527471007285)
                ·
                  refine ⟨29401064276018580700406933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313611352277531527471007285 29401064276018580700406933)
                  ·
                    refine ⟨1378174887938370970331575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29401064276018580700406933 1378174887938370970331575)
                    ·
                      rfl

theorem cell23_8051958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_8051958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051958 prefixEnd_8051958 := by exact prefixLift 8051958
  have htrace : WordTrace (prefixWord ++ tailWord_8051958) baseStart_8051958 baseEnd_8051958 := by
    simpa [prefixWord, tailWord_8051958, baseEnd_8051958] using wordTrace_append hprefix tailTrace_8051958
  have hstable : (prefixWord ++ tailWord_8051958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051958).length < 2 ^ (prefixWord ++ tailWord_8051958).sum := by decide
  have hdescent : baseEnd_8051958 < baseStart_8051958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051982 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_8051982 : Nat := 118140960795 + 8051982 * 2 ^ 59
def prefixEnd_8051982 : Nat := 4983230072969 + 3 ^ 40 * 8051982 * 2
def baseEnd_8051982 : Nat := 4134536987350820817094615

theorem tailTrace_8051982 : CollatzResearch.WordTrace tailWord_8051982 prefixEnd_8051982 4134536987350820817094615 := by
  unfold tailWord_8051982
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709988789381482235988775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195786606876701238591940133 36709988789381482235988775)
  ·
    refine ⟨55064983184072223353983163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36709988789381482235988775 55064983184072223353983163)
    ·
      refine ⟨82597474776108335030974745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55064983184072223353983163 82597474776108335030974745)
      ·
        refine ⟨61948106082081251273231059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82597474776108335030974745 61948106082081251273231059)
        ·
          refine ⟨92922159123121876909846589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61948106082081251273231059 92922159123121876909846589)
          ·
            refine ⟨34845809671170703841192471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92922159123121876909846589 34845809671170703841192471)
            ·
              refine ⟨52268714506756055761788707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34845809671170703841192471 52268714506756055761788707)
              ·
                refine ⟨78403071760134083642683061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52268714506756055761788707 78403071760134083642683061)
                ·
                  refine ⟨7350287977512570341501537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78403071760134083642683061 7350287977512570341501537)
                  ·
                    refine ⟨5512715983134427756126153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7350287977512570341501537 5512715983134427756126153)
                    ·
                      refine ⟨4134536987350820817094615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512715983134427756126153 4134536987350820817094615)
                      ·
                        rfl

theorem cell23_8051982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_8051982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051982 prefixEnd_8051982 := by exact prefixLift 8051982
  have htrace : WordTrace (prefixWord ++ tailWord_8051982) baseStart_8051982 baseEnd_8051982 := by
    simpa [prefixWord, tailWord_8051982, baseEnd_8051982] using wordTrace_append hprefix tailTrace_8051982
  have hstable : (prefixWord ++ tailWord_8051982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051982).length < 2 ^ (prefixWord ++ tailWord_8051982).sum := by decide
  have hdescent : baseEnd_8051982 < baseStart_8051982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051985 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_8051985 : Nat := 118140960795 + 8051985 * 2 ^ 59
def prefixEnd_8051985 : Nat := 4983230072969 + 3 ^ 40 * 8051985 * 2
def baseEnd_8051985 : Nat := 4134538527792784305357101

theorem tailTrace_8051985 : CollatzResearch.WordTrace tailWord_8051985 prefixEnd_8051985 4134538527792784305357101 := by
  unfold tailWord_8051985
  simp only [CollatzResearch.WordTrace]
  refine ⟨293680019734040989400269409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195786679822693992933512939 293680019734040989400269409)
  ·
    refine ⟨220260014800530742050202057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293680019734040989400269409 220260014800530742050202057)
    ·
      refine ⟨165195011100398056537651543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220260014800530742050202057 165195011100398056537651543)
      ·
        refine ⟨247792516650597084806477315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165195011100398056537651543 247792516650597084806477315)
        ·
          refine ⟨371688774975895627209715973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247792516650597084806477315 371688774975895627209715973)
          ·
            refine ⟨69691645307980430101821745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371688774975895627209715973 69691645307980430101821745)
            ·
              refine ⟨52268733980985322576366309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69691645307980430101821745 52268733980985322576366309)
              ·
                refine ⟨9800387621434747983068683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52268733980985322576366309 9800387621434747983068683)
                ·
                  refine ⟨14700581432152121974603025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800387621434747983068683 14700581432152121974603025)
                  ·
                    refine ⟨11025436074114091480952269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14700581432152121974603025 11025436074114091480952269)
                    ·
                      refine ⟨4134538527792784305357101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11025436074114091480952269 4134538527792784305357101)
                      ·
                        rfl

theorem cell23_8051985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_8051985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051985 prefixEnd_8051985 := by exact prefixLift 8051985
  have htrace : WordTrace (prefixWord ++ tailWord_8051985) baseStart_8051985 baseEnd_8051985 := by
    simpa [prefixWord, tailWord_8051985, baseEnd_8051985] using wordTrace_append hprefix tailTrace_8051985
  have hstable : (prefixWord ++ tailWord_8051985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051985).length < 2 ^ (prefixWord ++ tailWord_8051985).sum := by decide
  have hdescent : baseEnd_8051985 < baseStart_8051985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8051999 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 1, 1, 4]
def baseStart_8051999 : Nat := 118140960795 + 8051999 * 2 ^ 59
def prefixEnd_8051999 : Nat := 4983230072969 + 3 ^ 40 * 8051999 * 2
def baseEnd_8051999 : Nat := 4134545716521947250582037

theorem tailTrace_8051999 : CollatzResearch.WordTrace tailWord_8051999 prefixEnd_8051999 4134545716521947250582037 := by
  unfold tailWord_8051999
  simp only [CollatzResearch.WordTrace]
  refine ⟨293680530355990269791279051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195787020237326846527519367 293680530355990269791279051)
  ·
    refine ⟨440520795533985404686918577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293680530355990269791279051 440520795533985404686918577)
    ·
      refine ⟨330390596650489053515188933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440520795533985404686918577 330390596650489053515188933)
      ·
        refine ⟨61948236871966697534097925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330390596650489053515188933 61948236871966697534097925)
        ·
          refine ⟨11615294413493755787643361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61948236871966697534097925 11615294413493755787643361)
          ·
            refine ⟨8711470810120316840732521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11615294413493755787643361 8711470810120316840732521)
            ·
              refine ⟨6533603107590237630549391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8711470810120316840732521 6533603107590237630549391)
              ·
                refine ⟨9800404661385356445824087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533603107590237630549391 9800404661385356445824087)
                ·
                  refine ⟨14700606992078034668736131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800404661385356445824087 14700606992078034668736131)
                  ·
                    refine ⟨22050910488117052003104197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14700606992078034668736131 22050910488117052003104197)
                    ·
                      refine ⟨4134545716521947250582037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22050910488117052003104197 4134545716521947250582037)
                      ·
                        rfl

theorem cell23_8051999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_8051999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8051999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8051999 prefixEnd_8051999 := by exact prefixLift 8051999
  have htrace : WordTrace (prefixWord ++ tailWord_8051999) baseStart_8051999 baseEnd_8051999 := by
    simpa [prefixWord, tailWord_8051999, baseEnd_8051999] using wordTrace_append hprefix tailTrace_8051999
  have hstable : (prefixWord ++ tailWord_8051999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8051999).length < 2 ^ (prefixWord ++ tailWord_8051999).sum := by decide
  have hdescent : baseEnd_8051999 < baseStart_8051999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8051999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052029 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8052029 : Nat := 118140960795 + 8052029 * 2 ^ 59
def prefixEnd_8052029 : Nat := 4983230072969 + 3 ^ 40 * 8052029 * 2
def baseEnd_8052029 : Nat := 4134561120941582133206899

theorem tailTrace_8052029 : CollatzResearch.WordTrace tailWord_8052029 prefixEnd_8052029 4134561120941582133206899 := by
  unfold tailWord_8052029
  simp only [CollatzResearch.WordTrace]
  refine ⟨293681624545881584914871141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195787749697254389943247427 293681624545881584914871141)
  ·
    refine ⟨55065304602352797171538339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293681624545881584914871141 55065304602352797171538339)
    ·
      refine ⟨82597956903529195757307509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55065304602352797171538339 82597956903529195757307509)
      ·
        refine ⟨7743558459705862102247579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82597956903529195757307509 7743558459705862102247579)
        ·
          refine ⟨11615337689558793153371369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7743558459705862102247579 11615337689558793153371369)
          ·
            refine ⟨8711503267169094865028527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11615337689558793153371369 8711503267169094865028527)
            ·
              refine ⟨13067254900753642297542791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711503267169094865028527 13067254900753642297542791)
              ·
                refine ⟨19600882351130463446314187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067254900753642297542791 19600882351130463446314187)
                ·
                  refine ⟨29401323526695695169471281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19600882351130463446314187 29401323526695695169471281)
                  ·
                    refine ⟨22050992645021771377103461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29401323526695695169471281 22050992645021771377103461)
                    ·
                      refine ⟨4134561120941582133206899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22050992645021771377103461 4134561120941582133206899)
                      ·
                        rfl

theorem cell23_8052029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8052029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052029 prefixEnd_8052029 := by exact prefixLift 8052029
  have htrace : WordTrace (prefixWord ++ tailWord_8052029) baseStart_8052029 baseEnd_8052029 := by
    simpa [prefixWord, tailWord_8052029, baseEnd_8052029] using wordTrace_append hprefix tailTrace_8052029
  have hstable : (prefixWord ++ tailWord_8052029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052029).length < 2 ^ (prefixWord ++ tailWord_8052029).sum := by decide
  have hdescent : baseEnd_8052029 < baseStart_8052029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052058 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_8052058 : Nat := 118140960795 + 8052058 * 2 ^ 59
def prefixEnd_8052058 : Nat := 4983230072969 + 3 ^ 40 * 8052058 * 2
def baseEnd_8052058 : Nat := 4134576011880562519744265

theorem tailTrace_8052058 : CollatzResearch.WordTrace tailWord_8052058 prefixEnd_8052058 4134576011880562519744265 := by
  unfold tailWord_8052058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73420670565694130716919207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195788454841851015245117885 73420670565694130716919207)
  ·
    refine ⟨110131005848541196075378811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73420670565694130716919207 110131005848541196075378811)
    ·
      refine ⟨165196508772811794113068217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110131005848541196075378811 165196508772811794113068217)
      ·
        refine ⟨123897381579608845584801163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165196508772811794113068217 123897381579608845584801163)
        ·
          refine ⟨185846072369413268377201745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123897381579608845584801163 185846072369413268377201745)
          ·
            refine ⟨139384554277059951282901309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185846072369413268377201745 139384554277059951282901309)
            ·
              refine ⟨52269207853897481731087991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139384554277059951282901309 52269207853897481731087991)
              ·
                refine ⟨78403811780846222596631987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52269207853897481731087991 78403811780846222596631987)
                ·
                  refine ⟨117605717671269333894947981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78403811780846222596631987 117605717671269333894947981)
                  ·
                    refine ⟨44102144126726000210605493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117605717671269333894947981 44102144126726000210605493)
                    ·
                      refine ⟨4134576011880562519744265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44102144126726000210605493 4134576011880562519744265)
                      ·
                        rfl

theorem cell23_8052058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_8052058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052058 prefixEnd_8052058 := by exact prefixLift 8052058
  have htrace : WordTrace (prefixWord ++ tailWord_8052058) baseStart_8052058 baseEnd_8052058 := by
    simpa [prefixWord, tailWord_8052058, baseEnd_8052058] using wordTrace_append hprefix tailTrace_8052058
  have hstable : (prefixWord ++ tailWord_8052058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052058).length < 2 ^ (prefixWord ++ tailWord_8052058).sum := by decide
  have hdescent : baseEnd_8052058 < baseStart_8052058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052115 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 5, 2]
def baseStart_8052115 : Nat := 118140960795 + 8052115 * 2 ^ 59
def prefixEnd_8052115 : Nat := 4983230072969 + 3 ^ 40 * 8052115 * 2
def baseEnd_8052115 : Nat := 4134605280277868796731503

theorem tailTrace_8052115 : CollatzResearch.WordTrace tailWord_8052115 prefixEnd_8052115 4134605280277868796731503 := by
  unfold tailWord_8052115
  simp only [CollatzResearch.WordTrace]
  refine ⟨293684761223570021602501799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195789840815713347735001199 293684761223570021602501799)
  ·
    refine ⟨440527141835355032403752699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293684761223570021602501799 440527141835355032403752699)
    ·
      refine ⟨660790712753032548605629049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440527141835355032403752699 660790712753032548605629049)
      ·
        refine ⟨495593034564774411454221787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660790712753032548605629049 495593034564774411454221787)
        ·
          refine ⟨743389551847161617181332681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495593034564774411454221787 743389551847161617181332681)
          ·
            refine ⟨557542163885371212885999511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743389551847161617181332681 557542163885371212885999511)
            ·
              refine ⟨836313245828056819328999267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557542163885371212885999511 836313245828056819328999267)
              ·
                refine ⟨1254469868742085228993498901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836313245828056819328999267 1254469868742085228993498901)
                ·
                  refine ⟨58803275097285245109070261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1254469868742085228993498901 58803275097285245109070261)
                  ·
                    refine ⟨5512807040370491728975337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58803275097285245109070261 5512807040370491728975337)
                    ·
                      refine ⟨4134605280277868796731503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512807040370491728975337 4134605280277868796731503)
                      ·
                        rfl

theorem cell23_8052115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5, 2].length) (baseStart_8052115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052115 prefixEnd_8052115 := by exact prefixLift 8052115
  have htrace : WordTrace (prefixWord ++ tailWord_8052115) baseStart_8052115 baseEnd_8052115 := by
    simpa [prefixWord, tailWord_8052115, baseEnd_8052115] using wordTrace_append hprefix tailTrace_8052115
  have hstable : (prefixWord ++ tailWord_8052115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052115).length < 2 ^ (prefixWord ++ tailWord_8052115).sum := by decide
  have hdescent : baseEnd_8052115 < baseStart_8052115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052135 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_8052135 : Nat := 118140960795 + 8052135 * 2 ^ 59
def prefixEnd_8052135 : Nat := 4983230072969 + 3 ^ 40 * 8052135 * 2
def baseEnd_8052135 : Nat := 4134615549890958718481411

theorem tailTrace_8052135 : CollatzResearch.WordTrace tailWord_8052135 prefixEnd_8052135 4134615549890958718481411 := by
  unfold tailWord_8052135
  simp only [CollatzResearch.WordTrace]
  refine ⟨293685490683497565018229859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195790327122331710012153239 293685490683497565018229859)
  ·
    refine ⟨440528236025246347527344789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293685490683497565018229859 440528236025246347527344789)
    ·
      refine ⟨20649761063683422540344287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440528236025246347527344789 20649761063683422540344287)
      ·
        refine ⟨30974641595525133810516431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20649761063683422540344287 30974641595525133810516431)
        ·
          refine ⟨46461962393287700715774647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30974641595525133810516431 46461962393287700715774647)
          ·
            refine ⟨69692943589931551073661971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46461962393287700715774647 69692943589931551073661971)
            ·
              refine ⟨104539415384897326610492957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69692943589931551073661971 104539415384897326610492957)
              ·
                refine ⟨39202280769336497478934859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104539415384897326610492957 39202280769336497478934859)
                ·
                  refine ⟨58803421154004746218402289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39202280769336497478934859 58803421154004746218402289)
                  ·
                    refine ⟨44102565865503559663801717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58803421154004746218402289 44102565865503559663801717)
                    ·
                      refine ⟨4134615549890958718481411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44102565865503559663801717 4134615549890958718481411)
                      ·
                        rfl

theorem cell23_8052135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_8052135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052135 prefixEnd_8052135 := by exact prefixLift 8052135
  have htrace : WordTrace (prefixWord ++ tailWord_8052135) baseStart_8052135 baseEnd_8052135 := by
    simpa [prefixWord, tailWord_8052135, baseEnd_8052135] using wordTrace_append hprefix tailTrace_8052135
  have hstable : (prefixWord ++ tailWord_8052135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052135).length < 2 ^ (prefixWord ++ tailWord_8052135).sum := by decide
  have hdescent : baseEnd_8052135 < baseStart_8052135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052145 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_8052145 : Nat := 118140960795 + 8052145 * 2 ^ 59
def prefixEnd_8052145 : Nat := 4983230072969 + 3 ^ 40 * 8052145 * 2
def baseEnd_8052145 : Nat := 4134620684697503679356365

theorem tailTrace_8052145 : CollatzResearch.WordTrace tailWord_8052145 prefixEnd_8052145 4134620684697503679356365 := by
  unfold tailWord_8052145
  simp only [CollatzResearch.WordTrace]
  refine ⟨293685855413461336726093889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195790570275640891150729259 293685855413461336726093889)
  ·
    refine ⟨220264391560096002544570417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293685855413461336726093889 220264391560096002544570417)
    ·
      refine ⟨165198293670072001908427813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220264391560096002544570417 165198293670072001908427813)
      ·
        refine ⟨30974680063138500357830215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165198293670072001908427813 30974680063138500357830215)
        ·
          refine ⟨46462020094707750536745323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30974680063138500357830215 46462020094707750536745323)
          ·
            refine ⟨69693030142061625805117985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46462020094707750536745323 69693030142061625805117985)
            ·
              refine ⟨52269772606546219353838489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69693030142061625805117985 52269772606546219353838489)
              ·
                refine ⟨39202329454909664515378867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52269772606546219353838489 39202329454909664515378867)
                ·
                  refine ⟨58803494182364496773068301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39202329454909664515378867 58803494182364496773068301)
                  ·
                    refine ⟨22051310318386686289900613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58803494182364496773068301 22051310318386686289900613)
                    ·
                      refine ⟨4134620684697503679356365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22051310318386686289900613 4134620684697503679356365)
                      ·
                        rfl

theorem cell23_8052145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_8052145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052145 prefixEnd_8052145 := by exact prefixLift 8052145
  have htrace : WordTrace (prefixWord ++ tailWord_8052145) baseStart_8052145 baseEnd_8052145 := by
    simpa [prefixWord, tailWord_8052145, baseEnd_8052145] using wordTrace_append hprefix tailTrace_8052145
  have hstable : (prefixWord ++ tailWord_8052145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052145).length < 2 ^ (prefixWord ++ tailWord_8052145).sum := by decide
  have hdescent : baseEnd_8052145 < baseStart_8052145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052185 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 8]
def baseStart_8052185 : Nat := 118140960795 + 8052185 * 2 ^ 59
def prefixEnd_8052185 : Nat := 4983230072969 + 3 ^ 40 * 8052185 * 2
def baseEnd_8052185 : Nat := 459404580435964835872909

theorem tailTrace_8052185 : CollatzResearch.WordTrace tailWord_8052185 prefixEnd_8052185 459404580435964835872909 := by
  unfold tailWord_8052185
  simp only [CollatzResearch.WordTrace]
  refine ⟨293687314333316423557550009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195791542888877615705033339 293687314333316423557550009)
  ·
    refine ⟨220265485749987317668162507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293687314333316423557550009 220265485749987317668162507)
    ·
      refine ⟨330398228624980976502243761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220265485749987317668162507 330398228624980976502243761)
      ·
        refine ⟨247798671468735732376682821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330398228624980976502243761 247798671468735732376682821)
        ·
          refine ⟨46462250900387949820628029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247798671468735732376682821 46462250900387949820628029)
          ·
            refine ⟨17423344087645481182735511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46462250900387949820628029 17423344087645481182735511)
            ·
              refine ⟨26135016131468221774103267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17423344087645481182735511 26135016131468221774103267)
              ·
                refine ⟨39202524197202332661154901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26135016131468221774103267 39202524197202332661154901)
                ·
                  refine ⟨459404580435964835872909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39202524197202332661154901 459404580435964835872909)
                  ·
                    rfl

theorem cell23_8052185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_8052185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052185 prefixEnd_8052185 := by exact prefixLift 8052185
  have htrace : WordTrace (prefixWord ++ tailWord_8052185) baseStart_8052185 baseEnd_8052185 := by
    simpa [prefixWord, tailWord_8052185, baseEnd_8052185] using wordTrace_append hprefix tailTrace_8052185
  have hstable : (prefixWord ++ tailWord_8052185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052185).length < 2 ^ (prefixWord ++ tailWord_8052185).sum := by decide
  have hdescent : baseEnd_8052185 < baseStart_8052185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052189 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_8052189 : Nat := 118140960795 + 8052189 * 2 ^ 59
def prefixEnd_8052189 : Nat := 4983230072969 + 3 ^ 40 * 8052189 * 2
def baseEnd_8052189 : Nat := 1378214425948767169068721

theorem tailTrace_8052189 : CollatzResearch.WordTrace tailWord_8052189 prefixEnd_8052189 1378214425948767169068721 := by
  unfold tailWord_8052189
  simp only [CollatzResearch.WordTrace]
  refine ⟨293687460225301932240695621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195791640150201288160463747 293687460225301932240695621)
  ·
    refine ⟨55066398792244112295130429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293687460225301932240695621 55066398792244112295130429)
    ·
      refine ⟨20649899547091542110673911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55066398792244112295130429 20649899547091542110673911)
      ·
        refine ⟨30974849320637313166010867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20649899547091542110673911 30974849320637313166010867)
        ·
          refine ⟨46462273980955969749016301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30974849320637313166010867 46462273980955969749016301)
          ·
            refine ⟨17423352742858488655881113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46462273980955969749016301 17423352742858488655881113)
            ·
              refine ⟨13067514557143866491910835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17423352742858488655881113 13067514557143866491910835)
              ·
                refine ⟨19601271835715799737866253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067514557143866491910835 19601271835715799737866253)
                ·
                  refine ⟨7350476938393424901699845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19601271835715799737866253 7350476938393424901699845)
                  ·
                    refine ⟨1378214425948767169068721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7350476938393424901699845 1378214425948767169068721)
                    ·
                      rfl

theorem cell23_8052189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_8052189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052189 prefixEnd_8052189 := by exact prefixLift 8052189
  have htrace : WordTrace (prefixWord ++ tailWord_8052189) baseStart_8052189 baseEnd_8052189 := by
    simpa [prefixWord, tailWord_8052189, baseEnd_8052189] using wordTrace_append hprefix tailTrace_8052189
  have hstable : (prefixWord ++ tailWord_8052189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052189).length < 2 ^ (prefixWord ++ tailWord_8052189).sum := by decide
  have hdescent : baseEnd_8052189 < baseStart_8052189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052232 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_8052232 : Nat := 118140960795 + 8052232 * 2 ^ 59
def prefixEnd_8052232 : Nat := 4983230072969 + 3 ^ 40 * 8052232 * 2
def baseEnd_8052232 : Nat := 1378221785838148279656155

theorem tailTrace_8052232 : CollatzResearch.WordTrace tailWord_8052232 prefixEnd_8052232 1378221785838148279656155 := by
  unfold tailWord_8052232
  simp only [CollatzResearch.WordTrace]
  refine ⟨146844514282073075292255475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195792685709430767056340633 146844514282073075292255475)
  ·
    refine ⟨220266771423109612938383213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146844514282073075292255475 220266771423109612938383213)
    ·
      refine ⟨82600039283666104851893705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220266771423109612938383213 82600039283666104851893705)
      ·
        refine ⟨61950029462749578638920279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82600039283666104851893705 61950029462749578638920279)
        ·
          refine ⟨92925044194124367958380419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61950029462749578638920279 92925044194124367958380419)
          ·
            refine ⟨139387566291186551937570629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92925044194124367958380419 139387566291186551937570629)
            ·
              refine ⟨26135168679597478488294493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139387566291186551937570629 26135168679597478488294493)
              ·
                refine ⟨9800688254849054433110435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26135168679597478488294493 9800688254849054433110435)
                ·
                  refine ⟨14701032382273581649665653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800688254849054433110435 14701032382273581649665653)
                  ·
                    refine ⟨1378221785838148279656155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14701032382273581649665653 1378221785838148279656155)
                    ·
                      rfl

theorem cell23_8052232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_8052232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052232 prefixEnd_8052232 := by exact prefixLift 8052232
  have htrace : WordTrace (prefixWord ++ tailWord_8052232) baseStart_8052232 baseEnd_8052232 := by
    simpa [prefixWord, tailWord_8052232, baseEnd_8052232] using wordTrace_append hprefix tailTrace_8052232
  have hstable : (prefixWord ++ tailWord_8052232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052232).length < 2 ^ (prefixWord ++ tailWord_8052232).sum := by decide
  have hdescent : baseEnd_8052232 < baseStart_8052232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052252 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_8052252 : Nat := 118140960795 + 8052252 * 2 ^ 59
def prefixEnd_8052252 : Nat := 4983230072969 + 3 ^ 40 * 8052252 * 2
def baseEnd_8052252 : Nat := 4134675627127534760718373

theorem tailTrace_8052252 : CollatzResearch.WordTrace tailWord_8052252 prefixEnd_8052252 4134675627127534760718373 := by
  unfold tailWord_8052252
  simp only [CollatzResearch.WordTrace]
  refine ⟨146844879012036847000119505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195793172016049129333492673 146844879012036847000119505)
  ·
    refine ⟨110133659259027635250089629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146844879012036847000119505 110133659259027635250089629)
    ·
      refine ⟨41300122222135363218783611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110133659259027635250089629 41300122222135363218783611)
      ·
        refine ⟨61950183333203044828175417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41300122222135363218783611 61950183333203044828175417)
        ·
          refine ⟨46462637499902283621131563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61950183333203044828175417 46462637499902283621131563)
          ·
            refine ⟨69693956249853425431697345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46462637499902283621131563 69693956249853425431697345)
            ·
              refine ⟨52270467187390069073773009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69693956249853425431697345 52270467187390069073773009)
              ·
                refine ⟨39202850390542551805329757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52270467187390069073773009 39202850390542551805329757)
                ·
                  refine ⟨14701068896453456926998659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39202850390542551805329757 14701068896453456926998659)
                  ·
                    refine ⟨22051603344680185390497989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14701068896453456926998659 22051603344680185390497989)
                    ·
                      refine ⟨4134675627127534760718373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22051603344680185390497989 4134675627127534760718373)
                      ·
                        rfl

theorem cell23_8052252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_8052252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052252 prefixEnd_8052252 := by exact prefixLift 8052252
  have htrace : WordTrace (prefixWord ++ tailWord_8052252) baseStart_8052252 baseEnd_8052252 := by
    simpa [prefixWord, tailWord_8052252, baseEnd_8052252] using wordTrace_append hprefix tailTrace_8052252
  have hstable : (prefixWord ++ tailWord_8052252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052252).length < 2 ^ (prefixWord ++ tailWord_8052252).sum := by decide
  have hdescent : baseEnd_8052252 < baseStart_8052252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052275 : List Nat := [1, 1, 1, 2, 4, 3, 2, 9]
def baseStart_8052275 : Nat := 118140960795 + 8052275 * 2 ^ 59
def prefixEnd_8052275 : Nat := 4983230072969 + 3 ^ 40 * 8052275 * 2
def baseEnd_8052275 : Nat := 153136571747503265582621

theorem tailTrace_8052275 : CollatzResearch.WordTrace tailWord_8052275 prefixEnd_8052275 153136571747503265582621 := by
  unfold tailWord_8052275
  simp only [CollatzResearch.WordTrace]
  refine ⟨293690596902990368928326279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195793731268660245952217519 293690596902990368928326279)
  ·
    refine ⟨440535895354485553392489419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293690596902990368928326279 440535895354485553392489419)
    ·
      refine ⟨660803843031728330088734129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440535895354485553392489419 660803843031728330088734129)
      ·
        refine ⟨495602882273796247566550597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660803843031728330088734129 495602882273796247566550597)
        ·
          refine ⟨92925540426336796418728237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495602882273796247566550597 92925540426336796418728237)
          ·
            refine ⟨34847077659876298657023089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92925540426336796418728237 34847077659876298657023089)
            ·
              refine ⟨26135308244907223992767317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34847077659876298657023089 26135308244907223992767317)
              ·
                refine ⟨153136571747503265582621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26135308244907223992767317 153136571747503265582621)
                ·
                  rfl

theorem cell23_8052275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 9].length) (baseStart_8052275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052275 prefixEnd_8052275 := by exact prefixLift 8052275
  have htrace : WordTrace (prefixWord ++ tailWord_8052275) baseStart_8052275 baseEnd_8052275 := by
    simpa [prefixWord, tailWord_8052275, baseEnd_8052275] using wordTrace_append hprefix tailTrace_8052275
  have hstable : (prefixWord ++ tailWord_8052275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052275).length < 2 ^ (prefixWord ++ tailWord_8052275).sum := by decide
  have hdescent : baseEnd_8052275 < baseStart_8052275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052282 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_8052282 : Nat := 118140960795 + 8052282 * 2 ^ 59
def prefixEnd_8052282 : Nat := 4983230072969 + 3 ^ 40 * 8052282 * 2
def baseEnd_8052282 : Nat := 4134691031547169643343235

theorem tailTrace_8052282 : CollatzResearch.WordTrace tailWord_8052282 prefixEnd_8052282 4134691031547169643343235 := by
  unfold tailWord_8052282
  simp only [CollatzResearch.WordTrace]
  refine ⟨73422713053491252280957775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195793901475976672749220733 73422713053491252280957775)
  ·
    refine ⟨110134069580236878421436663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73422713053491252280957775 110134069580236878421436663)
    ·
      refine ⟨165201104370355317632154995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110134069580236878421436663 165201104370355317632154995)
      ·
        refine ⟨247801656555532976448232493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165201104370355317632154995 247801656555532976448232493)
        ·
          refine ⟨92925621208324866168087185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247801656555532976448232493 92925621208324866168087185)
          ·
            refine ⟨69694215906243649626065389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92925621208324866168087185 69694215906243649626065389)
            ·
              refine ⟨26135330964841368609774521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69694215906243649626065389 26135330964841368609774521)
              ·
                refine ⟨19601498223631026457330891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26135330964841368609774521 19601498223631026457330891)
                ·
                  refine ⟨29402247335446539685996337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19601498223631026457330891 29402247335446539685996337)
                  ·
                    refine ⟨22051685501584904764497253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29402247335446539685996337 22051685501584904764497253)
                    ·
                      refine ⟨4134691031547169643343235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22051685501584904764497253 4134691031547169643343235)
                      ·
                        rfl

theorem cell23_8052282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_8052282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052282 prefixEnd_8052282 := by exact prefixLift 8052282
  have htrace : WordTrace (prefixWord ++ tailWord_8052282) baseStart_8052282 baseEnd_8052282 := by
    simpa [prefixWord, tailWord_8052282, baseEnd_8052282] using wordTrace_append hprefix tailTrace_8052282
  have hstable : (prefixWord ++ tailWord_8052282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052282).length < 2 ^ (prefixWord ++ tailWord_8052282).sum := by decide
  have hdescent : baseEnd_8052282 < baseStart_8052282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052292 : List Nat := [2, 3, 5, 13]
def baseStart_8052292 : Nat := 118140960795 + 8052292 * 2 ^ 59
def prefixEnd_8052292 : Nat := 4983230072969 + 3 ^ 40 * 8052292 * 2
def baseEnd_8052292 : Nat := 1890578951236266394247

theorem tailTrace_8052292 : CollatzResearch.WordTrace tailWord_8052292 prefixEnd_8052292 1890578951236266394247 := by
  unfold tailWord_8052292
  simp only [CollatzResearch.WordTrace]
  refine ⟨146845608471964390415847565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195794144629285853887796753 146845608471964390415847565)
  ·
    refine ⟨55067103176986646405942837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146845608471964390415847565 55067103176986646405942837)
    ·
      refine ⟨5162540922842498100557141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55067103176986646405942837 5162540922842498100557141)
      ·
        refine ⟨1890578951236266394247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5162540922842498100557141 1890578951236266394247)
        ·
          rfl

theorem cell23_8052292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 13].length) (baseStart_8052292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052292 prefixEnd_8052292 := by exact prefixLift 8052292
  have htrace : WordTrace (prefixWord ++ tailWord_8052292) baseStart_8052292 baseEnd_8052292 := by
    simpa [prefixWord, tailWord_8052292, baseEnd_8052292] using wordTrace_append hprefix tailTrace_8052292
  have hstable : (prefixWord ++ tailWord_8052292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052292).length < 2 ^ (prefixWord ++ tailWord_8052292).sum := by decide
  have hdescent : baseEnd_8052292 < baseStart_8052292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052302 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_8052302 : Nat := 118140960795 + 8052302 * 2 ^ 59
def prefixEnd_8052302 : Nat := 4983230072969 + 3 ^ 40 * 8052302 * 2
def baseEnd_8052302 : Nat := 4134701301160259565093143

theorem tailTrace_8052302 : CollatzResearch.WordTrace tailWord_8052302 prefixEnd_8052302 4134701301160259565093143 := by
  unfold tailWord_8052302
  simp only [CollatzResearch.WordTrace]
  refine ⟨36711447709236569067444895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195794387782595035026372773 36711447709236569067444895)
  ·
    refine ⟨55067171563854853601167343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36711447709236569067444895 55067171563854853601167343)
    ·
      refine ⟨82600757345782280401751015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55067171563854853601167343 82600757345782280401751015)
      ·
        refine ⟨123901136018673420602626523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82600757345782280401751015 123901136018673420602626523)
        ·
          refine ⟨185851704028010130903939785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123901136018673420602626523 185851704028010130903939785)
          ·
            refine ⟨139388778021007598177954839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185851704028010130903939785 139388778021007598177954839)
            ·
              refine ⟨209083167031511397266932259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139388778021007598177954839 209083167031511397266932259)
              ·
                refine ⟨313624750547267095900398389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209083167031511397266932259 313624750547267095900398389)
                ·
                  refine ⟨29402320363806290240662349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313624750547267095900398389 29402320363806290240662349)
                  ·
                    refine ⟨11025870136427358840248381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29402320363806290240662349 11025870136427358840248381)
                    ·
                      refine ⟨4134701301160259565093143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11025870136427358840248381 4134701301160259565093143)
                      ·
                        rfl

theorem cell23_8052302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_8052302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052302 prefixEnd_8052302 := by exact prefixLift 8052302
  have htrace : WordTrace (prefixWord ++ tailWord_8052302) baseStart_8052302 baseEnd_8052302 := by
    simpa [prefixWord, tailWord_8052302, baseEnd_8052302] using wordTrace_append hprefix tailTrace_8052302
  have hstable : (prefixWord ++ tailWord_8052302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052302).length < 2 ^ (prefixWord ++ tailWord_8052302).sum := by decide
  have hdescent : baseEnd_8052302 < baseStart_8052302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052305 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_8052305 : Nat := 118140960795 + 8052305 * 2 ^ 59
def prefixEnd_8052305 : Nat := 4983230072969 + 3 ^ 40 * 8052305 * 2
def baseEnd_8052305 : Nat := 1378234280534074351118543

theorem tailTrace_8052305 : CollatzResearch.WordTrace tailWord_8052305 prefixEnd_8052305 1378234280534074351118543 := by
  unfold tailWord_8052305
  simp only [CollatzResearch.WordTrace]
  refine ⟨293691691092881684051918369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195794460728587789367945579 293691691092881684051918369)
  ·
    refine ⟨220268768319661263038938777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293691691092881684051918369 220268768319661263038938777)
    ·
      refine ⟨165201576239745947279204083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220268768319661263038938777 165201576239745947279204083)
      ·
        refine ⟨247802364359618920918806125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165201576239745947279204083 247802364359618920918806125)
        ·
          refine ⟨92925886634857095344552297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247802364359618920918806125 92925886634857095344552297)
          ·
            refine ⟨69694414976142821508414223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92925886634857095344552297 69694414976142821508414223)
            ·
              refine ⟨104541622464214232262621335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69694414976142821508414223 104541622464214232262621335)
              ·
                refine ⟨156812433696321348393932003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104541622464214232262621335 156812433696321348393932003)
                ·
                  refine ⟨235218650544482022590898005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156812433696321348393932003 235218650544482022590898005)
                  ·
                    refine ⟨1378234280534074351118543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235218650544482022590898005 1378234280534074351118543)
                    ·
                      rfl

theorem cell23_8052305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_8052305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052305 prefixEnd_8052305 := by exact prefixLift 8052305
  have htrace : WordTrace (prefixWord ++ tailWord_8052305) baseStart_8052305 baseEnd_8052305 := by
    simpa [prefixWord, tailWord_8052305, baseEnd_8052305] using wordTrace_append hprefix tailTrace_8052305
  have hstable : (prefixWord ++ tailWord_8052305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052305).length < 2 ^ (prefixWord ++ tailWord_8052305).sum := by decide
  have hdescent : baseEnd_8052305 < baseStart_8052305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052329 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 3, 3, 2]
def baseStart_8052329 : Nat := 118140960795 + 8052329 * 2 ^ 59
def prefixEnd_8052329 : Nat := 4983230072969 + 3 ^ 40 * 8052329 * 2
def baseEnd_8052329 : Nat := 4134715165137930959455519

theorem tailTrace_8052329 : CollatzResearch.WordTrace tailWord_8052329 prefixEnd_8052329 4134715165137930959455519 := by
  unfold tailWord_8052329
  simp only [CollatzResearch.WordTrace]
  refine ⟨293692566444794736150792041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195795044296529824100528027 293692566444794736150792041)
  ·
    refine ⟨220269424833596052113094031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293692566444794736150792041 220269424833596052113094031)
    ·
      refine ⟨330404137250394078169641047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220269424833596052113094031 330404137250394078169641047)
      ·
        refine ⟨495606205875591117254461571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330404137250394078169641047 495606205875591117254461571)
        ·
          refine ⟨743409308813386675881692357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495606205875591117254461571 743409308813386675881692357)
          ·
            refine ⟨139389245402510001727817317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 743409308813386675881692357 139389245402510001727817317)
            ·
              refine ⟨26135483512970625323965747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139389245402510001727817317 26135483512970625323965747)
              ·
                refine ⟨39203225269455937985948621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26135483512970625323965747 39203225269455937985948621)
                ·
                  refine ⟨14701209476045976744730733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39203225269455937985948621 14701209476045976744730733)
                  ·
                    refine ⟨5512953553517241279274025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14701209476045976744730733 5512953553517241279274025)
                    ·
                      refine ⟨4134715165137930959455519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512953553517241279274025 4134715165137930959455519)
                      ·
                        rfl

theorem cell23_8052329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3, 2].length) (baseStart_8052329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052329 prefixEnd_8052329 := by exact prefixLift 8052329
  have htrace : WordTrace (prefixWord ++ tailWord_8052329) baseStart_8052329 baseEnd_8052329 := by
    simpa [prefixWord, tailWord_8052329, baseEnd_8052329] using wordTrace_append hprefix tailTrace_8052329
  have hstable : (prefixWord ++ tailWord_8052329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052329).length < 2 ^ (prefixWord ++ tailWord_8052329).sum := by decide
  have hdescent : baseEnd_8052329 < baseStart_8052329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052335 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 8]
def baseStart_8052335 : Nat := 118140960795 + 8052335 * 2 ^ 59
def prefixEnd_8052335 : Nat := 4983230072969 + 3 ^ 40 * 8052335 * 2
def baseEnd_8052335 : Nat := 1378239415340619311993497

theorem tailTrace_8052335 : CollatzResearch.WordTrace tailWord_8052335 prefixEnd_8052335 1378239415340619311993497 := by
  unfold tailWord_8052335
  simp only [CollatzResearch.WordTrace]
  refine ⟨293692785282772999175510459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195795190188515332783673639 293692785282772999175510459)
  ·
    refine ⟨440539177924159498763265689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293692785282772999175510459 440539177924159498763265689)
    ·
      refine ⟨330404383443119624072449267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440539177924159498763265689 330404383443119624072449267)
      ·
        refine ⟨495606575164679436108673901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330404383443119624072449267 495606575164679436108673901)
        ·
          refine ⟨185852465686754788540752713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495606575164679436108673901 185852465686754788540752713)
          ·
            refine ⟨139389349265066091405564535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185852465686754788540752713 139389349265066091405564535)
            ·
              refine ⟨209084023897599137108346803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139389349265066091405564535 209084023897599137108346803)
              ·
                refine ⟨313626035846398705662520205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209084023897599137108346803 313626035846398705662520205)
                ·
                  refine ⟨117609763442399514623445077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313626035846398705662520205 117609763442399514623445077)
                  ·
                    refine ⟨1378239415340619311993497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117609763442399514623445077 1378239415340619311993497)
                    ·
                      rfl

theorem cell23_8052335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_8052335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052335 prefixEnd_8052335 := by exact prefixLift 8052335
  have htrace : WordTrace (prefixWord ++ tailWord_8052335) baseStart_8052335 baseEnd_8052335 := by
    simpa [prefixWord, tailWord_8052335, baseEnd_8052335] using wordTrace_append hprefix tailTrace_8052335
  have hstable : (prefixWord ++ tailWord_8052335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052335).length < 2 ^ (prefixWord ++ tailWord_8052335).sum := by decide
  have hdescent : baseEnd_8052335 < baseStart_8052335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052353 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_8052353 : Nat := 118140960795 + 8052353 * 2 ^ 59
def prefixEnd_8052353 : Nat := 4983230072969 + 3 ^ 40 * 8052353 * 2
def baseEnd_8052353 : Nat := 4134727488673638865555409

theorem tailTrace_8052353 : CollatzResearch.WordTrace tailWord_8052353 prefixEnd_8052353 4134727488673638865555409 := by
  unfold tailWord_8052353
  simp only [CollatzResearch.WordTrace]
  refine ⟨293693441796707788249665713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195795627864471858833110475 293693441796707788249665713)
  ·
    refine ⟨220270081347530841187249285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293693441796707788249665713 220270081347530841187249285)
    ·
      refine ⟨41300640252662032722609241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220270081347530841187249285 41300640252662032722609241)
      ·
        refine ⟨30975480189496524541956931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41300640252662032722609241 30975480189496524541956931)
        ·
          refine ⟨46463220284244786812935397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30975480189496524541956931 46463220284244786812935397)
          ·
            refine ⟨8711853803295897527425387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46463220284244786812935397 8711853803295897527425387)
            ·
              refine ⟨13067780704943846291138081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711853803295897527425387 13067780704943846291138081)
              ·
                refine ⟨9800835528707884718353561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13067780704943846291138081 9800835528707884718353561)
                ·
                  refine ⟨7350626646530913538765171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9800835528707884718353561 7350626646530913538765171)
                  ·
                    refine ⟨11025939969796370308147757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7350626646530913538765171 11025939969796370308147757)
                    ·
                      refine ⟨4134727488673638865555409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11025939969796370308147757 4134727488673638865555409)
                      ·
                        rfl

theorem cell23_8052353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_8052353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052353 prefixEnd_8052353 := by exact prefixLift 8052353
  have htrace : WordTrace (prefixWord ++ tailWord_8052353) baseStart_8052353 baseEnd_8052353 := by
    simpa [prefixWord, tailWord_8052353, baseEnd_8052353] using wordTrace_append hprefix tailTrace_8052353
  have hstable : (prefixWord ++ tailWord_8052353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052353).length < 2 ^ (prefixWord ++ tailWord_8052353).sum := by decide
  have hdescent : baseEnd_8052353 < baseStart_8052353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052370 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_8052370 : Nat := 118140960795 + 8052370 * 2 ^ 59
def prefixEnd_8052370 : Nat := 4983230072969 + 3 ^ 40 * 8052370 * 2
def baseEnd_8052370 : Nat := 4134736217844765299042831

theorem tailTrace_8052370 : CollatzResearch.WordTrace tailWord_8052370 prefixEnd_8052370 4134736217844765299042831 := by
  unfold tailWord_8052370
  simp only [CollatzResearch.WordTrace]
  refine ⟨73423515459411550038258641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195796041225097466768689709 73423515459411550038258641)
  ·
    refine ⟨55067636594558662528693981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73423515459411550038258641 55067636594558662528693981)
    ·
      refine ⟨20650363722959498448260243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55067636594558662528693981 20650363722959498448260243)
      ·
        refine ⟨30975545584439247672390365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20650363722959498448260243 30975545584439247672390365)
        ·
          refine ⟨11615829594164717877146387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30975545584439247672390365 11615829594164717877146387)
          ·
            refine ⟨17423744391247076815719581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11615829594164717877146387 17423744391247076815719581)
            ·
              refine ⟨6533904146717653805894843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17423744391247076815719581 6533904146717653805894843)
              ·
                refine ⟨9800856220076480708842265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533904146717653805894843 9800856220076480708842265)
                ·
                  refine ⟨7350642165057360531631699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9800856220076480708842265 7350642165057360531631699)
                  ·
                    refine ⟨11025963247586040797447549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7350642165057360531631699 11025963247586040797447549)
                    ·
                      refine ⟨4134736217844765299042831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11025963247586040797447549 4134736217844765299042831)
                      ·
                        rfl

theorem cell23_8052370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_8052370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052370 prefixEnd_8052370 := by exact prefixLift 8052370
  have htrace : WordTrace (prefixWord ++ tailWord_8052370) baseStart_8052370 baseEnd_8052370 := by
    simpa [prefixWord, tailWord_8052370, baseEnd_8052370] using wordTrace_append hprefix tailTrace_8052370
  have hstable : (prefixWord ++ tailWord_8052370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052370).length < 2 ^ (prefixWord ++ tailWord_8052370).sum := by decide
  have hdescent : baseEnd_8052370 < baseStart_8052370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052376 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_8052376 : Nat := 118140960795 + 8052376 * 2 ^ 59
def prefixEnd_8052376 : Nat := 4983230072969 + 3 ^ 40 * 8052376 * 2
def baseEnd_8052376 : Nat := 4134739298728692275567803

theorem tailTrace_8052376 : CollatzResearch.WordTrace tailWord_8052376 prefixEnd_8052376 4134739298728692275567803 := by
  unfold tailWord_8052376
  simp only [CollatzResearch.WordTrace]
  refine ⟨146847140337812231588876491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195796187117082975451835321 146847140337812231588876491)
  ·
    refine ⟨220270710506718347383314737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146847140337812231588876491 220270710506718347383314737)
    ·
      refine ⟨165203032880038760537486053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220270710506718347383314737 165203032880038760537486053)
      ·
        refine ⟨30975568665007267600778635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165203032880038760537486053 30975568665007267600778635)
        ·
          refine ⟨46463352997510901401167953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30975568665007267600778635 46463352997510901401167953)
          ·
            refine ⟨34847514748133176050875965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46463352997510901401167953 34847514748133176050875965)
            ·
              refine ⟨13067818030549941019078487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34847514748133176050875965 13067818030549941019078487)
              ·
                refine ⟨19601727045824911528617731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067818030549941019078487 19601727045824911528617731)
                ·
                  refine ⟨29402590568737367292926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19601727045824911528617731 29402590568737367292926597)
                  ·
                    refine ⟨5512985731638256367423737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29402590568737367292926597 5512985731638256367423737)
                    ·
                      refine ⟨4134739298728692275567803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5512985731638256367423737 4134739298728692275567803)
                      ·
                        rfl

theorem cell23_8052376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_8052376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052376 prefixEnd_8052376 := by exact prefixLift 8052376
  have htrace : WordTrace (prefixWord ++ tailWord_8052376) baseStart_8052376 baseEnd_8052376 := by
    simpa [prefixWord, tailWord_8052376, baseEnd_8052376] using wordTrace_append hprefix tailTrace_8052376
  have hstable : (prefixWord ++ tailWord_8052376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052376).length < 2 ^ (prefixWord ++ tailWord_8052376).sum := by decide
  have hdescent : baseEnd_8052376 < baseStart_8052376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052416 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 5]
def baseStart_8052416 : Nat := 118140960795 + 8052416 * 2 ^ 59
def prefixEnd_8052416 : Nat := 4983230072969 + 3 ^ 40 * 8052416 * 2
def baseEnd_8052416 : Nat := 459417759772763568785291

theorem tailTrace_8052416 : CollatzResearch.WordTrace tailWord_8052416 prefixEnd_8052416 459417759772763568785291 := by
  unfold tailWord_8052416
  simp only [CollatzResearch.WordTrace]
  refine ⟨146847869797739775004604551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195797159730319700006139401 146847869797739775004604551)
  ·
    refine ⟨220271804696609662506906827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146847869797739775004604551 220271804696609662506906827)
    ·
      refine ⟨330407707044914493760360241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220271804696609662506906827 330407707044914493760360241)
      ·
        refine ⟨247805780283685870320270181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330407707044914493760360241 247805780283685870320270181)
        ·
          refine ⟨46463583803191100685050659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247805780283685870320270181 46463583803191100685050659)
          ·
            refine ⟨69695375704786651027575989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46463583803191100685050659 69695375704786651027575989)
            ·
              refine ⟨6533941472323748533835249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69695375704786651027575989 6533941472323748533835249)
              ·
                refine ⟨4900456104242811400376437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533941472323748533835249 4900456104242811400376437)
                ·
                  refine ⟨459417759772763568785291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900456104242811400376437 459417759772763568785291)
                  ·
                    rfl

theorem cell23_8052416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 5].length) (baseStart_8052416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052416 prefixEnd_8052416 := by exact prefixLift 8052416
  have htrace : WordTrace (prefixWord ++ tailWord_8052416) baseStart_8052416 baseEnd_8052416 := by
    simpa [prefixWord, tailWord_8052416, baseEnd_8052416] using wordTrace_append hprefix tailTrace_8052416
  have hstable : (prefixWord ++ tailWord_8052416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052416).length < 2 ^ (prefixWord ++ tailWord_8052416).sum := by decide
  have hdescent : baseEnd_8052416 < baseStart_8052416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052432 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_8052432 : Nat := 118140960795 + 8052432 * 2 ^ 59
def prefixEnd_8052432 : Nat := 4983230072969 + 3 ^ 40 * 8052432 * 2
def baseEnd_8052432 : Nat := 4134768053645344056467545

theorem tailTrace_8052432 : CollatzResearch.WordTrace tailWord_8052432 prefixEnd_8052432 4134768053645344056467545 := by
  unfold tailWord_8052432
  simp only [CollatzResearch.WordTrace]
  refine ⟨146848161581710792370895775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195797548775614389827861033 146848161581710792370895775)
  ·
    refine ⟨220272242372566188556343663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146848161581710792370895775 220272242372566188556343663)
    ·
      refine ⟨330408363558849282834515495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220272242372566188556343663 330408363558849282834515495)
      ·
        refine ⟨495612545338273924251773243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330408363558849282834515495 495612545338273924251773243)
        ·
          refine ⟨743418818007410886377659865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495612545338273924251773243 743418818007410886377659865)
          ·
            refine ⟨557564113505558164783244899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743418818007410886377659865 557564113505558164783244899)
            ·
              refine ⟨836346170258337247174867349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557564113505558164783244899 836346170258337247174867349)
              ·
                refine ⟨39203726730859558461321907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 836346170258337247174867349 39203726730859558461321907)
                ·
                  refine ⟨58805590096289337691982861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39203726730859558461321907 58805590096289337691982861)
                  ·
                    refine ⟨22052096286108501634493573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58805590096289337691982861 22052096286108501634493573)
                    ·
                      refine ⟨4134768053645344056467545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22052096286108501634493573 4134768053645344056467545)
                      ·
                        rfl

theorem cell23_8052432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_8052432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052432 prefixEnd_8052432 := by exact prefixLift 8052432
  have htrace : WordTrace (prefixWord ++ tailWord_8052432) baseStart_8052432 baseEnd_8052432 := by
    simpa [prefixWord, tailWord_8052432, baseEnd_8052432] using wordTrace_append hprefix tailTrace_8052432
  have hstable : (prefixWord ++ tailWord_8052432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052432).length < 2 ^ (prefixWord ++ tailWord_8052432).sum := by decide
  have hdescent : baseEnd_8052432 < baseStart_8052432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052466 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_8052466 : Nat := 118140960795 + 8052466 * 2 ^ 59
def prefixEnd_8052466 : Nat := 4983230072969 + 3 ^ 40 * 8052466 * 2
def baseEnd_8052466 : Nat := 4134785511987596923442389

theorem tailTrace_8052466 : CollatzResearch.WordTrace tailWord_8052466 prefixEnd_8052466 4134785511987596923442389 := by
  unfold tailWord_8052466
  simp only [CollatzResearch.WordTrace]
  refine ⟨73424390811324602137132313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195798375496865605699019501 73424390811324602137132313)
  ·
    refine ⟨55068293108493451602849235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73424390811324602137132313 55068293108493451602849235)
    ·
      refine ⟨82602439662740177404273853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55068293108493451602849235 82602439662740177404273853)
      ·
        refine ⟨30975914873527566526602695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82602439662740177404273853 30975914873527566526602695)
        ·
          refine ⟨46463872310291349789904043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30975914873527566526602695 46463872310291349789904043)
          ·
            refine ⟨69695808465437024684856065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46463872310291349789904043 69695808465437024684856065)
            ·
              refine ⟨52271856349077768513642049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69695808465437024684856065 52271856349077768513642049)
              ·
                refine ⟨39203892261808326385231537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52271856349077768513642049 39203892261808326385231537)
                ·
                  refine ⟨29402919196356244788923653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39203892261808326385231537 29402919196356244788923653)
                  ·
                    refine ⟨5513047349316795897923185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29402919196356244788923653 5513047349316795897923185)
                    ·
                      refine ⟨4134785511987596923442389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513047349316795897923185 4134785511987596923442389)
                      ·
                        rfl

theorem cell23_8052466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_8052466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052466 prefixEnd_8052466 := by exact prefixLift 8052466
  have htrace : WordTrace (prefixWord ++ tailWord_8052466) baseStart_8052466 baseEnd_8052466 := by
    simpa [prefixWord, tailWord_8052466, baseEnd_8052466] using wordTrace_append hprefix tailTrace_8052466
  have hstable : (prefixWord ++ tailWord_8052466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052466).length < 2 ^ (prefixWord ++ tailWord_8052466).sum := by decide
  have hdescent : baseEnd_8052466 < baseStart_8052466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052500 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_8052500 : Nat := 118140960795 + 8052500 * 2 ^ 59
def prefixEnd_8052500 : Nat := 4983230072969 + 3 ^ 40 * 8052500 * 2
def baseEnd_8052500 : Nat := 4134802970329849790417233

theorem tailTrace_8052500 : CollatzResearch.WordTrace tailWord_8052500 prefixEnd_8052500 4134802970329849790417233 := by
  unfold tailWord_8052500
  simp only [CollatzResearch.WordTrace]
  refine ⟨146849401663587616177633477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195799202218116821570177969 146849401663587616177633477)
  ·
    refine ⟨27534262811922678033306277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146849401663587616177633477 27534262811922678033306277)
    ·
      refine ⟨5162674277235502131244927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27534262811922678033306277 5162674277235502131244927)
      ·
        refine ⟨7744011415853253196867391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162674277235502131244927 7744011415853253196867391)
        ·
          refine ⟨11616017123779879795301087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744011415853253196867391 11616017123779879795301087)
          ·
            refine ⟨17424025685669819692951631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616017123779879795301087 17424025685669819692951631)
            ·
              refine ⟨26136038528504729539427447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17424025685669819692951631 26136038528504729539427447)
              ·
                refine ⟨39204057792757094309141171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26136038528504729539427447 39204057792757094309141171)
                ·
                  refine ⟨58806086689135641463711757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39204057792757094309141171 58806086689135641463711757)
                  ·
                    refine ⟨22052282508425865548891909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58806086689135641463711757 22052282508425865548891909)
                    ·
                      refine ⟨4134802970329849790417233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22052282508425865548891909 4134802970329849790417233)
                      ·
                        rfl

theorem cell23_8052500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_8052500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052500 prefixEnd_8052500 := by exact prefixLift 8052500
  have htrace : WordTrace (prefixWord ++ tailWord_8052500) baseStart_8052500 baseEnd_8052500 := by
    simpa [prefixWord, tailWord_8052500, baseEnd_8052500] using wordTrace_append hprefix tailTrace_8052500
  have hstable : (prefixWord ++ tailWord_8052500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052500).length < 2 ^ (prefixWord ++ tailWord_8052500).sum := by decide
  have hdescent : baseEnd_8052500 < baseStart_8052500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052503 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_8052503 : Nat := 118140960795 + 8052503 * 2 ^ 59
def prefixEnd_8052503 : Nat := 4983230072969 + 3 ^ 40 * 8052503 * 2
def baseEnd_8052503 : Nat := 4134804510771813278679719

theorem tailTrace_8052503 : CollatzResearch.WordTrace tailWord_8052503 prefixEnd_8052503 4134804510771813278679719 := by
  unfold tailWord_8052503
  simp only [CollatzResearch.WordTrace]
  refine ⟨293698912746164363867626163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195799275164109575911750775 293698912746164363867626163)
  ·
    refine ⟨440548369119246545801439245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293698912746164363867626163 440548369119246545801439245)
    ·
      refine ⟨165205638419717454675539717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440548369119246545801439245 165205638419717454675539717)
      ·
        refine ⟨30976057203697022751663697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165205638419717454675539717 30976057203697022751663697)
        ·
          refine ⟨23232042902772767063747773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30976057203697022751663697 23232042902772767063747773)
          ·
            refine ⟨8712016088539787648905415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23232042902772767063747773 8712016088539787648905415)
            ·
              refine ⟨13068024132809681473358123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712016088539787648905415 13068024132809681473358123)
              ·
                refine ⟨19602036199214522210037185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068024132809681473358123 19602036199214522210037185)
                ·
                  refine ⟨14701527149410891657527889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19602036199214522210037185 14701527149410891657527889)
                  ·
                    refine ⟨11026145362058168743145917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14701527149410891657527889 11026145362058168743145917)
                    ·
                      refine ⟨4134804510771813278679719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026145362058168743145917 4134804510771813278679719)
                      ·
                        rfl

theorem cell23_8052503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_8052503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052503 prefixEnd_8052503 := by exact prefixLift 8052503
  have htrace : WordTrace (prefixWord ++ tailWord_8052503) baseStart_8052503 baseEnd_8052503 := by
    simpa [prefixWord, tailWord_8052503, baseEnd_8052503] using wordTrace_append hprefix tailTrace_8052503
  have hstable : (prefixWord ++ tailWord_8052503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052503).length < 2 ^ (prefixWord ++ tailWord_8052503).sum := by decide
  have hdescent : baseEnd_8052503 < baseStart_8052503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052567 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 1, 1, 3]
def baseStart_8052567 : Nat := 118140960795 + 8052567 * 2 ^ 59
def prefixEnd_8052567 : Nat := 4983230072969 + 3 ^ 40 * 8052567 * 2
def baseEnd_8052567 : Nat := 4134837373533701028279425

theorem tailTrace_8052567 : CollatzResearch.WordTrace tailWord_8052567 prefixEnd_8052567 4134837373533701028279425 := by
  unfold tailWord_8052567
  simp only [CollatzResearch.WordTrace]
  refine ⟨293701247017932502797955955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195800831345288335198637303 293701247017932502797955955)
  ·
    refine ⟨440551870526898754196933933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293701247017932502797955955 440551870526898754196933933)
    ·
      refine ⟨165206951447587032823850225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440551870526898754196933933 165206951447587032823850225)
      ·
        refine ⟨123905213585690274617887669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165206951447587032823850225 123905213585690274617887669)
        ·
          refine ⟨11616113773658463245426969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123905213585690274617887669 11616113773658463245426969)
          ·
            refine ⟨8712085330243847434070227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616113773658463245426969 8712085330243847434070227)
            ·
              refine ⟨13068127995365771151105341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712085330243847434070227 13068127995365771151105341)
              ·
                refine ⟨4900547998262164181664503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13068127995365771151105341 4900547998262164181664503)
                ·
                  refine ⟨7350821997393246272496755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900547998262164181664503 7350821997393246272496755)
                  ·
                    refine ⟨11026232996089869408745133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7350821997393246272496755 11026232996089869408745133)
                    ·
                      refine ⟨4134837373533701028279425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026232996089869408745133 4134837373533701028279425)
                      ·
                        rfl

theorem cell23_8052567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_8052567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052567 prefixEnd_8052567 := by exact prefixLift 8052567
  have htrace : WordTrace (prefixWord ++ tailWord_8052567) baseStart_8052567 baseEnd_8052567 := by
    simpa [prefixWord, tailWord_8052567, baseEnd_8052567] using wordTrace_append hprefix tailTrace_8052567
  have hstable : (prefixWord ++ tailWord_8052567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052567).length < 2 ^ (prefixWord ++ tailWord_8052567).sum := by decide
  have hdescent : baseEnd_8052567 < baseStart_8052567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052569 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_8052569 : Nat := 118140960795 + 8052569 * 2 ^ 59
def prefixEnd_8052569 : Nat := 4983230072969 + 3 ^ 40 * 8052569 * 2
def baseEnd_8052569 : Nat := 4134838400495010020454415

theorem tailTrace_8052569 : CollatzResearch.WordTrace tailWord_8052569 prefixEnd_8052569 4134838400495010020454415 := by
  unfold tailWord_8052569
  simp only [CollatzResearch.WordTrace]
  refine ⟨293701319963925257139528761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195800879975950171426352507 293701319963925257139528761)
  ·
    refine ⟨220275989972943942854646571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293701319963925257139528761 220275989972943942854646571)
    ·
      refine ⟨330413984959415914281969857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220275989972943942854646571 330413984959415914281969857)
      ·
        refine ⟨247810488719561935711477393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330413984959415914281969857 247810488719561935711477393)
        ·
          refine ⟨185857866539671451783608045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247810488719561935711477393 185857866539671451783608045)
          ·
            refine ⟨69696699952376794418853017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185857866539671451783608045 69696699952376794418853017)
            ·
              refine ⟨52272524964282595814139763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69696699952376794418853017 52272524964282595814139763)
              ·
                refine ⟨78408787446423893721209645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52272524964282595814139763 78408787446423893721209645)
                ·
                  refine ⟨29403295292408960145453617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78408787446423893721209645 29403295292408960145453617)
                  ·
                    refine ⟨22052471469306720109090213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29403295292408960145453617 22052471469306720109090213)
                    ·
                      refine ⟨4134838400495010020454415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22052471469306720109090213 4134838400495010020454415)
                      ·
                        rfl

theorem cell23_8052569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_8052569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052569 prefixEnd_8052569 := by exact prefixLift 8052569
  have htrace : WordTrace (prefixWord ++ tailWord_8052569) baseStart_8052569 baseEnd_8052569 := by
    simpa [prefixWord, tailWord_8052569, baseEnd_8052569] using wordTrace_append hprefix tailTrace_8052569
  have hstable : (prefixWord ++ tailWord_8052569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052569).length < 2 ^ (prefixWord ++ tailWord_8052569).sum := by decide
  have hdescent : baseEnd_8052569 < baseStart_8052569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052576 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_8052576 : Nat := 118140960795 + 8052576 * 2 ^ 59
def prefixEnd_8052576 : Nat := 4983230072969 + 3 ^ 40 * 8052576 * 2
def baseEnd_8052576 : Nat := 4134841994859591493066883

theorem tailTrace_8052576 : CollatzResearch.WordTrace tailWord_8052576 prefixEnd_8052576 4134841994859591493066883 := by
  unfold tailWord_8052576
  simp only [CollatzResearch.WordTrace]
  refine ⟨146850787637449948667516791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195801050183266598223355721 146850787637449948667516791)
  ·
    refine ⟨220276181456174923001275187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146850787637449948667516791 220276181456174923001275187)
    ·
      refine ⟨330414272184262384501912781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220276181456174923001275187 330414272184262384501912781)
      ·
        refine ⟨123905352069098394188217293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330414272184262384501912781 123905352069098394188217293)
        ·
          refine ⟨46464507025911897820581485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123905352069098394188217293 46464507025911897820581485)
          ·
            refine ⟨17424190134716961682718057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46464507025911897820581485 17424190134716961682718057)
            ·
              refine ⟨13068142601037721262038543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17424190134716961682718057 13068142601037721262038543)
              ·
                refine ⟨19602213901556581893057815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068142601037721262038543 19602213901556581893057815)
                ·
                  refine ⟨29403320852334872839586723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19602213901556581893057815 29403320852334872839586723)
                  ·
                    refine ⟨44104981278502309259380085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29403320852334872839586723 44104981278502309259380085)
                    ·
                      refine ⟨4134841994859591493066883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44104981278502309259380085 4134841994859591493066883)
                      ·
                        rfl

theorem cell23_8052576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_8052576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052576 prefixEnd_8052576 := by exact prefixLift 8052576
  have htrace : WordTrace (prefixWord ++ tailWord_8052576) baseStart_8052576 baseEnd_8052576 := by
    simpa [prefixWord, tailWord_8052576, baseEnd_8052576] using wordTrace_append hprefix tailTrace_8052576
  have hstable : (prefixWord ++ tailWord_8052576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052576).length < 2 ^ (prefixWord ++ tailWord_8052576).sum := by decide
  have hdescent : baseEnd_8052576 < baseStart_8052576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052630 : List Nat := [5, 3, 1, 1, 3, 10]
def baseStart_8052630 : Nat := 118140960795 + 8052630 * 2 ^ 59
def prefixEnd_8052630 : Nat := 4983230072969 + 3 ^ 40 * 8052630 * 2
def baseEnd_8052630 : Nat := 17015924785246643134945

theorem tailTrace_8052630 : CollatzResearch.WordTrace tailWord_8052630 prefixEnd_8052630 17015924785246643134945 := by
  unfold tailWord_8052630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356471551044016534843709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195802363211136176371666229 18356471551044016534843709)
  ·
    refine ⟨6883676831641506200566391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18356471551044016534843709 6883676831641506200566391)
    ·
      refine ⟨10325515247462259300849587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883676831641506200566391 10325515247462259300849587)
      ·
        refine ⟨15488272871193388951274381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325515247462259300849587 15488272871193388951274381)
        ·
          refine ⟨5808102326697520856727893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15488272871193388951274381 5808102326697520856727893)
          ·
            refine ⟨17015924785246643134945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5808102326697520856727893 17015924785246643134945)
            ·
              rfl

theorem cell23_8052630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 10].length) (baseStart_8052630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052630 prefixEnd_8052630 := by exact prefixLift 8052630
  have htrace : WordTrace (prefixWord ++ tailWord_8052630) baseStart_8052630 baseEnd_8052630 := by
    simpa [prefixWord, tailWord_8052630, baseEnd_8052630] using wordTrace_append hprefix tailTrace_8052630
  have hstable : (prefixWord ++ tailWord_8052630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052630).length < 2 ^ (prefixWord ++ tailWord_8052630).sum := by decide
  have hdescent : baseEnd_8052630 < baseStart_8052630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052633 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 1, 3, 2]
def baseStart_8052633 : Nat := 118140960795 + 8052633 * 2 ^ 59
def prefixEnd_8052633 : Nat := 4983230072969 + 3 ^ 40 * 8052633 * 2
def baseEnd_8052633 : Nat := 4134871263256897770054121

theorem tailTrace_8052633 : CollatzResearch.WordTrace tailWord_8052633 prefixEnd_8052633 4134871263256897770054121 := by
  unfold tailWord_8052633
  simp only [CollatzResearch.WordTrace]
  refine ⟨293703654235693396069858553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195802436157128930713239035 293703654235693396069858553)
  ·
    refine ⟨220277740676770047052393915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293703654235693396069858553 220277740676770047052393915)
    ·
      refine ⟨330416611015155070578590873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220277740676770047052393915 330416611015155070578590873)
      ·
        refine ⟨247812458261366302933943155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330416611015155070578590873 247812458261366302933943155)
        ·
          refine ⟨371718687392049454400914733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247812458261366302933943155 371718687392049454400914733)
          ·
            refine ⟨139394507772018545400343025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371718687392049454400914733 139394507772018545400343025)
            ·
              refine ⟨104545880829013909050257269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139394507772018545400343025 104545880829013909050257269)
              ·
                refine ⟨9801176327720053973461619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104545880829013909050257269 9801176327720053973461619)
                ·
                  refine ⟨14701764491580080960192429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801176327720053973461619 14701764491580080960192429)
                  ·
                    refine ⟨5513161684342530360072161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14701764491580080960192429 5513161684342530360072161)
                    ·
                      refine ⟨4134871263256897770054121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513161684342530360072161 4134871263256897770054121)
                      ·
                        rfl

theorem cell23_8052633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_8052633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052633 prefixEnd_8052633 := by exact prefixLift 8052633
  have htrace : WordTrace (prefixWord ++ tailWord_8052633) baseStart_8052633 baseEnd_8052633 := by
    simpa [prefixWord, tailWord_8052633, baseEnd_8052633] using wordTrace_append hprefix tailTrace_8052633
  have hstable : (prefixWord ++ tailWord_8052633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052633).length < 2 ^ (prefixWord ++ tailWord_8052633).sum := by decide
  have hdescent : baseEnd_8052633 < baseStart_8052633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052641 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_8052641 : Nat := 118140960795 + 8052641 * 2 ^ 59
def prefixEnd_8052641 : Nat := 4983230072969 + 3 ^ 40 * 8052641 * 2
def baseEnd_8052641 : Nat := 4134875371102133738754085

theorem tailTrace_8052641 : CollatzResearch.WordTrace tailWord_8052641 prefixEnd_8052641 4134875371102133738754085 := by
  unfold tailWord_8052641
  simp only [CollatzResearch.WordTrace]
  refine ⟨293703946019664413436149777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195802630679776275624099851 293703946019664413436149777)
  ·
    refine ⟨220277959514748310077112333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293703946019664413436149777 220277959514748310077112333)
    ·
      refine ⟨82604234818030616278917125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220277959514748310077112333 82604234818030616278917125)
      ·
        refine ⟨15488294028380740552296961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82604234818030616278917125 15488294028380740552296961)
        ·
          refine ⟨11616220521285555414222721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15488294028380740552296961 11616220521285555414222721)
          ·
            refine ⟨8712165390964166560667041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616220521285555414222721 8712165390964166560667041)
            ·
              refine ⟨6534124043223124920500281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8712165390964166560667041 6534124043223124920500281)
              ·
                refine ⟨4900593032417343690375211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534124043223124920500281 4900593032417343690375211)
                ·
                  refine ⟨7350889548626015535562817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900593032417343690375211 7350889548626015535562817)
                  ·
                    refine ⟨5513167161469511651672113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7350889548626015535562817 5513167161469511651672113)
                    ·
                      refine ⟨4134875371102133738754085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513167161469511651672113 4134875371102133738754085)
                      ·
                        rfl

theorem cell23_8052641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_8052641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052641 prefixEnd_8052641 := by exact prefixLift 8052641
  have htrace : WordTrace (prefixWord ++ tailWord_8052641) baseStart_8052641 baseEnd_8052641 := by
    simpa [prefixWord, tailWord_8052641, baseEnd_8052641] using wordTrace_append hprefix tailTrace_8052641
  have hstable : (prefixWord ++ tailWord_8052641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052641).length < 2 ^ (prefixWord ++ tailWord_8052641).sum := by decide
  have hdescent : baseEnd_8052641 < baseStart_8052641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052649 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_8052649 : Nat := 118140960795 + 8052649 * 2 ^ 59
def prefixEnd_8052649 : Nat := 4983230072969 + 3 ^ 40 * 8052649 * 2
def baseEnd_8052649 : Nat := 4134879478947369707454047

theorem tailTrace_8052649 : CollatzResearch.WordTrace tailWord_8052649 prefixEnd_8052649 4134879478947369707454047 := by
  unfold tailWord_8052649
  simp only [CollatzResearch.WordTrace]
  refine ⟨293704237803635430802441001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195802825202423620534960667 293704237803635430802441001)
  ·
    refine ⟨220278178352726573101830751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293704237803635430802441001 220278178352726573101830751)
    ·
      refine ⟨330417267529089859652746127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220278178352726573101830751 330417267529089859652746127)
      ·
        refine ⟨495625901293634789479119191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330417267529089859652746127 495625901293634789479119191)
        ·
          refine ⟨743438851940452184218678787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495625901293634789479119191 743438851940452184218678787)
          ·
            refine ⟨1115158277910678276328018181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743438851940452184218678787 1115158277910678276328018181)
            ·
              refine ⟨209092177108252176811503409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1115158277910678276328018181 209092177108252176811503409)
              ·
                refine ⟨156819132831189132608627557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209092177108252176811503409 156819132831189132608627557)
                ·
                  refine ⟨29403587405847962364117667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156819132831189132608627557 29403587405847962364117667)
                  ·
                    refine ⟨44105381108771943546176501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29403587405847962364117667 44105381108771943546176501)
                    ·
                      refine ⟨4134879478947369707454047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44105381108771943546176501 4134879478947369707454047)
                      ·
                        rfl

theorem cell23_8052649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_8052649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052649 prefixEnd_8052649 := by exact prefixLift 8052649
  have htrace : WordTrace (prefixWord ++ tailWord_8052649) baseStart_8052649 baseEnd_8052649 := by
    simpa [prefixWord, tailWord_8052649, baseEnd_8052649] using wordTrace_append hprefix tailTrace_8052649
  have hstable : (prefixWord ++ tailWord_8052649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052649).length < 2 ^ (prefixWord ++ tailWord_8052649).sum := by decide
  have hdescent : baseEnd_8052649 < baseStart_8052649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052663 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 6, 2, 2]
def baseStart_8052663 : Nat := 118140960795 + 8052663 * 2 ^ 59
def prefixEnd_8052663 : Nat := 4983230072969 + 3 ^ 40 * 8052663 * 2
def baseEnd_8052663 : Nat := 4134886667676532652678983

theorem tailTrace_8052663 : CollatzResearch.WordTrace tailWord_8052663 prefixEnd_8052663 4134886667676532652678983 := by
  unfold tailWord_8052663
  simp only [CollatzResearch.WordTrace]
  refine ⟨293704748425584711193450643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195803165617056474128967095 293704748425584711193450643)
  ·
    refine ⟨440557122638377066790175965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293704748425584711193450643 440557122638377066790175965)
    ·
      refine ⟨165208920989391400046315987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440557122638377066790175965 165208920989391400046315987)
      ·
        refine ⟨247813381484087100069473981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165208920989391400046315987 247813381484087100069473981)
        ·
          refine ⟨92930018056532662526052743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247813381484087100069473981 92930018056532662526052743)
          ·
            refine ⟨139395027084798993789079115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92930018056532662526052743 139395027084798993789079115)
            ·
              refine ⟨209092540627198490683618673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139395027084798993789079115 209092540627198490683618673)
              ·
                refine ⟨156819405470398868012714005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209092540627198490683618673 156819405470398868012714005)
                ·
                  refine ⟨7350909631424946938095969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156819405470398868012714005 7350909631424946938095969)
                  ·
                    refine ⟨5513182223568710203571977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7350909631424946938095969 5513182223568710203571977)
                    ·
                      refine ⟨4134886667676532652678983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513182223568710203571977 4134886667676532652678983)
                      ·
                        rfl

theorem cell23_8052663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_8052663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052663 prefixEnd_8052663 := by exact prefixLift 8052663
  have htrace : WordTrace (prefixWord ++ tailWord_8052663) baseStart_8052663 baseEnd_8052663 := by
    simpa [prefixWord, tailWord_8052663, baseEnd_8052663] using wordTrace_append hprefix tailTrace_8052663
  have hstable : (prefixWord ++ tailWord_8052663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052663).length < 2 ^ (prefixWord ++ tailWord_8052663).sum := by decide
  have hdescent : baseEnd_8052663 < baseStart_8052663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052679 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_8052679 : Nat := 118140960795 + 8052679 * 2 ^ 59
def prefixEnd_8052679 : Nat := 4983230072969 + 3 ^ 40 * 8052679 * 2
def baseEnd_8052679 : Nat := 4134894883367004590078909

theorem tailTrace_8052679 : CollatzResearch.WordTrace tailWord_8052679 prefixEnd_8052679 4134894883367004590078909 := by
  unfold tailWord_8052679
  simp only [CollatzResearch.WordTrace]
  refine ⟨293705331993526745926033091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195803554662351163950688727 293705331993526745926033091)
  ·
    refine ⟨440557997990290118889049637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293705331993526745926033091 440557997990290118889049637)
    ·
      refine ⟨82604624623179397291696807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440557997990290118889049637 82604624623179397291696807)
      ·
        refine ⟨123906936934769095937545211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82604624623179397291696807 123906936934769095937545211)
        ·
          refine ⟨185860405402153643906317817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123906936934769095937545211 185860405402153643906317817)
          ·
            refine ⟨139395304051615232929738363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185860405402153643906317817 139395304051615232929738363)
            ·
              refine ⟨209092956077422849394607545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139395304051615232929738363 209092956077422849394607545)
              ·
                refine ⟨156819717058067137045955659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209092956077422849394607545 156819717058067137045955659)
                ·
                  refine ⟨235229575587100705568933489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156819717058067137045955659 235229575587100705568933489)
                  ·
                    refine ⟨176422181690325529176700117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235229575587100705568933489 176422181690325529176700117)
                    ·
                      refine ⟨4134894883367004590078909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176422181690325529176700117 4134894883367004590078909)
                      ·
                        rfl

theorem cell23_8052679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_8052679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052679 prefixEnd_8052679 := by exact prefixLift 8052679
  have htrace : WordTrace (prefixWord ++ tailWord_8052679) baseStart_8052679 baseEnd_8052679 := by
    simpa [prefixWord, tailWord_8052679, baseEnd_8052679] using wordTrace_append hprefix tailTrace_8052679
  have hstable : (prefixWord ++ tailWord_8052679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052679).length < 2 ^ (prefixWord ++ tailWord_8052679).sum := by decide
  have hdescent : baseEnd_8052679 < baseStart_8052679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052696 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_8052696 : Nat := 118140960795 + 8052696 * 2 ^ 59
def prefixEnd_8052696 : Nat := 4983230072969 + 3 ^ 40 * 8052696 * 2
def baseEnd_8052696 : Nat := 4134903612538131023566331

theorem tailTrace_8052696 : CollatzResearch.WordTrace tailWord_8052696 prefixEnd_8052696 4134903612538131023566331 := by
  unfold tailWord_8052696
  simp only [CollatzResearch.WordTrace]
  refine ⟨146852976017232578914700971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195803968022976771886267961 146852976017232578914700971)
  ·
    refine ⟨220279464025848868372051457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146852976017232578914700971 220279464025848868372051457)
    ·
      refine ⟨165209598019386651279038593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220279464025848868372051457 165209598019386651279038593)
      ·
        refine ⟨123907198514539988459278945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165209598019386651279038593 123907198514539988459278945)
        ·
          refine ⟨92930398885904991344459209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123907198514539988459278945 92930398885904991344459209)
          ·
            refine ⟨69697799164428743508344407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92930398885904991344459209 69697799164428743508344407)
            ·
              refine ⟨104546698746643115262516611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69697799164428743508344407 104546698746643115262516611)
              ·
                refine ⟨156820048119964672893774917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104546698746643115262516611 156820048119964672893774917)
                ·
                  refine ⟨29403759022493376167582797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156820048119964672893774917 29403759022493376167582797)
                  ·
                    refine ⟨11026409633435016062843549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29403759022493376167582797 11026409633435016062843549)
                    ·
                      refine ⟨4134903612538131023566331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026409633435016062843549 4134903612538131023566331)
                      ·
                        rfl

theorem cell23_8052696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_8052696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052696 prefixEnd_8052696 := by exact prefixLift 8052696
  have htrace : WordTrace (prefixWord ++ tailWord_8052696) baseStart_8052696 baseEnd_8052696 := by
    simpa [prefixWord, tailWord_8052696, baseEnd_8052696] using wordTrace_append hprefix tailTrace_8052696
  have hstable : (prefixWord ++ tailWord_8052696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052696).length < 2 ^ (prefixWord ++ tailWord_8052696).sum := by decide
  have hdescent : baseEnd_8052696 < baseStart_8052696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052703 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 5]
def baseStart_8052703 : Nat := 118140960795 + 8052703 * 2 ^ 59
def prefixEnd_8052703 : Nat := 4983230072969 + 3 ^ 40 * 8052703 * 2
def baseEnd_8052703 : Nat := 459434134100301388464311

theorem tailTrace_8052703 : CollatzResearch.WordTrace tailWord_8052703 prefixEnd_8052703 459434134100301388464311 := by
  unfold tailWord_8052703
  simp only [CollatzResearch.WordTrace]
  refine ⟨293706207345439798024906763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195804138230293198683271175 293706207345439798024906763)
  ·
    refine ⟨440559311018159697037360145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293706207345439798024906763 440559311018159697037360145)
    ·
      refine ⟨330419483263619772778020109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440559311018159697037360145 330419483263619772778020109)
      ·
        refine ⟨123907306223857414791757541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330419483263619772778020109 123907306223857414791757541)
        ·
          refine ⟨23232619916973265273454539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123907306223857414791757541 23232619916973265273454539)
          ·
            refine ⟨34848929875459897910181809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23232619916973265273454539 34848929875459897910181809)
            ·
              refine ⟨26136697406594923432636357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34848929875459897910181809 26136697406594923432636357)
              ·
                refine ⟨4900630763736548143619317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26136697406594923432636357 4900630763736548143619317)
                ·
                  refine ⟨459434134100301388464311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4900630763736548143619317 459434134100301388464311)
                  ·
                    rfl

theorem cell23_8052703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 5].length) (baseStart_8052703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052703 prefixEnd_8052703 := by exact prefixLift 8052703
  have htrace : WordTrace (prefixWord ++ tailWord_8052703) baseStart_8052703 baseEnd_8052703 := by
    simpa [prefixWord, tailWord_8052703, baseEnd_8052703] using wordTrace_append hprefix tailTrace_8052703
  have hstable : (prefixWord ++ tailWord_8052703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052703).length < 2 ^ (prefixWord ++ tailWord_8052703).sum := by decide
  have hdescent : baseEnd_8052703 < baseStart_8052703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052803 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 3]
def baseStart_8052803 : Nat := 118140960795 + 8052803 * 2 ^ 59
def prefixEnd_8052803 : Nat := 4983230072969 + 3 ^ 40 * 8052803 * 2
def baseEnd_8052803 : Nat := 4134958554968162104928339

theorem tailTrace_8052803 : CollatzResearch.WordTrace tailWord_8052803 prefixEnd_8052803 4134958554968162104928339 := by
  unfold tailWord_8052803
  simp only [CollatzResearch.WordTrace]
  refine ⟨293709854645077515103547063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195806569763385010069031375 293709854645077515103547063)
  ·
    refine ⟨440564781967616272655320595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293709854645077515103547063 440564781967616272655320595)
    ·
      refine ⟨660847172951424408982980893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440564781967616272655320595 660847172951424408982980893)
      ·
        refine ⟨247817689856784153368617835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 660847172951424408982980893 247817689856784153368617835)
        ·
          refine ⟨371726534785176230052926753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247817689856784153368617835 371726534785176230052926753)
          ·
            refine ⟨278794901088882172539695065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371726534785176230052926753 278794901088882172539695065)
            ·
              refine ⟨209096175816661629404771299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278794901088882172539695065 209096175816661629404771299)
              ·
                refine ⟨313644263724992444107156949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209096175816661629404771299 313644263724992444107156949)
                ·
                  refine ⟨7351037431054510408761491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 313644263724992444107156949 7351037431054510408761491)
                  ·
                    refine ⟨11026556146581765613142237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7351037431054510408761491 11026556146581765613142237)
                    ·
                      refine ⟨4134958554968162104928339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026556146581765613142237 4134958554968162104928339)
                      ·
                        rfl

theorem cell23_8052803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_8052803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052803 prefixEnd_8052803 := by exact prefixLift 8052803
  have htrace : WordTrace (prefixWord ++ tailWord_8052803) baseStart_8052803 baseEnd_8052803 := by
    simpa [prefixWord, tailWord_8052803, baseEnd_8052803] using wordTrace_append hprefix tailTrace_8052803
  have hstable : (prefixWord ++ tailWord_8052803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052803).length < 2 ^ (prefixWord ++ tailWord_8052803).sum := by decide
  have hdescent : baseEnd_8052803 < baseStart_8052803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052813 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_8052813 : Nat := 118140960795 + 8052813 * 2 ^ 59
def prefixEnd_8052813 : Nat := 4983230072969 + 3 ^ 40 * 8052813 * 2
def baseEnd_8052813 : Nat := 4134963689774707065803293

theorem tailTrace_8052813 : CollatzResearch.WordTrace tailWord_8052813 prefixEnd_8052813 4134963689774707065803293 := by
  unfold tailWord_8052813
  simp only [CollatzResearch.WordTrace]
  refine ⟨293710219375041286811411093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195806812916694191207607395 293710219375041286811411093)
  ·
    refine ⟨13767666533205060319284895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293710219375041286811411093 13767666533205060319284895)
    ·
      refine ⟨20651499799807590478927343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13767666533205060319284895 20651499799807590478927343)
      ·
        refine ⟨30977249699711385718391015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20651499799807590478927343 30977249699711385718391015)
        ·
          refine ⟨46465874549567078577586523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30977249699711385718391015 46465874549567078577586523)
          ·
            refine ⟨69698811824350617866379785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46465874549567078577586523 69698811824350617866379785)
            ·
              refine ⟨52274108868262963399784839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69698811824350617866379785 52274108868262963399784839)
              ·
                refine ⟨78411163302394445099677259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52274108868262963399784839 78411163302394445099677259)
                ·
                  refine ⟨117616744953591667649515889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78411163302394445099677259 117616744953591667649515889)
                  ·
                    refine ⟨88212558715193750737136917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117616744953591667649515889 88212558715193750737136917)
                    ·
                      refine ⟨4134963689774707065803293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88212558715193750737136917 4134963689774707065803293)
                      ·
                        rfl

theorem cell23_8052813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_8052813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052813 prefixEnd_8052813 := by exact prefixLift 8052813
  have htrace : WordTrace (prefixWord ++ tailWord_8052813) baseStart_8052813 baseEnd_8052813 := by
    simpa [prefixWord, tailWord_8052813, baseEnd_8052813] using wordTrace_append hprefix tailTrace_8052813
  have hstable : (prefixWord ++ tailWord_8052813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052813).length < 2 ^ (prefixWord ++ tailWord_8052813).sum := by decide
  have hdescent : baseEnd_8052813 < baseStart_8052813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052814 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_8052814 : Nat := 118140960795 + 8052814 * 2 ^ 59
def prefixEnd_8052814 : Nat := 4983230072969 + 3 ^ 40 * 8052814 * 2
def baseEnd_8052814 : Nat := 1378321401085120520630263

theorem tailTrace_8052814 : CollatzResearch.WordTrace tailWord_8052814 prefixEnd_8052814 1378321401085120520630263 := by
  unfold tailWord_8052814
  simp only [CollatzResearch.WordTrace]
  refine ⟨36713781981004707997774687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195806837232025109321464997 36713781981004707997774687)
  ·
    refine ⟨55070672971507061996662031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36713781981004707997774687 55070672971507061996662031)
    ·
      refine ⟨82606009457260592994993047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55070672971507061996662031 82606009457260592994993047)
      ·
        refine ⟨123909014185890889492489571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82606009457260592994993047 123909014185890889492489571)
        ·
          refine ⟨185863521278836334238734357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123909014185890889492489571 185863521278836334238734357)
          ·
            refine ⟨8712352559945453167440673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185863521278836334238734357 8712352559945453167440673)
            ·
              refine ⟨6534264419959089875580505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8712352559945453167440673 6534264419959089875580505)
              ·
                refine ⟨4900698314969317406685379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534264419959089875580505 4900698314969317406685379)
                ·
                  refine ⟨7351047472453976110028069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900698314969317406685379 7351047472453976110028069)
                  ·
                    refine ⟨1378321401085120520630263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351047472453976110028069 1378321401085120520630263)
                    ·
                      rfl

theorem cell23_8052814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_8052814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052814 prefixEnd_8052814 := by exact prefixLift 8052814
  have htrace : WordTrace (prefixWord ++ tailWord_8052814) baseStart_8052814 baseEnd_8052814 := by
    simpa [prefixWord, tailWord_8052814, baseEnd_8052814] using wordTrace_append hprefix tailTrace_8052814
  have hstable : (prefixWord ++ tailWord_8052814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052814).length < 2 ^ (prefixWord ++ tailWord_8052814).sum := by decide
  have hdescent : baseEnd_8052814 < baseStart_8052814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052820 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_8052820 : Nat := 118140960795 + 8052820 * 2 ^ 59
def prefixEnd_8052820 : Nat := 4983230072969 + 3 ^ 40 * 8052820 * 2
def baseEnd_8052820 : Nat := 4134967284139288538415761

theorem tailTrace_8052820 : CollatzResearch.WordTrace tailWord_8052820 prefixEnd_8052820 4134967284139288538415761 := by
  unfold tailWord_8052820
  simp only [CollatzResearch.WordTrace]
  refine ⟨146855237343007963503457957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195806983124010618004610609 146855237343007963503457957)
  ·
    refine ⟨27535357001813993156898367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146855237343007963503457957 27535357001813993156898367)
    ·
      refine ⟨41303035502720989735347551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27535357001813993156898367 41303035502720989735347551)
      ·
        refine ⟨61954553254081484603021327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41303035502720989735347551 61954553254081484603021327)
        ·
          refine ⟨92931829881122226904531991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61954553254081484603021327 92931829881122226904531991)
          ·
            refine ⟨139397744821683340356797987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92931829881122226904531991 139397744821683340356797987)
            ·
              refine ⟨209096617232525010535196981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139397744821683340356797987 209096617232525010535196981)
              ·
                refine ⟨19602807865549219737674717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209096617232525010535196981 19602807865549219737674717)
                ·
                  refine ⟨7351052949580957401628019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19602807865549219737674717 7351052949580957401628019)
                  ·
                    refine ⟨11026579424371436102442029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7351052949580957401628019 11026579424371436102442029)
                    ·
                      refine ⟨4134967284139288538415761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026579424371436102442029 4134967284139288538415761)
                      ·
                        rfl

theorem cell23_8052820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_8052820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052820 prefixEnd_8052820 := by exact prefixLift 8052820
  have htrace : WordTrace (prefixWord ++ tailWord_8052820) baseStart_8052820 baseEnd_8052820 := by
    simpa [prefixWord, tailWord_8052820, baseEnd_8052820] using wordTrace_append hprefix tailTrace_8052820
  have hstable : (prefixWord ++ tailWord_8052820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052820).length < 2 ^ (prefixWord ++ tailWord_8052820).sum := by decide
  have hdescent : baseEnd_8052820 < baseStart_8052820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052847 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 2, 3, 2]
def baseStart_8052847 : Nat := 118140960795 + 8052847 * 2 ^ 59
def prefixEnd_8052847 : Nat := 4983230072969 + 3 ^ 40 * 8052847 * 2
def baseEnd_8052847 : Nat := 4134981148116959932778137

theorem tailTrace_8052847 : CollatzResearch.WordTrace tailWord_8052847 prefixEnd_8052847 4134981148116959932778137 := by
  unfold tailWord_8052847
  simp only [CollatzResearch.WordTrace]
  refine ⟨293711459456918110618148795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195807639637945407078765863 293711459456918110618148795)
  ·
    refine ⟨440567189185377165927223193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293711459456918110618148795 440567189185377165927223193)
    ·
      refine ⟨330425391889032874445417395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440567189185377165927223193 330425391889032874445417395)
      ·
        refine ⟨495638087833549311668126093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330425391889032874445417395 495638087833549311668126093)
        ·
          refine ⟨185864282937580991875547285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495638087833549311668126093 185864282937580991875547285)
          ·
            refine ⟨8712388262699108994166279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185864282937580991875547285 8712388262699108994166279)
            ·
              refine ⟨13068582394048663491249419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712388262699108994166279 13068582394048663491249419)
              ·
                refine ⟨19602873591072995236874129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068582394048663491249419 19602873591072995236874129)
                ·
                  refine ⟨14702155193304746427655597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19602873591072995236874129 14702155193304746427655597)
                  ·
                    refine ⟨5513308197489279910370849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14702155193304746427655597 5513308197489279910370849)
                    ·
                      refine ⟨4134981148116959932778137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513308197489279910370849 4134981148116959932778137)
                      ·
                        rfl

theorem cell23_8052847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3, 2].length) (baseStart_8052847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052847 prefixEnd_8052847 := by exact prefixLift 8052847
  have htrace : WordTrace (prefixWord ++ tailWord_8052847) baseStart_8052847 baseEnd_8052847 := by
    simpa [prefixWord, tailWord_8052847, baseEnd_8052847] using wordTrace_append hprefix tailTrace_8052847
  have hstable : (prefixWord ++ tailWord_8052847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052847).length < 2 ^ (prefixWord ++ tailWord_8052847).sum := by decide
  have hdescent : baseEnd_8052847 < baseStart_8052847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052854 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_8052854 : Nat := 118140960795 + 8052854 * 2 ^ 59
def prefixEnd_8052854 : Nat := 4983230072969 + 3 ^ 40 * 8052854 * 2
def baseEnd_8052854 : Nat := 4134984742481541405390605

theorem tailTrace_8052854 : CollatzResearch.WordTrace tailWord_8052854 prefixEnd_8052854 4134984742481541405390605 := by
  unfold tailWord_8052854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356982172993296925853351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195807809845261833875769077 18356982172993296925853351)
  ·
    refine ⟨27535473259489945388780027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18356982172993296925853351 27535473259489945388780027)
    ·
      refine ⟨41303209889234918083170041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27535473259489945388780027 41303209889234918083170041)
      ·
        refine ⟨30977407416926188562377531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41303209889234918083170041 30977407416926188562377531)
        ·
          refine ⟨46466111125389282843566297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30977407416926188562377531 46466111125389282843566297)
          ·
            refine ⟨34849583344041962132674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46466111125389282843566297 34849583344041962132674723)
            ·
              refine ⟨52274375016062943199012085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34849583344041962132674723 52274375016062943199012085)
              ·
                refine ⟨4900722657755900924907383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52274375016062943199012085 4900722657755900924907383)
                ·
                  refine ⟨7351083986633851387361075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900722657755900924907383 7351083986633851387361075)
                  ·
                    refine ⟨11026625979950777081041613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7351083986633851387361075 11026625979950777081041613)
                    ·
                      refine ⟨4134984742481541405390605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026625979950777081041613 4134984742481541405390605)
                      ·
                        rfl

theorem cell23_8052854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_8052854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052854 prefixEnd_8052854 := by exact prefixLift 8052854
  have htrace : WordTrace (prefixWord ++ tailWord_8052854) baseStart_8052854 baseEnd_8052854 := by
    simpa [prefixWord, tailWord_8052854, baseEnd_8052854] using wordTrace_append hprefix tailTrace_8052854
  have hstable : (prefixWord ++ tailWord_8052854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052854).length < 2 ^ (prefixWord ++ tailWord_8052854).sum := by decide
  have hdescent : baseEnd_8052854 < baseStart_8052854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052856 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_8052856 : Nat := 118140960795 + 8052856 * 2 ^ 59
def prefixEnd_8052856 : Nat := 4983230072969 + 3 ^ 40 * 8052856 * 2
def baseEnd_8052856 : Nat := 4134985769442850397565595

theorem tailTrace_8052856 : CollatzResearch.WordTrace tailWord_8052856 prefixEnd_8052856 4134985769442850397565595 := by
  unfold tailWord_8052856
  simp only [CollatzResearch.WordTrace]
  refine ⟨146855893856942752577613211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195807858475923670103484281 146855893856942752577613211)
  ·
    refine ⟨220283840785414128866419817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146855893856942752577613211 220283840785414128866419817)
    ·
      refine ⟨165212880589060596649814863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220283840785414128866419817 165212880589060596649814863)
      ·
        refine ⟨247819320883590894974722295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165212880589060596649814863 247819320883590894974722295)
        ·
          refine ⟨371728981325386342462083443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247819320883590894974722295 371728981325386342462083443)
          ·
            refine ⟨557593471988079513693125165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371728981325386342462083443 557593471988079513693125165)
            ·
              refine ⟨209097551995529817634921937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557593471988079513693125165 209097551995529817634921937)
              ·
                refine ⟨156823163996647363226191453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209097551995529817634921937 156823163996647363226191453)
                ·
                  refine ⟨58808686498742761209821795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156823163996647363226191453 58808686498742761209821795)
                  ·
                    refine ⟨88213029748114141814732693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58808686498742761209821795 88213029748114141814732693)
                    ·
                      refine ⟨4134985769442850397565595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88213029748114141814732693 4134985769442850397565595)
                      ·
                        rfl

theorem cell23_8052856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_8052856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052856 prefixEnd_8052856 := by exact prefixLift 8052856
  have htrace : WordTrace (prefixWord ++ tailWord_8052856) baseStart_8052856 baseEnd_8052856 := by
    simpa [prefixWord, tailWord_8052856, baseEnd_8052856] using wordTrace_append hprefix tailTrace_8052856
  have hstable : (prefixWord ++ tailWord_8052856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052856).length < 2 ^ (prefixWord ++ tailWord_8052856).sum := by decide
  have hdescent : baseEnd_8052856 < baseStart_8052856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052857 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 1, 5]
def baseStart_8052857 : Nat := 118140960795 + 8052857 * 2 ^ 59
def prefixEnd_8052857 : Nat := 4983230072969 + 3 ^ 40 * 8052857 * 2
def baseEnd_8052857 : Nat := 1378328760974501631217697

theorem tailTrace_8052857 : CollatzResearch.WordTrace tailWord_8052857 prefixEnd_8052857 1378328760974501631217697 := by
  unfold tailWord_8052857
  simp only [CollatzResearch.WordTrace]
  refine ⟨293711824186881882326012825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195807882791254588217341883 293711824186881882326012825)
  ·
    refine ⟨220283868140161411744509619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293711824186881882326012825 220283868140161411744509619)
    ·
      refine ⟨330425802210242117616764429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220283868140161411744509619 330425802210242117616764429)
      ·
        refine ⟨123909675828840794106286661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330425802210242117616764429 123909675828840794106286661)
        ·
          refine ⟨23233064217907648894928749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123909675828840794106286661 23233064217907648894928749)
          ·
            refine ⟨8712399081715368335598281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23233064217907648894928749 8712399081715368335598281)
            ·
              refine ⟨6534299311286526251698711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8712399081715368335598281 6534299311286526251698711)
              ·
                refine ⟨9801448966929789377548067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534299311286526251698711 9801448966929789377548067)
                ·
                  refine ⟨14702173450394684066322101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801448966929789377548067 14702173450394684066322101)
                  ·
                    refine ⟨1378328760974501631217697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14702173450394684066322101 1378328760974501631217697)
                    ·
                      rfl

theorem cell23_8052857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_8052857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052857 prefixEnd_8052857 := by exact prefixLift 8052857
  have htrace : WordTrace (prefixWord ++ tailWord_8052857) baseStart_8052857 baseEnd_8052857 := by
    simpa [prefixWord, tailWord_8052857, baseEnd_8052857] using wordTrace_append hprefix tailTrace_8052857
  have hstable : (prefixWord ++ tailWord_8052857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052857).length < 2 ^ (prefixWord ++ tailWord_8052857).sum := by decide
  have hdescent : baseEnd_8052857 < baseStart_8052857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052860 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_8052860 : Nat := 118140960795 + 8052860 * 2 ^ 59
def prefixEnd_8052860 : Nat := 4983230072969 + 3 ^ 40 * 8052860 * 2
def baseEnd_8052860 : Nat := 4134987823365468381915577

theorem tailTrace_8052860 : CollatzResearch.WordTrace tailWord_8052860 prefixEnd_8052860 4134987823365468381915577 := by
  unfold tailWord_8052860
  simp only [CollatzResearch.WordTrace]
  refine ⟨146855966802935506919186017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195807955737247342558914689 146855966802935506919186017)
  ·
    refine ⟨110141975102201630189389513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146855966802935506919186017 110141975102201630189389513)
    ·
      refine ⟨82606481326651222642042135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110141975102201630189389513 82606481326651222642042135)
      ·
        refine ⟨123909721989976833963063203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82606481326651222642042135 123909721989976833963063203)
        ·
          refine ⟨185864582984965250944594805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123909721989976833963063203 185864582984965250944594805)
          ·
            refine ⟨17424804654840492276055763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185864582984965250944594805 17424804654840492276055763)
            ·
              refine ⟨26137206982260738414083645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17424804654840492276055763 26137206982260738414083645)
              ·
                refine ⟨9801452618347776905281367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26137206982260738414083645 9801452618347776905281367)
                ·
                  refine ⟨14702178927521665357922051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801452618347776905281367 14702178927521665357922051)
                  ·
                    refine ⟨22053268391282498036883077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14702178927521665357922051 22053268391282498036883077)
                    ·
                      refine ⟨4134987823365468381915577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22053268391282498036883077 4134987823365468381915577)
                      ·
                        rfl

theorem cell23_8052860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_8052860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052860 prefixEnd_8052860 := by exact prefixLift 8052860
  have htrace : WordTrace (prefixWord ++ tailWord_8052860) baseStart_8052860 baseEnd_8052860 := by
    simpa [prefixWord, tailWord_8052860, baseEnd_8052860] using wordTrace_append hprefix tailTrace_8052860
  have hstable : (prefixWord ++ tailWord_8052860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052860).length < 2 ^ (prefixWord ++ tailWord_8052860).sum := by decide
  have hdescent : baseEnd_8052860 < baseStart_8052860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052876 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_8052876 : Nat := 118140960795 + 8052876 * 2 ^ 59
def prefixEnd_8052876 : Nat := 4983230072969 + 3 ^ 40 * 8052876 * 2
def baseEnd_8052876 : Nat := 4134996039055940319315503

theorem tailTrace_8052876 : CollatzResearch.WordTrace tailWord_8052876 prefixEnd_8052876 4134996039055940319315503 := by
  unfold tailWord_8052876
  simp only [CollatzResearch.WordTrace]
  refine ⟨146856258586906524285477241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195808344782542032380636321 146856258586906524285477241)
  ·
    refine ⟨110142193940179893214107931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146856258586906524285477241 110142193940179893214107931)
    ·
      refine ⟨165213290910269839821161897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110142193940179893214107931 165213290910269839821161897)
      ·
        refine ⟨123909968182702379865871423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165213290910269839821161897 123909968182702379865871423)
        ·
          refine ⟨185864952274053569798807135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123909968182702379865871423 185864952274053569798807135)
          ·
            refine ⟨278797428411080354698210703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185864952274053569798807135 278797428411080354698210703)
            ·
              refine ⟨418196142616620532047316055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278797428411080354698210703 418196142616620532047316055)
              ·
                refine ⟨627294213924930798070974083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418196142616620532047316055 627294213924930798070974083)
                ·
                  refine ⟨940941320887396197106461125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627294213924930798070974083 940941320887396197106461125)
                  ·
                    refine ⟨176426497666386786957461461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 940941320887396197106461125 176426497666386786957461461)
                    ·
                      refine ⟨4134996039055940319315503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176426497666386786957461461 4134996039055940319315503)
                      ·
                        rfl

theorem cell23_8052876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_8052876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052876 prefixEnd_8052876 := by exact prefixLift 8052876
  have htrace : WordTrace (prefixWord ++ tailWord_8052876) baseStart_8052876 baseEnd_8052876 := by
    simpa [prefixWord, tailWord_8052876, baseEnd_8052876] using wordTrace_append hprefix tailTrace_8052876
  have hstable : (prefixWord ++ tailWord_8052876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052876).length < 2 ^ (prefixWord ++ tailWord_8052876).sum := by decide
  have hdescent : baseEnd_8052876 < baseStart_8052876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052887 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 1, 6]
def baseStart_8052887 : Nat := 118140960795 + 8052887 * 2 ^ 59
def prefixEnd_8052887 : Nat := 4983230072969 + 3 ^ 40 * 8052887 * 2
def baseEnd_8052887 : Nat := 1378333895781046592092651

theorem tailTrace_8052887 : CollatzResearch.WordTrace tailWord_8052887 prefixEnd_8052887 1378333895781046592092651 := by
  unfold tailWord_8052887
  simp only [CollatzResearch.WordTrace]
  refine ⟨293712918376773197449604915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195808612251182131633069943 293712918376773197449604915)
  ·
    refine ⟨440569377565159796174407373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293712918376773197449604915 440569377565159796174407373)
    ·
      refine ⟨165213516586934923565402765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440569377565159796174407373 165213516586934923565402765)
      ·
        refine ⟨61955068720100596337026037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165213516586934923565402765 61955068720100596337026037)
        ·
          refine ⟨5808287692509430906596191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61955068720100596337026037 5808287692509430906596191)
          ·
            refine ⟨8712431538764146359894287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808287692509430906596191 8712431538764146359894287)
            ·
              refine ⟨13068647308146219539841431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8712431538764146359894287 13068647308146219539841431)
              ·
                refine ⟨19602970962219329309762147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13068647308146219539841431 19602970962219329309762147)
                ·
                  refine ⟨29404456443328993964643221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19602970962219329309762147 29404456443328993964643221)
                  ·
                    refine ⟨1378333895781046592092651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29404456443328993964643221 1378333895781046592092651)
                    ·
                      rfl

theorem cell23_8052887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_8052887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052887 prefixEnd_8052887 := by exact prefixLift 8052887
  have htrace : WordTrace (prefixWord ++ tailWord_8052887) baseStart_8052887 baseEnd_8052887 := by
    simpa [prefixWord, tailWord_8052887, baseEnd_8052887] using wordTrace_append hprefix tailTrace_8052887
  have hstable : (prefixWord ++ tailWord_8052887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052887).length < 2 ^ (prefixWord ++ tailWord_8052887).sum := by decide
  have hdescent : baseEnd_8052887 < baseStart_8052887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052890 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_8052890 : Nat := 118140960795 + 8052890 * 2 ^ 59
def prefixEnd_8052890 : Nat := 4983230072969 + 3 ^ 40 * 8052890 * 2
def baseEnd_8052890 : Nat := 4135003227785103264540439

theorem tailTrace_8052890 : CollatzResearch.WordTrace tailWord_8052890 prefixEnd_8052890 4135003227785103264540439 := by
  unfold tailWord_8052890
  simp only [CollatzResearch.WordTrace]
  refine ⟨73428256948940582240491031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195808685197174885974642749 73428256948940582240491031)
  ·
    refine ⟨110142385423410873360736547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73428256948940582240491031 110142385423410873360736547)
    ·
      refine ⟨165213578135116310041104821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110142385423410873360736547 165213578135116310041104821)
      ·
        refine ⟨15488772950167154066353577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165213578135116310041104821 15488772950167154066353577)
        ·
          refine ⟨11616579712625365549765183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15488772950167154066353577 11616579712625365549765183)
          ·
            refine ⟨17424869568938048324647775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616579712625365549765183 17424869568938048324647775)
            ·
              refine ⟨26137304353407072486971663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17424869568938048324647775 26137304353407072486971663)
              ·
                refine ⟨39205956530110608730457495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26137304353407072486971663 39205956530110608730457495)
                ·
                  refine ⟨58808934795165913095686243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39205956530110608730457495 58808934795165913095686243)
                  ·
                    refine ⟨88213402192748869643529365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58808934795165913095686243 88213402192748869643529365)
                    ·
                      refine ⟨4135003227785103264540439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88213402192748869643529365 4135003227785103264540439)
                      ·
                        rfl

theorem cell23_8052890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_8052890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052890 prefixEnd_8052890 := by exact prefixLift 8052890
  have htrace : WordTrace (prefixWord ++ tailWord_8052890) baseStart_8052890 baseEnd_8052890 := by
    simpa [prefixWord, tailWord_8052890, baseEnd_8052890] using wordTrace_append hprefix tailTrace_8052890
  have hstable : (prefixWord ++ tailWord_8052890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052890).length < 2 ^ (prefixWord ++ tailWord_8052890).sum := by decide
  have hdescent : baseEnd_8052890 < baseStart_8052890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052894 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_8052894 : Nat := 118140960795 + 8052894 * 2 ^ 59
def prefixEnd_8052894 : Nat := 4983230072969 + 3 ^ 40 * 8052894 * 2
def baseEnd_8052894 : Nat := 4135005281707721248890421

theorem tailTrace_8052894 : CollatzResearch.WordTrace tailWord_8052894 prefixEnd_8052894 4135005281707721248890421 := by
  unfold tailWord_8052894
  simp only [CollatzResearch.WordTrace]
  refine ⟨36714146710968479705638717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195808782458498558430073157 36714146710968479705638717)
  ·
    refine ⟨13767805016613179889614519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36714146710968479705638717 13767805016613179889614519)
    ·
      refine ⟨20651707524919769834421779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13767805016613179889614519 20651707524919769834421779)
      ·
        refine ⟨30977561287379654751632669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20651707524919769834421779 30977561287379654751632669)
        ·
          refine ⟨11616585482767370531862251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30977561287379654751632669 11616585482767370531862251)
          ·
            refine ⟨17424878224151055797793377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616585482767370531862251 17424878224151055797793377)
            ·
              refine ⟨13068658668113291848345033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17424878224151055797793377 13068658668113291848345033)
              ·
                refine ⟨9801494001084968886258775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13068658668113291848345033 9801494001084968886258775)
                ·
                  refine ⟨14702241001627453329388163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801494001084968886258775 14702241001627453329388163)
                  ·
                    refine ⟨22053361502441179994082245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14702241001627453329388163 22053361502441179994082245)
                    ·
                      refine ⟨4135005281707721248890421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22053361502441179994082245 4135005281707721248890421)
                      ·
                        rfl

theorem cell23_8052894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_8052894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052894 prefixEnd_8052894 := by exact prefixLift 8052894
  have htrace : WordTrace (prefixWord ++ tailWord_8052894) baseStart_8052894 baseEnd_8052894 := by
    simpa [prefixWord, tailWord_8052894, baseEnd_8052894] using wordTrace_append hprefix tailTrace_8052894
  have hstable : (prefixWord ++ tailWord_8052894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052894).length < 2 ^ (prefixWord ++ tailWord_8052894).sum := by decide
  have hdescent : baseEnd_8052894 < baseStart_8052894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052897 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_8052897 : Nat := 118140960795 + 8052897 * 2 ^ 59
def prefixEnd_8052897 : Nat := 4983230072969 + 3 ^ 40 * 8052897 * 2
def baseEnd_8052897 : Nat := 4135006822149684737152907

theorem tailTrace_8052897 : CollatzResearch.WordTrace tailWord_8052897 prefixEnd_8052897 4135006822149684737152907 := by
  unfold tailWord_8052897
  simp only [CollatzResearch.WordTrace]
  refine ⟨293713283106736969157468945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195808855404491312771645963 293713283106736969157468945)
  ·
    refine ⟨220284962330052726868101709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293713283106736969157468945 220284962330052726868101709)
    ·
      refine ⟨82606860873769772575538141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220284962330052726868101709 82606860873769772575538141)
      ·
        refine ⟨30977572827663664715826803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82606860873769772575538141 30977572827663664715826803)
        ·
          refine ⟨46466359241495497073740205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30977572827663664715826803 46466359241495497073740205)
          ·
            refine ⟨17424884715560811402652577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46466359241495497073740205 17424884715560811402652577)
            ·
              refine ⟨13068663536670608551989433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17424884715560811402652577 13068663536670608551989433)
              ·
                refine ⟨9801497652502956413992075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13068663536670608551989433 9801497652502956413992075)
                ·
                  refine ⟨14702246478754434620988113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9801497652502956413992075 14702246478754434620988113)
                  ·
                    refine ⟨11026684859065825965741085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14702246478754434620988113 11026684859065825965741085)
                    ·
                      refine ⟨4135006822149684737152907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026684859065825965741085 4135006822149684737152907)
                      ·
                        rfl

theorem cell23_8052897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_8052897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052897 prefixEnd_8052897 := by exact prefixLift 8052897
  have htrace : WordTrace (prefixWord ++ tailWord_8052897) baseStart_8052897 baseEnd_8052897 := by
    simpa [prefixWord, tailWord_8052897, baseEnd_8052897] using wordTrace_append hprefix tailTrace_8052897
  have hstable : (prefixWord ++ tailWord_8052897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052897).length < 2 ^ (prefixWord ++ tailWord_8052897).sum := by decide
  have hdescent : baseEnd_8052897 < baseStart_8052897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052917 : List Nat := [1, 3, 3, 4, 2, 1, 9]
def baseStart_8052917 : Nat := 118140960795 + 8052917 * 2 ^ 59
def prefixEnd_8052917 : Nat := 4983230072969 + 3 ^ 40 * 8052917 * 2
def baseEnd_8052917 : Nat := 51049593725466353813615

theorem tailTrace_8052917 : CollatzResearch.WordTrace tailWord_8052917 prefixEnd_8052917 51049593725466353813615 := by
  unfold tailWord_8052917
  simp only [CollatzResearch.WordTrace]
  refine ⟨293714012566664512573197005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195809341711109675048798003 293714012566664512573197005)
  ·
    refine ⟨110142754712499192214948877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293714012566664512573197005 110142754712499192214948877)
    ·
      refine ⟨41303533017187197080605829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110142754712499192214948877 41303533017187197080605829)
      ·
        refine ⟨7744412440722599452613593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41303533017187197080605829 7744412440722599452613593)
        ·
          refine ⟨5808309330541949589460195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7744412440722599452613593 5808309330541949589460195)
          ·
            refine ⟨8712463995812924384190293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808309330541949589460195 8712463995812924384190293)
            ·
              refine ⟨51049593725466353813615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8712463995812924384190293 51049593725466353813615)
              ·
                rfl

theorem cell23_8052917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 9].length) (baseStart_8052917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052917 prefixEnd_8052917 := by exact prefixLift 8052917
  have htrace : WordTrace (prefixWord ++ tailWord_8052917) baseStart_8052917 baseEnd_8052917 := by
    simpa [prefixWord, tailWord_8052917, baseEnd_8052917] using wordTrace_append hprefix tailTrace_8052917
  have hstable : (prefixWord ++ tailWord_8052917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052917).length < 2 ^ (prefixWord ++ tailWord_8052917).sum := by decide
  have hdescent : baseEnd_8052917 < baseStart_8052917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052953 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_8052953 : Nat := 118140960795 + 8052953 * 2 ^ 59
def prefixEnd_8052953 : Nat := 4983230072969 + 3 ^ 40 * 8052953 * 2
def baseEnd_8052953 : Nat := 4135035577066336518052649

theorem tailTrace_8052953 : CollatzResearch.WordTrace tailWord_8052953 prefixEnd_8052953 4135035577066336518052649 := by
  unfold tailWord_8052953
  simp only [CollatzResearch.WordTrace]
  refine ⟨293715325594534090721507513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195810217063022727147671675 293715325594534090721507513)
  ·
    refine ⟨220286494195900568041130635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293715325594534090721507513 220286494195900568041130635)
    ·
      refine ⟨330429741293850852061695953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220286494195900568041130635 330429741293850852061695953)
      ·
        refine ⟨247822305970388139046271965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330429741293850852061695953 247822305970388139046271965)
        ·
          refine ⟨92933364738895552142351987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247822305970388139046271965 92933364738895552142351987)
          ·
            refine ⟨139400047108343328213527981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92933364738895552142351987 139400047108343328213527981)
            ·
              refine ⟨52275017665628748080072993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139400047108343328213527981 52275017665628748080072993)
              ·
                refine ⟨39206263249221561060054745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52275017665628748080072993 39206263249221561060054745)
                ·
                  refine ⟨29404697436916170795041059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39206263249221561060054745 29404697436916170795041059)
                  ·
                    refine ⟨44107046155374256192561589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29404697436916170795041059 44107046155374256192561589)
                    ·
                      refine ⟨4135035577066336518052649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44107046155374256192561589 4135035577066336518052649)
                      ·
                        rfl

theorem cell23_8052953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_8052953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052953 prefixEnd_8052953 := by exact prefixLift 8052953
  have htrace : WordTrace (prefixWord ++ tailWord_8052953) baseStart_8052953 baseEnd_8052953 := by
    simpa [prefixWord, tailWord_8052953, baseEnd_8052953] using wordTrace_append hprefix tailTrace_8052953
  have hstable : (prefixWord ++ tailWord_8052953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052953).length < 2 ^ (prefixWord ++ tailWord_8052953).sum := by decide
  have hdescent : baseEnd_8052953 < baseStart_8052953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052967 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_8052967 : Nat := 118140960795 + 8052967 * 2 ^ 59
def prefixEnd_8052967 : Nat := 4983230072969 + 3 ^ 40 * 8052967 * 2
def baseEnd_8052967 : Nat := 4135042765795499463277585

theorem tailTrace_8052967 : CollatzResearch.WordTrace tailWord_8052967 prefixEnd_8052967 4135042765795499463277585 := by
  unfold tailWord_8052967
  simp only [CollatzResearch.WordTrace]
  refine ⟨293715836216483371112517155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195810557477655580741678103 293715836216483371112517155)
  ·
    refine ⟨440573754324725056668775733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293715836216483371112517155 440573754324725056668775733)
    ·
      refine ⟨41303789467942974062697725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 440573754324725056668775733 41303789467942974062697725)
      ·
        refine ⟨15488921050478615273511647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41303789467942974062697725 15488921050478615273511647)
        ·
          refine ⟨23233381575717922910267471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15488921050478615273511647 23233381575717922910267471)
          ·
            refine ⟨34850072363576884365401207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23233381575717922910267471 34850072363576884365401207)
            ·
              refine ⟨52275108545365326548101811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34850072363576884365401207 52275108545365326548101811)
              ·
                refine ⟨78412662818047989822152717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52275108545365326548101811 78412662818047989822152717)
                ·
                  refine ⟨29404748556767996183307269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78412662818047989822152717 29404748556767996183307269)
                  ·
                    refine ⟨5513390354393999284370113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29404748556767996183307269 5513390354393999284370113)
                    ·
                      refine ⟨4135042765795499463277585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513390354393999284370113 4135042765795499463277585)
                      ·
                        rfl

theorem cell23_8052967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_8052967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052967 prefixEnd_8052967 := by exact prefixLift 8052967
  have htrace : WordTrace (prefixWord ++ tailWord_8052967) baseStart_8052967 baseEnd_8052967 := by
    simpa [prefixWord, tailWord_8052967, baseEnd_8052967] using wordTrace_append hprefix tailTrace_8052967
  have hstable : (prefixWord ++ tailWord_8052967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052967).length < 2 ^ (prefixWord ++ tailWord_8052967).sum := by decide
  have hdescent : baseEnd_8052967 < baseStart_8052967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8052990 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_8052990 : Nat := 118140960795 + 8052990 * 2 ^ 59
def prefixEnd_8052990 : Nat := 4983230072969 + 3 ^ 40 * 8052990 * 2
def baseEnd_8052990 : Nat := 459450508427839208143331

theorem tailTrace_8052990 : CollatzResearch.WordTrace tailWord_8052990 prefixEnd_8052990 459450508427839208143331 := by
  unfold tailWord_8052990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36714584386925005755075553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195811116730266697360402949 36714584386925005755075553)
  ·
    refine ⟨27535938290193754316306665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36714584386925005755075553 27535938290193754316306665)
    ·
      refine ⟨20651953717645315737229999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27535938290193754316306665 20651953717645315737229999)
      ·
        refine ⟨30977930576467973605844999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20651953717645315737229999 30977930576467973605844999)
        ·
          refine ⟨46466895864701960408767499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30977930576467973605844999 46466895864701960408767499)
          ·
            refine ⟨69700343797052940613151249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46466895864701960408767499 69700343797052940613151249)
            ·
              refine ⟨52275257847789705459863437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69700343797052940613151249 52275257847789705459863437)
              ·
                refine ⟨19603221692921139547448789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52275257847789705459863437 19603221692921139547448789)
                ·
                  refine ⟨459450508427839208143331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19603221692921139547448789 459450508427839208143331)
                  ·
                    rfl

theorem cell23_8052990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_8052990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8052990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8052990 prefixEnd_8052990 := by exact prefixLift 8052990
  have htrace : WordTrace (prefixWord ++ tailWord_8052990) baseStart_8052990 baseEnd_8052990 := by
    simpa [prefixWord, tailWord_8052990, baseEnd_8052990] using wordTrace_append hprefix tailTrace_8052990
  have hstable : (prefixWord ++ tailWord_8052990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8052990).length < 2 ^ (prefixWord ++ tailWord_8052990).sum := by decide
  have hdescent : baseEnd_8052990 < baseStart_8052990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8052990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053000 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_8053000 : Nat := 118140960795 + 8053000 * 2 ^ 59
def prefixEnd_8053000 : Nat := 4983230072969 + 3 ^ 40 * 8053000 * 2
def baseEnd_8053000 : Nat := 4135059710657097834164933

theorem tailTrace_8053000 : CollatzResearch.WordTrace tailWord_8053000 prefixEnd_8053000 4135059710657097834164933 := by
  unfold tailWord_8053000
  simp only [CollatzResearch.WordTrace]
  refine ⟨146858519912681908874234227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195811359883575878498978969 146858519912681908874234227)
  ·
    refine ⟨220287779869022863311351341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146858519912681908874234227 220287779869022863311351341)
    ·
      refine ⟨82607917450883573741756753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220287779869022863311351341 82607917450883573741756753)
      ·
        refine ⟨61955938088162680306317565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82607917450883573741756753 61955938088162680306317565)
        ·
          refine ⟨23233476783061005114869087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61955938088162680306317565 23233476783061005114869087)
          ·
            refine ⟨34850215174591507672303631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23233476783061005114869087 34850215174591507672303631)
            ·
              refine ⟨52275322761887261508455447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34850215174591507672303631 52275322761887261508455447)
              ·
                refine ⟨78412984142830892262683171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52275322761887261508455447 78412984142830892262683171)
                ·
                  refine ⟨117619476214246338394024757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78412984142830892262683171 117619476214246338394024757)
                  ·
                    refine ⟨11026825895085594224439821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117619476214246338394024757 11026825895085594224439821)
                    ·
                      refine ⟨4135059710657097834164933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11026825895085594224439821 4135059710657097834164933)
                      ·
                        rfl

theorem cell23_8053000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_8053000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053000 prefixEnd_8053000 := by exact prefixLift 8053000
  have htrace : WordTrace (prefixWord ++ tailWord_8053000) baseStart_8053000 baseEnd_8053000 := by
    simpa [prefixWord, tailWord_8053000, baseEnd_8053000] using wordTrace_append hprefix tailTrace_8053000
  have hstable : (prefixWord ++ tailWord_8053000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053000).length < 2 ^ (prefixWord ++ tailWord_8053000).sum := by decide
  have hdescent : baseEnd_8053000 < baseStart_8053000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053003 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 7]
def baseStart_8053003 : Nat := 118140960795 + 8053003 * 2 ^ 59
def prefixEnd_8053003 : Nat := 4983230072969 + 3 ^ 40 * 8053003 * 2
def baseEnd_8053003 : Nat := 1378353750366353774142473

theorem tailTrace_8053003 : CollatzResearch.WordTrace tailWord_8053003 prefixEnd_8053003 1378353750366353774142473 := by
  unfold tailWord_8053003
  simp only [CollatzResearch.WordTrace]
  refine ⟨293717149244352949260827663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195811432829568632840551775 293717149244352949260827663)
  ·
    refine ⟨440575723866529423891241495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293717149244352949260827663 440575723866529423891241495)
    ·
      refine ⟨660863585799794135836862243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440575723866529423891241495 660863585799794135836862243)
      ·
        refine ⟨991295378699691203755293365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660863585799794135836862243 991295378699691203755293365)
        ·
          refine ⟨92933941753096050352058753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 991295378699691203755293365 92933941753096050352058753)
          ·
            refine ⟨69700456314822037764044065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92933941753096050352058753 69700456314822037764044065)
            ·
              refine ⟨52275342236116528323033049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69700456314822037764044065 52275342236116528323033049)
              ·
                refine ⟨39206506677087396242274787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52275342236116528323033049 39206506677087396242274787)
                ·
                  refine ⟨58809760015631094363412181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39206506677087396242274787 58809760015631094363412181)
                  ·
                    refine ⟨1378353750366353774142473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58809760015631094363412181 1378353750366353774142473)
                    ·
                      rfl

theorem cell23_8053003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_8053003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053003 prefixEnd_8053003 := by exact prefixLift 8053003
  have htrace : WordTrace (prefixWord ++ tailWord_8053003) baseStart_8053003 baseEnd_8053003 := by
    simpa [prefixWord, tailWord_8053003, baseEnd_8053003] using wordTrace_append hprefix tailTrace_8053003
  have hstable : (prefixWord ++ tailWord_8053003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053003).length < 2 ^ (prefixWord ++ tailWord_8053003).sum := by decide
  have hdescent : baseEnd_8053003 < baseStart_8053003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053013 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_8053013 : Nat := 118140960795 + 8053013 * 2 ^ 59
def prefixEnd_8053013 : Nat := 4983230072969 + 3 ^ 40 * 8053013 * 2
def baseEnd_8053013 : Nat := 4135066385905606283302373

theorem tailTrace_8053013 : CollatzResearch.WordTrace tailWord_8053013 prefixEnd_8053013 4135066385905606283302373 := by
  unfold tailWord_8053013
  simp only [CollatzResearch.WordTrace]
  refine ⟨293717513974316720968691693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195811675982877813979127795 293717513974316720968691693)
  ·
    refine ⟨110144067740368770363259385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293717513974316720968691693 110144067740368770363259385)
    ·
      refine ⟨82608050805276577772444539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110144067740368770363259385 82608050805276577772444539)
      ·
        refine ⟨123912076207914866658666809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82608050805276577772444539 123912076207914866658666809)
        ·
          refine ⟨92934057155936149994000107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123912076207914866658666809 92934057155936149994000107)
          ·
            refine ⟨139401085733904224991000161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92934057155936149994000107 139401085733904224991000161)
            ·
              refine ⟨104550814300428168743250121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139401085733904224991000161 104550814300428168743250121)
              ·
                refine ⟨78413110725321126557437591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104550814300428168743250121 78413110725321126557437591)
                ·
                  refine ⟨117619666087981689836156387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78413110725321126557437591 117619666087981689836156387)
                  ·
                    refine ⟨176429499131972534754234581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117619666087981689836156387 176429499131972534754234581)
                    ·
                      refine ⟨4135066385905606283302373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176429499131972534754234581 4135066385905606283302373)
                      ·
                        rfl

theorem cell23_8053013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_8053013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053013 prefixEnd_8053013 := by exact prefixLift 8053013
  have htrace : WordTrace (prefixWord ++ tailWord_8053013) baseStart_8053013 baseEnd_8053013 := by
    simpa [prefixWord, tailWord_8053013, baseEnd_8053013] using wordTrace_append hprefix tailTrace_8053013
  have hstable : (prefixWord ++ tailWord_8053013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053013).length < 2 ^ (prefixWord ++ tailWord_8053013).sum := by decide
  have hdescent : baseEnd_8053013 < baseStart_8053013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053101 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_8053101 : Nat := 118140960795 + 8053101 * 2 ^ 59
def prefixEnd_8053101 : Nat := 4983230072969 + 3 ^ 40 * 8053101 * 2
def baseEnd_8053101 : Nat := 1378370524067733979667323

theorem tailTrace_8053101 : CollatzResearch.WordTrace tailWord_8053101 prefixEnd_8053101 1378370524067733979667323 := by
  unfold tailWord_8053101
  simp only [CollatzResearch.WordTrace]
  refine ⟨293720723597997911997895157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195813815731998607998596771 293720723597997911997895157)
  ·
    refine ⟨27536317837312304249802671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293720723597997911997895157 27536317837312304249802671)
    ·
      refine ⟨41304476755968456374704007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27536317837312304249802671 41304476755968456374704007)
      ·
        refine ⟨61956715133952684562056011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41304476755968456374704007 61956715133952684562056011)
        ·
          refine ⟨92935072700929026843084017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61956715133952684562056011 92935072700929026843084017)
          ·
            refine ⟨69701304525696770132313013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92935072700929026843084017 69701304525696770132313013)
            ·
              refine ⟨6534497299284072199904345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69701304525696770132313013 6534497299284072199904345)
              ·
                refine ⟨4900872974463054149928259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534497299284072199904345 4900872974463054149928259)
                ·
                  refine ⟨7351309461694581224892389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900872974463054149928259 7351309461694581224892389)
                  ·
                    refine ⟨1378370524067733979667323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351309461694581224892389 1378370524067733979667323)
                    ·
                      rfl

theorem cell23_8053101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_8053101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053101 prefixEnd_8053101 := by exact prefixLift 8053101
  have htrace : WordTrace (prefixWord ++ tailWord_8053101) baseStart_8053101 baseEnd_8053101 := by
    simpa [prefixWord, tailWord_8053101, baseEnd_8053101] using wordTrace_append hprefix tailTrace_8053101
  have hstable : (prefixWord ++ tailWord_8053101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053101).length < 2 ^ (prefixWord ++ tailWord_8053101).sum := by decide
  have hdescent : baseEnd_8053101 < baseStart_8053101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053164 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_8053164 : Nat := 118140960795 + 8053164 * 2 ^ 59
def prefixEnd_8053164 : Nat := 4983230072969 + 3 ^ 40 * 8053164 * 2
def baseEnd_8053164 : Nat := 4135143921484435192514179

theorem tailTrace_8053164 : CollatzResearch.WordTrace tailWord_8053164 prefixEnd_8053164 4135143921484435192514179 := by
  unfold tailWord_8053164
  simp only [CollatzResearch.WordTrace]
  refine ⟨146861510698384836878719273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195815347597846449171625697 146861510698384836878719273)
  ·
    refine ⟨110146133023788627659039455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146861510698384836878719273 110146133023788627659039455)
    ·
      refine ⟨165219199535682941488559183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110146133023788627659039455 165219199535682941488559183)
      ·
        refine ⟨247828799303524412232838775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165219199535682941488559183 247828799303524412232838775)
        ·
          refine ⟨371743198955286618349258163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247828799303524412232838775 371743198955286618349258163)
          ·
            refine ⟨557614798432929927523887245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371743198955286618349258163 557614798432929927523887245)
            ·
              refine ⟨209105549412348722821457717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557614798432929927523887245 209105549412348722821457717)
              ·
                refine ⟨19603645257407692764511661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209105549412348722821457717 19603645257407692764511661)
                ·
                  refine ⟨7351366971527884786691873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19603645257407692764511661 7351366971527884786691873)
                  ·
                    refine ⟨5513525228645913590018905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7351366971527884786691873 5513525228645913590018905)
                    ·
                      refine ⟨4135143921484435192514179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513525228645913590018905 4135143921484435192514179)
                      ·
                        rfl

theorem cell23_8053164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_8053164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053164 prefixEnd_8053164 := by exact prefixLift 8053164
  have htrace : WordTrace (prefixWord ++ tailWord_8053164) baseStart_8053164 baseEnd_8053164 := by
    simpa [prefixWord, tailWord_8053164, baseEnd_8053164] using wordTrace_append hprefix tailTrace_8053164
  have hstable : (prefixWord ++ tailWord_8053164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053164).length < 2 ^ (prefixWord ++ tailWord_8053164).sum := by decide
  have hdescent : baseEnd_8053164 < baseStart_8053164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053177 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_8053177 : Nat := 118140960795 + 8053177 * 2 ^ 59
def prefixEnd_8053177 : Nat := 4983230072969 + 3 ^ 40 * 8053177 * 2
def baseEnd_8053177 : Nat := 4135150596732943641651619

theorem tailTrace_8053177 : CollatzResearch.WordTrace tailWord_8053177 prefixEnd_8053177 4135150596732943641651619 := by
  unfold tailWord_8053177
  simp only [CollatzResearch.WordTrace]
  refine ⟨293723495545722576977661785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195815663697148384651774523 293723495545722576977661785)
  ·
    refine ⟨220292621659291932733246339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293723495545722576977661785 220292621659291932733246339)
    ·
      refine ⟨330438932488937899099869509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220292621659291932733246339 330438932488937899099869509)
      ·
        refine ⟨61957299841675856081225533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330438932488937899099869509 61957299841675856081225533)
        ·
          refine ⟨23233987440628446030459575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61957299841675856081225533 23233987440628446030459575)
          ·
            refine ⟨34850981160942669045689363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23233987440628446030459575 34850981160942669045689363)
            ·
              refine ⟨52276471741414003568534045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34850981160942669045689363 52276471741414003568534045)
              ·
                refine ⟨19603676903030251338200267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52276471741414003568534045 19603676903030251338200267)
                ·
                  refine ⟨29405515354545377007300401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19603676903030251338200267 29405515354545377007300401)
                  ·
                    refine ⟨22054136515909032755475301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29405515354545377007300401 22054136515909032755475301)
                    ·
                      refine ⟨4135150596732943641651619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22054136515909032755475301 4135150596732943641651619)
                      ·
                        rfl

theorem cell23_8053177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_8053177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053177 prefixEnd_8053177 := by exact prefixLift 8053177
  have htrace : WordTrace (prefixWord ++ tailWord_8053177) baseStart_8053177 baseEnd_8053177 := by
    simpa [prefixWord, tailWord_8053177, baseEnd_8053177] using wordTrace_append hprefix tailTrace_8053177
  have hstable : (prefixWord ++ tailWord_8053177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053177).length < 2 ^ (prefixWord ++ tailWord_8053177).sum := by decide
  have hdescent : baseEnd_8053177 < baseStart_8053177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053181 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_8053181 : Nat := 118140960795 + 8053181 * 2 ^ 59
def prefixEnd_8053181 : Nat := 4983230072969 + 3 ^ 40 * 8053181 * 2
def baseEnd_8053181 : Nat := 4135152650655561626001601

theorem tailTrace_8053181 : CollatzResearch.WordTrace tailWord_8053181 prefixEnd_8053181 4135152650655561626001601 := by
  unfold tailWord_8053181
  simp only [CollatzResearch.WordTrace]
  refine ⟨293723641437708085660807397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195815760958472057107204931 293723641437708085660807397)
  ·
    refine ⟨55073182769570266061401387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293723641437708085660807397 55073182769570266061401387)
    ·
      refine ⟨82609774154355399092102081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55073182769570266061401387 82609774154355399092102081)
      ·
        refine ⟨61957330615766549319076561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82609774154355399092102081 61957330615766549319076561)
        ·
          refine ⟨46467997961824911989307421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61957330615766549319076561 46467997961824911989307421)
          ·
            refine ⟨17425499235684341995990283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46467997961824911989307421 17425499235684341995990283)
            ·
              refine ⟨26138248853526512993985425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17425499235684341995990283 26138248853526512993985425)
              ·
                refine ⟨19603686640144884745489069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26138248853526512993985425 19603686640144884745489069)
                ·
                  refine ⟨7351382490054331779558401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19603686640144884745489069 7351382490054331779558401)
                  ·
                    refine ⟨5513536867540748834668801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7351382490054331779558401 5513536867540748834668801)
                    ·
                      refine ⟨4135152650655561626001601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513536867540748834668801 4135152650655561626001601)
                      ·
                        rfl

theorem cell23_8053181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_8053181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053181 prefixEnd_8053181 := by exact prefixLift 8053181
  have htrace : WordTrace (prefixWord ++ tailWord_8053181) baseStart_8053181 baseEnd_8053181 := by
    simpa [prefixWord, tailWord_8053181, baseEnd_8053181] using wordTrace_append hprefix tailTrace_8053181
  have hstable : (prefixWord ++ tailWord_8053181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053181).length < 2 ^ (prefixWord ++ tailWord_8053181).sum := by decide
  have hdescent : baseEnd_8053181 < baseStart_8053181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053317 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_8053317 : Nat := 118140960795 + 8053317 * 2 ^ 59
def prefixEnd_8053317 : Nat := 4983230072969 + 3 ^ 40 * 8053317 * 2
def baseEnd_8053317 : Nat := 4135222484024573093900975

theorem tailTrace_8053317 : CollatzResearch.WordTrace tailWord_8053317 prefixEnd_8053317 4135222484024573093900975 := by
  unfold tailWord_8053317
  simp only [CollatzResearch.WordTrace]
  refine ⟨293728601765215380887758205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195819067843476920591838803 293728601765215380887758205)
  ·
    refine ⟨110148225661955767832909327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293728601765215380887758205 110148225661955767832909327)
    ·
      refine ⟨165222338492933651749363991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110148225661955767832909327 165222338492933651749363991)
      ·
        refine ⟨247833507739400477624045987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165222338492933651749363991 247833507739400477624045987)
        ·
          refine ⟨371750261609100716436068981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247833507739400477624045987 371750261609100716436068981)
          ·
            refine ⟨34851587025853192165881467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371750261609100716436068981 34851587025853192165881467)
            ·
              refine ⟨52277380538779788248822201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34851587025853192165881467 52277380538779788248822201)
              ·
                refine ⟨39208035404084841186616651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52277380538779788248822201 39208035404084841186616651)
                ·
                  refine ⟨58812053106127261779924977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39208035404084841186616651 58812053106127261779924977)
                  ·
                    refine ⟨44109039829595446334943733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58812053106127261779924977 44109039829595446334943733)
                    ·
                      refine ⟨4135222484024573093900975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44109039829595446334943733 4135222484024573093900975)
                      ·
                        rfl

theorem cell23_8053317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_8053317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053317 prefixEnd_8053317 := by exact prefixLift 8053317
  have htrace : WordTrace (prefixWord ++ tailWord_8053317) baseStart_8053317 baseEnd_8053317 := by
    simpa [prefixWord, tailWord_8053317, baseEnd_8053317] using wordTrace_append hprefix tailTrace_8053317
  have hstable : (prefixWord ++ tailWord_8053317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053317).length < 2 ^ (prefixWord ++ tailWord_8053317).sum := by decide
  have hdescent : baseEnd_8053317 < baseStart_8053317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053344 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2]
def baseStart_8053344 : Nat := 118140960795 + 8053344 * 2 ^ 59
def prefixEnd_8053344 : Nat := 4983230072969 + 3 ^ 40 * 8053344 * 2
def baseEnd_8053344 : Nat := 4135236348002244488263351

theorem tailTrace_8053344 : CollatzResearch.WordTrace tailWord_8053344 prefixEnd_8053344 4135236348002244488263351 := by
  unfold tailWord_8053344
  simp only [CollatzResearch.WordTrace]
  refine ⟨146864793268058782249495543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195819724357411709665994057 146864793268058782249495543)
  ·
    refine ⟨220297189902088173374243315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146864793268058782249495543 220297189902088173374243315)
    ·
      refine ⟨330445784853132260061364973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220297189902088173374243315 330445784853132260061364973)
      ·
        refine ⟨123917169319924597523011865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330445784853132260061364973 123917169319924597523011865)
        ·
          refine ⟨92937876989943448142258899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123917169319924597523011865 92937876989943448142258899)
          ·
            refine ⟨139406815484915172213388349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92937876989943448142258899 139406815484915172213388349)
            ·
              refine ⟨52277555806843189580020631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139406815484915172213388349 52277555806843189580020631)
              ·
                refine ⟨78416333710264784370030947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52277555806843189580020631 78416333710264784370030947)
                ·
                  refine ⟨117624500565397176555046421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78416333710264784370030947 117624500565397176555046421)
                  ·
                    refine ⟨5513648464002992651017801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117624500565397176555046421 5513648464002992651017801)
                    ·
                      refine ⟨4135236348002244488263351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513648464002992651017801 4135236348002244488263351)
                      ·
                        rfl

theorem cell23_8053344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_8053344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053344 prefixEnd_8053344 := by exact prefixLift 8053344
  have htrace : WordTrace (prefixWord ++ tailWord_8053344) baseStart_8053344 baseEnd_8053344 := by
    simpa [prefixWord, tailWord_8053344, baseEnd_8053344] using wordTrace_append hprefix tailTrace_8053344
  have hstable : (prefixWord ++ tailWord_8053344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053344).length < 2 ^ (prefixWord ++ tailWord_8053344).sum := by decide
  have hdescent : baseEnd_8053344 < baseStart_8053344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053422 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_8053422 : Nat := 118140960795 + 8053422 * 2 ^ 59
def prefixEnd_8053422 : Nat := 4983230072969 + 3 ^ 40 * 8053422 * 2
def baseEnd_8053422 : Nat := 1378425466497765061029331

theorem tailTrace_8053422 : CollatzResearch.WordTrace tailWord_8053422 prefixEnd_8053422 1378425466497765061029331 := by
  unfold tailWord_8053422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36716553928729372977541315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195821620953223322546887013 36716553928729372977541315)
  ·
    refine ⟨55074830893094059466311973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36716553928729372977541315 55074830893094059466311973)
    ·
      refine ⟨10326530792455136149933495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55074830893094059466311973 10326530792455136149933495)
      ·
        refine ⟨15489796188682704224900243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326530792455136149933495 15489796188682704224900243)
        ·
          refine ⟨23234694283024056337350365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15489796188682704224900243 23234694283024056337350365)
          ·
            refine ⟨8713010356134021126506387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23234694283024056337350365 8713010356134021126506387)
            ·
              refine ⟨13069515534201031689759581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713010356134021126506387 13069515534201031689759581)
              ·
                refine ⟨4901068325325386883659843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13069515534201031689759581 4901068325325386883659843)
                ·
                  refine ⟨7351602487988080325489765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901068325325386883659843 7351602487988080325489765)
                  ·
                    refine ⟨1378425466497765061029331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351602487988080325489765 1378425466497765061029331)
                    ·
                      rfl

theorem cell23_8053422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_8053422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053422 prefixEnd_8053422 := by exact prefixLift 8053422
  have htrace : WordTrace (prefixWord ++ tailWord_8053422) baseStart_8053422 baseEnd_8053422 := by
    simpa [prefixWord, tailWord_8053422, baseEnd_8053422] using wordTrace_append hprefix tailTrace_8053422
  have hstable : (prefixWord ++ tailWord_8053422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053422).length < 2 ^ (prefixWord ++ tailWord_8053422).sum := by decide
  have hdescent : baseEnd_8053422 < baseStart_8053422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053438 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_8053438 : Nat := 118140960795 + 8053438 * 2 ^ 59
def prefixEnd_8053438 : Nat := 4983230072969 + 3 ^ 40 * 8053438 * 2
def baseEnd_8053438 : Nat := 4135284615183767120487919

theorem tailTrace_8053438 : CollatzResearch.WordTrace tailWord_8053438 prefixEnd_8053438 4135284615183767120487919 := by
  unfold tailWord_8053438
  simp only [CollatzResearch.WordTrace]
  refine ⟨36716626874722127319114121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195822009998518012368608645 36716626874722127319114121)
  ·
    refine ⟨27537470156041595489335591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36716626874722127319114121 27537470156041595489335591)
    ·
      refine ⟨41306205234062393234003387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27537470156041595489335591 41306205234062393234003387)
      ·
        refine ⟨61959307851093589851005081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41306205234062393234003387 61959307851093589851005081)
        ·
          refine ⟨46469480888320192388253811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61959307851093589851005081 46469480888320192388253811)
          ·
            refine ⟨69704221332480288582380717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46469480888320192388253811 69704221332480288582380717)
            ·
              refine ⟨26139082999680108218392769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69704221332480288582380717 26139082999680108218392769)
              ·
                refine ⟨19604312249760081163794577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26139082999680108218392769 19604312249760081163794577)
                ·
                  refine ⟨14703234187320060872845933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19604312249760081163794577 14703234187320060872845933)
                  ·
                    refine ⟨5513712820245022827317225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14703234187320060872845933 5513712820245022827317225)
                    ·
                      refine ⟨4135284615183767120487919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513712820245022827317225 4135284615183767120487919)
                      ·
                        rfl

theorem cell23_8053438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_8053438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053438 prefixEnd_8053438 := by exact prefixLift 8053438
  have htrace : WordTrace (prefixWord ++ tailWord_8053438) baseStart_8053438 baseEnd_8053438 := by
    simpa [prefixWord, tailWord_8053438, baseEnd_8053438] using wordTrace_append hprefix tailTrace_8053438
  have hstable : (prefixWord ++ tailWord_8053438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053438).length < 2 ^ (prefixWord ++ tailWord_8053438).sum := by decide
  have hdescent : baseEnd_8053438 < baseStart_8053438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053464 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_8053464 : Nat := 118140960795 + 8053464 * 2 ^ 59
def prefixEnd_8053464 : Nat := 4983230072969 + 3 ^ 40 * 8053464 * 2
def baseEnd_8053464 : Nat := 4135297965680784018762799

theorem tailTrace_8053464 : CollatzResearch.WordTrace tailWord_8053464 prefixEnd_8053464 4135297965680784018762799 := by
  unfold tailWord_8053464
  simp only [CollatzResearch.WordTrace]
  refine ⟨146866981647841412496679723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195822642197121883328906297 146866981647841412496679723)
  ·
    refine ⟨220300472471762118745019585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146866981647841412496679723 220300472471762118745019585)
    ·
      refine ⟨165225354353821589058764689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220300472471762118745019585 165225354353821589058764689)
      ·
        refine ⟨123919015765366191794073517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165225354353821589058764689 123919015765366191794073517)
        ·
          refine ⟨46469630912012321922777569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123919015765366191794073517 46469630912012321922777569)
          ·
            refine ⟨34852223184009241442083177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46469630912012321922777569 34852223184009241442083177)
            ·
              refine ⟨26139167388006931081562383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34852223184009241442083177 26139167388006931081562383)
              ·
                refine ⟨39208751082010396622343575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26139167388006931081562383 39208751082010396622343575)
                ·
                  refine ⟨58813126623015594933515363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39208751082010396622343575 58813126623015594933515363)
                  ·
                    refine ⟨88219689934523392400273045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58813126623015594933515363 88219689934523392400273045)
                    ·
                      refine ⟨4135297965680784018762799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88219689934523392400273045 4135297965680784018762799)
                      ·
                        rfl

theorem cell23_8053464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_8053464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053464 prefixEnd_8053464 := by exact prefixLift 8053464
  have htrace : WordTrace (prefixWord ++ tailWord_8053464) baseStart_8053464 baseEnd_8053464 := by
    simpa [prefixWord, tailWord_8053464, baseEnd_8053464] using wordTrace_append hprefix tailTrace_8053464
  have hstable : (prefixWord ++ tailWord_8053464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053464).length < 2 ^ (prefixWord ++ tailWord_8053464).sum := by decide
  have hdescent : baseEnd_8053464 < baseStart_8053464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053467 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_8053467 : Nat := 118140960795 + 8053467 * 2 ^ 59
def prefixEnd_8053467 : Nat := 4983230072969 + 3 ^ 40 * 8053467 * 2
def baseEnd_8053467 : Nat := 4135299506122747507025285

theorem tailTrace_8053467 : CollatzResearch.WordTrace tailWord_8053467 prefixEnd_8053467 4135299506122747507025285 := by
  unfold tailWord_8053467
  simp only [CollatzResearch.WordTrace]
  refine ⟨293734072714671956505718655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195822715143114637670479103 293734072714671956505718655)
  ·
    refine ⟨440601109072007934758577983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293734072714671956505718655 440601109072007934758577983)
    ·
      refine ⟨660901663608011902137866975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440601109072007934758577983 660901663608011902137866975)
      ·
        refine ⟨991352495412017853206800463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660901663608011902137866975 991352495412017853206800463)
        ·
          refine ⟨1487028743118026779810200695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991352495412017853206800463 1487028743118026779810200695)
          ·
            refine ⟨2230543114677040169715301043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487028743118026779810200695 2230543114677040169715301043)
            ·
              refine ⟨3345814672015560254572951565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230543114677040169715301043 3345814672015560254572951565)
              ·
                refine ⟨1254680502005835095464856837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3345814672015560254572951565 1254680502005835095464856837)
                ·
                  refine ⟨235252594126094080399660657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254680502005835095464856837 235252594126094080399660657)
                  ·
                    refine ⟨176439445594570560299745493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235252594126094080399660657 176439445594570560299745493)
                    ·
                      refine ⟨4135299506122747507025285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176439445594570560299745493 4135299506122747507025285)
                      ·
                        rfl

theorem cell23_8053467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_8053467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053467 prefixEnd_8053467 := by exact prefixLift 8053467
  have htrace : WordTrace (prefixWord ++ tailWord_8053467) baseStart_8053467 baseEnd_8053467 := by
    simpa [prefixWord, tailWord_8053467, baseEnd_8053467] using wordTrace_append hprefix tailTrace_8053467
  have hstable : (prefixWord ++ tailWord_8053467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053467).length < 2 ^ (prefixWord ++ tailWord_8053467).sum := by decide
  have hdescent : baseEnd_8053467 < baseStart_8053467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053468 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_8053468 : Nat := 118140960795 + 8053468 * 2 ^ 59
def prefixEnd_8053468 : Nat := 4983230072969 + 3 ^ 40 * 8053468 * 2
def baseEnd_8053468 : Nat := 4135300019603402003112781

theorem tailTrace_8053468 : CollatzResearch.WordTrace tailWord_8053468 prefixEnd_8053468 4135300019603402003112781 := by
  unfold tailWord_8053468
  simp only [CollatzResearch.WordTrace]
  refine ⟨146867054593834166838252529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195822739458445555784336705 146867054593834166838252529)
  ·
    refine ⟨110150290945375625128689397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146867054593834166838252529 110150290945375625128689397)
    ·
      refine ⟨10326589776128964855814631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110150290945375625128689397 10326589776128964855814631)
      ·
        refine ⟨15489884664193447283721947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326589776128964855814631 15489884664193447283721947)
        ·
          refine ⟨23234826996290170925582921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15489884664193447283721947 23234826996290170925582921)
          ·
            refine ⟨17426120247217628194187191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23234826996290170925582921 17426120247217628194187191)
            ·
              refine ⟨26139180370826442291280787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426120247217628194187191 26139180370826442291280787)
              ·
                refine ⟨39208770556239663436921181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26139180370826442291280787 39208770556239663436921181)
                ·
                  refine ⟨14703288958589873788845443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39208770556239663436921181 14703288958589873788845443)
                  ·
                    refine ⟨22054933437884810683268165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14703288958589873788845443 22054933437884810683268165)
                    ·
                      refine ⟨4135300019603402003112781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22054933437884810683268165 4135300019603402003112781)
                      ·
                        rfl

theorem cell23_8053468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_8053468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053468 prefixEnd_8053468 := by exact prefixLift 8053468
  have htrace : WordTrace (prefixWord ++ tailWord_8053468) baseStart_8053468 baseEnd_8053468 := by
    simpa [prefixWord, tailWord_8053468, baseEnd_8053468] using wordTrace_append hprefix tailTrace_8053468
  have hstable : (prefixWord ++ tailWord_8053468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053468).length < 2 ^ (prefixWord ++ tailWord_8053468).sum := by decide
  have hdescent : baseEnd_8053468 < baseStart_8053468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053471 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_8053471 : Nat := 118140960795 + 8053471 * 2 ^ 59
def prefixEnd_8053471 : Nat := 4983230072969 + 3 ^ 40 * 8053471 * 2
def baseEnd_8053471 : Nat := 4135301560045365491375267

theorem tailTrace_8053471 : CollatzResearch.WordTrace tailWord_8053471 prefixEnd_8053471 4135301560045365491375267 := by
  unfold tailWord_8053471
  simp only [CollatzResearch.WordTrace]
  refine ⟨293734218606657465188864267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195822812404438310125909511 293734218606657465188864267)
  ·
    refine ⟨440601327909986197783296401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293734218606657465188864267 440601327909986197783296401)
    ·
      refine ⟨330450995932489648337472301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440601327909986197783296401 330450995932489648337472301)
      ·
        refine ⟨123919123474683618126552113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330450995932489648337472301 123919123474683618126552113)
        ·
          refine ⟨92939342606012713594914085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123919123474683618126552113 92939342606012713594914085)
          ·
            refine ⟨17426126738627383799046391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92939342606012713594914085 17426126738627383799046391)
            ·
              refine ⟨26139190107941075698569587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426126738627383799046391 26139190107941075698569587)
              ·
                refine ⟨39208785161911613547854381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26139190107941075698569587 39208785161911613547854381)
                ·
                  refine ⟨14703294435716855080445393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39208785161911613547854381 14703294435716855080445393)
                  ·
                    refine ⟨11027470826787641310334045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14703294435716855080445393 11027470826787641310334045)
                    ·
                      refine ⟨4135301560045365491375267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11027470826787641310334045 4135301560045365491375267)
                      ·
                        rfl

theorem cell23_8053471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_8053471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053471 prefixEnd_8053471 := by exact prefixLift 8053471
  have htrace : WordTrace (prefixWord ++ tailWord_8053471) baseStart_8053471 baseEnd_8053471 := by
    simpa [prefixWord, tailWord_8053471, baseEnd_8053471] using wordTrace_append hprefix tailTrace_8053471
  have hstable : (prefixWord ++ tailWord_8053471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053471).length < 2 ^ (prefixWord ++ tailWord_8053471).sum := by decide
  have hdescent : baseEnd_8053471 < baseStart_8053471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053488 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3]
def baseStart_8053488 : Nat := 118140960795 + 8053488 * 2 ^ 59
def prefixEnd_8053488 : Nat := 4983230072969 + 3 ^ 40 * 8053488 * 2
def baseEnd_8053488 : Nat := 4135310289216491924862689

theorem tailTrace_8053488 : CollatzResearch.WordTrace tailWord_8053488 prefixEnd_8053488 4135310289216491924862689 := by
  unfold tailWord_8053488
  simp only [CollatzResearch.WordTrace]
  refine ⟨146867419323797938546116559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195823225765063918061488745 146867419323797938546116559)
  ·
    refine ⟨220301128985696907819174839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146867419323797938546116559 220301128985696907819174839)
    ·
      refine ⟨330451693478545361728762259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220301128985696907819174839 330451693478545361728762259)
      ·
        refine ⟨495677540217818042593143389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330451693478545361728762259 495677540217818042593143389)
        ·
          refine ⟨185879077581681765972428771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495677540217818042593143389 185879077581681765972428771)
          ·
            refine ⟨278818616372522648958643157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185879077581681765972428771 278818616372522648958643157)
            ·
              refine ⟨6534811321230999584968199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278818616372522648958643157 6534811321230999584968199)
              ·
                refine ⟨9802216981846499377452299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534811321230999584968199 9802216981846499377452299)
                ·
                  refine ⟨14703325472769749066178449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802216981846499377452299 14703325472769749066178449)
                  ·
                    refine ⟨11027494104577311799633837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14703325472769749066178449 11027494104577311799633837)
                    ·
                      refine ⟨4135310289216491924862689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11027494104577311799633837 4135310289216491924862689)
                      ·
                        rfl

theorem cell23_8053488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3].length) (baseStart_8053488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053488 prefixEnd_8053488 := by exact prefixLift 8053488
  have htrace : WordTrace (prefixWord ++ tailWord_8053488) baseStart_8053488 baseEnd_8053488 := by
    simpa [prefixWord, tailWord_8053488, baseEnd_8053488] using wordTrace_append hprefix tailTrace_8053488
  have hstable : (prefixWord ++ tailWord_8053488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053488).length < 2 ^ (prefixWord ++ tailWord_8053488).sum := by decide
  have hdescent : baseEnd_8053488 < baseStart_8053488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053528 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_8053528 : Nat := 118140960795 + 8053528 * 2 ^ 59
def prefixEnd_8053528 : Nat := 4983230072969 + 3 ^ 40 * 8053528 * 2
def baseEnd_8053528 : Nat := 4135330828442671768362505

theorem tailTrace_8053528 : CollatzResearch.WordTrace tailWord_8053528 prefixEnd_8053528 4135330828442671768362505 := by
  unfold tailWord_8053528
  simp only [CollatzResearch.WordTrace]
  refine ⟨146868148783725481961844619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195824198378300642615792825 146868148783725481961844619)
  ·
    refine ⟨220302223175588222942766929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146868148783725481961844619 220302223175588222942766929)
    ·
      refine ⟨165226667381691167207075197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220302223175588222942766929 165226667381691167207075197)
      ·
        refine ⟨61960000268134187702653199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165226667381691167207075197 61960000268134187702653199)
        ·
          refine ⟨92940000402201281553979799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61960000268134187702653199 92940000402201281553979799)
          ·
            refine ⟨139410000603301922330969699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92940000402201281553979799 139410000603301922330969699)
            ·
              refine ⟨209115000904952883496454549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139410000603301922330969699 209115000904952883496454549)
              ·
                refine ⟨9802265667419666413896307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209115000904952883496454549 9802265667419666413896307)
                ·
                  refine ⟨14703398501129499620844461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802265667419666413896307 14703398501129499620844461)
                  ·
                    refine ⟨5513774437923562357816673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14703398501129499620844461 5513774437923562357816673)
                    ·
                      refine ⟨4135330828442671768362505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513774437923562357816673 4135330828442671768362505)
                      ·
                        rfl

theorem cell23_8053528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_8053528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053528 prefixEnd_8053528 := by exact prefixLift 8053528
  have htrace : WordTrace (prefixWord ++ tailWord_8053528) baseStart_8053528 baseEnd_8053528 := by
    simpa [prefixWord, tailWord_8053528, baseEnd_8053528] using wordTrace_append hprefix tailTrace_8053528
  have hstable : (prefixWord ++ tailWord_8053528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053528).length < 2 ^ (prefixWord ++ tailWord_8053528).sum := by decide
  have hdescent : baseEnd_8053528 < baseStart_8053528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053569 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8053569 : Nat := 118140960795 + 8053569 * 2 ^ 59
def prefixEnd_8053569 : Nat := 4983230072969 + 3 ^ 40 * 8053569 * 2
def baseEnd_8053569 : Nat := 4135351881149506107949817

theorem tailTrace_8053569 : CollatzResearch.WordTrace tailWord_8053569 prefixEnd_8053569 4135351881149506107949817 := by
  unfold tailWord_8053569
  simp only [CollatzResearch.WordTrace]
  refine ⟨293737792960302427925931761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195825195306868285283954507 293737792960302427925931761)
  ·
    refine ⟨220303344720226820944448821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293737792960302427925931761 220303344720226820944448821)
    ·
      refine ⟨20653438567521264463542077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220303344720226820944448821 20653438567521264463542077)
      ·
        refine ⟨7745039462820474173828279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20653438567521264463542077 7745039462820474173828279)
        ·
          refine ⟨11617559194230711260742419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745039462820474173828279 11617559194230711260742419)
          ·
            refine ⟨17426338791346066891113629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617559194230711260742419 17426338791346066891113629)
            ·
              refine ⟨6534877046754775084167611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17426338791346066891113629 6534877046754775084167611)
              ·
                refine ⟨9802315570132162626251417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6534877046754775084167611 9802315570132162626251417)
                ·
                  refine ⟨7351736677599121969688563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802315570132162626251417 7351736677599121969688563)
                  ·
                    refine ⟨11027605016398682954532845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7351736677599121969688563 11027605016398682954532845)
                    ·
                      refine ⟨4135351881149506107949817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11027605016398682954532845 4135351881149506107949817)
                      ·
                        rfl

theorem cell23_8053569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8053569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053569 prefixEnd_8053569 := by exact prefixLift 8053569
  have htrace : WordTrace (prefixWord ++ tailWord_8053569) baseStart_8053569 baseEnd_8053569 := by
    simpa [prefixWord, tailWord_8053569, baseEnd_8053569] using wordTrace_append hprefix tailTrace_8053569
  have hstable : (prefixWord ++ tailWord_8053569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053569).length < 2 ^ (prefixWord ++ tailWord_8053569).sum := by decide
  have hdescent : baseEnd_8053569 < baseStart_8053569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053621 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_8053621 : Nat := 118140960795 + 8053621 * 2 ^ 59
def prefixEnd_8053621 : Nat := 4983230072969 + 3 ^ 40 * 8053621 * 2
def baseEnd_8053621 : Nat := 4135378582143539904499577

theorem tailTrace_8053621 : CollatzResearch.WordTrace tailWord_8053621 prefixEnd_8053621 4135378582143539904499577 := by
  unfold tailWord_8053621
  simp only [CollatzResearch.WordTrace]
  refine ⟨293739689556114040806824717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195826459704076027204549811 293739689556114040806824717)
  ·
    refine ⟨110152383583542765302559269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293739689556114040806824717 110152383583542765302559269)
    ·
      refine ⟨20653571921914268494229863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110152383583542765302559269 20653571921914268494229863)
      ·
        refine ⟨30980357882871402741344795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20653571921914268494229863 30980357882871402741344795)
        ·
          refine ⟨46470536824307104112017193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30980357882871402741344795 46470536824307104112017193)
          ·
            refine ⟨34852902618230328084012895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46470536824307104112017193 34852902618230328084012895)
            ·
              refine ⟨52279353927345492126019343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34852902618230328084012895 52279353927345492126019343)
              ·
                refine ⟨78419030891018238189029015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52279353927345492126019343 78419030891018238189029015)
                ·
                  refine ⟨117628546336527357283543523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78419030891018238189029015 117628546336527357283543523)
                  ·
                    refine ⟨176442819504791035925315285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117628546336527357283543523 176442819504791035925315285)
                    ·
                      refine ⟨4135378582143539904499577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176442819504791035925315285 4135378582143539904499577)
                      ·
                        rfl

theorem cell23_8053621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_8053621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053621 prefixEnd_8053621 := by exact prefixLift 8053621
  have htrace : WordTrace (prefixWord ++ tailWord_8053621) baseStart_8053621 baseEnd_8053621 := by
    simpa [prefixWord, tailWord_8053621, baseEnd_8053621] using wordTrace_append hprefix tailTrace_8053621
  have hstable : (prefixWord ++ tailWord_8053621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053621).length < 2 ^ (prefixWord ++ tailWord_8053621).sum := by decide
  have hdescent : baseEnd_8053621 < baseStart_8053621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053624 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_8053624 : Nat := 118140960795 + 8053624 * 2 ^ 59
def prefixEnd_8053624 : Nat := 4983230072969 + 3 ^ 40 * 8053624 * 2
def baseEnd_8053624 : Nat := 1378460040861834464254021

theorem tailTrace_8053624 : CollatzResearch.WordTrace tailWord_8053624 prefixEnd_8053624 1378460040861834464254021 := by
  unfold tailWord_8053624
  simp only [CollatzResearch.WordTrace]
  refine ⟨146869899487551586159591963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195826532650068781546122617 146869899487551586159591963)
  ·
    refine ⟨220304849231327379239387945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146869899487551586159591963 220304849231327379239387945)
    ·
      refine ⟨165228636923495534429540959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220304849231327379239387945 165228636923495534429540959)
      ·
        refine ⟨247842955385243301644311439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165228636923495534429540959 247842955385243301644311439)
        ·
          refine ⟨371764433077864952466467159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247842955385243301644311439 371764433077864952466467159)
          ·
            refine ⟨557646649616797428699700739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371764433077864952466467159 557646649616797428699700739)
            ·
              refine ⟨836469974425196143049551109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557646649616797428699700739 836469974425196143049551109)
              ·
                refine ⟨156838120204724276821790833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836469974425196143049551109 156838120204724276821790833)
                ·
                  refine ⟨117628590153543207616343125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156838120204724276821790833 117628590153543207616343125)
                  ·
                    refine ⟨1378460040861834464254021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117628590153543207616343125 1378460040861834464254021)
                    ·
                      rfl

theorem cell23_8053624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_8053624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053624 prefixEnd_8053624 := by exact prefixLift 8053624
  have htrace : WordTrace (prefixWord ++ tailWord_8053624) baseStart_8053624 baseEnd_8053624 := by
    simpa [prefixWord, tailWord_8053624, baseEnd_8053624] using wordTrace_append hprefix tailTrace_8053624
  have hstable : (prefixWord ++ tailWord_8053624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053624).length < 2 ^ (prefixWord ++ tailWord_8053624).sum := by decide
  have hdescent : baseEnd_8053624 < baseStart_8053624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053661 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_8053661 : Nat := 118140960795 + 8053661 * 2 ^ 59
def prefixEnd_8053661 : Nat := 4983230072969 + 3 ^ 40 * 8053661 * 2
def baseEnd_8053661 : Nat := 4135399121369719747999393

theorem tailTrace_8053661 : CollatzResearch.WordTrace tailWord_8053661 prefixEnd_8053661 4135399121369719747999393 := by
  unfold tailWord_8053661
  simp only [CollatzResearch.WordTrace]
  refine ⟨293741148475969127638280837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195827432317312751758853891 293741148475969127638280837)
  ·
    refine ⟨55076465339244211432177657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293741148475969127638280837 55076465339244211432177657)
    ·
      refine ⟨41307349004433158574133243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55076465339244211432177657 41307349004433158574133243)
      ·
        refine ⟨61961023506649737861199865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41307349004433158574133243 61961023506649737861199865)
        ·
          refine ⟨46470767629987303395899899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61961023506649737861199865 46470767629987303395899899)
          ·
            refine ⟨69706151444980955093849849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46470767629987303395899899 69706151444980955093849849)
            ·
              refine ⟨52279613583735716320387387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69706151444980955093849849 52279613583735716320387387)
              ·
                refine ⟨78419420375603574480581081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52279613583735716320387387 78419420375603574480581081)
                ·
                  refine ⟨58814565281702680860435811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78419420375603574480581081 58814565281702680860435811)
                  ·
                    refine ⟨88221847922554021290653717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58814565281702680860435811 88221847922554021290653717)
                    ·
                      refine ⟨4135399121369719747999393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88221847922554021290653717 4135399121369719747999393)
                      ·
                        rfl

theorem cell23_8053661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_8053661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053661 prefixEnd_8053661 := by exact prefixLift 8053661
  have htrace : WordTrace (prefixWord ++ tailWord_8053661) baseStart_8053661 baseEnd_8053661 := by
    simpa [prefixWord, tailWord_8053661, baseEnd_8053661] using wordTrace_append hprefix tailTrace_8053661
  have hstable : (prefixWord ++ tailWord_8053661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053661).length < 2 ^ (prefixWord ++ tailWord_8053661).sum := by decide
  have hdescent : baseEnd_8053661 < baseStart_8053661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053668 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_8053668 : Nat := 118140960795 + 8053668 * 2 ^ 59
def prefixEnd_8053668 : Nat := 4983230072969 + 3 ^ 40 * 8053668 * 2
def baseEnd_8053668 : Nat := 4135402715734301220611861

theorem tailTrace_8053668 : CollatzResearch.WordTrace tailWord_8053668 prefixEnd_8053668 4135402715734301220611861 := by
  unfold tailWord_8053668
  simp only [CollatzResearch.WordTrace]
  refine ⟨146870701893471883916892829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195827602524629178555857105 146870701893471883916892829)
  ·
    refine ⟨55076513210051956468834811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146870701893471883916892829 55076513210051956468834811)
    ·
      refine ⟨82614769815077934703252217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55076513210051956468834811 82614769815077934703252217)
      ·
        refine ⟨61961077361308451027439163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82614769815077934703252217 61961077361308451027439163)
        ·
          refine ⟨92941616041962676541158745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61961077361308451027439163 92941616041962676541158745)
          ·
            refine ⟨69706212031472007405869059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92941616041962676541158745 69706212031472007405869059)
            ·
              refine ⟨104559318047208011108803589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69706212031472007405869059 104559318047208011108803589)
              ·
                refine ⟨19604872133851502082900673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104559318047208011108803589 19604872133851502082900673)
                ·
                  refine ⟨14703654100388626562175505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19604872133851502082900673 14703654100388626562175505)
                  ·
                    refine ⟨11027740575291469921631629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14703654100388626562175505 11027740575291469921631629)
                    ·
                      refine ⟨4135402715734301220611861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11027740575291469921631629 4135402715734301220611861)
                      ·
                        rfl

theorem cell23_8053668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_8053668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053668 prefixEnd_8053668 := by exact prefixLift 8053668
  have htrace : WordTrace (prefixWord ++ tailWord_8053668) baseStart_8053668 baseEnd_8053668 := by
    simpa [prefixWord, tailWord_8053668, baseEnd_8053668] using wordTrace_append hprefix tailTrace_8053668
  have hstable : (prefixWord ++ tailWord_8053668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053668).length < 2 ^ (prefixWord ++ tailWord_8053668).sum := by decide
  have hdescent : baseEnd_8053668 < baseStart_8053668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053799 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 2, 4]
def baseStart_8053799 : Nat := 118140960795 + 8053799 * 2 ^ 59
def prefixEnd_8053799 : Nat := 4983230072969 + 3 ^ 40 * 8053799 * 2
def baseEnd_8053799 : Nat := 1378489993900013402691253

theorem tailTrace_8053799 : CollatzResearch.WordTrace tailWord_8053799 prefixEnd_8053799 1378489993900013402691253 := by
  unfold tailWord_8053799
  simp only [CollatzResearch.WordTrace]
  refine ⟨293746181749469177206804451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195830787832979451471202967 293746181749469177206804451)
  ·
    refine ⟨440619272624203765810206677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293746181749469177206804451 440619272624203765810206677)
    ·
      refine ⟨10327014202129775761176719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 440619272624203765810206677 10327014202129775761176719)
      ·
        refine ⟨15490521303194663641765079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327014202129775761176719 15490521303194663641765079)
        ·
          refine ⟨23235781954791995462647619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15490521303194663641765079 23235781954791995462647619)
          ·
            refine ⟨34853672932187993193971429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23235781954791995462647619 34853672932187993193971429)
            ·
              refine ⟨6535063674785248723869643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34853672932187993193971429 6535063674785248723869643)
              ·
                refine ⟨9802595512177873085804465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535063674785248723869643 9802595512177873085804465)
                ·
                  refine ⟨7351946634133404814353349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802595512177873085804465 7351946634133404814353349)
                  ·
                    refine ⟨1378489993900013402691253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7351946634133404814353349 1378489993900013402691253)
                    ·
                      rfl

theorem cell23_8053799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_8053799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053799 prefixEnd_8053799 := by exact prefixLift 8053799
  have htrace : WordTrace (prefixWord ++ tailWord_8053799) baseStart_8053799 baseEnd_8053799 := by
    simpa [prefixWord, tailWord_8053799, baseEnd_8053799] using wordTrace_append hprefix tailTrace_8053799
  have hstable : (prefixWord ++ tailWord_8053799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053799).length < 2 ^ (prefixWord ++ tailWord_8053799).sum := by decide
  have hdescent : baseEnd_8053799 < baseStart_8053799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053811 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_8053811 : Nat := 118140960795 + 8053811 * 2 ^ 59
def prefixEnd_8053811 : Nat := 4983230072969 + 3 ^ 40 * 8053811 * 2
def baseEnd_8053811 : Nat := 4135476143467894161123703

theorem tailTrace_8053811 : CollatzResearch.WordTrace tailWord_8053811 prefixEnd_8053811 4135476143467894161123703 := by
  unfold tailWord_8053811
  simp only [CollatzResearch.WordTrace]
  refine ⟨293746619425425703256241287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195831079616950468837494191 293746619425425703256241287)
  ·
    refine ⟨440619929138138554884361931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293746619425425703256241287 440619929138138554884361931)
    ·
      refine ⟨660929893707207832326542897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440619929138138554884361931 660929893707207832326542897)
      ·
        refine ⟨495697420280405874244907173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660929893707207832326542897 495697420280405874244907173)
        ·
          refine ⟨92943266302576101420920095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495697420280405874244907173 92943266302576101420920095)
          ·
            refine ⟨139414899453864152131380143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92943266302576101420920095 139414899453864152131380143)
            ·
              refine ⟨209122349180796228197070215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139414899453864152131380143 209122349180796228197070215)
              ·
                refine ⟨313683523771194342295605323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209122349180796228197070215 313683523771194342295605323)
                ·
                  refine ⟨470525285656791513443407985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313683523771194342295605323 470525285656791513443407985)
                  ·
                    refine ⟨352893964242593635082555989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 470525285656791513443407985 352893964242593635082555989)
                    ·
                      refine ⟨4135476143467894161123703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 352893964242593635082555989 4135476143467894161123703)
                      ·
                        rfl

theorem cell23_8053811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_8053811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053811 prefixEnd_8053811 := by exact prefixLift 8053811
  have htrace : WordTrace (prefixWord ++ tailWord_8053811) baseStart_8053811 baseEnd_8053811 := by
    simpa [prefixWord, tailWord_8053811, baseEnd_8053811] using wordTrace_append hprefix tailTrace_8053811
  have hstable : (prefixWord ++ tailWord_8053811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053811).length < 2 ^ (prefixWord ++ tailWord_8053811).sum := by decide
  have hdescent : baseEnd_8053811 < baseStart_8053811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053822 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_8053822 : Nat := 118140960795 + 8053822 * 2 ^ 59
def prefixEnd_8053822 : Nat := 4983230072969 + 3 ^ 40 * 8053822 * 2
def baseEnd_8053822 : Nat := 4135481791755093618086153

theorem tailTrace_8053822 : CollatzResearch.WordTrace tailWord_8053822 prefixEnd_8053822 4135481791755093618086153 := by
  unfold tailWord_8053822
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718377578548231516861465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195831347085590568089927813 36718377578548231516861465)
  ·
    refine ⟨27538783183911173637646099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36718377578548231516861465 27538783183911173637646099)
    ·
      refine ⟨41308174775866760456469149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27538783183911173637646099 41308174775866760456469149)
      ·
        refine ⟨15490565540950035171175931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41308174775866760456469149 15490565540950035171175931)
        ·
          refine ⟨23235848311425052756763897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15490565540950035171175931 23235848311425052756763897)
          ·
            refine ⟨17426886233568789567572923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23235848311425052756763897 17426886233568789567572923)
            ·
              refine ⟨26140329350353184351359385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17426886233568789567572923 26140329350353184351359385)
              ·
                refine ⟨19605247012764888263519539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26140329350353184351359385 19605247012764888263519539)
                ·
                  refine ⟨29407870519147332395279309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19605247012764888263519539 29407870519147332395279309)
                  ·
                    refine ⟨11027951444680249648229741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29407870519147332395279309 11027951444680249648229741)
                    ·
                      refine ⟨4135481791755093618086153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11027951444680249648229741 4135481791755093618086153)
                      ·
                        rfl

theorem cell23_8053822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_8053822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053822 prefixEnd_8053822 := by exact prefixLift 8053822
  have htrace : WordTrace (prefixWord ++ tailWord_8053822) baseStart_8053822 baseEnd_8053822 := by
    simpa [prefixWord, tailWord_8053822, baseEnd_8053822] using wordTrace_append hprefix tailTrace_8053822
  have hstable : (prefixWord ++ tailWord_8053822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053822).length < 2 ^ (prefixWord ++ tailWord_8053822).sum := by decide
  have hdescent : baseEnd_8053822 < baseStart_8053822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053838 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_8053838 : Nat := 118140960795 + 8053838 * 2 ^ 59
def prefixEnd_8053838 : Nat := 4983230072969 + 3 ^ 40 * 8053838 * 2
def baseEnd_8053838 : Nat := 1378496669148521851828693

theorem tailTrace_8053838 : CollatzResearch.WordTrace tailWord_8053838 prefixEnd_8053838 1378496669148521851828693 := by
  unfold tailWord_8053838
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718450524540985858434271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195831736130885257911649445 36718450524540985858434271)
  ·
    refine ⟨55077675786811478787651407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36718450524540985858434271 55077675786811478787651407)
    ·
      refine ⟨82616513680217218181477111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55077675786811478787651407 82616513680217218181477111)
      ·
        refine ⟨123924770520325827272215667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82616513680217218181477111 123924770520325827272215667)
        ·
          refine ⟨185887155780488740908323501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123924770520325827272215667 185887155780488740908323501)
          ·
            refine ⟨69707683417683277840621313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185887155780488740908323501 69707683417683277840621313)
            ·
              refine ⟨52280762563262458380465985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69707683417683277840621313 52280762563262458380465985)
              ·
                refine ⟨39210571922446843785349489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52280762563262458380465985 39210571922446843785349489)
                ·
                  refine ⟨29407928941835132839012117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39210571922446843785349489 29407928941835132839012117)
                  ·
                    refine ⟨1378496669148521851828693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29407928941835132839012117 1378496669148521851828693)
                    ·
                      rfl

theorem cell23_8053838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_8053838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053838 prefixEnd_8053838 := by exact prefixLift 8053838
  have htrace : WordTrace (prefixWord ++ tailWord_8053838) baseStart_8053838 baseEnd_8053838 := by
    simpa [prefixWord, tailWord_8053838, baseEnd_8053838] using wordTrace_append hprefix tailTrace_8053838
  have hstable : (prefixWord ++ tailWord_8053838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053838).length < 2 ^ (prefixWord ++ tailWord_8053838).sum := by decide
  have hdescent : baseEnd_8053838 < baseStart_8053838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053845 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_8053845 : Nat := 118140960795 + 8053845 * 2 ^ 59
def prefixEnd_8053845 : Nat := 4983230072969 + 3 ^ 40 * 8053845 * 2
def baseEnd_8053845 : Nat := 4135493601810147028098547

theorem tailTrace_8053845 : CollatzResearch.WordTrace tailWord_8053845 prefixEnd_8053845 4135493601810147028098547 := by
  unfold tailWord_8053845
  simp only [CollatzResearch.WordTrace]
  refine ⟨293747859507302527062978989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195831906338201684708652659 293747859507302527062978989)
  ·
    refine ⟨110155447315238447648617121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293747859507302527062978989 110155447315238447648617121)
    ·
      refine ⟨82616585486428835736462841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110155447315238447648617121 82616585486428835736462841)
      ·
        refine ⟨61962439114821626802347131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82616585486428835736462841 61962439114821626802347131)
        ·
          refine ⟨92943658672232440203520697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61962439114821626802347131 92943658672232440203520697)
          ·
            refine ⟨69707744004174330152640523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92943658672232440203520697 69707744004174330152640523)
            ·
              refine ⟨104561616006261495228960785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69707744004174330152640523 104561616006261495228960785)
              ·
                refine ⟨78421212004696121421720589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104561616006261495228960785 78421212004696121421720589)
                ·
                  refine ⟨29407954501761045533145221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78421212004696121421720589 29407954501761045533145221)
                  ·
                    refine ⟨5513991469080196037464729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29407954501761045533145221 5513991469080196037464729)
                    ·
                      refine ⟨4135493601810147028098547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5513991469080196037464729 4135493601810147028098547)
                      ·
                        rfl

theorem cell23_8053845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_8053845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053845 prefixEnd_8053845 := by exact prefixLift 8053845
  have htrace : WordTrace (prefixWord ++ tailWord_8053845) baseStart_8053845 baseEnd_8053845 := by
    simpa [prefixWord, tailWord_8053845, baseEnd_8053845] using wordTrace_append hprefix tailTrace_8053845
  have hstable : (prefixWord ++ tailWord_8053845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053845).length < 2 ^ (prefixWord ++ tailWord_8053845).sum := by decide
  have hdescent : baseEnd_8053845 < baseStart_8053845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053848 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_8053848 : Nat := 118140960795 + 8053848 * 2 ^ 59
def prefixEnd_8053848 : Nat := 4983230072969 + 3 ^ 40 * 8053848 * 2
def baseEnd_8053848 : Nat := 4135495142252110516361033

theorem tailTrace_8053848 : CollatzResearch.WordTrace tailWord_8053848 prefixEnd_8053848 4135495142252110516361033 := by
  unfold tailWord_8053848
  simp only [CollatzResearch.WordTrace]
  refine ⟨146873984463145829287669099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195831979284194439050225465 146873984463145829287669099)
  ·
    refine ⟨220310976694718743931503649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146873984463145829287669099 220310976694718743931503649)
    ·
      refine ⟨165233232521039057948627737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220310976694718743931503649 165233232521039057948627737)
      ·
        refine ⟨123924924390779293461470803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165233232521039057948627737 123924924390779293461470803)
        ·
          refine ⟨185887386586168940192206205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123924924390779293461470803 185887386586168940192206205)
          ·
            refine ⟨69707769969813352572077327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185887386586168940192206205 69707769969813352572077327)
            ·
              refine ⟨104561654954720028858115991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69707769969813352572077327 104561654954720028858115991)
              ·
                refine ⟨156842482432080043287173987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104561654954720028858115991 156842482432080043287173987)
                ·
                  refine ⟨235263723648120064930760981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156842482432080043287173987 235263723648120064930760981)
                  ·
                    refine ⟨11027987046005628043629421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 235263723648120064930760981 11027987046005628043629421)
                    ·
                      refine ⟨4135495142252110516361033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11027987046005628043629421 4135495142252110516361033)
                      ·
                        rfl

theorem cell23_8053848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_8053848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053848 prefixEnd_8053848 := by exact prefixLift 8053848
  have htrace : WordTrace (prefixWord ++ tailWord_8053848) baseStart_8053848 baseEnd_8053848 := by
    simpa [prefixWord, tailWord_8053848, baseEnd_8053848] using wordTrace_append hprefix tailTrace_8053848
  have hstable : (prefixWord ++ tailWord_8053848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053848).length < 2 ^ (prefixWord ++ tailWord_8053848).sum := by decide
  have hdescent : baseEnd_8053848 < baseStart_8053848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053868 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 7]
def baseStart_8053868 : Nat := 118140960795 + 8053868 * 2 ^ 59
def prefixEnd_8053868 : Nat := 4983230072969 + 3 ^ 40 * 8053868 * 2
def baseEnd_8053868 : Nat := 459500601318355604234549

theorem tailTrace_8053868 : CollatzResearch.WordTrace tailWord_8053868 prefixEnd_8053868 459500601318355604234549 := by
  unfold tailWord_8053868
  simp only [CollatzResearch.WordTrace]
  refine ⟨146874349193109600995533129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195832465590812801327377505 146874349193109600995533129)
  ·
    refine ⟨110155761894832200746649847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146874349193109600995533129 110155761894832200746649847)
    ·
      refine ⟨165233642842248301119974771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110155761894832200746649847 165233642842248301119974771)
      ·
        refine ⟨247850464263372451679962157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165233642842248301119974771 247850464263372451679962157)
        ·
          refine ⟨92943924098764669379985809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247850464263372451679962157 92943924098764669379985809)
          ·
            refine ⟨69707943074073502034989357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92943924098764669379985809 69707943074073502034989357)
            ·
              refine ⟨26140478652777563263121009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69707943074073502034989357 26140478652777563263121009)
              ·
                refine ⟨19605358989583172447340757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26140478652777563263121009 19605358989583172447340757)
                ·
                  refine ⟨459500601318355604234549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19605358989583172447340757 459500601318355604234549)
                  ·
                    rfl

theorem cell23_8053868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_8053868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053868 prefixEnd_8053868 := by exact prefixLift 8053868
  have htrace : WordTrace (prefixWord ++ tailWord_8053868) baseStart_8053868 baseEnd_8053868 := by
    simpa [prefixWord, tailWord_8053868, baseEnd_8053868] using wordTrace_append hprefix tailTrace_8053868
  have hstable : (prefixWord ++ tailWord_8053868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053868).length < 2 ^ (prefixWord ++ tailWord_8053868).sum := by decide
  have hdescent : baseEnd_8053868 < baseStart_8053868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053902 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_8053902 : Nat := 118140960795 + 8053902 * 2 ^ 59
def prefixEnd_8053902 : Nat := 4983230072969 + 3 ^ 40 * 8053902 * 2
def baseEnd_8053902 : Nat := 459502541134161478342865

theorem tailTrace_8053902 : CollatzResearch.WordTrace tailWord_8053902 prefixEnd_8053902 459502541134161478342865 := by
  unfold tailWord_8053902
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718742308512003224725495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195833292312064017198535973 36718742308512003224725495)
  ·
    refine ⟨55078113462768004837088243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36718742308512003224725495 55078113462768004837088243)
    ·
      refine ⟨82617170194152007255632365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55078113462768004837088243 82617170194152007255632365)
      ·
        refine ⟨30981438822807002720862137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82617170194152007255632365 30981438822807002720862137)
        ·
          refine ⟨23236079117105252040646603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30981438822807002720862137 23236079117105252040646603)
          ·
            refine ⟨34854118675657878060969905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23236079117105252040646603 34854118675657878060969905)
            ·
              refine ⟨26140589006743408545727429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34854118675657878060969905 26140589006743408545727429)
              ·
                refine ⟨4901360438764389102323893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26140589006743408545727429 4901360438764389102323893)
                ·
                  refine ⟨459502541134161478342865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4901360438764389102323893 459502541134161478342865)
                  ·
                    rfl

theorem cell23_8053902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_8053902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053902 prefixEnd_8053902 := by exact prefixLift 8053902
  have htrace : WordTrace (prefixWord ++ tailWord_8053902) baseStart_8053902 baseEnd_8053902 := by
    simpa [prefixWord, tailWord_8053902, baseEnd_8053902] using wordTrace_append hprefix tailTrace_8053902
  have hstable : (prefixWord ++ tailWord_8053902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053902).length < 2 ^ (prefixWord ++ tailWord_8053902).sum := by decide
  have hdescent : baseEnd_8053902 < baseStart_8053902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053935 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 6, 2]
def baseStart_8053935 : Nat := 118140960795 + 8053935 * 2 ^ 59
def prefixEnd_8053935 : Nat := 4983230072969 + 3 ^ 40 * 8053935 * 2
def baseEnd_8053935 : Nat := 4135539815069051675973133

theorem tailTrace_8053935 : CollatzResearch.WordTrace tailWord_8053935 prefixEnd_8053935 4135539815069051675973133 := by
  unfold tailWord_8053935
  simp only [CollatzResearch.WordTrace]
  refine ⟨293751142076976472433755259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195834094717984314955836839 293751142076976472433755259)
  ·
    refine ⟨440626713115464708650632889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293751142076976472433755259 440626713115464708650632889)
    ·
      refine ⟨330470034836598531487974667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440626713115464708650632889 330470034836598531487974667)
      ·
        refine ⟨495705052254897797231962001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330470034836598531487974667 495705052254897797231962001)
        ·
          refine ⟨371778789191173347923971501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495705052254897797231962001 371778789191173347923971501)
          ·
            refine ⟨139417045946690005471489313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371778789191173347923971501 139417045946690005471489313)
            ·
              refine ⟨104562784460017504103616985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139417045946690005471489313 104562784460017504103616985)
              ·
                refine ⟨78422088345013128077712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104562784460017504103616985 78422088345013128077712739)
                ·
                  refine ⟨117633132517519692116569109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78422088345013128077712739 117633132517519692116569109)
                  ·
                    refine ⟨5514053086758735567964177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117633132517519692116569109 5514053086758735567964177)
                    ·
                      refine ⟨4135539815069051675973133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514053086758735567964177 4135539815069051675973133)
                      ·
                        rfl

theorem cell23_8053935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 6, 2].length) (baseStart_8053935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053935 prefixEnd_8053935 := by exact prefixLift 8053935
  have htrace : WordTrace (prefixWord ++ tailWord_8053935) baseStart_8053935 baseEnd_8053935 := by
    simpa [prefixWord, tailWord_8053935, baseEnd_8053935] using wordTrace_append hprefix tailTrace_8053935
  have hstable : (prefixWord ++ tailWord_8053935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053935).length < 2 ^ (prefixWord ++ tailWord_8053935).sum := by decide
  have hdescent : baseEnd_8053935 < baseStart_8053935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053952 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_8053952 : Nat := 118140960795 + 8053952 * 2 ^ 59
def prefixEnd_8053952 : Nat := 4983230072969 + 3 ^ 40 * 8053952 * 2
def baseEnd_8053952 : Nat := 4135548544240178109460555

theorem tailTrace_8053952 : CollatzResearch.WordTrace tailWord_8053952 prefixEnd_8053952 4135548544240178109460555 := by
  unfold tailWord_8053952
  simp only [CollatzResearch.WordTrace]
  refine ⟨146875881058957442168562055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195834508078609922891416073 146875881058957442168562055)
  ·
    refine ⟨220313821588436163252843083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146875881058957442168562055 220313821588436163252843083)
    ·
      refine ⟨330470732382654244879264625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220313821588436163252843083 330470732382654244879264625)
      ·
        refine ⟨247853049286990683659448469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330470732382654244879264625 247853049286990683659448469)
        ·
          refine ⟨11618111685327688296536647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247853049286990683659448469 11618111685327688296536647)
          ·
            refine ⟨17427167527991532444804971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618111685327688296536647 17427167527991532444804971)
            ·
              refine ⟨26140751291987298667207457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17427167527991532444804971 26140751291987298667207457)
              ·
                refine ⟨19605563468990474000405593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26140751291987298667207457 19605563468990474000405593)
                ·
                  refine ⟨14704172601742855500304195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19605563468990474000405593 14704172601742855500304195)
                  ·
                    refine ⟨22056258902614283250456293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14704172601742855500304195 22056258902614283250456293)
                    ·
                      refine ⟨4135548544240178109460555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22056258902614283250456293 4135548544240178109460555)
                      ·
                        rfl

theorem cell23_8053952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_8053952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053952 prefixEnd_8053952 := by exact prefixLift 8053952
  have htrace : WordTrace (prefixWord ++ tailWord_8053952) baseStart_8053952 baseEnd_8053952 := by
    simpa [prefixWord, tailWord_8053952, baseEnd_8053952] using wordTrace_append hprefix tailTrace_8053952
  have hstable : (prefixWord ++ tailWord_8053952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053952).length < 2 ^ (prefixWord ++ tailWord_8053952).sum := by decide
  have hdescent : baseEnd_8053952 < baseStart_8053952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053962 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_8053962 : Nat := 118140960795 + 8053962 * 2 ^ 59
def prefixEnd_8053962 : Nat := 4983230072969 + 3 ^ 40 * 8053962 * 2
def baseEnd_8053962 : Nat := 1378517893015574356778503

theorem tailTrace_8053962 : CollatzResearch.WordTrace tailWord_8053962 prefixEnd_8053962 1378517893015574356778503 := by
  unfold tailWord_8053962
  simp only [CollatzResearch.WordTrace]
  refine ⟨73438031711969664011247035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195834751231919104029992093 73438031711969664011247035)
  ·
    refine ⟨110157047567954496016870553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73438031711969664011247035 110157047567954496016870553)
    ·
      refine ⟨82617785675965872012652915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110157047567954496016870553 82617785675965872012652915)
      ·
        refine ⟨123926678513948808018979373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82617785675965872012652915 123926678513948808018979373)
        ·
          refine ⟨46472504442730803007117265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123926678513948808018979373 46472504442730803007117265)
          ·
            refine ⟨34854378332048102255337949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46472504442730803007117265 34854378332048102255337949)
            ·
              refine ⟨13070391874518038345751731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34854378332048102255337949 13070391874518038345751731)
              ·
                refine ⟨19605587811777057518627597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070391874518038345751731 19605587811777057518627597)
                ·
                  refine ⟨7352095429416396569485349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19605587811777057518627597 7352095429416396569485349)
                  ·
                    refine ⟨1378517893015574356778503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352095429416396569485349 1378517893015574356778503)
                    ·
                      rfl

theorem cell23_8053962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_8053962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053962 prefixEnd_8053962 := by exact prefixLift 8053962
  have htrace : WordTrace (prefixWord ++ tailWord_8053962) baseStart_8053962 baseEnd_8053962 := by
    simpa [prefixWord, tailWord_8053962, baseEnd_8053962] using wordTrace_append hprefix tailTrace_8053962
  have hstable : (prefixWord ++ tailWord_8053962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053962).length < 2 ^ (prefixWord ++ tailWord_8053962).sum := by decide
  have hdescent : baseEnd_8053962 < baseStart_8053962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8053989 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_8053989 : Nat := 118140960795 + 8053989 * 2 ^ 59
def prefixEnd_8053989 : Nat := 4983230072969 + 3 ^ 40 * 8053989 * 2
def baseEnd_8053989 : Nat := 4135567543024394464697885

theorem tailTrace_8053989 : CollatzResearch.WordTrace tailWord_8053989 prefixEnd_8053989 4135567543024394464697885 := by
  unfold tailWord_8053989
  simp only [CollatzResearch.WordTrace]
  refine ⟨293753111618780839656221021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195835407745853893104147347 293753111618780839656221021)
  ·
    refine ⟨110157416857042814871082883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293753111618780839656221021 110157416857042814871082883)
    ·
      refine ⟨165236125285564222306624325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110157416857042814871082883 165236125285564222306624325)
      ·
        refine ⟨30981773491043291682492061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165236125285564222306624325 30981773491043291682492061)
        ·
          refine ⟨11618165059141234380934523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30981773491043291682492061 11618165059141234380934523)
          ·
            refine ⟨17427247588711851571401785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618165059141234380934523 17427247588711851571401785)
            ·
              refine ⟨13070435691533888678551339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17427247588711851571401785 13070435691533888678551339)
              ·
                refine ⟨19605653537300833017827009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070435691533888678551339 19605653537300833017827009)
                ·
                  refine ⟨14704240152975624763370257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19605653537300833017827009 14704240152975624763370257)
                  ·
                    refine ⟨11028180114731718572527693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14704240152975624763370257 11028180114731718572527693)
                    ·
                      refine ⟨4135567543024394464697885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11028180114731718572527693 4135567543024394464697885)
                      ·
                        rfl

theorem cell23_8053989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_8053989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8053989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8053989 prefixEnd_8053989 := by exact prefixLift 8053989
  have htrace : WordTrace (prefixWord ++ tailWord_8053989) baseStart_8053989 baseEnd_8053989 := by
    simpa [prefixWord, tailWord_8053989, baseEnd_8053989] using wordTrace_append hprefix tailTrace_8053989
  have hstable : (prefixWord ++ tailWord_8053989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8053989).length < 2 ^ (prefixWord ++ tailWord_8053989).sum := by decide
  have hdescent : baseEnd_8053989 < baseStart_8053989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8053989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054025 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_8054025 : Nat := 118140960795 + 8054025 * 2 ^ 59
def prefixEnd_8054025 : Nat := 4983230072969 + 3 ^ 40 * 8054025 * 2
def baseEnd_8054025 : Nat := 4135586028327956323847719

theorem tailTrace_8054025 : CollatzResearch.WordTrace tailWord_8054025 prefixEnd_8054025 4135586028327956323847719 := by
  unfold tailWord_8054025
  simp only [CollatzResearch.WordTrace]
  refine ⟨293754424646650417804531529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195836283097766945203021019 293754424646650417804531529)
  ·
    refine ⟨220315818484987813353398647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293754424646650417804531529 220315818484987813353398647)
    ·
      refine ⟨330473727727481720030097971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220315818484987813353398647 330473727727481720030097971)
      ·
        refine ⟨495710591591222580045146957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330473727727481720030097971 495710591591222580045146957)
        ·
          refine ⟨185891471846708467516930109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495710591591222580045146957 185891471846708467516930109)
          ·
            refine ⟨69709301942515675318848791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185891471846708467516930109 69709301942515675318848791)
            ·
              refine ⟨104563952913773512978273187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69709301942515675318848791 104563952913773512978273187)
              ·
                refine ⟨156845929370660269467409781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104563952913773512978273187 156845929370660269467409781)
                ·
                  refine ⟨14704305878499400262569667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156845929370660269467409781 14704305878499400262569667)
                  ·
                    refine ⟨22056458817749100393854501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14704305878499400262569667 22056458817749100393854501)
                    ·
                      refine ⟨4135586028327956323847719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22056458817749100393854501 4135586028327956323847719)
                      ·
                        rfl

theorem cell23_8054025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_8054025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054025 prefixEnd_8054025 := by exact prefixLift 8054025
  have htrace : WordTrace (prefixWord ++ tailWord_8054025) baseStart_8054025 baseEnd_8054025 := by
    simpa [prefixWord, tailWord_8054025, baseEnd_8054025] using wordTrace_append hprefix tailTrace_8054025
  have hstable : (prefixWord ++ tailWord_8054025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054025).length < 2 ^ (prefixWord ++ tailWord_8054025).sum := by decide
  have hdescent : baseEnd_8054025 < baseStart_8054025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054035 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 8, 4]
def baseStart_8054035 : Nat := 118140960795 + 8054035 * 2 ^ 59
def prefixEnd_8054035 : Nat := 4983230072969 + 3 ^ 40 * 8054035 * 2
def baseEnd_8054035 : Nat := 1378530387711500428240891

theorem tailTrace_8054035 : CollatzResearch.WordTrace tailWord_8054035 prefixEnd_8054035 1378530387711500428240891 := by
  unfold tailWord_8054035
  simp only [CollatzResearch.WordTrace]
  refine ⟨293754789376614189512395559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195836526251076126341597039 293754789376614189512395559)
  ·
    refine ⟨440632184064921284268593339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293754789376614189512395559 440632184064921284268593339)
    ·
      refine ⟨660948276097381926402890009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440632184064921284268593339 660948276097381926402890009)
      ·
        refine ⟨495711207073036444802167507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660948276097381926402890009 495711207073036444802167507)
        ·
          refine ⟨743566810609554667203251261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495711207073036444802167507 743566810609554667203251261)
          ·
            refine ⟨278837553978583000201219223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743566810609554667203251261 278837553978583000201219223)
            ·
              refine ⟨418256330967874500301828835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278837553978583000201219223 418256330967874500301828835)
              ·
                refine ⟨627384496451811750452743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418256330967874500301828835 627384496451811750452743253)
                ·
                  refine ⟨7352162067794668950618085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 627384496451811750452743253 7352162067794668950618085)
                  ·
                    refine ⟨1378530387711500428240891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352162067794668950618085 1378530387711500428240891)
                    ·
                      rfl

theorem cell23_8054035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 4].length) (baseStart_8054035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054035 prefixEnd_8054035 := by exact prefixLift 8054035
  have htrace : WordTrace (prefixWord ++ tailWord_8054035) baseStart_8054035 baseEnd_8054035 := by
    simpa [prefixWord, tailWord_8054035, baseEnd_8054035] using wordTrace_append hprefix tailTrace_8054035
  have hstable : (prefixWord ++ tailWord_8054035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054035).length < 2 ^ (prefixWord ++ tailWord_8054035).sum := by decide
  have hdescent : baseEnd_8054035 < baseStart_8054035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054042 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_8054042 : Nat := 118140960795 + 8054042 * 2 ^ 59
def prefixEnd_8054042 : Nat := 4983230072969 + 3 ^ 40 * 8054042 * 2
def baseEnd_8054042 : Nat := 4135594757499082757335141

theorem tailTrace_8054042 : CollatzResearch.WordTrace tailWord_8054042 prefixEnd_8054042 4135594757499082757335141 := by
  unfold tailWord_8054042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73438761171897207426975095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195836696458392553138600253 73438761171897207426975095)
  ·
    refine ⟨110158141757845811140462643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73438761171897207426975095 110158141757845811140462643)
    ·
      refine ⟨165237212636768716710693965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110158141757845811140462643 165237212636768716710693965)
      ·
        refine ⟨61963954738788268766510237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165237212636768716710693965 61963954738788268766510237)
        ·
          refine ⟨23236483027045600787441339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61963954738788268766510237 23236483027045600787441339)
          ·
            refine ⟨34854724540568401181162009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23236483027045600787441339 34854724540568401181162009)
            ·
              refine ⟨26141043405426300885871507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34854724540568401181162009 26141043405426300885871507)
              ·
                refine ⟨39211565108139451328807261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26141043405426300885871507 39211565108139451328807261)
                ·
                  refine ⟨14704336915552294248302723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39211565108139451328807261 14704336915552294248302723)
                  ·
                    refine ⟨22056505373328441372454085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14704336915552294248302723 22056505373328441372454085)
                    ·
                      refine ⟨4135594757499082757335141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22056505373328441372454085 4135594757499082757335141)
                      ·
                        rfl

theorem cell23_8054042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_8054042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054042 prefixEnd_8054042 := by exact prefixLift 8054042
  have htrace : WordTrace (prefixWord ++ tailWord_8054042) baseStart_8054042 baseEnd_8054042 := by
    simpa [prefixWord, tailWord_8054042, baseEnd_8054042] using wordTrace_append hprefix tailTrace_8054042
  have hstable : (prefixWord ++ tailWord_8054042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054042).length < 2 ^ (prefixWord ++ tailWord_8054042).sum := by decide
  have hdescent : baseEnd_8054042 < baseStart_8054042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054052 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_8054052 : Nat := 118140960795 + 8054052 * 2 ^ 59
def prefixEnd_8054052 : Nat := 4983230072969 + 3 ^ 40 * 8054052 * 2
def baseEnd_8054052 : Nat := 1378533297435209239403365

theorem tailTrace_8054052 : CollatzResearch.WordTrace tailWord_8054052 prefixEnd_8054052 1378533297435209239403365 := by
  unfold tailWord_8054052
  simp only [CollatzResearch.WordTrace]
  refine ⟨146877704708776300707882205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195836939611701734277176273 146877704708776300707882205)
  ·
    refine ⟨55079139265791112765455827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146877704708776300707882205 55079139265791112765455827)
    ·
      refine ⟨82618708898686669148183741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55079139265791112765455827 82618708898686669148183741)
      ·
        refine ⟨30982015837007500930568903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82618708898686669148183741 30982015837007500930568903)
        ·
          refine ⟨46473023755511251395853355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982015837007500930568903 46473023755511251395853355)
          ·
            refine ⟨69709535633266877093780033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46473023755511251395853355 69709535633266877093780033)
            ·
              refine ⟨52282151724950157820335025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69709535633266877093780033 52282151724950157820335025)
              ·
                refine ⟨39211613793712618365251269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52282151724950157820335025 39211613793712618365251269)
                ·
                  refine ⟨7352177586321115943484613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39211613793712618365251269 7352177586321115943484613)
                  ·
                    refine ⟨1378533297435209239403365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352177586321115943484613 1378533297435209239403365)
                    ·
                      rfl

theorem cell23_8054052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_8054052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054052 prefixEnd_8054052 := by exact prefixLift 8054052
  have htrace : WordTrace (prefixWord ++ tailWord_8054052) baseStart_8054052 baseEnd_8054052 := by
    simpa [prefixWord, tailWord_8054052, baseEnd_8054052] using wordTrace_append hprefix tailTrace_8054052
  have hstable : (prefixWord ++ tailWord_8054052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054052).length < 2 ^ (prefixWord ++ tailWord_8054052).sum := by decide
  have hdescent : baseEnd_8054052 < baseStart_8054052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054056 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 1, 5]
def baseStart_8054056 : Nat := 118140960795 + 8054056 * 2 ^ 59
def prefixEnd_8054056 : Nat := 4983230072969 + 3 ^ 40 * 8054056 * 2
def baseEnd_8054056 : Nat := 1378533982076081900853359

theorem tailTrace_8054056 : CollatzResearch.WordTrace tailWord_8054056 prefixEnd_8054056 1378533982076081900853359 := by
  unfold tailWord_8054056
  simp only [CollatzResearch.WordTrace]
  refine ⟨146877777654769055049455011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195837036873025406732606681 146877777654769055049455011)
  ·
    refine ⟨220316666482153582574182517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146877777654769055049455011 220316666482153582574182517)
    ·
      refine ⟨20654687482701898366329611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220316666482153582574182517 20654687482701898366329611)
      ·
        refine ⟨30982031224052847549494417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20654687482701898366329611 30982031224052847549494417)
        ·
          refine ⟨23236523418039635662120813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30982031224052847549494417 23236523418039635662120813)
          ·
            refine ⟨8713696281764863373295305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23236523418039635662120813 8713696281764863373295305)
            ·
              refine ⟨6535272211323647529971479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8713696281764863373295305 6535272211323647529971479)
              ·
                refine ⟨9802908316985471294957219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535272211323647529971479 9802908316985471294957219)
                ·
                  refine ⟨14704362475478206942435829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802908316985471294957219 14704362475478206942435829)
                  ·
                    refine ⟨1378533982076081900853359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14704362475478206942435829 1378533982076081900853359)
                    ·
                      rfl

theorem cell23_8054056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_8054056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054056 prefixEnd_8054056 := by exact prefixLift 8054056
  have htrace : WordTrace (prefixWord ++ tailWord_8054056) baseStart_8054056 baseEnd_8054056 := by
    simpa [prefixWord, tailWord_8054056, baseEnd_8054056] using wordTrace_append hprefix tailTrace_8054056
  have hstable : (prefixWord ++ tailWord_8054056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054056).length < 2 ^ (prefixWord ++ tailWord_8054056).sum := by decide
  have hdescent : baseEnd_8054056 < baseStart_8054056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054065 : List Nat := [1, 2, 2, 3, 3, 2, 10]
def baseStart_8054065 : Nat := 118140960795 + 8054065 * 2 ^ 59
def prefixEnd_8054065 : Nat := 4983230072969 + 3 ^ 40 * 8054065 * 2
def baseEnd_8054065 : Nat := 51056871204372051448735

theorem tailTrace_8054065 : CollatzResearch.WordTrace tailWord_8054065 prefixEnd_8054065 51056871204372051448735 := by
  unfold tailWord_8054065
  simp only [CollatzResearch.WordTrace]
  refine ⟨293755883566505504635987649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195837255711003669757325099 293755883566505504635987649)
  ·
    refine ⟨220316912674879128476990737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293755883566505504635987649 220316912674879128476990737)
    ·
      refine ⟨165237684506159346357743053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220316912674879128476990737 165237684506159346357743053)
      ·
        refine ⟨61964131689809754884153645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165237684506159346357743053 61964131689809754884153645)
        ·
          refine ⟨23236549383678658081557617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61964131689809754884153645 23236549383678658081557617)
          ·
            refine ⟨17427412037758993561168213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23236549383678658081557617 17427412037758993561168213)
            ·
              refine ⟨51056871204372051448735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17427412037758993561168213 51056871204372051448735)
              ·
                rfl

theorem cell23_8054065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 10].length) (baseStart_8054065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054065 prefixEnd_8054065 := by exact prefixLift 8054065
  have htrace : WordTrace (prefixWord ++ tailWord_8054065) baseStart_8054065 baseEnd_8054065 := by
    simpa [prefixWord, tailWord_8054065, baseEnd_8054065] using wordTrace_append hprefix tailTrace_8054065
  have hstable : (prefixWord ++ tailWord_8054065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054065).length < 2 ^ (prefixWord ++ tailWord_8054065).sum := by decide
  have hdescent : baseEnd_8054065 < baseStart_8054065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054069 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_8054069 : Nat := 118140960795 + 8054069 * 2 ^ 59
def prefixEnd_8054069 : Nat := 4983230072969 + 3 ^ 40 * 8054069 * 2
def baseEnd_8054069 : Nat := 1378536207158918050565839

theorem tailTrace_8054069 : CollatzResearch.WordTrace tailWord_8054069 prefixEnd_8054069 1378536207158918050565839 := by
  unfold tailWord_8054069
  simp only [CollatzResearch.WordTrace]
  refine ⟨293756029458491013319133261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195837352972327342212755507 293756029458491013319133261)
  ·
    refine ⟨110158511046934129994674973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293756029458491013319133261 110158511046934129994674973)
    ·
      refine ⟨41309441642600298748003115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110158511046934129994674973 41309441642600298748003115)
      ·
        refine ⟨61964162463900448122004673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41309441642600298748003115 61964162463900448122004673)
        ·
          refine ⟨46473121847925336091503505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61964162463900448122004673 46473121847925336091503505)
          ·
            refine ⟨34854841385944002068627629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46473121847925336091503505 34854841385944002068627629)
            ·
              refine ⟨13070565519729000775735361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34854841385944002068627629 13070565519729000775735361)
              ·
                refine ⟨9802924139796750581801521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070565519729000775735361 9802924139796750581801521)
                ·
                  refine ⟨7352193104847562936351141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802924139796750581801521 7352193104847562936351141)
                  ·
                    refine ⟨1378536207158918050565839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352193104847562936351141 1378536207158918050565839)
                    ·
                      rfl

theorem cell23_8054069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_8054069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054069 prefixEnd_8054069 := by exact prefixLift 8054069
  have htrace : WordTrace (prefixWord ++ tailWord_8054069) baseStart_8054069 baseEnd_8054069 := by
    simpa [prefixWord, tailWord_8054069, baseEnd_8054069] using wordTrace_append hprefix tailTrace_8054069
  have hstable : (prefixWord ++ tailWord_8054069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054069).length < 2 ^ (prefixWord ++ tailWord_8054069).sum := by decide
  have hdescent : baseEnd_8054069 < baseStart_8054069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8054076 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_8054076 : Nat := 118140960795 + 8054076 * 2 ^ 59
def prefixEnd_8054076 : Nat := 4983230072969 + 3 ^ 40 * 8054076 * 2
def baseEnd_8054076 : Nat := 4135612215841335624309985

theorem tailTrace_8054076 : CollatzResearch.WordTrace tailWord_8054076 prefixEnd_8054076 4135612215841335624309985 := by
  unfold tailWord_8054076
  simp only [CollatzResearch.WordTrace]
  refine ⟨146878142384732826757319041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195837523179643769009758721 146878142384732826757319041)
  ·
    refine ⟨110158606788549620067989281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146878142384732826757319041 110158606788549620067989281)
    ·
      refine ⟨82618955091412215050991961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110158606788549620067989281 82618955091412215050991961)
      ·
        refine ⟨61964216318559161288243971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82618955091412215050991961 61964216318559161288243971)
        ·
          refine ⟨92946324477838741932365957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61964216318559161288243971 92946324477838741932365957)
          ·
            refine ⟨17427435839594764112318617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92946324477838741932365957 17427435839594764112318617)
            ·
              refine ⟨13070576879696073084238963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17427435839594764112318617 13070576879696073084238963)
              ·
                refine ⟨19605865319544109626358445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070576879696073084238963 19605865319544109626358445)
                ·
                  refine ⟨7352199494829041109884417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19605865319544109626358445 7352199494829041109884417)
                  ·
                    refine ⟨5514149621121780832413313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7352199494829041109884417 5514149621121780832413313)
                    ·
                      refine ⟨4135612215841335624309985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5514149621121780832413313 4135612215841335624309985)
                      ·
                        rfl

theorem cell23_8054076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_8054076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8054076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8054076 prefixEnd_8054076 := by exact prefixLift 8054076
  have htrace : WordTrace (prefixWord ++ tailWord_8054076) baseStart_8054076 baseEnd_8054076 := by
    simpa [prefixWord, tailWord_8054076, baseEnd_8054076] using wordTrace_append hprefix tailTrace_8054076
  have hstable : (prefixWord ++ tailWord_8054076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8054076).length < 2 ^ (prefixWord ++ tailWord_8054076).sum := by decide
  have hdescent : baseEnd_8054076 < baseStart_8054076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8054076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
