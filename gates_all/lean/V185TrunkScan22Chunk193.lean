import V185TrunkScan22Chunk192

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1719954 : List Nat := [3, 2, 3, 1, 3, 1, 1, 8]
def baseStart_1719954 : Nat := 118140960795 + 1719954 * 2 ^ 59
def prefixEnd_1719954 : Nat := 4983230072969 + 3 ^ 40 * 1719954 * 2
def baseEnd_1719954 : Nat := 65419489305427326352969

theorem tailTrace_1719954 : CollatzResearch.WordTrace tailWord_1719954 prefixEnd_1719954 65419489305427326352969 := by
  unfold tailWord_1719954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682969002726969400523729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41821250673938585068063277 15682969002726969400523729)
  ·
    refine ⟨11762226752045227050392797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15682969002726969400523729 11762226752045227050392797)
    ·
      refine ⟨4410835032016960143897299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11762226752045227050392797 4410835032016960143897299)
      ·
        refine ⟨6616252548025440215845949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410835032016960143897299 6616252548025440215845949)
        ·
          refine ⟨2481094705509540080942231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6616252548025440215845949 2481094705509540080942231)
          ·
            refine ⟨3721642058264310121413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481094705509540080942231 3721642058264310121413347)
            ·
              refine ⟨5582463087396465182120021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721642058264310121413347 5582463087396465182120021)
              ·
                refine ⟨65419489305427326352969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5582463087396465182120021 65419489305427326352969)
                ·
                  rfl

theorem cell22_1719954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_1719954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719954 prefixEnd_1719954 := by exact prefixLift 1719954
  have htrace : WordTrace (prefixWord ++ tailWord_1719954) baseStart_1719954 baseEnd_1719954 := by
    simpa [prefixWord, tailWord_1719954, baseEnd_1719954] using wordTrace_append hprefix tailTrace_1719954
  have hstable : (prefixWord ++ tailWord_1719954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719954).length < 2 ^ (prefixWord ++ tailWord_1719954).sum := by decide
  have hdescent : baseEnd_1719954 < baseStart_1719954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719986 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_1719986 : Nat := 118140960795 + 1719986 * 2 ^ 59
def prefixEnd_1719986 : Nat := 4983230072969 + 3 ^ 40 * 1719986 * 2
def baseEnd_1719986 : Nat := 588786358002808520376623

theorem tailTrace_1719986 : CollatzResearch.WordTrace tailWord_1719986 prefixEnd_1719986 588786358002808520376623 := by
  unfold tailWord_1719986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15683260786697986766814953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41822028764527964711506541 15683260786697986766814953)
  ·
    refine ⟨11762445590023490075111215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15683260786697986766814953 11762445590023490075111215)
    ·
      refine ⟨17643668385035235112666823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11762445590023490075111215 17643668385035235112666823)
      ·
        refine ⟨26465502577552852669000235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17643668385035235112666823 26465502577552852669000235)
        ·
          refine ⟨39698253866329279003500353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26465502577552852669000235 39698253866329279003500353)
          ·
            refine ⟨29773690399746959252625265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39698253866329279003500353 29773690399746959252625265)
            ·
              refine ⟨22330267799810219439468949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29773690399746959252625265 22330267799810219439468949)
              ·
                refine ⟨1046731303116104036225107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22330267799810219439468949 1046731303116104036225107)
                ·
                  refine ⟨1570096954674156054337661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046731303116104036225107 1570096954674156054337661)
                  ·
                    refine ⟨588786358002808520376623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570096954674156054337661 588786358002808520376623)
                    ·
                      rfl

theorem cell22_1719986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_1719986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719986 prefixEnd_1719986 := by exact prefixLift 1719986
  have htrace : WordTrace (prefixWord ++ tailWord_1719986) baseStart_1719986 baseEnd_1719986 := by
    simpa [prefixWord, tailWord_1719986, baseEnd_1719986] using wordTrace_append hprefix tailTrace_1719986
  have hstable : (prefixWord ++ tailWord_1719986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719986).length < 2 ^ (prefixWord ++ tailWord_1719986).sum := by decide
  have hdescent : baseEnd_1719986 < baseStart_1719986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719997 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1719997 : Nat := 118140960795 + 1719997 * 2 ^ 59
def prefixEnd_1719997 : Nat := 4983230072969 + 3 ^ 40 * 1719997 * 2
def baseEnd_1719997 : Nat := 588790123527608158351589

theorem tailTrace_1719997 : CollatzResearch.WordTrace tailWord_1719997 prefixEnd_1719997 588790123527608158351589 := by
  unfold tailWord_1719997
  simp only [CollatzResearch.WordTrace]
  refine ⟨62733444349752095945910245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41822296233168063963940163 62733444349752095945910245)
  ·
    refine ⟨11762520815578517989858171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62733444349752095945910245 11762520815578517989858171)
    ·
      refine ⟨17643781223367776984787257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11762520815578517989858171 17643781223367776984787257)
      ·
        refine ⟨13232835917525832738590443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17643781223367776984787257 13232835917525832738590443)
        ·
          refine ⟨19849253876288749107885665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232835917525832738590443 19849253876288749107885665)
          ·
            refine ⟨14886940407216561830914249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19849253876288749107885665 14886940407216561830914249)
            ·
              refine ⟨11165205305412421373185687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14886940407216561830914249 11165205305412421373185687)
              ·
                refine ⟨16747807958118632059778531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165205305412421373185687 16747807958118632059778531)
                ·
                  refine ⟨25121711937177948089667797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16747807958118632059778531 25121711937177948089667797)
                  ·
                    refine ⟨588790123527608158351589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25121711937177948089667797 588790123527608158351589)
                    ·
                      rfl

theorem cell22_1719997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1719997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719997 prefixEnd_1719997 := by exact prefixLift 1719997
  have htrace : WordTrace (prefixWord ++ tailWord_1719997) baseStart_1719997 baseEnd_1719997 := by
    simpa [prefixWord, tailWord_1719997, baseEnd_1719997] using wordTrace_append hprefix tailTrace_1719997
  have hstable : (prefixWord ++ tailWord_1719997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719997).length < 2 ^ (prefixWord ++ tailWord_1719997).sum := by decide
  have hdescent : baseEnd_1719997 < baseStart_1719997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720074 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1720074 : Nat := 118140960795 + 1720074 * 2 ^ 59
def prefixEnd_1720074 : Nat := 4983230072969 + 3 ^ 40 * 1720074 * 2
def baseEnd_1720074 : Nat := 588816482201205624176353

theorem tailTrace_1720074 : CollatzResearch.WordTrace tailWord_1720074 prefixEnd_1720074 588816482201205624176353 := by
  unfold tailWord_1720074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15684063192618284524115819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41824168513648758730975517 15684063192618284524115819)
  ·
    refine ⟨23526094788927426786173729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15684063192618284524115819 23526094788927426786173729)
    ·
      refine ⟨17644571091695570089630297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23526094788927426786173729 17644571091695570089630297)
      ·
        refine ⟨13233428318771677567222723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17644571091695570089630297 13233428318771677567222723)
        ·
          refine ⟨19850142478157516350834085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233428318771677567222723 19850142478157516350834085)
          ·
            refine ⟨3721901714654534315781391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19850142478157516350834085 3721901714654534315781391)
            ·
              refine ⟨5582852571981801473672087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721901714654534315781391 5582852571981801473672087)
              ·
                refine ⟨8374278857972702210508131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582852571981801473672087 8374278857972702210508131)
                ·
                  refine ⟨12561418286959053315762197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374278857972702210508131 12561418286959053315762197)
                  ·
                    refine ⟨588816482201205624176353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12561418286959053315762197 588816482201205624176353)
                    ·
                      rfl

theorem cell22_1720074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1720074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720074 prefixEnd_1720074 := by exact prefixLift 1720074
  have htrace : WordTrace (prefixWord ++ tailWord_1720074) baseStart_1720074 baseEnd_1720074 := by
    simpa [prefixWord, tailWord_1720074, baseEnd_1720074] using wordTrace_append hprefix tailTrace_1720074
  have hstable : (prefixWord ++ tailWord_1720074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720074).length < 2 ^ (prefixWord ++ tailWord_1720074).sum := by decide
  have hdescent : baseEnd_1720074 < baseStart_1720074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720110 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1720110 : Nat := 118140960795 + 1720110 * 2 ^ 59
def prefixEnd_1720110 : Nat := 4983230072969 + 3 ^ 40 * 1720110 * 2
def baseEnd_1720110 : Nat := 588828805736913530276243

theorem tailTrace_1720110 : CollatzResearch.WordTrace tailWord_1720110 prefixEnd_1720110 588828805736913530276243 := by
  unfold tailWord_1720110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842195724792839530596723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41825043865561810829849189 7842195724792839530596723)
  ·
    refine ⟨11763293587189259295895085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842195724792839530596723 11763293587189259295895085)
    ·
      refine ⟨4411235095195972235960657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11763293587189259295895085 4411235095195972235960657)
      ·
        refine ⟨3308426321396979176970493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411235095195972235960657 3308426321396979176970493)
        ·
          refine ⟨1240659870523867191363935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3308426321396979176970493 1240659870523867191363935)
          ·
            refine ⟨1860989805785800787045903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240659870523867191363935 1860989805785800787045903)
            ·
              refine ⟨2791484708678701180568855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860989805785800787045903 2791484708678701180568855)
              ·
                refine ⟨4187227063018051770853283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791484708678701180568855 4187227063018051770853283)
                ·
                  refine ⟨6280840594527077656279925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187227063018051770853283 6280840594527077656279925)
                  ·
                    refine ⟨588828805736913530276243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6280840594527077656279925 588828805736913530276243)
                    ·
                      rfl

theorem cell22_1720110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1720110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720110 prefixEnd_1720110 := by exact prefixLift 1720110
  have htrace : WordTrace (prefixWord ++ tailWord_1720110) baseStart_1720110 baseEnd_1720110 := by
    simpa [prefixWord, tailWord_1720110, baseEnd_1720110] using wordTrace_append hprefix tailTrace_1720110
  have hstable : (prefixWord ++ tailWord_1720110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720110).length < 2 ^ (prefixWord ++ tailWord_1720110).sum := by decide
  have hdescent : baseEnd_1720110 < baseStart_1720110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720181 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1720181 : Nat := 118140960795 + 1720181 * 2 ^ 59
def prefixEnd_1720181 : Nat := 4983230072969 + 3 ^ 40 * 1720181 * 2
def baseEnd_1720181 : Nat := 588853110487893011751025

theorem tailTrace_1720181 : CollatzResearch.WordTrace tailWord_1720181 prefixEnd_1720181 588853110487893011751025 := by
  unfold tailWord_1720181
  simp only [CollatzResearch.WordTrace]
  refine ⟨62740155381085495370608397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41826770254056996913738931 62740155381085495370608397)
  ·
    refine ⟨23527558267907060763978149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62740155381085495370608397 23527558267907060763978149)
    ·
      refine ⟨4411417175232573893245903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23527558267907060763978149 4411417175232573893245903)
      ·
        refine ⟨6617125762848860839868855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411417175232573893245903 6617125762848860839868855)
        ·
          refine ⟨9925688644273291259803283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617125762848860839868855 9925688644273291259803283)
          ·
            refine ⟨14888532966409936889704925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9925688644273291259803283 14888532966409936889704925)
            ·
              refine ⟨5583199862403726333639347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14888532966409936889704925 5583199862403726333639347)
              ·
                refine ⟨8374799793605589500459021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583199862403726333639347 8374799793605589500459021)
                ·
                  refine ⟨3140549922602096062672133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8374799793605589500459021 3140549922602096062672133)
                  ·
                    refine ⟨588853110487893011751025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3140549922602096062672133 588853110487893011751025)
                    ·
                      rfl

theorem cell22_1720181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1720181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720181 prefixEnd_1720181 := by exact prefixLift 1720181
  have htrace : WordTrace (prefixWord ++ tailWord_1720181) baseStart_1720181 baseEnd_1720181 := by
    simpa [prefixWord, tailWord_1720181, baseEnd_1720181] using wordTrace_append hprefix tailTrace_1720181
  have hstable : (prefixWord ++ tailWord_1720181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720181).length < 2 ^ (prefixWord ++ tailWord_1720181).sum := by decide
  have hdescent : baseEnd_1720181 < baseStart_1720181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720206 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_1720206 : Nat := 118140960795 + 1720206 * 2 ^ 59
def prefixEnd_1720206 : Nat := 4983230072969 + 3 ^ 40 * 1720206 * 2
def baseEnd_1720206 : Nat := 588861668498801279875949

theorem tailTrace_1720206 : CollatzResearch.WordTrace tailWord_1720206 prefixEnd_1720206 588861668498801279875949 := by
  unfold tailWord_1720206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842633400749365580033559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41827378137329949760178981 7842633400749365580033559)
  ·
    refine ⟨11763950101124048370050339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842633400749365580033559 11763950101124048370050339)
    ·
      refine ⟨17645925151686072555075509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763950101124048370050339 17645925151686072555075509)
      ·
        refine ⟨1654305482970569302038329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17645925151686072555075509 1654305482970569302038329)
        ·
          refine ⟨1240729112227926976528747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654305482970569302038329 1240729112227926976528747)
          ·
            refine ⟨1861093668341890464793121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240729112227926976528747 1861093668341890464793121)
            ·
              refine ⟨1395820251256417848594841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861093668341890464793121 1395820251256417848594841)
              ·
                refine ⟨1046865188442313386446131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395820251256417848594841 1046865188442313386446131)
                ·
                  refine ⟨1570297782663470079669197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046865188442313386446131 1570297782663470079669197)
                  ·
                    refine ⟨588861668498801279875949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570297782663470079669197 588861668498801279875949)
                    ·
                      rfl

theorem cell22_1720206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_1720206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720206 prefixEnd_1720206 := by exact prefixLift 1720206
  have htrace : WordTrace (prefixWord ++ tailWord_1720206) baseStart_1720206 baseEnd_1720206 := by
    simpa [prefixWord, tailWord_1720206, baseEnd_1720206] using wordTrace_append hprefix tailTrace_1720206
  have hstable : (prefixWord ++ tailWord_1720206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720206).length < 2 ^ (prefixWord ++ tailWord_1720206).sum := by decide
  have hdescent : baseEnd_1720206 < baseStart_1720206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720228 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_1720228 : Nat := 118140960795 + 1720228 * 2 ^ 59
def prefixEnd_1720228 : Nat := 4983230072969 + 3 ^ 40 * 1720228 * 2
def baseEnd_1720228 : Nat := 588869199548400555825881

theorem tailTrace_1720228 : CollatzResearch.WordTrace tailWord_1720228 prefixEnd_1720228 588869199548400555825881 := by
  unfold tailWord_1720228
  simp only [CollatzResearch.WordTrace]
  refine ⟨31370934805957611198784669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41827913074610148265046225 31370934805957611198784669)
  ·
    refine ⟨11764100552234104199544251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31370934805957611198784669 11764100552234104199544251)
    ·
      refine ⟨17646150828351156299316377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11764100552234104199544251 17646150828351156299316377)
      ·
        refine ⟨13234613121263367224487283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17646150828351156299316377 13234613121263367224487283)
        ·
          refine ⟨19851919681895050836730925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234613121263367224487283 19851919681895050836730925)
          ·
            refine ⟨7444469880710644063774097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19851919681895050836730925 7444469880710644063774097)
            ·
              refine ⟨5583352410532983047830573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444469880710644063774097 5583352410532983047830573)
              ·
                refine ⟨2093757153949868642936465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5583352410532983047830573 2093757153949868642936465)
                ·
                  refine ⟨1570317865462401482202349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093757153949868642936465 1570317865462401482202349)
                  ·
                    refine ⟨588869199548400555825881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570317865462401482202349 588869199548400555825881)
                    ·
                      rfl

theorem cell22_1720228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_1720228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720228 prefixEnd_1720228 := by exact prefixLift 1720228
  have htrace : WordTrace (prefixWord ++ tailWord_1720228) baseStart_1720228 baseEnd_1720228 := by
    simpa [prefixWord, tailWord_1720228, baseEnd_1720228] using wordTrace_append hprefix tailTrace_1720228
  have hstable : (prefixWord ++ tailWord_1720228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720228).length < 2 ^ (prefixWord ++ tailWord_1720228).sum := by decide
  have hdescent : baseEnd_1720228 < baseStart_1720228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720256 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_1720256 : Nat := 118140960795 + 1720256 * 2 ^ 59
def prefixEnd_1720256 : Nat := 4983230072969 + 3 ^ 40 * 1720256 * 2
def baseEnd_1720256 : Nat := 588878784520617816125795

theorem tailTrace_1720256 : CollatzResearch.WordTrace tailWord_1720256 prefixEnd_1720256 588878784520617816125795 := by
  unfold tailWord_1720256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31371445427906891589794311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41828593903875855453059081 31371445427906891589794311)
  ·
    refine ⟨47057168141860337384691467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31371445427906891589794311 47057168141860337384691467)
    ·
      refine ⟨70585752212790506077037201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47057168141860337384691467 70585752212790506077037201)
      ·
        refine ⟨52939314159592879557777901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70585752212790506077037201 52939314159592879557777901)
        ·
          refine ⟨19852242809847329834166713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52939314159592879557777901 19852242809847329834166713)
          ·
            refine ⟨14889182107385497375625035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19852242809847329834166713 14889182107385497375625035)
            ·
              refine ⟨22333773161078246063437553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14889182107385497375625035 22333773161078246063437553)
              ·
                refine ⟨16750329870808684547578165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22333773161078246063437553 16750329870808684547578165)
                ·
                  refine ⟨1570343425388314176335453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16750329870808684547578165 1570343425388314176335453)
                  ·
                    refine ⟨588878784520617816125795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570343425388314176335453 588878784520617816125795)
                    ·
                      rfl

theorem cell22_1720256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_1720256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720256 prefixEnd_1720256 := by exact prefixLift 1720256
  have htrace : WordTrace (prefixWord ++ tailWord_1720256) baseStart_1720256 baseEnd_1720256 := by
    simpa [prefixWord, tailWord_1720256, baseEnd_1720256] using wordTrace_append hprefix tailTrace_1720256
  have hstable : (prefixWord ++ tailWord_1720256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720256).length < 2 ^ (prefixWord ++ tailWord_1720256).sum := by decide
  have hdescent : baseEnd_1720256 < baseStart_1720256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720299 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_1720299 : Nat := 118140960795 + 1720299 * 2 ^ 59
def prefixEnd_1720299 : Nat := 4983230072969 + 3 ^ 40 * 1720299 * 2
def baseEnd_1720299 : Nat := 588893504299380037300663

theorem tailTrace_1720299 : CollatzResearch.WordTrace tailWord_1720299 prefixEnd_1720299 588893504299380037300663 := by
  unfold tailWord_1720299
  simp only [CollatzResearch.WordTrace]
  refine ⟨62744459194658001523403951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41829639463105334348935967 62744459194658001523403951)
  ·
    refine ⟨94116688791987002285105927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62744459194658001523403951 94116688791987002285105927)
    ·
      refine ⟨141175033187980503427658891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94116688791987002285105927 141175033187980503427658891)
      ·
        refine ⟨211762549781970755141488337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141175033187980503427658891 211762549781970755141488337)
        ·
          refine ⟨158821912336478066356116253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211762549781970755141488337 158821912336478066356116253)
          ·
            refine ⟨59558217126179274883543595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158821912336478066356116253 59558217126179274883543595)
            ·
              refine ⟨89337325689268912325315393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59558217126179274883543595 89337325689268912325315393)
              ·
                refine ⟨67002994266951684243986545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89337325689268912325315393 67002994266951684243986545)
                ·
                  refine ⟨50252245700213763182989909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67002994266951684243986545 50252245700213763182989909)
                  ·
                    refine ⟨588893504299380037300663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50252245700213763182989909 588893504299380037300663)
                    ·
                      rfl

theorem cell22_1720299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_1720299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720299 prefixEnd_1720299 := by exact prefixLift 1720299
  have htrace : WordTrace (prefixWord ++ tailWord_1720299) baseStart_1720299 baseEnd_1720299 := by
    simpa [prefixWord, tailWord_1720299, baseEnd_1720299] using wordTrace_append hprefix tailTrace_1720299
  have hstable : (prefixWord ++ tailWord_1720299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720299).length < 2 ^ (prefixWord ++ tailWord_1720299).sum := by decide
  have hdescent : baseEnd_1720299 < baseStart_1720299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720324 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1720324 : Nat := 118140960795 + 1720324 * 2 ^ 59
def prefixEnd_1720324 : Nat := 4983230072969 + 3 ^ 40 * 1720324 * 2
def baseEnd_1720324 : Nat := 588902062310288305425587

theorem tailTrace_1720324 : CollatzResearch.WordTrace tailWord_1720324 prefixEnd_1720324 588902062310288305425587 := by
  unfold tailWord_1720324
  simp only [CollatzResearch.WordTrace]
  refine ⟨31372685509783715396532013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41830247346378287195376017 31372685509783715396532013)
  ·
    refine ⟨11764757066168893273699505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31372685509783715396532013 11764757066168893273699505)
    ·
      refine ⟨8823567799626669955274629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11764757066168893273699505 8823567799626669955274629)
      ·
        refine ⟨1654418962430000616613993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8823567799626669955274629 1654418962430000616613993)
        ·
          refine ⟨1240814221822500462460495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654418962430000616613993 1240814221822500462460495)
          ·
            refine ⟨1861221332733750693690743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240814221822500462460495 1861221332733750693690743)
            ·
              refine ⟨2791831999100626040536115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861221332733750693690743 2791831999100626040536115)
              ·
                refine ⟨4187747998650939060804173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791831999100626040536115 4187747998650939060804173)
                ·
                  refine ⟨1570405499494102147801565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4187747998650939060804173 1570405499494102147801565)
                  ·
                    refine ⟨588902062310288305425587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570405499494102147801565 588902062310288305425587)
                    ·
                      rfl

theorem cell22_1720324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1720324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720324 prefixEnd_1720324 := by exact prefixLift 1720324
  have htrace : WordTrace (prefixWord ++ tailWord_1720324) baseStart_1720324 baseEnd_1720324 := by
    simpa [prefixWord, tailWord_1720324, baseEnd_1720324] using wordTrace_append hprefix tailTrace_1720324
  have hstable : (prefixWord ++ tailWord_1720324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720324).length < 2 ^ (prefixWord ++ tailWord_1720324).sum := by decide
  have hdescent : baseEnd_1720324 < baseStart_1720324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720376 : List Nat := [2, 1, 2, 1, 6, 10]
def baseStart_1720376 : Nat := 118140960795 + 1720376 * 2 ^ 59
def prefixEnd_1720376 : Nat := 4983230072969 + 3 ^ 40 * 1720376 * 2
def baseEnd_1720376 : Nat := 7270615592258981520067

theorem tailTrace_1720376 : CollatzResearch.WordTrace tailWord_1720376 prefixEnd_1720376 7270615592258981520067 := by
  unfold tailWord_1720376
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373633807689521836978491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41831511743586029115971321 31373633807689521836978491)
  ·
    refine ⟨47060450711534282755467737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31373633807689521836978491 47060450711534282755467737)
    ·
      refine ⟨35295338033650712066600803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47060450711534282755467737 35295338033650712066600803)
      ·
        refine ⟨52943007050476068099901205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35295338033650712066600803 52943007050476068099901205)
        ·
          refine ⟨2481703455491065692182869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52943007050476068099901205 2481703455491065692182869)
          ·
            refine ⟨7270615592258981520067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2481703455491065692182869 7270615592258981520067)
            ·
              rfl

theorem cell22_1720376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 10].length) (baseStart_1720376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720376 prefixEnd_1720376 := by exact prefixLift 1720376
  have htrace : WordTrace (prefixWord ++ tailWord_1720376) baseStart_1720376 baseEnd_1720376 := by
    simpa [prefixWord, tailWord_1720376, baseEnd_1720376] using wordTrace_append hprefix tailTrace_1720376
  have hstable : (prefixWord ++ tailWord_1720376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720376).length < 2 ^ (prefixWord ++ tailWord_1720376).sum := by decide
  have hdescent : baseEnd_1720376 < baseStart_1720376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720380 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1720380 : Nat := 118140960795 + 1720380 * 2 ^ 59
def prefixEnd_1720380 : Nat := 4983230072969 + 3 ^ 40 * 1720380 * 2
def baseEnd_1720380 : Nat := 588921232254722826025415

theorem tailTrace_1720380 : CollatzResearch.WordTrace tailWord_1720380 prefixEnd_1720380 588921232254722826025415 := by
  unfold tailWord_1720380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373706753682276178551297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41831609004909701571401729 31373706753682276178551297)
  ·
    refine ⟨23530280065261707133913473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31373706753682276178551297 23530280065261707133913473)
    ·
      refine ⟨17647710048946280350435105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23530280065261707133913473 17647710048946280350435105)
      ·
        refine ⟨13235782536709710262826329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17647710048946280350435105 13235782536709710262826329)
        ·
          refine ⟨9926836902532282697119747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13235782536709710262826329 9926836902532282697119747)
          ·
            refine ⟨14890255353798424045679621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926836902532282697119747 14890255353798424045679621)
            ·
              refine ⟨2791922878837204508564929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14890255353798424045679621 2791922878837204508564929)
              ·
                refine ⟨2093942159127903381423697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791922878837204508564929 2093942159127903381423697)
                ·
                  refine ⟨1570456619345927536067773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093942159127903381423697 1570456619345927536067773)
                  ·
                    refine ⟨588921232254722826025415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570456619345927536067773 588921232254722826025415)
                    ·
                      rfl

theorem cell22_1720380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1720380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720380 prefixEnd_1720380 := by exact prefixLift 1720380
  have htrace : WordTrace (prefixWord ++ tailWord_1720380) baseStart_1720380 baseEnd_1720380 := by
    simpa [prefixWord, tailWord_1720380, baseEnd_1720380] using wordTrace_append hprefix tailTrace_1720380
  have hstable : (prefixWord ++ tailWord_1720380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720380).length < 2 ^ (prefixWord ++ tailWord_1720380).sum := by decide
  have hdescent : baseEnd_1720380 < baseStart_1720380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720382 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1720382 : Nat := 118140960795 + 1720382 * 2 ^ 59
def prefixEnd_1720382 : Nat := 4983230072969 + 3 ^ 40 * 1720382 * 2
def baseEnd_1720382 : Nat := 196307305631865162491803

theorem tailTrace_1720382 : CollatzResearch.WordTrace tailWord_1720382 prefixEnd_1720382 196307305631865162491803 := by
  unfold tailWord_1720382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843435806669663337334425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41831657635571537799116933 7843435806669663337334425)
  ·
    refine ⟨5882576855002247503000819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7843435806669663337334425 5882576855002247503000819)
    ·
      refine ⟨8823865282503371254501229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882576855002247503000819 8823865282503371254501229)
      ·
        refine ⟨3308949480938764220437961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8823865282503371254501229 3308949480938764220437961)
        ·
          refine ⟨2481712110704073165328471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308949480938764220437961 2481712110704073165328471)
          ·
            refine ⟨3722568166056109747992707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481712110704073165328471 3722568166056109747992707)
            ·
              refine ⟨5583852249084164621989061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722568166056109747992707 5583852249084164621989061)
              ·
                refine ⟨1046972296703280866622949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5583852249084164621989061 1046972296703280866622949)
                ·
                  refine ⟨196307305631865162491803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046972296703280866622949 196307305631865162491803)
                  ·
                    rfl

theorem cell22_1720382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1720382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720382 prefixEnd_1720382 := by exact prefixLift 1720382
  have htrace : WordTrace (prefixWord ++ tailWord_1720382) baseStart_1720382 baseEnd_1720382 := by
    simpa [prefixWord, tailWord_1720382, baseEnd_1720382] using wordTrace_append hprefix tailTrace_1720382
  have hstable : (prefixWord ++ tailWord_1720382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720382).length < 2 ^ (prefixWord ++ tailWord_1720382).sum := by decide
  have hdescent : baseEnd_1720382 < baseStart_1720382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720408 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_1720408 : Nat := 118140960795 + 1720408 * 2 ^ 59
def prefixEnd_1720408 : Nat := 4983230072969 + 3 ^ 40 * 1720408 * 2
def baseEnd_1720408 : Nat := 588930817226940086325329

theorem tailTrace_1720408 : CollatzResearch.WordTrace tailWord_1720408 prefixEnd_1720408 588930817226940086325329 := by
  unfold tailWord_1720408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31374217375631556569560939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41832289834175408759414585 31374217375631556569560939)
  ·
    refine ⟨47061326063447334854341409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31374217375631556569560939 47061326063447334854341409)
    ·
      refine ⟨35295994547585501140756057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47061326063447334854341409 35295994547585501140756057)
      ·
        refine ⟨26471995910689125855567043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35295994547585501140756057 26471995910689125855567043)
        ·
          refine ⟨39707993866033688783350565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26471995910689125855567043 39707993866033688783350565)
          ·
            refine ⟨7445248849881316646878231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39707993866033688783350565 7445248849881316646878231)
            ·
              refine ⟨11167873274821974970317347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445248849881316646878231 11167873274821974970317347)
              ·
                refine ⟨16751809912232962455476021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11167873274821974970317347 16751809912232962455476021)
                ·
                  refine ⟨1570482179271840230200877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16751809912232962455476021 1570482179271840230200877)
                  ·
                    refine ⟨588930817226940086325329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570482179271840230200877 588930817226940086325329)
                    ·
                      rfl

theorem cell22_1720408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_1720408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720408 prefixEnd_1720408 := by exact prefixLift 1720408
  have htrace : WordTrace (prefixWord ++ tailWord_1720408) baseStart_1720408 baseEnd_1720408 := by
    simpa [prefixWord, tailWord_1720408, baseEnd_1720408] using wordTrace_append hprefix tailTrace_1720408
  have hstable : (prefixWord ++ tailWord_1720408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720408).length < 2 ^ (prefixWord ++ tailWord_1720408).sum := by decide
  have hdescent : baseEnd_1720408 < baseStart_1720408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720453 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1720453 : Nat := 118140960795 + 1720453 * 2 ^ 59
def prefixEnd_1720453 : Nat := 4983230072969 + 3 ^ 40 * 1720453 * 2
def baseEnd_1720453 : Nat := 588946221646574968950191

theorem tailTrace_1720453 : CollatzResearch.WordTrace tailWord_1720453 prefixEnd_1720453 588946221646574968950191 := by
  unfold tailWord_1720453
  simp only [CollatzResearch.WordTrace]
  refine ⟨62750076036100085824510013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41833384024066723883006675 62750076036100085824510013)
  ·
    refine ⟨23531278513537532184191255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62750076036100085824510013 23531278513537532184191255)
    ·
      refine ⟨35296917770306298276286883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23531278513537532184191255 35296917770306298276286883)
      ·
        refine ⟨52945376655459447414430325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35296917770306298276286883 52945376655459447414430325)
        ·
          refine ⟨4963629061449323195102843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52945376655459447414430325 4963629061449323195102843)
          ·
            refine ⟨7445443592173984792654265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963629061449323195102843 7445443592173984792654265)
            ·
              refine ⟨5584082694130488594490699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7445443592173984792654265 5584082694130488594490699)
              ·
                refine ⟨8376124041195732891736049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584082694130488594490699 8376124041195732891736049)
                ·
                  refine ⟨6282093030896799668802037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8376124041195732891736049 6282093030896799668802037)
                  ·
                    refine ⟨588946221646574968950191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6282093030896799668802037 588946221646574968950191)
                    ·
                      rfl

theorem cell22_1720453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1720453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720453 prefixEnd_1720453 := by exact prefixLift 1720453
  have htrace : WordTrace (prefixWord ++ tailWord_1720453) baseStart_1720453 baseEnd_1720453 := by
    simpa [prefixWord, tailWord_1720453, baseEnd_1720453] using wordTrace_append hprefix tailTrace_1720453
  have hstable : (prefixWord ++ tailWord_1720453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720453).length < 2 ^ (prefixWord ++ tailWord_1720453).sum := by decide
  have hdescent : baseEnd_1720453 < baseStart_1720453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720530 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1720530 : Nat := 118140960795 + 1720530 * 2 ^ 59
def prefixEnd_1720530 : Nat := 4983230072969 + 3 ^ 40 * 1720530 * 2
def baseEnd_1720530 : Nat := 588972580320172434774955

theorem tailTrace_1720530 : CollatzResearch.WordTrace tailWord_1720530 prefixEnd_1720530 588972580320172434774955 := by
  unfold tailWord_1720530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15688221114205281993765761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41835256304547418650042029 15688221114205281993765761)
  ·
    refine ⟨11766165835653961495324321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15688221114205281993765761 11766165835653961495324321)
    ·
      refine ⟨8824624376740471121493241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11766165835653961495324321 8824624376740471121493241)
      ·
        refine ⟨6618468282555353341119931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8824624376740471121493241 6618468282555353341119931)
        ·
          refine ⟨9927702423833030011679897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618468282555353341119931 9927702423833030011679897)
          ·
            refine ⟨7445776817874772508759923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9927702423833030011679897 7445776817874772508759923)
            ·
              refine ⟨11168665226812158763139885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445776817874772508759923 11168665226812158763139885)
              ·
                refine ⟨4188249460054559536177457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11168665226812158763139885 4188249460054559536177457)
                ·
                  refine ⟨3141187095040919652133093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4188249460054559536177457 3141187095040919652133093)
                  ·
                    refine ⟨588972580320172434774955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3141187095040919652133093 588972580320172434774955)
                    ·
                      rfl

theorem cell22_1720530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1720530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720530 prefixEnd_1720530 := by exact prefixLift 1720530
  have htrace : WordTrace (prefixWord ++ tailWord_1720530) baseStart_1720530 baseEnd_1720530 := by
    simpa [prefixWord, tailWord_1720530, baseEnd_1720530] using wordTrace_append hprefix tailTrace_1720530
  have hstable : (prefixWord ++ tailWord_1720530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720530).length < 2 ^ (prefixWord ++ tailWord_1720530).sum := by decide
  have hdescent : baseEnd_1720530 < baseStart_1720530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720588 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1720588 : Nat := 118140960795 + 1720588 * 2 ^ 59
def prefixEnd_1720588 : Nat := 4983230072969 + 3 ^ 40 * 1720588 * 2
def baseEnd_1720588 : Nat := 588992434905479616824777

theorem tailTrace_1720588 : CollatzResearch.WordTrace tailWord_1720588 prefixEnd_1720588 588992434905479616824777 := by
  unfold tailWord_1720588
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377499945305501940337209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41836666593740669253782945 31377499945305501940337209)
  ·
    refine ⟨23533124958979126455252907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31377499945305501940337209 23533124958979126455252907)
    ·
      refine ⟨35299687438468689682879361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23533124958979126455252907 35299687438468689682879361)
      ·
        refine ⟨26474765578851517262159521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35299687438468689682879361 26474765578851517262159521)
        ·
          refine ⟨19856074184138637946619641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26474765578851517262159521 19856074184138637946619641)
          ·
            refine ⟨14892055638103978459964731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19856074184138637946619641 14892055638103978459964731)
            ·
              refine ⟨22338083457155967689947097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892055638103978459964731 22338083457155967689947097)
              ·
                refine ⟨16753562592866975767460323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22338083457155967689947097 16753562592866975767460323)
                ·
                  refine ⟨25130343889300463651190485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16753562592866975767460323 25130343889300463651190485)
                  ·
                    refine ⟨588992434905479616824777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25130343889300463651190485 588992434905479616824777)
                    ·
                      rfl

theorem cell22_1720588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1720588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720588 prefixEnd_1720588 := by exact prefixLift 1720588
  have htrace : WordTrace (prefixWord ++ tailWord_1720588) baseStart_1720588 baseEnd_1720588 := by
    simpa [prefixWord, tailWord_1720588, baseEnd_1720588] using wordTrace_append hprefix tailTrace_1720588
  have hstable : (prefixWord ++ tailWord_1720588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720588).length < 2 ^ (prefixWord ++ tailWord_1720588).sum := by decide
  have hdescent : baseEnd_1720588 < baseStart_1720588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720607 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 5]
def baseStart_1720607 : Nat := 118140960795 + 1720607 * 2 ^ 59
def prefixEnd_1720607 : Nat := 4983230072969 + 3 ^ 40 * 1720607 * 2
def baseEnd_1720607 : Nat := 196332979664589966866573

theorem tailTrace_1720607 : CollatzResearch.WordTrace tailWord_1720607 prefixEnd_1720607 196332979664589966866573 := by
  unfold tailWord_1720607
  simp only [CollatzResearch.WordTrace]
  refine ⟨62755692877542170125616075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41837128585028113417077383 62755692877542170125616075)
  ·
    refine ⟨94133539316313255188424113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62755692877542170125616075 94133539316313255188424113)
    ·
      refine ⟨70600154487234941391318085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94133539316313255188424113 70600154487234941391318085)
      ·
        refine ⟨13237528966356551510872141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70600154487234941391318085 13237528966356551510872141)
        ·
          refine ⟨4964073362383706816577053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13237528966356551510872141 4964073362383706816577053)
          ·
            refine ⟨1861527510893890056216395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4964073362383706816577053 1861527510893890056216395)
            ·
              refine ⟨2792291266340835084324593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861527510893890056216395 2792291266340835084324593)
              ·
                refine ⟨2094218449755626313243445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2792291266340835084324593 2094218449755626313243445)
                ·
                  refine ⟨196332979664589966866573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2094218449755626313243445 196332979664589966866573)
                  ·
                    rfl

theorem cell22_1720607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 5].length) (baseStart_1720607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720607 prefixEnd_1720607 := by exact prefixLift 1720607
  have htrace : WordTrace (prefixWord ++ tailWord_1720607) baseStart_1720607 baseEnd_1720607 := by
    simpa [prefixWord, tailWord_1720607, baseEnd_1720607] using wordTrace_append hprefix tailTrace_1720607
  have hstable : (prefixWord ++ tailWord_1720607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720607).length < 2 ^ (prefixWord ++ tailWord_1720607).sum := by decide
  have hdescent : baseEnd_1720607 < baseStart_1720607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720680 : List Nat := [2, 1, 4, 2, 2, 1, 1, 9]
def baseStart_1720680 : Nat := 118140960795 + 1720680 * 2 ^ 59
def prefixEnd_1720680 : Nat := 4983230072969 + 3 ^ 40 * 1720680 * 2
def baseEnd_1720680 : Nat := 65447103153958004836055

theorem tailTrace_1720680 : CollatzResearch.WordTrace tailWord_1720680 prefixEnd_1720680 65447103153958004836055 := by
  unfold tailWord_1720680
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379177703138851796511747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41838903604185135728682329 31379177703138851796511747)
  ·
    refine ⟨47068766554708277694767621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31379177703138851796511747 47068766554708277694767621)
    ·
      refine ⟨8825393729007802067768929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47068766554708277694767621 8825393729007802067768929)
      ·
        refine ⟨6619045296755851550826697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8825393729007802067768929 6619045296755851550826697)
        ·
          refine ⟨4964283972566888663120023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6619045296755851550826697 4964283972566888663120023)
          ·
            refine ⟨7446425958850332994680035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964283972566888663120023 7446425958850332994680035)
            ·
              refine ⟨11169638938275499492020053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446425958850332994680035 11169638938275499492020053)
              ·
                refine ⟨65447103153958004836055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11169638938275499492020053 65447103153958004836055)
                ·
                  rfl

theorem cell22_1720680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_1720680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720680 prefixEnd_1720680 := by exact prefixLift 1720680
  have htrace : WordTrace (prefixWord ++ tailWord_1720680) baseStart_1720680 baseEnd_1720680 := by
    simpa [prefixWord, tailWord_1720680, baseEnd_1720680] using wordTrace_append hprefix tailTrace_1720680
  have hstable : (prefixWord ++ tailWord_1720680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720680).length < 2 ^ (prefixWord ++ tailWord_1720680).sum := by decide
  have hdescent : baseEnd_1720680 < baseStart_1720680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720684 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_1720684 : Nat := 118140960795 + 1720684 * 2 ^ 59
def prefixEnd_1720684 : Nat := 4983230072969 + 3 ^ 40 * 1720684 * 2
def baseEnd_1720684 : Nat := 589025297667367366424483

theorem tailTrace_1720684 : CollatzResearch.WordTrace tailWord_1720684 prefixEnd_1720684 589025297667367366424483 := by
  unfold tailWord_1720684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379250649131606138084553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41839000865508808184112737 31379250649131606138084553)
  ·
    refine ⟨23534437986848704603563415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31379250649131606138084553 23534437986848704603563415)
    ·
      refine ⟨35301656980273056905345123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23534437986848704603563415 35301656980273056905345123)
      ·
        refine ⟨52952485470409585358017685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35301656980273056905345123 52952485470409585358017685)
        ·
          refine ⟨2482147756425449313657079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52952485470409585358017685 2482147756425449313657079)
          ·
            refine ⟨3723221634638173970485619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482147756425449313657079 3723221634638173970485619)
            ·
              refine ⟨5584832451957260955728429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723221634638173970485619 5584832451957260955728429)
              ·
                refine ⟨2094312169483972858398161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5584832451957260955728429 2094312169483972858398161)
                ·
                  refine ⟨1570734127112979643798621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2094312169483972858398161 1570734127112979643798621)
                  ·
                    refine ⟨589025297667367366424483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570734127112979643798621 589025297667367366424483)
                    ·
                      rfl

theorem cell22_1720684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_1720684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720684 prefixEnd_1720684 := by exact prefixLift 1720684
  have htrace : WordTrace (prefixWord ++ tailWord_1720684) baseStart_1720684 baseEnd_1720684 := by
    simpa [prefixWord, tailWord_1720684, baseEnd_1720684] using wordTrace_append hprefix tailTrace_1720684
  have hstable : (prefixWord ++ tailWord_1720684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720684).length < 2 ^ (prefixWord ++ tailWord_1720684).sum := by decide
  have hdescent : baseEnd_1720684 < baseStart_1720684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720729 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 1, 3]
def baseStart_1720729 : Nat := 118140960795 + 1720729 * 2 ^ 59
def prefixEnd_1720729 : Nat := 4983230072969 + 3 ^ 40 * 1720729 * 2
def baseEnd_1720729 : Nat := 589040702087002249049345

theorem tailTrace_1720729 : CollatzResearch.WordTrace tailWord_1720729 prefixEnd_1720729 589040702087002249049345 := by
  unfold tailWord_1720729
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760142583100184961557241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41840095055400123307704827 62760142583100184961557241)
  ·
    refine ⟨47070106937325138721167931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62760142583100184961557241 47070106937325138721167931)
    ·
      refine ⟨70605160405987708081751897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47070106937325138721167931 70605160405987708081751897)
      ·
        refine ⟨52953870304490781061313923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70605160405987708081751897 52953870304490781061313923)
        ·
          refine ⟨79430805456736171591970885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52953870304490781061313923 79430805456736171591970885)
          ·
            refine ⟨14893276023138032173494541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79430805456736171591970885 14893276023138032173494541)
            ·
              refine ⟨5584978508676762065060453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14893276023138032173494541 5584978508676762065060453)
              ·
                refine ⟨1047183470376892887198835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5584978508676762065060453 1047183470376892887198835)
                ·
                  refine ⟨1570775205565339330798253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047183470376892887198835 1570775205565339330798253)
                  ·
                    refine ⟨589040702087002249049345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570775205565339330798253 589040702087002249049345)
                    ·
                      rfl

theorem cell22_1720729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_1720729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720729 prefixEnd_1720729 := by exact prefixLift 1720729
  have htrace : WordTrace (prefixWord ++ tailWord_1720729) baseStart_1720729 baseEnd_1720729 := by
    simpa [prefixWord, tailWord_1720729, baseEnd_1720729] using wordTrace_append hprefix tailTrace_1720729
  have hstable : (prefixWord ++ tailWord_1720729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720729).length < 2 ^ (prefixWord ++ tailWord_1720729).sum := by decide
  have hdescent : baseEnd_1720729 < baseStart_1720729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720740 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1720740 : Nat := 118140960795 + 1720740 * 2 ^ 59
def prefixEnd_1720740 : Nat := 4983230072969 + 3 ^ 40 * 1720740 * 2
def baseEnd_1720740 : Nat := 589044467611801887024311

theorem tailTrace_1720740 : CollatzResearch.WordTrace tailWord_1720740 prefixEnd_1720740 589044467611801887024311 := by
  unfold tailWord_1720740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31380271893030166920103837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41840362524040222560138449 31380271893030166920103837)
  ·
    refine ⟨11767601959886312595038939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31380271893030166920103837 11767601959886312595038939)
    ·
      refine ⟨17651402939829468892558409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11767601959886312595038939 17651402939829468892558409)
      ·
        refine ⟨13238552204872101669418807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17651402939829468892558409 13238552204872101669418807)
        ·
          refine ⟨19857828307308152504128211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238552204872101669418807 19857828307308152504128211)
          ·
            refine ⟨29786742460962228756192317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19857828307308152504128211 29786742460962228756192317)
            ·
              refine ⟨11170028422860835783572119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29786742460962228756192317 11170028422860835783572119)
              ·
                refine ⟨16755042634291253675358179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170028422860835783572119 16755042634291253675358179)
                ·
                  refine ⟨25132563951436880513037269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16755042634291253675358179 25132563951436880513037269)
                  ·
                    refine ⟨589044467611801887024311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25132563951436880513037269 589044467611801887024311)
                    ·
                      rfl

theorem cell22_1720740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1720740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720740 prefixEnd_1720740 := by exact prefixLift 1720740
  have htrace : WordTrace (prefixWord ++ tailWord_1720740) baseStart_1720740 baseEnd_1720740 := by
    simpa [prefixWord, tailWord_1720740, baseEnd_1720740] using wordTrace_append hprefix tailTrace_1720740
  have hstable : (prefixWord ++ tailWord_1720740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720740).length < 2 ^ (prefixWord ++ tailWord_1720740).sum := by decide
  have hdescent : baseEnd_1720740 < baseStart_1720740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720785 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1720785 : Nat := 118140960795 + 1720785 * 2 ^ 59
def prefixEnd_1720785 : Nat := 4983230072969 + 3 ^ 40 * 1720785 * 2
def baseEnd_1720785 : Nat := 589059872031436769649173

theorem tailTrace_1720785 : CollatzResearch.WordTrace tailWord_1720785 prefixEnd_1720785 589059872031436769649173 := by
  unfold tailWord_1720785
  simp only [CollatzResearch.WordTrace]
  refine ⟨62762185070897306525595809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41841456713931537683730539 62762185070897306525595809)
  ·
    refine ⟨47071638803172979894196857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62762185070897306525595809 47071638803172979894196857)
    ·
      refine ⟨35303729102379734920647643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47071638803172979894196857 35303729102379734920647643)
      ·
        refine ⟨52955593653569602380971465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35303729102379734920647643 52955593653569602380971465)
        ·
          refine ⟨39716695240177201785728599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52955593653569602380971465 39716695240177201785728599)
          ·
            refine ⟨59575042860265802678592899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39716695240177201785728599 59575042860265802678592899)
            ·
              refine ⟨89362564290398704017889349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59575042860265802678592899 89362564290398704017889349)
              ·
                refine ⟨16755480804449757003354253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89362564290398704017889349 16755480804449757003354253)
                ·
                  refine ⟨6283305301668658876257845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16755480804449757003354253 6283305301668658876257845)
                  ·
                    refine ⟨589059872031436769649173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6283305301668658876257845 589059872031436769649173)
                    ·
                      rfl

theorem cell22_1720785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1720785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720785 prefixEnd_1720785 := by exact prefixLift 1720785
  have htrace : WordTrace (prefixWord ++ tailWord_1720785) baseStart_1720785 baseEnd_1720785 := by
    simpa [prefixWord, tailWord_1720785, baseEnd_1720785] using wordTrace_append hprefix tailTrace_1720785
  have hstable : (prefixWord ++ tailWord_1720785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720785).length < 2 ^ (prefixWord ++ tailWord_1720785).sum := by decide
  have hdescent : baseEnd_1720785 < baseStart_1720785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720800 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_1720800 : Nat := 118140960795 + 1720800 * 2 ^ 59
def prefixEnd_1720800 : Nat := 4983230072969 + 3 ^ 40 * 1720800 * 2
def baseEnd_1720800 : Nat := 589065006837981730524127

theorem tailTrace_1720800 : CollatzResearch.WordTrace tailWord_1720800 prefixEnd_1720800 589065006837981730524127 := by
  unfold tailWord_1720800
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381366082921482043695927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41841821443895309391594569 31381366082921482043695927)
  ·
    refine ⟨47072049124382223065543891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31381366082921482043695927 47072049124382223065543891)
    ·
      refine ⟨70608073686573334598315837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47072049124382223065543891 70608073686573334598315837)
      ·
        refine ⟨26478027632465000474368439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70608073686573334598315837 26478027632465000474368439)
        ·
          refine ⟨39717041448697500711552659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26478027632465000474368439 39717041448697500711552659)
          ·
            refine ⟨59575562173046251067328989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39717041448697500711552659 59575562173046251067328989)
            ·
              refine ⟨22340835814892344150248371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59575562173046251067328989 22340835814892344150248371)
              ·
                refine ⟨33511253722338516225372557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22340835814892344150248371 33511253722338516225372557)
                ·
                  refine ⟨12566720145876943584514709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33511253722338516225372557 12566720145876943584514709)
                  ·
                    refine ⟨589065006837981730524127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12566720145876943584514709 589065006837981730524127)
                    ·
                      rfl

theorem cell22_1720800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_1720800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720800 prefixEnd_1720800 := by exact prefixLift 1720800
  have htrace : WordTrace (prefixWord ++ tailWord_1720800) baseStart_1720800 baseEnd_1720800 := by
    simpa [prefixWord, tailWord_1720800, baseEnd_1720800] using wordTrace_append hprefix tailTrace_1720800
  have hstable : (prefixWord ++ tailWord_1720800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720800).length < 2 ^ (prefixWord ++ tailWord_1720800).sum := by decide
  have hdescent : baseEnd_1720800 < baseStart_1720800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720817 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1720817 : Nat := 118140960795 + 1720817 * 2 ^ 59
def prefixEnd_1720817 : Nat := 4983230072969 + 3 ^ 40 * 1720817 * 2
def baseEnd_1720817 : Nat := 589070826285399352849075

theorem tailTrace_1720817 : CollatzResearch.WordTrace tailWord_1720817 prefixEnd_1720817 589070826285399352849075 := by
  unfold tailWord_1720817
  simp only [CollatzResearch.WordTrace]
  refine ⟨62763352206781375990760705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41842234804520917327173803 62763352206781375990760705)
  ·
    refine ⟨47072514155086031993070529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62763352206781375990760705 47072514155086031993070529)
    ·
      refine ⟨35304385616314523994802897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47072514155086031993070529 35304385616314523994802897)
      ·
        refine ⟨26478289212235892996102173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35304385616314523994802897 26478289212235892996102173)
        ·
          refine ⟨9929358454588459873538315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26478289212235892996102173 9929358454588459873538315)
          ·
            refine ⟨14894037681882689810307473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929358454588459873538315 14894037681882689810307473)
            ·
              refine ⟨11170528261412017357730605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14894037681882689810307473 11170528261412017357730605)
              ·
                refine ⟨4188948098029506509148977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11170528261412017357730605 4188948098029506509148977)
                ·
                  refine ⟨3141711073522129881861733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4188948098029506509148977 3141711073522129881861733)
                  ·
                    refine ⟨589070826285399352849075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3141711073522129881861733 589070826285399352849075)
                    ·
                      rfl

theorem cell22_1720817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1720817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720817 prefixEnd_1720817 := by exact prefixLift 1720817
  have htrace : WordTrace (prefixWord ++ tailWord_1720817) baseStart_1720817 baseEnd_1720817 := by
    simpa [prefixWord, tailWord_1720817, baseEnd_1720817] using wordTrace_append hprefix tailTrace_1720817
  have hstable : (prefixWord ++ tailWord_1720817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720817).length < 2 ^ (prefixWord ++ tailWord_1720817).sum := by decide
  have hdescent : baseEnd_1720817 < baseStart_1720817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720838 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1720838 : Nat := 118140960795 + 1720838 * 2 ^ 59
def prefixEnd_1720838 : Nat := 4983230072969 + 3 ^ 40 * 1720838 * 2
def baseEnd_1720838 : Nat := 196359338338187432691337

theorem tailTrace_1720838 : CollatzResearch.WordTrace tailWord_1720838 prefixEnd_1720838 196359338338187432691337 := by
  unfold tailWord_1720838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961378691865790518039849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41842745426470197718183445 1961378691865790518039849)
  ·
    refine ⟨1471034018899342888529887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1961378691865790518039849 1471034018899342888529887)
    ·
      refine ⟨2206551028349014332794831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471034018899342888529887 2206551028349014332794831)
      ·
        refine ⟨3309826542523521499192247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206551028349014332794831 3309826542523521499192247)
        ·
          refine ⟨4964739813785282248788371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309826542523521499192247 4964739813785282248788371)
          ·
            refine ⟨7447109720677923373182557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964739813785282248788371 7447109720677923373182557)
            ·
              refine ⟨2792666145254221264943459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7447109720677923373182557 2792666145254221264943459)
              ·
                refine ⟨4188999217881331897415189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792666145254221264943459 4188999217881331897415189)
                ·
                  refine ⟨196359338338187432691337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4188999217881331897415189 196359338338187432691337)
                  ·
                    rfl

theorem cell22_1720838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1720838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720838 prefixEnd_1720838 := by exact prefixLift 1720838
  have htrace : WordTrace (prefixWord ++ tailWord_1720838) baseStart_1720838 baseEnd_1720838 := by
    simpa [prefixWord, tailWord_1720838, baseEnd_1720838] using wordTrace_append hprefix tailTrace_1720838
  have hstable : (prefixWord ++ tailWord_1720838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720838).length < 2 ^ (prefixWord ++ tailWord_1720838).sum := by decide
  have hdescent : baseEnd_1720838 < baseStart_1720838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720900 : List Nat := [2, 3, 5, 1, 2, 1, 1, 7]
def baseStart_1720900 : Nat := 118140960795 + 1720900 * 2 ^ 59
def prefixEnd_1720900 : Nat := 4983230072969 + 3 ^ 40 * 1720900 * 2
def baseEnd_1720900 : Nat := 65455470986846089224869

theorem tailTrace_1720900 : CollatzResearch.WordTrace tailWord_1720900 prefixEnd_1720900 65455470986846089224869 := by
  unfold tailWord_1720900
  simp only [CollatzResearch.WordTrace]
  refine ⟨31383189732740340583016077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41844252976987120777354769 31383189732740340583016077)
  ·
    refine ⟨11768696149777627718631029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31383189732740340583016077 11768696149777627718631029)
    ·
      refine ⟨1103315264041652598621659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11768696149777627718631029 1103315264041652598621659)
      ·
        refine ⟨1654972896062478897932489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103315264041652598621659 1654972896062478897932489)
        ·
          refine ⟨1241229672046859173449367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654972896062478897932489 1241229672046859173449367)
          ·
            refine ⟨1861844508070288760174051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241229672046859173449367 1861844508070288760174051)
            ·
              refine ⟨2792766762105433140261077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861844508070288760174051 2792766762105433140261077)
              ·
                refine ⟨65455470986846089224869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2792766762105433140261077 65455470986846089224869)
                ·
                  rfl

theorem cell22_1720900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_1720900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720900 prefixEnd_1720900 := by exact prefixLift 1720900
  have htrace : WordTrace (prefixWord ++ tailWord_1720900) baseStart_1720900 baseEnd_1720900 := by
    simpa [prefixWord, tailWord_1720900, baseEnd_1720900] using wordTrace_append hprefix tailTrace_1720900
  have hstable : (prefixWord ++ tailWord_1720900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720900).length < 2 ^ (prefixWord ++ tailWord_1720900).sum := by decide
  have hdescent : baseEnd_1720900 < baseStart_1720900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720907 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_1720907 : Nat := 118140960795 + 1720907 * 2 ^ 59
def prefixEnd_1720907 : Nat := 4983230072969 + 3 ^ 40 * 1720907 * 2
def baseEnd_1720907 : Nat := 589101635124669118098799

theorem tailTrace_1720907 : CollatzResearch.WordTrace tailWord_1720907 prefixEnd_1720907 589101635124669118098799 := by
  unfold tailWord_1720907
  simp only [CollatzResearch.WordTrace]
  refine ⟨62766634776455321361536975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41844423184303547574357983 62766634776455321361536975)
  ·
    refine ⟨94149952164682982042305463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62766634776455321361536975 94149952164682982042305463)
    ·
      refine ⟨141224928247024473063458195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94149952164682982042305463 141224928247024473063458195)
      ·
        refine ⟨211837392370536709595187293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141224928247024473063458195 211837392370536709595187293)
        ·
          refine ⟨79439022138951266098195235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211837392370536709595187293 79439022138951266098195235)
          ·
            refine ⟨119158533208426899147292853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79439022138951266098195235 119158533208426899147292853)
            ·
              refine ⟨11171112488290021795058705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119158533208426899147292853 11171112488290021795058705)
              ·
                refine ⟨8378334366217516346294029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11171112488290021795058705 8378334366217516346294029)
                ·
                  refine ⟨3141875387331568629860261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8378334366217516346294029 3141875387331568629860261)
                  ·
                    refine ⟨589101635124669118098799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3141875387331568629860261 589101635124669118098799)
                    ·
                      rfl

theorem cell22_1720907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_1720907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720907 prefixEnd_1720907 := by exact prefixLift 1720907
  have htrace : WordTrace (prefixWord ++ tailWord_1720907) baseStart_1720907 baseEnd_1720907 := by
    simpa [prefixWord, tailWord_1720907, baseEnd_1720907] using wordTrace_append hprefix tailTrace_1720907
  have hstable : (prefixWord ++ tailWord_1720907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720907).length < 2 ^ (prefixWord ++ tailWord_1720907).sum := by decide
  have hdescent : baseEnd_1720907 < baseStart_1720907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720909 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1720909 : Nat := 118140960795 + 1720909 * 2 ^ 59
def prefixEnd_1720909 : Nat := 4983230072969 + 3 ^ 40 * 1720909 * 2
def baseEnd_1720909 : Nat := 589102319765541779548793

theorem tailTrace_1720909 : CollatzResearch.WordTrace tailWord_1720909 prefixEnd_1720909 589102319765541779548793 := by
  unfold tailWord_1720909
  simp only [CollatzResearch.WordTrace]
  refine ⟨62766707722448075703109781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41844471814965383802073187 62766707722448075703109781)
  ·
    refine ⟨2942189424489753548583271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62766707722448075703109781 2942189424489753548583271)
    ·
      refine ⟨4413284136734630322874907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942189424489753548583271 4413284136734630322874907)
      ·
        refine ⟨6619926205101945484312361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413284136734630322874907 6619926205101945484312361)
        ·
          refine ⟨4964944653826459113234271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6619926205101945484312361 4964944653826459113234271)
          ·
            refine ⟨7447416980739688669851407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964944653826459113234271 7447416980739688669851407)
            ·
              refine ⟨11171125471109533004777111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447416980739688669851407 11171125471109533004777111)
              ·
                refine ⟨16756688206664299507165667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11171125471109533004777111 16756688206664299507165667)
                ·
                  refine ⟨25135032309996449260748501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16756688206664299507165667 25135032309996449260748501)
                  ·
                    refine ⟨589102319765541779548793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25135032309996449260748501 589102319765541779548793)
                    ·
                      rfl

theorem cell22_1720909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1720909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720909 prefixEnd_1720909 := by exact prefixLift 1720909
  have htrace : WordTrace (prefixWord ++ tailWord_1720909) baseStart_1720909 baseEnd_1720909 := by
    simpa [prefixWord, tailWord_1720909, baseEnd_1720909] using wordTrace_append hprefix tailTrace_1720909
  have hstable : (prefixWord ++ tailWord_1720909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720909).length < 2 ^ (prefixWord ++ tailWord_1720909).sum := by decide
  have hdescent : baseEnd_1720909 < baseStart_1720909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720941 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1720941 : Nat := 118140960795 + 1720941 * 2 ^ 59
def prefixEnd_1720941 : Nat := 4983230072969 + 3 ^ 40 * 1720941 * 2
def baseEnd_1720941 : Nat := 589113274019504362748695

theorem tailTrace_1720941 : CollatzResearch.WordTrace tailWord_1720941 prefixEnd_1720941 589113274019504362748695 := by
  unfold tailWord_1720941
  simp only [CollatzResearch.WordTrace]
  refine ⟨62767874858332145168274677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41845249905554763445516451 62767874858332145168274677)
  ·
    refine ⟨5884488267968638609525751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62767874858332145168274677 5884488267968638609525751)
    ·
      refine ⟨8826732401952957914288627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884488267968638609525751 8826732401952957914288627)
      ·
        refine ⟨13240098602929436871432941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8826732401952957914288627 13240098602929436871432941)
        ·
          refine ⟨4965036976098538826787353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13240098602929436871432941 4965036976098538826787353)
          ·
            refine ⟨3723777732073904120090515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4965036976098538826787353 3723777732073904120090515)
            ·
              refine ⟨5585666598110856180135773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723777732073904120090515 5585666598110856180135773)
              ·
                refine ⟨2094624974291571067550915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5585666598110856180135773 2094624974291571067550915)
                ·
                  refine ⟨3141937461437356601326373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094624974291571067550915 3141937461437356601326373)
                  ·
                    refine ⟨589113274019504362748695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3141937461437356601326373 589113274019504362748695)
                    ·
                      rfl

theorem cell22_1720941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1720941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720941 prefixEnd_1720941 := by exact prefixLift 1720941
  have htrace : WordTrace (prefixWord ++ tailWord_1720941) baseStart_1720941 baseEnd_1720941 := by
    simpa [prefixWord, tailWord_1720941, baseEnd_1720941] using wordTrace_append hprefix tailTrace_1720941
  have hstable : (prefixWord ++ tailWord_1720941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720941).length < 2 ^ (prefixWord ++ tailWord_1720941).sum := by decide
  have hdescent : baseEnd_1720941 < baseStart_1720941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720962 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1720962 : Nat := 118140960795 + 1720962 * 2 ^ 59
def prefixEnd_1720962 : Nat := 4983230072969 + 3 ^ 40 * 1720962 * 2
def baseEnd_1720962 : Nat := 196373487582889102657877

theorem tailTrace_1720962 : CollatzResearch.WordTrace tailWord_1720962 prefixEnd_1720962 196373487582889102657877 := by
  unfold tailWord_1720962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15692160197814016438697285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41845760527504043836526093 15692160197814016438697285)
  ·
    refine ⟨2942280037090128082255741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15692160197814016438697285 2942280037090128082255741)
    ·
      refine ⟨1103355013908798030845903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2942280037090128082255741 1103355013908798030845903)
      ·
        refine ⟨1655032520863197046268855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103355013908798030845903 1655032520863197046268855)
        ·
          refine ⟨2482548781294795569403283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655032520863197046268855 2482548781294795569403283)
          ·
            refine ⟨3723823171942193354104925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482548781294795569403283 3723823171942193354104925)
            ·
              refine ⟨1396433689478322507789347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3723823171942193354104925 1396433689478322507789347)
              ·
                refine ⟨2094650534217483761684021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396433689478322507789347 2094650534217483761684021)
                ·
                  refine ⟨196373487582889102657877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2094650534217483761684021 196373487582889102657877)
                  ·
                    rfl

theorem cell22_1720962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1720962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720962 prefixEnd_1720962 := by exact prefixLift 1720962
  have htrace : WordTrace (prefixWord ++ tailWord_1720962) baseStart_1720962 baseEnd_1720962 := by
    simpa [prefixWord, tailWord_1720962, baseEnd_1720962] using wordTrace_append hprefix tailTrace_1720962
  have hstable : (prefixWord ++ tailWord_1720962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720962).length < 2 ^ (prefixWord ++ tailWord_1720962).sum := by decide
  have hdescent : baseEnd_1720962 < baseStart_1720962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720967 : List Nat := [1, 1, 4, 2, 1, 2, 2, 9]
def baseStart_1720967 : Nat := 118140960795 + 1720967 * 2 ^ 59
def prefixEnd_1720967 : Nat := 4983230072969 + 3 ^ 40 * 1720967 * 2
def baseEnd_1720967 : Nat := 65458019372316551288735

theorem tailTrace_1720967 : CollatzResearch.WordTrace tailWord_1720967 prefixEnd_1720967 65458019372316551288735 := by
  unfold tailWord_1720967
  simp only [CollatzResearch.WordTrace]
  refine ⟨62768823156237951608721155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41845882104158634405814103 62768823156237951608721155)
  ·
    refine ⟨94153234734356927413081733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62768823156237951608721155 94153234734356927413081733)
    ·
      refine ⟨17653731512691923889952825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94153234734356927413081733 17653731512691923889952825)
      ·
        refine ⟨13240298634518942917464619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17653731512691923889952825 13240298634518942917464619)
        ·
          refine ⟨19860447951778414376196929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240298634518942917464619 19860447951778414376196929)
          ·
            refine ⟨14895335963833810782147697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19860447951778414376196929 14895335963833810782147697)
            ·
              refine ⟨11171501972875358086610773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14895335963833810782147697 11171501972875358086610773)
              ·
                refine ⟨65458019372316551288735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11171501972875358086610773 65458019372316551288735)
                ·
                  rfl

theorem cell22_1720967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 9].length) (baseStart_1720967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720967 prefixEnd_1720967 := by exact prefixLift 1720967
  have htrace : WordTrace (prefixWord ++ tailWord_1720967) baseStart_1720967 baseEnd_1720967 := by
    simpa [prefixWord, tailWord_1720967, baseEnd_1720967] using wordTrace_append hprefix tailTrace_1720967
  have hstable : (prefixWord ++ tailWord_1720967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720967).length < 2 ^ (prefixWord ++ tailWord_1720967).sum := by decide
  have hdescent : baseEnd_1720967 < baseStart_1720967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720997 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1720997 : Nat := 118140960795 + 1720997 * 2 ^ 59
def prefixEnd_1720997 : Nat := 4983230072969 + 3 ^ 40 * 1720997 * 2
def baseEnd_1720997 : Nat := 589132443963938883348523

theorem tailTrace_1720997 : CollatzResearch.WordTrace tailWord_1720997 prefixEnd_1720997 589132443963938883348523 := by
  unfold tailWord_1720997
  simp only [CollatzResearch.WordTrace]
  refine ⟨62769917346129266732313245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41846611564086177821542163 62769917346129266732313245)
  ·
    refine ⟨23538719004798475024617467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62769917346129266732313245 23538719004798475024617467)
    ·
      refine ⟨35308078507197712536926201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23538719004798475024617467 35308078507197712536926201)
      ·
        refine ⟨26481058880398284402694651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35308078507197712536926201 26481058880398284402694651)
        ·
          refine ⟨39721588320597426604041977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26481058880398284402694651 39721588320597426604041977)
          ·
            refine ⟨29791191240448069953031483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39721588320597426604041977 29791191240448069953031483)
            ·
              refine ⟨44686786860672104929547225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29791191240448069953031483 44686786860672104929547225)
              ·
                refine ⟨33515090145504078697160419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44686786860672104929547225 33515090145504078697160419)
                ·
                  refine ⟨50272635218256118045740629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33515090145504078697160419 50272635218256118045740629)
                  ·
                    refine ⟨589132443963938883348523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50272635218256118045740629 589132443963938883348523)
                    ·
                      rfl

theorem cell22_1720997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1720997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1720997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1720997 prefixEnd_1720997 := by exact prefixLift 1720997
  have htrace : WordTrace (prefixWord ++ tailWord_1720997) baseStart_1720997 baseEnd_1720997 := by
    simpa [prefixWord, tailWord_1720997, baseEnd_1720997] using wordTrace_append hprefix tailTrace_1720997
  have hstable : (prefixWord ++ tailWord_1720997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720997).length < 2 ^ (prefixWord ++ tailWord_1720997).sum := by decide
  have hdescent : baseEnd_1720997 < baseStart_1720997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721119 : List Nat := [1, 1, 2, 4, 2, 3, 9]
def baseStart_1721119 : Nat := 118140960795 + 1721119 * 2 ^ 59
def prefixEnd_1721119 : Nat := 4983230072969 + 3 ^ 40 * 1721119 * 2
def baseEnd_1721119 : Nat := 21821266928043378955487

theorem tailTrace_1721119 : CollatzResearch.WordTrace tailWord_1721119 prefixEnd_1721119 21821266928043378955487 := by
  unfold tailWord_1721119
  simp only [CollatzResearch.WordTrace]
  refine ⟨62774367051687281568254411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41849578034458187712169607 62774367051687281568254411)
  ·
    refine ⟨94161550577530922352381617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62774367051687281568254411 94161550577530922352381617)
    ·
      refine ⟨70621162933148191764286213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94161550577530922352381617 70621162933148191764286213)
      ·
        refine ⟨13241468049965285955803665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70621162933148191764286213 13241468049965285955803665)
        ·
          refine ⟨9931101037473964466852749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13241468049965285955803665 9931101037473964466852749)
          ·
            refine ⟨3724162889052736675069781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9931101037473964466852749 3724162889052736675069781)
            ·
              refine ⟨21821266928043378955487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3724162889052736675069781 21821266928043378955487)
              ·
                rfl

theorem cell22_1721119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 9].length) (baseStart_1721119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721119 prefixEnd_1721119 := by exact prefixLift 1721119
  have htrace : WordTrace (prefixWord ++ tailWord_1721119) baseStart_1721119 baseEnd_1721119 := by
    simpa [prefixWord, tailWord_1721119, baseEnd_1721119] using wordTrace_append hprefix tailTrace_1721119
  have hstable : (prefixWord ++ tailWord_1721119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721119).length < 2 ^ (prefixWord ++ tailWord_1721119).sum := by decide
  have hdescent : baseEnd_1721119 < baseStart_1721119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721140 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1721140 : Nat := 118140960795 + 1721140 * 2 ^ 59
def prefixEnd_1721140 : Nat := 4983230072969 + 3 ^ 40 * 1721140 * 2
def baseEnd_1721140 : Nat := 589181395786334177023085

theorem tailTrace_1721140 : CollatzResearch.WordTrace tailWord_1721140 prefixEnd_1721140 589181395786334177023085 := by
  unfold tailWord_1721140
  simp only [CollatzResearch.WordTrace]
  refine ⟨31387566492305601077384437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41850088656407468103179249 31387566492305601077384437)
  ·
    refine ⟨2942584358653650101004791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31387566492305601077384437 2942584358653650101004791)
    ·
      refine ⟨4413876537980475151507187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942584358653650101004791 4413876537980475151507187)
      ·
        refine ⟨6620814806970712727260781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413876537980475151507187 6620814806970712727260781)
        ·
          refine ⟨2482805552614017272722793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6620814806970712727260781 2482805552614017272722793)
          ·
            refine ⟨1862104164460512954542095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482805552614017272722793 1862104164460512954542095)
            ·
              refine ⟨2793156246690769431813143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862104164460512954542095 2793156246690769431813143)
              ·
                refine ⟨4189734370036154147719715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793156246690769431813143 4189734370036154147719715)
                ·
                  refine ⟨6284601555054231221579573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189734370036154147719715 6284601555054231221579573)
                  ·
                    refine ⟨589181395786334177023085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6284601555054231221579573 589181395786334177023085)
                    ·
                      rfl

theorem cell22_1721140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1721140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721140 prefixEnd_1721140 := by exact prefixLift 1721140
  have htrace : WordTrace (prefixWord ++ tailWord_1721140) baseStart_1721140 baseEnd_1721140 := by
    simpa [prefixWord, tailWord_1721140, baseEnd_1721140] using wordTrace_append hprefix tailTrace_1721140
  have hstable : (prefixWord ++ tailWord_1721140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721140).length < 2 ^ (prefixWord ++ tailWord_1721140).sum := by decide
  have hdescent : baseEnd_1721140 < baseStart_1721140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721153 : List Nat := [1, 2, 5, 3, 1, 1, 1, 8]
def baseStart_1721153 : Nat := 118140960795 + 1721153 * 2 ^ 59
def prefixEnd_1721153 : Nat := 4983230072969 + 3 ^ 40 * 1721153 * 2
def baseEnd_1721153 : Nat := 65465093994667386272005

theorem tailTrace_1721153 : CollatzResearch.WordTrace tailWord_1721153 prefixEnd_1721153 65465093994667386272005 := by
  unfold tailWord_1721153
  simp only [CollatzResearch.WordTrace]
  refine ⟨62775607133564105374992113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41850404755709403583328075 62775607133564105374992113)
  ·
    refine ⟨47081705350173079031244085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62775607133564105374992113 47081705350173079031244085)
    ·
      refine ⟨4413909876578726159179133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47081705350173079031244085 4413909876578726159179133)
      ·
        refine ⟨1655216203717022309692175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4413909876578726159179133 1655216203717022309692175)
        ·
          refine ⟨2482824305575533464538263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655216203717022309692175 2482824305575533464538263)
          ·
            refine ⟨3724236458363300196807395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482824305575533464538263 3724236458363300196807395)
            ·
              refine ⟨5586354687544950295211093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724236458363300196807395 5586354687544950295211093)
              ·
                refine ⟨65465093994667386272005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5586354687544950295211093 65465093994667386272005)
                ·
                  rfl

theorem cell22_1721153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 8].length) (baseStart_1721153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721153 prefixEnd_1721153 := by exact prefixLift 1721153
  have htrace : WordTrace (prefixWord ++ tailWord_1721153) baseStart_1721153 baseEnd_1721153 := by
    simpa [prefixWord, tailWord_1721153, baseEnd_1721153] using wordTrace_append hprefix tailTrace_1721153
  have hstable : (prefixWord ++ tailWord_1721153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721153).length < 2 ^ (prefixWord ++ tailWord_1721153).sum := by decide
  have hdescent : baseEnd_1721153 < baseStart_1721153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721273 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_1721273 : Nat := 118140960795 + 1721273 * 2 ^ 59
def prefixEnd_1721273 : Nat := 4983230072969 + 3 ^ 40 * 1721273 * 2
def baseEnd_1721273 : Nat := 589226924404366163447677

theorem tailTrace_1721273 : CollatzResearch.WordTrace tailWord_1721273 prefixEnd_1721273 589226924404366163447677 := by
  unfold tailWord_1721273
  simp only [CollatzResearch.WordTrace]
  refine ⟨62779983893129365869360473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41853322595419577246240315 62779983893129365869360473)
  ·
    refine ⟨47084987919847024402020355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62779983893129365869360473 47084987919847024402020355)
    ·
      refine ⟨70627481879770536603030533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47084987919847024402020355 70627481879770536603030533)
      ·
        refine ⟨13242652852456975613068225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70627481879770536603030533 13242652852456975613068225)
        ·
          refine ⟨9931989639342731709801169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13242652852456975613068225 9931989639342731709801169)
          ·
            refine ⟨7448992229507048782350877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9931989639342731709801169 7448992229507048782350877)
            ·
              refine ⟨2793372086065143293381579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7448992229507048782350877 2793372086065143293381579)
              ·
                refine ⟨4190058129097714940072369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793372086065143293381579 4190058129097714940072369)
                ·
                  refine ⟨3142543596823286205054277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190058129097714940072369 3142543596823286205054277)
                  ·
                    refine ⟨589226924404366163447677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142543596823286205054277 589226924404366163447677)
                    ·
                      rfl

theorem cell22_1721273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_1721273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721273 prefixEnd_1721273 := by exact prefixLift 1721273
  have htrace : WordTrace (prefixWord ++ tailWord_1721273) baseStart_1721273 baseEnd_1721273 := by
    simpa [prefixWord, tailWord_1721273, baseEnd_1721273] using wordTrace_append hprefix tailTrace_1721273
  have hstable : (prefixWord ++ tailWord_1721273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721273).length < 2 ^ (prefixWord ++ tailWord_1721273).sum := by decide
  have hdescent : baseEnd_1721273 < baseStart_1721273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721354 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_1721354 : Nat := 118140960795 + 1721354 * 2 ^ 59
def prefixEnd_1721354 : Nat := 4983230072969 + 3 ^ 40 * 1721354 * 2
def baseEnd_1721354 : Nat := 589254652359708952172429

theorem tailTrace_1721354 : CollatzResearch.WordTrace tailWord_1721354 prefixEnd_1721354 589254652359708952172429 := by
  unfold tailWord_1721354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695734551458979175764779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41855292137223944468706077 15695734551458979175764779)
  ·
    refine ⟨23543601827188468763647169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15695734551458979175764779 23543601827188468763647169)
    ·
      refine ⟨17657701370391351572735377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23543601827188468763647169 17657701370391351572735377)
      ·
        refine ⟨13243276027793513679551533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17657701370391351572735377 13243276027793513679551533)
        ·
          refine ⟨4966228510422567629831825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13243276027793513679551533 4966228510422567629831825)
          ·
            refine ⟨3724671382816925722373869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966228510422567629831825 3724671382816925722373869)
            ·
              refine ⟨1396751768556347145890201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3724671382816925722373869 1396751768556347145890201)
              ·
                refine ⟨1047563826417260359417651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396751768556347145890201 1047563826417260359417651)
                ·
                  refine ⟨1571345739625890539126477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047563826417260359417651 1571345739625890539126477)
                  ·
                    refine ⟨589254652359708952172429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571345739625890539126477 589254652359708952172429)
                    ·
                      rfl

theorem cell22_1721354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_1721354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721354 prefixEnd_1721354 := by exact prefixLift 1721354
  have htrace : WordTrace (prefixWord ++ tailWord_1721354) baseStart_1721354 baseEnd_1721354 := by
    simpa [prefixWord, tailWord_1721354, baseEnd_1721354] using wordTrace_append hprefix tailTrace_1721354
  have hstable : (prefixWord ++ tailWord_1721354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721354).length < 2 ^ (prefixWord ++ tailWord_1721354).sum := by decide
  have hdescent : baseEnd_1721354 < baseStart_1721354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721367 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 5]
def baseStart_1721367 : Nat := 118140960795 + 1721367 * 2 ^ 59
def prefixEnd_1721367 : Nat := 4983230072969 + 3 ^ 40 * 1721367 * 2
def baseEnd_1721367 : Nat := 196419700841793750532463

theorem tailTrace_1721367 : CollatzResearch.WordTrace tailWord_1721367 prefixEnd_1721367 196419700841793750532463 := by
  unfold tailWord_1721367
  simp only [CollatzResearch.WordTrace]
  refine ⟨62783412354788819923282355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41855608236525879948854903 62783412354788819923282355)
  ·
    refine ⟨94175118532183229884923533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62783412354788819923282355 94175118532183229884923533)
    ·
      refine ⟨35315669449568711206846325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94175118532183229884923533 35315669449568711206846325)
      ·
        refine ⟨3310844010897066675641843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35315669449568711206846325 3310844010897066675641843)
        ·
          refine ⟨4966266016345600013462765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310844010897066675641843 4966266016345600013462765)
          ·
            refine ⟨1862349756129600005048537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4966266016345600013462765 1862349756129600005048537)
            ·
              refine ⟨1396762317097200003786403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862349756129600005048537 1396762317097200003786403)
              ·
                refine ⟨2095143475645800005679605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396762317097200003786403 2095143475645800005679605)
                ·
                  refine ⟨196419700841793750532463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095143475645800005679605 196419700841793750532463)
                  ·
                    rfl

theorem cell22_1721367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 5].length) (baseStart_1721367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721367 prefixEnd_1721367 := by exact prefixLift 1721367
  have htrace : WordTrace (prefixWord ++ tailWord_1721367) baseStart_1721367 baseEnd_1721367 := by
    simpa [prefixWord, tailWord_1721367, baseEnd_1721367] using wordTrace_append hprefix tailTrace_1721367
  have hstable : (prefixWord ++ tailWord_1721367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721367).length < 2 ^ (prefixWord ++ tailWord_1721367).sum := by decide
  have hdescent : baseEnd_1721367 < baseStart_1721367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721380 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1721380 : Nat := 118140960795 + 1721380 * 2 ^ 59
def prefixEnd_1721380 : Nat := 4983230072969 + 3 ^ 40 * 1721380 * 2
def baseEnd_1721380 : Nat := 589263552691053551022349

theorem tailTrace_1721380 : CollatzResearch.WordTrace tailWord_1721380 prefixEnd_1721380 589263552691053551022349 := by
  unfold tailWord_1721380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391943251870861571752797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41855924335827815429003729 31391943251870861571752797)
  ·
    refine ⟨11771978719451573089407299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31391943251870861571752797 11771978719451573089407299)
    ·
      refine ⟨17657968079177359634110949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771978719451573089407299 17657968079177359634110949)
      ·
        refine ⟨3310869014845754931395803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17657968079177359634110949 3310869014845754931395803)
        ·
          refine ⟨4966303522268632397093705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310869014845754931395803 4966303522268632397093705)
          ·
            refine ⟨3724727641701474297820279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966303522268632397093705 3724727641701474297820279)
            ·
              refine ⟨5587091462552211446730419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724727641701474297820279 5587091462552211446730419)
              ·
                refine ⟨8380637193828317170095629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587091462552211446730419 8380637193828317170095629)
                ·
                  refine ⟨3142738947685618938785861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8380637193828317170095629 3142738947685618938785861)
                  ·
                    refine ⟨589263552691053551022349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142738947685618938785861 589263552691053551022349)
                    ·
                      rfl

theorem cell22_1721380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1721380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721380 prefixEnd_1721380 := by exact prefixLift 1721380
  have htrace : WordTrace (prefixWord ++ tailWord_1721380) baseStart_1721380 baseEnd_1721380 := by
    simpa [prefixWord, tailWord_1721380, baseEnd_1721380] using wordTrace_append hprefix tailTrace_1721380
  have hstable : (prefixWord ++ tailWord_1721380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721380).length < 2 ^ (prefixWord ++ tailWord_1721380).sum := by decide
  have hdescent : baseEnd_1721380 < baseStart_1721380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721391 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_1721391 : Nat := 118140960795 + 1721391 * 2 ^ 59
def prefixEnd_1721391 : Nat := 4983230072969 + 3 ^ 40 * 1721391 * 2
def baseEnd_1721391 : Nat := 589267318215853188997315

theorem tailTrace_1721391 : CollatzResearch.WordTrace tailWord_1721391 prefixEnd_1721391 589267318215853188997315 := by
  unfold tailWord_1721391
  simp only [CollatzResearch.WordTrace]
  refine ⟨62784287706701872022156027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41856191804467914681437351 62784287706701872022156027)
  ·
    refine ⟨94176431560052808033234041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62784287706701872022156027 94176431560052808033234041)
    ·
      refine ⟨70632323670039606024925531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94176431560052808033234041 70632323670039606024925531)
      ·
        refine ⟨105948485505059409037388297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70632323670039606024925531 105948485505059409037388297)
        ·
          refine ⟨79461364128794556778041223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105948485505059409037388297 79461364128794556778041223)
          ·
            refine ⟨119192046193191835167061835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79461364128794556778041223 119192046193191835167061835)
            ·
              refine ⟨178788069289787752750592753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119192046193191835167061835 178788069289787752750592753)
              ·
                refine ⟨134091051967340814562944565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178788069289787752750592753 134091051967340814562944565)
                ·
                  refine ⟨12571036121938201365276053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134091051967340814562944565 12571036121938201365276053)
                  ·
                    refine ⟨589267318215853188997315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12571036121938201365276053 589267318215853188997315)
                    ·
                      rfl

theorem cell22_1721391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_1721391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721391 prefixEnd_1721391 := by exact prefixLift 1721391
  have htrace : WordTrace (prefixWord ++ tailWord_1721391) baseStart_1721391 baseEnd_1721391 := by
    simpa [prefixWord, tailWord_1721391, baseEnd_1721391] using wordTrace_append hprefix tailTrace_1721391
  have hstable : (prefixWord ++ tailWord_1721391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721391).length < 2 ^ (prefixWord ++ tailWord_1721391).sum := by decide
  have hdescent : baseEnd_1721391 < baseStart_1721391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721393 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1721393 : Nat := 118140960795 + 1721393 * 2 ^ 59
def prefixEnd_1721393 : Nat := 4983230072969 + 3 ^ 40 * 1721393 * 2
def baseEnd_1721393 : Nat := 589268002856725850447309

theorem tailTrace_1721393 : CollatzResearch.WordTrace tailWord_1721393 prefixEnd_1721393 589268002856725850447309 := by
  unfold tailWord_1721393
  simp only [CollatzResearch.WordTrace]
  refine ⟨62784360652694626363728833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41856240435129750909152555 62784360652694626363728833)
  ·
    refine ⟨47088270489520969772796625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62784360652694626363728833 47088270489520969772796625)
    ·
      refine ⟨35316202867140727329597469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47088270489520969772796625 35316202867140727329597469)
      ·
        refine ⟨13243576075177772748599051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35316202867140727329597469 13243576075177772748599051)
        ·
          refine ⟨19865364112766659122898577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13243576075177772748599051 19865364112766659122898577)
          ·
            refine ⟨14899023084574994342173933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19865364112766659122898577 14899023084574994342173933)
            ·
              refine ⟨5587133656715622878315225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14899023084574994342173933 5587133656715622878315225)
              ·
                refine ⟨4190350242536717158736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5587133656715622878315225 4190350242536717158736419)
                ·
                  refine ⟨6285525363805075738104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190350242536717158736419 6285525363805075738104629)
                  ·
                    refine ⟨589268002856725850447309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6285525363805075738104629 589268002856725850447309)
                    ·
                      rfl

theorem cell22_1721393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1721393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721393 prefixEnd_1721393 := by exact prefixLift 1721393
  have htrace : WordTrace (prefixWord ++ tailWord_1721393) baseStart_1721393 baseEnd_1721393 := by
    simpa [prefixWord, tailWord_1721393, baseEnd_1721393] using wordTrace_append hprefix tailTrace_1721393
  have hstable : (prefixWord ++ tailWord_1721393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721393).length < 2 ^ (prefixWord ++ tailWord_1721393).sum := by decide
  have hdescent : baseEnd_1721393 < baseStart_1721393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721408 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_1721408 : Nat := 118140960795 + 1721408 * 2 ^ 59
def prefixEnd_1721408 : Nat := 4983230072969 + 3 ^ 40 * 1721408 * 2
def baseEnd_1721408 : Nat := 589273137663270811322263

theorem tailTrace_1721408 : CollatzResearch.WordTrace tailWord_1721408 prefixEnd_1721408 589273137663270811322263 := by
  unfold tailWord_1721408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31392453873820141962762439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41856605165093522617016585 31392453873820141962762439)
  ·
    refine ⟨47088680810730212944143659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31392453873820141962762439 47088680810730212944143659)
    ·
      refine ⟨70633021216095319416215489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47088680810730212944143659 70633021216095319416215489)
      ·
        refine ⟨52974765912071489562161617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70633021216095319416215489 52974765912071489562161617)
        ·
          refine ⟨39731074434053617171621213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52974765912071489562161617 39731074434053617171621213)
          ·
            refine ⟨14899152912770106439357955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39731074434053617171621213 14899152912770106439357955)
            ·
              refine ⟨22348729369155159659036933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899152912770106439357955 22348729369155159659036933)
              ·
                refine ⟨4190386756716592436069425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22348729369155159659036933 4190386756716592436069425)
                ·
                  refine ⟨3142790067537444327052069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190386756716592436069425 3142790067537444327052069)
                  ·
                    refine ⟨589273137663270811322263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142790067537444327052069 589273137663270811322263)
                    ·
                      rfl

theorem cell22_1721408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_1721408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721408 prefixEnd_1721408 := by exact prefixLift 1721408
  have htrace : WordTrace (prefixWord ++ tailWord_1721408) baseStart_1721408 baseEnd_1721408 := by
    simpa [prefixWord, tailWord_1721408, baseEnd_1721408] using wordTrace_append hprefix tailTrace_1721408
  have hstable : (prefixWord ++ tailWord_1721408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721408).length < 2 ^ (prefixWord ++ tailWord_1721408).sum := by decide
  have hdescent : baseEnd_1721408 < baseStart_1721408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721442 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1721442 : Nat := 118140960795 + 1721442 * 2 ^ 59
def prefixEnd_1721442 : Nat := 4983230072969 + 3 ^ 40 * 1721442 * 2
def baseEnd_1721442 : Nat := 589284776558106055972159

theorem tailTrace_1721442 : CollatzResearch.WordTrace tailWord_1721442 prefixEnd_1721442 589284776558106055972159 := by
  unfold tailWord_1721442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696536957379276933065645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41857431886344738488175053 15696536957379276933065645)
  ·
    refine ⟨5886201359017228849899617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15696536957379276933065645 5886201359017228849899617)
    ·
      refine ⟨4414651019262921637424713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5886201359017228849899617 4414651019262921637424713)
      ·
        refine ⟨3310988264447191228068535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4414651019262921637424713 3310988264447191228068535)
        ·
          refine ⟨4966482396670786842102803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310988264447191228068535 4966482396670786842102803)
          ·
            refine ⟨7449723595006180263154205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966482396670786842102803 7449723595006180263154205)
            ·
              refine ⟨2793646348127317598682827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7449723595006180263154205 2793646348127317598682827)
              ·
                refine ⟨4190469522190976398024241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793646348127317598682827 4190469522190976398024241)
                ·
                  refine ⟨3142852141643232298518181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190469522190976398024241 3142852141643232298518181)
                  ·
                    refine ⟨589284776558106055972159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3142852141643232298518181 589284776558106055972159)
                    ·
                      rfl

theorem cell22_1721442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1721442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721442 prefixEnd_1721442 := by exact prefixLift 1721442
  have htrace : WordTrace (prefixWord ++ tailWord_1721442) baseStart_1721442 baseEnd_1721442 := by
    simpa [prefixWord, tailWord_1721442, baseEnd_1721442] using wordTrace_append hprefix tailTrace_1721442
  have hstable : (prefixWord ++ tailWord_1721442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721442).length < 2 ^ (prefixWord ++ tailWord_1721442).sum := by decide
  have hdescent : baseEnd_1721442 < baseStart_1721442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721461 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1721461 : Nat := 118140960795 + 1721461 * 2 ^ 59
def prefixEnd_1721461 : Nat := 4983230072969 + 3 ^ 40 * 1721461 * 2
def baseEnd_1721461 : Nat := 589291280646396339747101

theorem tailTrace_1721461 : CollatzResearch.WordTrace tailWord_1721461 prefixEnd_1721461 589291280646396339747101 := by
  unfold tailWord_1721461
  simp only [CollatzResearch.WordTrace]
  refine ⟨62786840816448273977204237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41857893877632182651469491 62786840816448273977204237)
  ·
    refine ⟨23545065306168102741451589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62786840816448273977204237 23545065306168102741451589)
    ·
      refine ⟨4414699744906519264022173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23545065306168102741451589 4414699744906519264022173)
      ·
        refine ⟨1655512404339944724008315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4414699744906519264022173 1655512404339944724008315)
        ·
          refine ⟨2483268606509917086012473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655512404339944724008315 2483268606509917086012473)
          ·
            refine ⟨1862451454882437814509355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2483268606509917086012473 1862451454882437814509355)
            ·
              refine ⟨2793677182323656721764033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862451454882437814509355 2793677182323656721764033)
              ·
                refine ⟨2095257886742742541323025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793677182323656721764033 2095257886742742541323025)
                ·
                  refine ⟨1571443415057056905992269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095257886742742541323025 1571443415057056905992269)
                  ·
                    refine ⟨589291280646396339747101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571443415057056905992269 589291280646396339747101)
                    ·
                      rfl

theorem cell22_1721461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1721461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721461 prefixEnd_1721461 := by exact prefixLift 1721461
  have htrace : WordTrace (prefixWord ++ tailWord_1721461) baseStart_1721461 baseEnd_1721461 := by
    simpa [prefixWord, tailWord_1721461, baseEnd_1721461] using wordTrace_append hprefix tailTrace_1721461
  have hstable : (prefixWord ++ tailWord_1721461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721461).length < 2 ^ (prefixWord ++ tailWord_1721461).sum := by decide
  have hdescent : baseEnd_1721461 < baseStart_1721461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721468 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_1721468 : Nat := 118140960795 + 1721468 * 2 ^ 59
def prefixEnd_1721468 : Nat := 4983230072969 + 3 ^ 40 * 1721468 * 2
def baseEnd_1721468 : Nat := 196431225629816884940693

theorem tailTrace_1721468 : CollatzResearch.WordTrace tailWord_1721468 prefixEnd_1721468 196431225629816884940693 := by
  unfold tailWord_1721468
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393548063711457086354529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41858064084948609448472705 31393548063711457086354529)
  ·
    refine ⟨23545161047783592814765897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31393548063711457086354529 23545161047783592814765897)
    ·
      refine ⟨17658870785837694611074423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23545161047783592814765897 17658870785837694611074423)
      ·
        refine ⟨26488306178756541916611635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17658870785837694611074423 26488306178756541916611635)
        ·
          refine ⟨39732459268134812874917453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26488306178756541916611635 39732459268134812874917453)
          ·
            refine ⟨14899672225550554828094045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39732459268134812874917453 14899672225550554828094045)
            ·
              refine ⟨5587377084581458060535267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14899672225550554828094045 5587377084581458060535267)
              ·
                refine ⟨8381065626872187090802901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587377084581458060535267 8381065626872187090802901)
                ·
                  refine ⟨196431225629816884940693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8381065626872187090802901 196431225629816884940693)
                  ·
                    rfl

theorem cell22_1721468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_1721468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721468 prefixEnd_1721468 := by exact prefixLift 1721468
  have htrace : WordTrace (prefixWord ++ tailWord_1721468) baseStart_1721468 baseEnd_1721468 := by
    simpa [prefixWord, tailWord_1721468, baseEnd_1721468] using wordTrace_append hprefix tailTrace_1721468
  have hstable : (prefixWord ++ tailWord_1721468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721468).length < 2 ^ (prefixWord ++ tailWord_1721468).sum := by decide
  have hdescent : baseEnd_1721468 < baseStart_1721468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721472 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 1, 3]
def baseStart_1721472 : Nat := 118140960795 + 1721472 * 2 ^ 59
def prefixEnd_1721472 : Nat := 4983230072969 + 3 ^ 40 * 1721472 * 2
def baseEnd_1721472 : Nat := 589295046171195977722067

theorem tailTrace_1721472 : CollatzResearch.WordTrace tailWord_1721472 prefixEnd_1721472 589295046171195977722067 := by
  unfold tailWord_1721472
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393621009704211427927335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41858161346272281903903113 31393621009704211427927335)
  ·
    refine ⟨47090431514556317141891003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31393621009704211427927335 47090431514556317141891003)
    ·
      refine ⟨70635647271834475712836505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47090431514556317141891003 70635647271834475712836505)
      ·
        refine ⟨52976735453875856784627379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70635647271834475712836505 52976735453875856784627379)
        ·
          refine ⟨79465103180813785176941069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52976735453875856784627379 79465103180813785176941069)
          ·
            refine ⟨29799413692805169441352901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79465103180813785176941069 29799413692805169441352901)
            ·
              refine ⟨5587390067400969270253669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29799413692805169441352901 5587390067400969270253669)
              ·
                refine ⟨1047635637637681738172563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5587390067400969270253669 1047635637637681738172563)
                ·
                  refine ⟨1571453456456522607258845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047635637637681738172563 1571453456456522607258845)
                  ·
                    refine ⟨589295046171195977722067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571453456456522607258845 589295046171195977722067)
                    ·
                      rfl

theorem cell22_1721472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_1721472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721472 prefixEnd_1721472 := by exact prefixLift 1721472
  have htrace : WordTrace (prefixWord ++ tailWord_1721472) baseStart_1721472 baseEnd_1721472 := by
    simpa [prefixWord, tailWord_1721472, baseEnd_1721472] using wordTrace_append hprefix tailTrace_1721472
  have hstable : (prefixWord ++ tailWord_1721472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721472).length < 2 ^ (prefixWord ++ tailWord_1721472).sum := by decide
  have hdescent : baseEnd_1721472 < baseStart_1721472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721528 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1721528 : Nat := 118140960795 + 1721528 * 2 ^ 59
def prefixEnd_1721528 : Nat := 4983230072969 + 3 ^ 40 * 1721528 * 2
def baseEnd_1721528 : Nat := 589314216115630498321895

theorem tailTrace_1721528 : CollatzResearch.WordTrace tailWord_1721528 prefixEnd_1721528 589314216115630498321895 := by
  unfold tailWord_1721528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31394642253602772209946619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41859523004803696279928825 31394642253602772209946619)
  ·
    refine ⟨47091963380404158314919929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31394642253602772209946619 47091963380404158314919929)
    ·
      refine ⟨35318972535303118736189947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47091963380404158314919929 35318972535303118736189947)
      ·
        refine ⟨52978458802954678104284921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35318972535303118736189947 52978458802954678104284921)
        ·
          refine ⟨39733844102216008578213691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52978458802954678104284921 39733844102216008578213691)
          ·
            refine ⟨59600766153324012867320537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39733844102216008578213691 59600766153324012867320537)
            ·
              refine ⟨44700574614993009650490403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59600766153324012867320537 44700574614993009650490403)
              ·
                refine ⟨67050861922489514475735605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44700574614993009650490403 67050861922489514475735605)
                ·
                  refine ⟨6286018305233391982100213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67050861922489514475735605 6286018305233391982100213)
                  ·
                    refine ⟨589314216115630498321895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6286018305233391982100213 589314216115630498321895)
                    ·
                      rfl

theorem cell22_1721528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1721528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721528 prefixEnd_1721528 := by exact prefixLift 1721528
  have htrace : WordTrace (prefixWord ++ tailWord_1721528) baseStart_1721528 baseEnd_1721528 := by
    simpa [prefixWord, tailWord_1721528, baseEnd_1721528] using wordTrace_append hprefix tailTrace_1721528
  have hstable : (prefixWord ++ tailWord_1721528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721528).length < 2 ^ (prefixWord ++ tailWord_1721528).sum := by decide
  have hdescent : baseEnd_1721528 < baseStart_1721528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721543 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1721543 : Nat := 118140960795 + 1721543 * 2 ^ 59
def prefixEnd_1721543 : Nat := 4983230072969 + 3 ^ 40 * 1721543 * 2
def baseEnd_1721543 : Nat := 589319350922175459196849

theorem tailTrace_1721543 : CollatzResearch.WordTrace tailWord_1721543 prefixEnd_1721543 589319350922175459196849 := by
  unfold tailWord_1721543
  simp only [CollatzResearch.WordTrace]
  refine ⟨62789831602151201981689283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41859887734767467987792855 62789831602151201981689283)
  ·
    refine ⟨94184747403226802972533925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62789831602151201981689283 94184747403226802972533925)
    ·
      refine ⟨17659640138105025557350111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94184747403226802972533925 17659640138105025557350111)
      ·
        refine ⟨26489460207157538336025167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17659640138105025557350111 26489460207157538336025167)
        ·
          refine ⟨39734190310736307504037751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26489460207157538336025167 39734190310736307504037751)
          ·
            refine ⟨59601285466104461256056627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39734190310736307504037751 59601285466104461256056627)
            ·
              refine ⟨89401928199156691884084941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59601285466104461256056627 89401928199156691884084941)
              ·
                refine ⟨33525723074683759456531853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89401928199156691884084941 33525723074683759456531853)
                ·
                  refine ⟨12572146153006409796199445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33525723074683759456531853 12572146153006409796199445)
                  ·
                    refine ⟨589319350922175459196849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12572146153006409796199445 589319350922175459196849)
                    ·
                      rfl

theorem cell22_1721543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1721543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721543 prefixEnd_1721543 := by exact prefixLift 1721543
  have htrace : WordTrace (prefixWord ++ tailWord_1721543) baseStart_1721543 baseEnd_1721543 := by
    simpa [prefixWord, tailWord_1721543, baseEnd_1721543] using wordTrace_append hprefix tailTrace_1721543
  have hstable : (prefixWord ++ tailWord_1721543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721543).length < 2 ^ (prefixWord ++ tailWord_1721543).sum := by decide
  have hdescent : baseEnd_1721543 < baseStart_1721543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721575 : List Nat := [1, 1, 5, 3, 2, 10]
def baseStart_1721575 : Nat := 118140960795 + 1721575 * 2 ^ 59
def prefixEnd_1721575 : Nat := 4983230072969 + 3 ^ 40 * 1721575 * 2
def baseEnd_1721575 : Nat := 7275682779952321511071

theorem tailTrace_1721575 : CollatzResearch.WordTrace tailWord_1721575 prefixEnd_1721575 7275682779952321511071 := by
  unfold tailWord_1721575
  simp only [CollatzResearch.WordTrace]
  refine ⟨62790998738035271446854179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41860665825356847631236119 62790998738035271446854179)
  ·
    refine ⟨94186498107052907170281269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62790998738035271446854179 94186498107052907170281269)
    ·
      refine ⟨8829984197536210047213869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94186498107052907170281269 8829984197536210047213869)
      ·
        refine ⟨3311244074076078767705201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8829984197536210047213869 3311244074076078767705201)
        ·
          refine ⟨2483433055557059075778901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3311244074076078767705201 2483433055557059075778901)
          ·
            refine ⟨7275682779952321511071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2483433055557059075778901 7275682779952321511071)
            ·
              rfl

theorem cell22_1721575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 10].length) (baseStart_1721575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721575 prefixEnd_1721575 := by exact prefixLift 1721575
  have htrace : WordTrace (prefixWord ++ tailWord_1721575) baseStart_1721575 baseEnd_1721575 := by
    simpa [prefixWord, tailWord_1721575, baseEnd_1721575] using wordTrace_append hprefix tailTrace_1721575
  have hstable : (prefixWord ++ tailWord_1721575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721575).length < 2 ^ (prefixWord ++ tailWord_1721575).sum := by decide
  have hdescent : baseEnd_1721575 < baseStart_1721575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721581 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1721581 : Nat := 118140960795 + 1721581 * 2 ^ 59
def prefixEnd_1721581 : Nat := 4983230072969 + 3 ^ 40 * 1721581 * 2
def baseEnd_1721581 : Nat := 196444119699585342248911

theorem tailTrace_1721581 : CollatzResearch.WordTrace tailWord_1721581 prefixEnd_1721581 196444119699585342248911 := by
  unfold tailWord_1721581
  simp only [CollatzResearch.WordTrace]
  refine ⟨62791217576013534471572597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41860811717342356314381731 62791217576013534471572597)
  ·
    refine ⟨5886676647751268856709931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62791217576013534471572597 5886676647751268856709931)
    ·
      refine ⟨8830014971626903285064897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886676647751268856709931 8830014971626903285064897)
      ·
        refine ⟨6622511228720177463798673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8830014971626903285064897 6622511228720177463798673)
        ·
          refine ⟨4966883421540133097849005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6622511228720177463798673 4966883421540133097849005)
          ·
            refine ⟨1862581283077549911693377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4966883421540133097849005 1862581283077549911693377)
            ·
              refine ⟨1396935962308162433770033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862581283077549911693377 1396935962308162433770033)
              ·
                refine ⟨1047701971731121825327525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396935962308162433770033 1047701971731121825327525)
                ·
                  refine ⟨196444119699585342248911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047701971731121825327525 196444119699585342248911)
                  ·
                    rfl

theorem cell22_1721581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1721581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721581 prefixEnd_1721581 := by exact prefixLift 1721581
  have htrace : WordTrace (prefixWord ++ tailWord_1721581) baseStart_1721581 baseEnd_1721581 := by
    simpa [prefixWord, tailWord_1721581, baseEnd_1721581] using wordTrace_append hprefix tailTrace_1721581
  have hstable : (prefixWord ++ tailWord_1721581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721581).length < 2 ^ (prefixWord ++ tailWord_1721581).sum := by decide
  have hdescent : baseEnd_1721581 < baseStart_1721581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1721590 : Nat := 118140960795 + 1721590 * 2 ^ 59
def prefixEnd_1721590 : Nat := 4983230072969 + 3 ^ 40 * 1721590 * 2
def baseEnd_1721590 : Nat := 589335439982683003271705

theorem tailTrace_1721590 : CollatzResearch.WordTrace tailWord_1721590 prefixEnd_1721590 589335439982683003271705 := by
  unfold tailWord_1721590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924471614561308063040639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41861030555320619339100149 3924471614561308063040639)
  ·
    refine ⟨5886707421841962094560959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924471614561308063040639 5886707421841962094560959)
    ·
      refine ⟨8830061132762943141841439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886707421841962094560959 8830061132762943141841439)
      ·
        refine ⟨13245091699144414712762159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830061132762943141841439 13245091699144414712762159)
        ·
          refine ⟨19867637548716622069143239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245091699144414712762159 19867637548716622069143239)
          ·
            refine ⟨29801456323074933103714859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19867637548716622069143239 29801456323074933103714859)
            ·
              refine ⟨44702184484612399655572289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29801456323074933103714859 44702184484612399655572289)
              ·
                refine ⟨33526638363459299741679217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44702184484612399655572289 33526638363459299741679217)
                ·
                  refine ⟨25144978772594474806259413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33526638363459299741679217 25144978772594474806259413)
                  ·
                    refine ⟨589335439982683003271705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25144978772594474806259413 589335439982683003271705)
                    ·
                      rfl

theorem cell22_1721590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1721590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721590 prefixEnd_1721590 := by exact prefixLift 1721590
  have htrace : WordTrace (prefixWord ++ tailWord_1721590) baseStart_1721590 baseEnd_1721590 := by
    simpa [prefixWord, tailWord_1721590, baseEnd_1721590] using wordTrace_append hprefix tailTrace_1721590
  have hstable : (prefixWord ++ tailWord_1721590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721590).length < 2 ^ (prefixWord ++ tailWord_1721590).sum := by decide
  have hdescent : baseEnd_1721590 < baseStart_1721590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721624 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 1, 3]
def baseStart_1721624 : Nat := 118140960795 + 1721624 * 2 ^ 59
def prefixEnd_1721624 : Nat := 4983230072969 + 3 ^ 40 * 1721624 * 2
def baseEnd_1721624 : Nat := 589347078877518247921601

theorem tailTrace_1721624 : CollatzResearch.WordTrace tailWord_1721624 prefixEnd_1721624 589347078877518247921601 := by
  unfold tailWord_1721624
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396392957428876407693963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41861857276571835210258617 31396392957428876407693963)
  ·
    refine ⟨47094589436143314611540945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31396392957428876407693963 47094589436143314611540945)
    ·
      refine ⟨35320942077107485958655709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47094589436143314611540945 35320942077107485958655709)
      ·
        refine ⟨13245353278915307234495891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35320942077107485958655709 13245353278915307234495891)
        ·
          refine ⟨19868029918372960851743837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245353278915307234495891 19868029918372960851743837)
          ·
            refine ⟨7450511219389860319403939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19868029918372960851743837 7450511219389860319403939)
            ·
              refine ⟨11175766829084790479105909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450511219389860319403939 11175766829084790479105909)
              ·
                refine ⟨1047728140226699107416179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11175766829084790479105909 1047728140226699107416179)
                ·
                  refine ⟨1571592210340048661124269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047728140226699107416179 1571592210340048661124269)
                  ·
                    refine ⟨589347078877518247921601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571592210340048661124269 589347078877518247921601)
                    ·
                      rfl

theorem cell22_1721624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_1721624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721624 prefixEnd_1721624 := by exact prefixLift 1721624
  have htrace : WordTrace (prefixWord ++ tailWord_1721624) baseStart_1721624 baseEnd_1721624 := by
    simpa [prefixWord, tailWord_1721624, baseEnd_1721624] using wordTrace_append hprefix tailTrace_1721624
  have hstable : (prefixWord ++ tailWord_1721624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721624).length < 2 ^ (prefixWord ++ tailWord_1721624).sum := by decide
  have hdescent : baseEnd_1721624 < baseStart_1721624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721630 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1721630 : Nat := 118140960795 + 1721630 * 2 ^ 59
def prefixEnd_1721630 : Nat := 4983230072969 + 3 ^ 40 * 1721630 * 2
def baseEnd_1721630 : Nat := 589349132800136232271583

theorem tailTrace_1721630 : CollatzResearch.WordTrace tailWord_1721630 prefixEnd_1721630 589349132800136232271583 := by
  unfold tailWord_1721630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849125594104501980013293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41862003168557343893404229 7849125594104501980013293)
  ·
    refine ⟨2943422097789188242504985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7849125594104501980013293 2943422097789188242504985)
    ·
      refine ⟨2207566573341891181878739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2943422097789188242504985 2207566573341891181878739)
      ·
        refine ⟨3311349860012836772818109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207566573341891181878739 3311349860012836772818109)
        ·
          refine ⟨1241756197504813789806791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3311349860012836772818109 1241756197504813789806791)
          ·
            refine ⟨1862634296257220684710187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241756197504813789806791 1862634296257220684710187)
            ·
              refine ⟨2793951444385831027065281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862634296257220684710187 2793951444385831027065281)
              ·
                refine ⟨2095463583289373270298961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793951444385831027065281 2095463583289373270298961)
                ·
                  refine ⟨1571597687467029952724221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095463583289373270298961 1571597687467029952724221)
                  ·
                    refine ⟨589349132800136232271583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571597687467029952724221 589349132800136232271583)
                    ·
                      rfl

theorem cell22_1721630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1721630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721630 prefixEnd_1721630 := by exact prefixLift 1721630
  have htrace : WordTrace (prefixWord ++ tailWord_1721630) baseStart_1721630 baseEnd_1721630 := by
    simpa [prefixWord, tailWord_1721630, baseEnd_1721630] using wordTrace_append hprefix tailTrace_1721630
  have hstable : (prefixWord ++ tailWord_1721630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721630).length < 2 ^ (prefixWord ++ tailWord_1721630).sum := by decide
  have hdescent : baseEnd_1721630 < baseStart_1721630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721635 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_1721635 : Nat := 118140960795 + 1721635 * 2 ^ 59
def prefixEnd_1721635 : Nat := 4983230072969 + 3 ^ 40 * 1721635 * 2
def baseEnd_1721635 : Nat := 589350844402317885896567

theorem tailTrace_1721635 : CollatzResearch.WordTrace tailWord_1721635 prefixEnd_1721635 589350844402317885896567 := by
  unfold tailWord_1721635
  simp only [CollatzResearch.WordTrace]
  refine ⟨62793187117817901694038359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41862124745211934462692239 62793187117817901694038359)
  ·
    refine ⟨94189780676726852541057539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62793187117817901694038359 94189780676726852541057539)
    ·
      refine ⟨141284671015090278811586309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94189780676726852541057539 141284671015090278811586309)
      ·
        refine ⟨26490875815329427277172433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141284671015090278811586309 26490875815329427277172433)
        ·
          refine ⟨19868156861497070457879325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26490875815329427277172433 19868156861497070457879325)
          ·
            refine ⟨7450558823061401421704747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19868156861497070457879325 7450558823061401421704747)
            ·
              refine ⟨11175838234592102132557121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450558823061401421704747 11175838234592102132557121)
              ·
                refine ⟨8381878675944076599417841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11175838234592102132557121 8381878675944076599417841)
                ·
                  refine ⟨6286409006958057449563381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381878675944076599417841 6286409006958057449563381)
                  ·
                    refine ⟨589350844402317885896567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6286409006958057449563381 589350844402317885896567)
                    ·
                      rfl

theorem cell22_1721635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_1721635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721635 prefixEnd_1721635 := by exact prefixLift 1721635
  have htrace : WordTrace (prefixWord ++ tailWord_1721635) baseStart_1721635 baseEnd_1721635 := by
    simpa [prefixWord, tailWord_1721635, baseEnd_1721635] using wordTrace_append hprefix tailTrace_1721635
  have hstable : (prefixWord ++ tailWord_1721635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721635).length < 2 ^ (prefixWord ++ tailWord_1721635).sum := by decide
  have hdescent : baseEnd_1721635 < baseStart_1721635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721637 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 5]
def baseStart_1721637 : Nat := 118140960795 + 1721637 * 2 ^ 59
def prefixEnd_1721637 : Nat := 4983230072969 + 3 ^ 40 * 1721637 * 2
def baseEnd_1721637 : Nat := 196450509681063515782187

theorem tailTrace_1721637 : CollatzResearch.WordTrace tailWord_1721637 prefixEnd_1721637 196450509681063515782187 := by
  unfold tailWord_1721637
  simp only [CollatzResearch.WordTrace]
  refine ⟨62793260063810656035611165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41862173375873770690407443 62793260063810656035611165)
  ·
    refine ⟨23547472523928996013354187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62793260063810656035611165 23547472523928996013354187)
    ·
      refine ⟨35321208785893494020031281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23547472523928996013354187 35321208785893494020031281)
      ·
        refine ⟨26490906589420120515023461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35321208785893494020031281 26490906589420120515023461)
        ·
          refine ⟨4967044985516272596566899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26490906589420120515023461 4967044985516272596566899)
          ·
            refine ⟨7450567478274408894850349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967044985516272596566899 7450567478274408894850349)
            ·
              refine ⟨2793962804352903335568881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7450567478274408894850349 2793962804352903335568881)
              ·
                refine ⟨2095472103264677501676661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793962804352903335568881 2095472103264677501676661)
                ·
                  refine ⟨196450509681063515782187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095472103264677501676661 196450509681063515782187)
                  ·
                    rfl

theorem cell22_1721637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_1721637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721637 prefixEnd_1721637 := by exact prefixLift 1721637
  have htrace : WordTrace (prefixWord ++ tailWord_1721637) baseStart_1721637 baseEnd_1721637 := by
    simpa [prefixWord, tailWord_1721637, baseEnd_1721637] using wordTrace_append hprefix tailTrace_1721637
  have hstable : (prefixWord ++ tailWord_1721637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721637).length < 2 ^ (prefixWord ++ tailWord_1721637).sum := by decide
  have hdescent : baseEnd_1721637 < baseStart_1721637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721652 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1721652 : Nat := 118140960795 + 1721652 * 2 ^ 59
def prefixEnd_1721652 : Nat := 4983230072969 + 3 ^ 40 * 1721652 * 2
def baseEnd_1721652 : Nat := 589356663849735508221515

theorem tailTrace_1721652 : CollatzResearch.WordTrace tailWord_1721652 prefixEnd_1721652 589356663849735508221515 := by
  unfold tailWord_1721652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396903579378156798703605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41862538105837542398271473 31396903579378156798703605)
  ·
    refine ⟨2943459710566702199878463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31396903579378156798703605 2943459710566702199878463)
    ·
      refine ⟨4415189565850053299817695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943459710566702199878463 4415189565850053299817695)
      ·
        refine ⟨6622784348775079949726543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415189565850053299817695 6622784348775079949726543)
        ·
          refine ⟨9934176523162619924589815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622784348775079949726543 9934176523162619924589815)
          ·
            refine ⟨14901264784743929886884723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934176523162619924589815 14901264784743929886884723)
            ·
              refine ⟨22351897177115894830327085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14901264784743929886884723 22351897177115894830327085)
              ·
                refine ⟨8381961441418460561372657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22351897177115894830327085 8381961441418460561372657)
                ·
                  refine ⟨6286471081063845421029493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381961441418460561372657 6286471081063845421029493)
                  ·
                    refine ⟨589356663849735508221515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6286471081063845421029493 589356663849735508221515)
                    ·
                      rfl

theorem cell22_1721652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1721652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721652 prefixEnd_1721652 := by exact prefixLift 1721652
  have htrace : WordTrace (prefixWord ++ tailWord_1721652) baseStart_1721652 baseEnd_1721652 := by
    simpa [prefixWord, tailWord_1721652, baseEnd_1721652] using wordTrace_append hprefix tailTrace_1721652
  have hstable : (prefixWord ++ tailWord_1721652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721652).length < 2 ^ (prefixWord ++ tailWord_1721652).sum := by decide
  have hdescent : baseEnd_1721652 < baseStart_1721652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721680 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_1721680 : Nat := 118140960795 + 1721680 * 2 ^ 59
def prefixEnd_1721680 : Nat := 4983230072969 + 3 ^ 40 * 1721680 * 2
def baseEnd_1721680 : Nat := 589366248821952768521429

theorem tailTrace_1721680 : CollatzResearch.WordTrace tailWord_1721680 prefixEnd_1721680 589366248821952768521429 := by
  unfold tailWord_1721680
  simp only [CollatzResearch.WordTrace]
  refine ⟨31397414201327437189713247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41863218935103249586284329 31397414201327437189713247)
  ·
    refine ⟨47096121301991155784569871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31397414201327437189713247 47096121301991155784569871)
    ·
      refine ⟨70644181952986733676854807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47096121301991155784569871 70644181952986733676854807)
      ·
        refine ⟨105966272929480100515282211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70644181952986733676854807 105966272929480100515282211)
        ·
          refine ⟨158949409394220150772923317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105966272929480100515282211 158949409394220150772923317)
          ·
            refine ⟨14901507130708139134961561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158949409394220150772923317 14901507130708139134961561)
            ·
              refine ⟨11176130348031104351221171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14901507130708139134961561 11176130348031104351221171)
              ·
                refine ⟨16764195522046656526831757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176130348031104351221171 16764195522046656526831757)
                ·
                  refine ⟨6286573320767496197561909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16764195522046656526831757 6286573320767496197561909)
                  ·
                    refine ⟨589366248821952768521429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6286573320767496197561909 589366248821952768521429)
                    ·
                      rfl

theorem cell22_1721680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_1721680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721680 prefixEnd_1721680 := by exact prefixLift 1721680
  have htrace : WordTrace (prefixWord ++ tailWord_1721680) baseStart_1721680 baseEnd_1721680 := by
    simpa [prefixWord, tailWord_1721680, baseEnd_1721680] using wordTrace_append hprefix tailTrace_1721680
  have hstable : (prefixWord ++ tailWord_1721680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721680).length < 2 ^ (prefixWord ++ tailWord_1721680).sum := by decide
  have hdescent : baseEnd_1721680 < baseStart_1721680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721714 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1721714 : Nat := 118140960795 + 1721714 * 2 ^ 59
def prefixEnd_1721714 : Nat := 4983230072969 + 3 ^ 40 * 1721714 * 2
def baseEnd_1721714 : Nat := 589377887716788013171325

theorem tailTrace_1721714 : CollatzResearch.WordTrace tailWord_1721714 prefixEnd_1721714 589377887716788013171325 := by
  unfold tailWord_1721714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699017121132924546541049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41864045656354465457442797 15699017121132924546541049)
  ·
    refine ⟨11774262840849693409905787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15699017121132924546541049 11774262840849693409905787)
    ·
      refine ⟨17661394261274540114858681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11774262840849693409905787 17661394261274540114858681)
      ·
        refine ⟨13246045695955905086144011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17661394261274540114858681 13246045695955905086144011)
        ·
          refine ⟨19869068543933857629216017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13246045695955905086144011 19869068543933857629216017)
          ·
            refine ⟨14901801407950393221912013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19869068543933857629216017 14901801407950393221912013)
            ·
              refine ⟨5588175527981397458217005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14901801407950393221912013 5588175527981397458217005)
              ·
                refine ⟨2095565822993024046831377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588175527981397458217005 2095565822993024046831377)
                ·
                  refine ⟨1571674367244768035123533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095565822993024046831377 1571674367244768035123533)
                  ·
                    refine ⟨589377887716788013171325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1571674367244768035123533 589377887716788013171325)
                    ·
                      rfl

theorem cell22_1721714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1721714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721714 prefixEnd_1721714 := by exact prefixLift 1721714
  have htrace : WordTrace (prefixWord ++ tailWord_1721714) baseStart_1721714 baseEnd_1721714 := by
    simpa [prefixWord, tailWord_1721714, baseEnd_1721714] using wordTrace_append hprefix tailTrace_1721714
  have hstable : (prefixWord ++ tailWord_1721714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721714).length < 2 ^ (prefixWord ++ tailWord_1721714).sum := by decide
  have hdescent : baseEnd_1721714 < baseStart_1721714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721757 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1721757 : Nat := 118140960795 + 1721757 * 2 ^ 59
def prefixEnd_1721757 : Nat := 4983230072969 + 3 ^ 40 * 1721757 * 2
def baseEnd_1721757 : Nat := 589392607495550234346193

theorem tailTrace_1721757 : CollatzResearch.WordTrace tailWord_1721757 prefixEnd_1721757 589392607495550234346193 := by
  unfold tailWord_1721757
  simp only [CollatzResearch.WordTrace]
  refine ⟨62797636823375916529979525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41865091215583944353319683 62797636823375916529979525)
  ·
    refine ⟨11774556904382984349371161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62797636823375916529979525 11774556904382984349371161)
    ·
      refine ⟨8830917678287238262028371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11774556904382984349371161 8830917678287238262028371)
      ·
        refine ⟨13246376517430857393042557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830917678287238262028371 13246376517430857393042557)
        ·
          refine ⟨4967391194036571522390959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13246376517430857393042557 4967391194036571522390959)
          ·
            refine ⟨7451086791054857283586439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967391194036571522390959 7451086791054857283586439)
            ·
              refine ⟨11176630186582285925379659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451086791054857283586439 11176630186582285925379659)
              ·
                refine ⟨16764945279873428888069489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176630186582285925379659 16764945279873428888069489)
                ·
                  refine ⟨12573708959905071666052117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16764945279873428888069489 12573708959905071666052117)
                  ·
                    refine ⟨589392607495550234346193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12573708959905071666052117 589392607495550234346193)
                    ·
                      rfl

theorem cell22_1721757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1721757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721757 prefixEnd_1721757 := by exact prefixLift 1721757
  have htrace : WordTrace (prefixWord ++ tailWord_1721757) baseStart_1721757 baseEnd_1721757 := by
    simpa [prefixWord, tailWord_1721757, baseEnd_1721757] using wordTrace_append hprefix tailTrace_1721757
  have hstable : (prefixWord ++ tailWord_1721757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721757).length < 2 ^ (prefixWord ++ tailWord_1721757).sum := by decide
  have hdescent : baseEnd_1721757 < baseStart_1721757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721772 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_1721772 : Nat := 118140960795 + 1721772 * 2 ^ 59
def prefixEnd_1721772 : Nat := 4983230072969 + 3 ^ 40 * 1721772 * 2
def baseEnd_1721772 : Nat := 196465914100698398407049

theorem tailTrace_1721772 : CollatzResearch.WordTrace tailWord_1721772 prefixEnd_1721772 196465914100698398407049 := by
  unfold tailWord_1721772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31399091959160787045887785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41865455945547716061183713 31399091959160787045887785)
  ·
    refine ⟨23549318969370590284415839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31399091959160787045887785 23549318969370590284415839)
    ·
      refine ⟨35323978454055885426623759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23549318969370590284415839 35323978454055885426623759)
      ·
        refine ⟨52985967681083828139935639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35323978454055885426623759 52985967681083828139935639)
        ·
          refine ⟨79478951521625742209903459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52985967681083828139935639 79478951521625742209903459)
          ·
            refine ⟨119218427282438613314855189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79478951521625742209903459 119218427282438613314855189)
            ·
              refine ⟨5588363778864309999133837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119218427282438613314855189 5588363778864309999133837)
              ·
                refine ⟨2095636417074116249675189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588363778864309999133837 2095636417074116249675189)
                ·
                  refine ⟨196465914100698398407049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095636417074116249675189 196465914100698398407049)
                  ·
                    rfl

theorem cell22_1721772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_1721772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721772 prefixEnd_1721772 := by exact prefixLift 1721772
  have htrace : WordTrace (prefixWord ++ tailWord_1721772) baseStart_1721772 baseEnd_1721772 := by
    simpa [prefixWord, tailWord_1721772, baseEnd_1721772] using wordTrace_append hprefix tailTrace_1721772
  have hstable : (prefixWord ++ tailWord_1721772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721772).length < 2 ^ (prefixWord ++ tailWord_1721772).sum := by decide
  have hdescent : baseEnd_1721772 < baseStart_1721772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721817 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 6]
def baseStart_1721817 : Nat := 118140960795 + 1721817 * 2 ^ 59
def prefixEnd_1721817 : Nat := 4983230072969 + 3 ^ 40 * 1721817 * 2
def baseEnd_1721817 : Nat := 196471048907243359282003

theorem tailTrace_1721817 : CollatzResearch.WordTrace tailWord_1721817 prefixEnd_1721817 196471048907243359282003 := by
  unfold tailWord_1721817
  simp only [CollatzResearch.WordTrace]
  refine ⟨62799825203158546777163705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41866550135439031184775803 62799825203158546777163705)
  ·
    refine ⟨47099868902368910082872779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62799825203158546777163705 47099868902368910082872779)
    ·
      refine ⟨70649803353553365124309169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47099868902368910082872779 70649803353553365124309169)
      ·
        refine ⟨52987352515165023843231877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70649803353553365124309169 52987352515165023843231877)
        ·
          refine ⟨9935128596593441970605977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52987352515165023843231877 9935128596593441970605977)
          ·
            refine ⟨7451346447445081477954483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9935128596593441970605977 7451346447445081477954483)
            ·
              refine ⟨11177019671167622216931725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451346447445081477954483 11177019671167622216931725)
              ·
                refine ⟨4191382376687858331349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11177019671167622216931725 4191382376687858331349397)
                ·
                  refine ⟨196471048907243359282003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4191382376687858331349397 196471048907243359282003)
                  ·
                    rfl

theorem cell22_1721817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_1721817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721817 prefixEnd_1721817 := by exact prefixLift 1721817
  have htrace : WordTrace (prefixWord ++ tailWord_1721817) baseStart_1721817 baseEnd_1721817 := by
    simpa [prefixWord, tailWord_1721817, baseEnd_1721817] using wordTrace_append hprefix tailTrace_1721817
  have hstable : (prefixWord ++ tailWord_1721817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721817).length < 2 ^ (prefixWord ++ tailWord_1721817).sum := by decide
  have hdescent : baseEnd_1721817 < baseStart_1721817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721868 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_1721868 : Nat := 118140960795 + 1721868 * 2 ^ 59
def prefixEnd_1721868 : Nat := 4983230072969 + 3 ^ 40 * 1721868 * 2
def baseEnd_1721868 : Nat := 196476868354660981606951

theorem tailTrace_1721868 : CollatzResearch.WordTrace tailWord_1721868 prefixEnd_1721868 196476868354660981606951 := by
  unfold tailWord_1721868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31400842662986891243635129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41867790217315854991513505 31400842662986891243635129)
  ·
    refine ⟨23550631997240168432726347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31400842662986891243635129 23550631997240168432726347)
    ·
      refine ⟨35325947995860252649089521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23550631997240168432726347 35325947995860252649089521)
      ·
        refine ⟨26494460996895189486817141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35325947995860252649089521 26494460996895189486817141)
        ·
          refine ⟨2483855718458924014389107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26494460996895189486817141 2483855718458924014389107)
          ·
            refine ⟨3725783577688386021583661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483855718458924014389107 3725783577688386021583661)
            ·
              refine ⟨1397168841633144758093873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3725783577688386021583661 1397168841633144758093873)
              ·
                refine ⟨1047876631224858568570405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397168841633144758093873 1047876631224858568570405)
                ·
                  refine ⟨196476868354660981606951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047876631224858568570405 196476868354660981606951)
                  ·
                    rfl

theorem cell22_1721868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_1721868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1721868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1721868 prefixEnd_1721868 := by exact prefixLift 1721868
  have htrace : WordTrace (prefixWord ++ tailWord_1721868) baseStart_1721868 baseEnd_1721868 := by
    simpa [prefixWord, tailWord_1721868, baseEnd_1721868] using wordTrace_append hprefix tailTrace_1721868
  have hstable : (prefixWord ++ tailWord_1721868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721868).length < 2 ^ (prefixWord ++ tailWord_1721868).sum := by decide
  have hdescent : baseEnd_1721868 < baseStart_1721868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722093 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1722093 : Nat := 118140960795 + 1722093 * 2 ^ 59
def prefixEnd_1722093 : Nat := 4983230072969 + 3 ^ 40 * 1722093 * 2
def baseEnd_1722093 : Nat := 196502542387385785981721

theorem tailTrace_1722093 : CollatzResearch.WordTrace tailWord_1722093 prefixEnd_1722093 196502542387385785981721 := by
  unfold tailWord_1722093
  simp only [CollatzResearch.WordTrace]
  refine ⟨62809891750158645914210933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41873261166772430609473955 62809891750158645914210933)
  ·
    refine ⟨5888427351577373054457275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62809891750158645914210933 5888427351577373054457275)
    ·
      refine ⟨8832641027366059581685913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5888427351577373054457275 8832641027366059581685913)
      ·
        refine ⟨6624480770524544686264435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8832641027366059581685913 6624480770524544686264435)
        ·
          refine ⟨9936721155786817029396653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624480770524544686264435 9936721155786817029396653)
          ·
            refine ⟨3726270433420056386023745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9936721155786817029396653 3726270433420056386023745)
            ·
              refine ⟨2794702825065042289517809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726270433420056386023745 2794702825065042289517809)
              ·
                refine ⟨2096027118798781717138357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2794702825065042289517809 2096027118798781717138357)
                ·
                  refine ⟨196502542387385785981721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2096027118798781717138357 196502542387385785981721)
                  ·
                    rfl

theorem cell22_1722093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1722093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722093 prefixEnd_1722093 := by exact prefixLift 1722093
  have htrace : WordTrace (prefixWord ++ tailWord_1722093) baseStart_1722093 baseEnd_1722093 := by
    simpa [prefixWord, tailWord_1722093, baseEnd_1722093] using wordTrace_append hprefix tailTrace_1722093
  have hstable : (prefixWord ++ tailWord_1722093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722093).length < 2 ^ (prefixWord ++ tailWord_1722093).sum := by decide
  have hdescent : baseEnd_1722093 < baseStart_1722093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722097 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 1, 3]
def baseStart_1722097 : Nat := 118140960795 + 1722097 * 2 ^ 59
def prefixEnd_1722097 : Nat := 4983230072969 + 3 ^ 40 * 1722097 * 2
def baseEnd_1722097 : Nat := 589508996443902680845151

theorem tailTrace_1722097 : CollatzResearch.WordTrace tailWord_1722097 prefixEnd_1722097 589508996443902680845151 := by
  unfold tailWord_1722097
  simp only [CollatzResearch.WordTrace]
  refine ⟨62810037642144154597356545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41873358428096103064904363 62810037642144154597356545)
  ·
    refine ⟨47107528231608115948017409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62810037642144154597356545 47107528231608115948017409)
    ·
      refine ⟨35330646173706086961013057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47107528231608115948017409 35330646173706086961013057)
      ·
        refine ⟨26497984630279565220759793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35330646173706086961013057 26497984630279565220759793)
        ·
          refine ⟨19873488472709673915569845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26497984630279565220759793 19873488472709673915569845)
          ·
            refine ⟨1863139544316531929584673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19873488472709673915569845 1863139544316531929584673)
            ·
              refine ⟨1397354658237398947188505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863139544316531929584673 1397354658237398947188505)
              ·
                refine ⟨1048015993678049210391379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397354658237398947188505 1048015993678049210391379)
                ·
                  refine ⟨1572023990517073815587069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048015993678049210391379 1572023990517073815587069)
                  ·
                    refine ⟨589508996443902680845151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572023990517073815587069 589508996443902680845151)
                    ·
                      rfl

theorem cell22_1722097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_1722097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722097 prefixEnd_1722097 := by exact prefixLift 1722097
  have htrace : WordTrace (prefixWord ++ tailWord_1722097) baseStart_1722097 baseEnd_1722097 := by
    simpa [prefixWord, tailWord_1722097, baseEnd_1722097] using wordTrace_append hprefix tailTrace_1722097
  have hstable : (prefixWord ++ tailWord_1722097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722097).length < 2 ^ (prefixWord ++ tailWord_1722097).sum := by decide
  have hdescent : baseEnd_1722097 < baseStart_1722097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722118 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1722118 : Nat := 118140960795 + 1722118 * 2 ^ 59
def prefixEnd_1722118 : Nat := 4983230072969 + 3 ^ 40 * 1722118 * 2
def baseEnd_1722118 : Nat := 589516185173065626070087

theorem tailTrace_1722118 : CollatzResearch.WordTrace tailWord_1722118 prefixEnd_1722118 589516185173065626070087 := by
  unfold tailWord_1722118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962837611720877349495969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41873869050045383455914005 1962837611720877349495969)
  ·
    refine ⟨1472128208790658012121977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1962837611720877349495969 1472128208790658012121977)
    ·
      refine ⟨1104096156592993509091483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1472128208790658012121977 1104096156592993509091483)
      ·
        refine ⟨1656144234889490263637225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104096156592993509091483 1656144234889490263637225)
        ·
          refine ⟨1242108176167117697727919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1656144234889490263637225 1242108176167117697727919)
          ·
            refine ⟨1863162264250676546591879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242108176167117697727919 1863162264250676546591879)
            ·
              refine ⟨2794743396376014819887819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863162264250676546591879 2794743396376014819887819)
              ·
                refine ⟨4192115094564022229831729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794743396376014819887819 4192115094564022229831729)
                ·
                  refine ⟨3144086320923016672373797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192115094564022229831729 3144086320923016672373797)
                  ·
                    refine ⟨589516185173065626070087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144086320923016672373797 589516185173065626070087)
                    ·
                      rfl

theorem cell22_1722118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1722118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722118 prefixEnd_1722118 := by exact prefixLift 1722118
  have htrace : WordTrace (prefixWord ++ tailWord_1722118) baseStart_1722118 baseEnd_1722118 := by
    simpa [prefixWord, tailWord_1722118, baseEnd_1722118] using wordTrace_append hprefix tailTrace_1722118
  have hstable : (prefixWord ++ tailWord_1722118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722118).length < 2 ^ (prefixWord ++ tailWord_1722118).sum := by decide
  have hdescent : baseEnd_1722118 < baseStart_1722118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722136 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_1722136 : Nat := 118140960795 + 1722136 * 2 ^ 59
def prefixEnd_1722136 : Nat := 4983230072969 + 3 ^ 40 * 1722136 * 2
def baseEnd_1722136 : Nat := 589522346940919579120031

theorem tailTrace_1722136 : CollatzResearch.WordTrace tailWord_1722136 prefixEnd_1722136 589522346940919579120031 := by
  unfold tailWord_1722136
  simp only [CollatzResearch.WordTrace]
  refine ⟨31405730044501432129013131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41874306726001909505350841 31405730044501432129013131)
  ·
    refine ⟨47108595066752148193519697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31405730044501432129013131 47108595066752148193519697)
    ·
      refine ⟨35331446300064111145139773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47108595066752148193519697 35331446300064111145139773)
      ·
        refine ⟨13249292362524041679427415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35331446300064111145139773 13249292362524041679427415)
        ·
          refine ⟨19873938543786062519141123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249292362524041679427415 19873938543786062519141123)
          ·
            refine ⟨29810907815679093778711685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19873938543786062519141123 29810907815679093778711685)
            ·
              refine ⟨5589545215439830083508441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29810907815679093778711685 5589545215439830083508441)
              ·
                refine ⟨4192158911579872562631331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589545215439830083508441 4192158911579872562631331)
                ·
                  refine ⟨6288238367369808843946997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192158911579872562631331 6288238367369808843946997)
                  ·
                    refine ⟨589522346940919579120031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6288238367369808843946997 589522346940919579120031)
                    ·
                      rfl

theorem cell22_1722136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_1722136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722136 prefixEnd_1722136 := by exact prefixLift 1722136
  have htrace : WordTrace (prefixWord ++ tailWord_1722136) baseStart_1722136 baseEnd_1722136 := by
    simpa [prefixWord, tailWord_1722136, baseEnd_1722136] using wordTrace_append hprefix tailTrace_1722136
  have hstable : (prefixWord ++ tailWord_1722136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722136).length < 2 ^ (prefixWord ++ tailWord_1722136).sum := by decide
  have hdescent : baseEnd_1722136 < baseStart_1722136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722138 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_1722138 : Nat := 118140960795 + 1722138 * 2 ^ 59
def prefixEnd_1722138 : Nat := 4983230072969 + 3 ^ 40 * 1722138 * 2
def baseEnd_1722138 : Nat := 196507677193930746856675

theorem tailTrace_1722138 : CollatzResearch.WordTrace tailWord_1722138 prefixEnd_1722138 196507677193930746856675 := by
  unfold tailWord_1722138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702883258748904649899767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41874355356663745733066045 15702883258748904649899767)
  ·
    refine ⟨23554324888123356974849651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15702883258748904649899767 23554324888123356974849651)
    ·
      refine ⟨35331487332185035462274477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23554324888123356974849651 35331487332185035462274477)
      ·
        refine ⟨13249307749569388298352929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35331487332185035462274477 13249307749569388298352929)
        ·
          refine ⟨9936980812177041223764697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13249307749569388298352929 9936980812177041223764697)
          ·
            refine ⟨7452735609132780917823523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9936980812177041223764697 7452735609132780917823523)
            ·
              refine ⟨11179103413699171376735285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452735609132780917823523 11179103413699171376735285)
              ·
                refine ⟨1048040945034297316568933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11179103413699171376735285 1048040945034297316568933)
                ·
                  refine ⟨196507677193930746856675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048040945034297316568933 196507677193930746856675)
                  ·
                    rfl

theorem cell22_1722138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_1722138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722138 prefixEnd_1722138 := by exact prefixLift 1722138
  have htrace : WordTrace (prefixWord ++ tailWord_1722138) baseStart_1722138 baseEnd_1722138 := by
    simpa [prefixWord, tailWord_1722138, baseEnd_1722138] using wordTrace_append hprefix tailTrace_1722138
  have hstable : (prefixWord ++ tailWord_1722138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722138).length < 2 ^ (prefixWord ++ tailWord_1722138).sum := by decide
  have hdescent : baseEnd_1722138 < baseStart_1722138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722226 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1722226 : Nat := 118140960795 + 1722226 * 2 ^ 59
def prefixEnd_1722226 : Nat := 4983230072969 + 3 ^ 40 * 1722226 * 2
def baseEnd_1722226 : Nat := 589553155780189344369755

theorem tailTrace_1722226 : CollatzResearch.WordTrace tailWord_1722226 prefixEnd_1722226 589553155780189344369755 := by
  unfold tailWord_1722226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703685664669202407200633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41876495105784539752535021 15703685664669202407200633)
  ·
    refine ⟨11777764248501901805400475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15703685664669202407200633 11777764248501901805400475)
    ·
      refine ⟨17666646372752852708100713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11777764248501901805400475 17666646372752852708100713)
      ·
        refine ⟨13249984779564639531075535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17666646372752852708100713 13249984779564639531075535)
        ·
          refine ⟨19874977169346959296613303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249984779564639531075535 19874977169346959296613303)
          ·
            refine ⟨29812465754020438944919955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19874977169346959296613303 29812465754020438944919955)
            ·
              refine ⟨44718698631030658417379933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29812465754020438944919955 44718698631030658417379933)
              ·
                refine ⟨16769511986636496906517475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44718698631030658417379933 16769511986636496906517475)
                ·
                  refine ⟨25154267979954745359776213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16769511986636496906517475 25154267979954745359776213)
                  ·
                    refine ⟨589553155780189344369755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25154267979954745359776213 589553155780189344369755)
                    ·
                      rfl

theorem cell22_1722226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1722226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722226 prefixEnd_1722226 := by exact prefixLift 1722226
  have htrace : WordTrace (prefixWord ++ tailWord_1722226) baseStart_1722226 baseEnd_1722226 := by
    simpa [prefixWord, tailWord_1722226, baseEnd_1722226] using wordTrace_append hprefix tailTrace_1722226
  have hstable : (prefixWord ++ tailWord_1722226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722226).length < 2 ^ (prefixWord ++ tailWord_1722226).sum := by decide
  have hdescent : baseEnd_1722226 < baseStart_1722226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722322 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1722322 : Nat := 118140960795 + 1722322 * 2 ^ 59
def prefixEnd_1722322 : Nat := 4983230072969 + 3 ^ 40 * 1722322 * 2
def baseEnd_1722322 : Nat := 589586018542077093969461

theorem tailTrace_1722322 : CollatzResearch.WordTrace tailWord_1722322 prefixEnd_1722322 589586018542077093969461 := by
  unfold tailWord_1722322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704561016582254506074305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41878829377552678682864813 15704561016582254506074305)
  ·
    refine ⟨11778420762436690879555729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15704561016582254506074305 11778420762436690879555729)
    ·
      refine ⟨8833815571827518159666797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778420762436690879555729 8833815571827518159666797)
      ·
        refine ⟨3312680839435319309875049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8833815571827518159666797 3312680839435319309875049)
        ·
          refine ⟨2484510629576489482406287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3312680839435319309875049 2484510629576489482406287)
          ·
            refine ⟨3726765944364734223609431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484510629576489482406287 3726765944364734223609431)
            ·
              refine ⟨5590148916547101335414147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726765944364734223609431 5590148916547101335414147)
              ·
                refine ⟨8385223374820652003121221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590148916547101335414147 8385223374820652003121221)
                ·
                  refine ⟨1572229382778872250585229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8385223374820652003121221 1572229382778872250585229)
                  ·
                    refine ⟨589586018542077093969461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572229382778872250585229 589586018542077093969461)
                    ·
                      rfl

theorem cell22_1722322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1722322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722322 prefixEnd_1722322 := by exact prefixLift 1722322
  have htrace : WordTrace (prefixWord ++ tailWord_1722322) baseStart_1722322 baseEnd_1722322 := by
    simpa [prefixWord, tailWord_1722322, baseEnd_1722322] using wordTrace_append hprefix tailTrace_1722322
  have hstable : (prefixWord ++ tailWord_1722322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722322).length < 2 ^ (prefixWord ++ tailWord_1722322).sum := by decide
  have hdescent : baseEnd_1722322 < baseStart_1722322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722393 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_1722393 : Nat := 118140960795 + 1722393 * 2 ^ 59
def prefixEnd_1722393 : Nat := 4983230072969 + 3 ^ 40 * 1722393 * 2
def baseEnd_1722393 : Nat := 589610323293056575444243

theorem tailTrace_1722393 : CollatzResearch.WordTrace tailWord_1722393 prefixEnd_1722393 589610323293056575444243 := by
  unfold tailWord_1722393
  simp only [CollatzResearch.WordTrace]
  refine ⟨62820833649071797150131833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41880555766047864766754555 62820833649071797150131833)
  ·
    refine ⟨47115625236803847862598875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62820833649071797150131833 47115625236803847862598875)
    ·
      refine ⟨70673437855205771793898313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47115625236803847862598875 70673437855205771793898313)
      ·
        refine ⟨53005078391404328845423735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70673437855205771793898313 53005078391404328845423735)
        ·
          refine ⟨79507617587106493268135603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53005078391404328845423735 79507617587106493268135603)
          ·
            refine ⟨119261426380659739902203405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79507617587106493268135603 119261426380659739902203405)
            ·
              refine ⟨44723034892747402463326277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119261426380659739902203405 44723034892747402463326277)
              ·
                refine ⟨8385569042390137961873677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44723034892747402463326277 8385569042390137961873677)
                ·
                  refine ⟨3144588390896301735702629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8385569042390137961873677 3144588390896301735702629)
                  ·
                    refine ⟨589610323293056575444243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144588390896301735702629 589610323293056575444243)
                    ·
                      rfl

theorem cell22_1722393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_1722393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722393 prefixEnd_1722393 := by exact prefixLift 1722393
  have htrace : WordTrace (prefixWord ++ tailWord_1722393) baseStart_1722393 baseEnd_1722393 := by
    simpa [prefixWord, tailWord_1722393, baseEnd_1722393] using wordTrace_append hprefix tailTrace_1722393
  have hstable : (prefixWord ++ tailWord_1722393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722393).length < 2 ^ (prefixWord ++ tailWord_1722393).sum := by decide
  have hdescent : baseEnd_1722393 < baseStart_1722393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722397 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 5]
def baseStart_1722397 : Nat := 118140960795 + 1722397 * 2 ^ 59
def prefixEnd_1722397 : Nat := 4983230072969 + 3 ^ 40 * 1722397 * 2
def baseEnd_1722397 : Nat := 196537230858267299448077

theorem tailTrace_1722397 : CollatzResearch.WordTrace tailWord_1722397 prefixEnd_1722397 196537230858267299448077 := by
  unfold tailWord_1722397
  simp only [CollatzResearch.WordTrace]
  refine ⟨62820979541057305833277445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41880653027371537222184963 62820979541057305833277445)
  ·
    refine ⟨11778933663948244843739521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62820979541057305833277445 11778933663948244843739521)
    ·
      refine ⟨8834200247961183632804641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778933663948244843739521 8834200247961183632804641)
      ·
        refine ⟨6625650185970887724603481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8834200247961183632804641 6625650185970887724603481)
        ·
          refine ⟨4969237639478165793452611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6625650185970887724603481 4969237639478165793452611)
          ·
            refine ⟨7453856459217248690178917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969237639478165793452611 7453856459217248690178917)
            ·
              refine ⟨1397598086103234129408547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7453856459217248690178917 1397598086103234129408547)
              ·
                refine ⟨2096397129154851194112821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397598086103234129408547 2096397129154851194112821)
                ·
                  refine ⟨196537230858267299448077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2096397129154851194112821 196537230858267299448077)
                  ·
                    rfl

theorem cell22_1722397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_1722397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722397 prefixEnd_1722397 := by exact prefixLift 1722397
  have htrace : WordTrace (prefixWord ++ tailWord_1722397) baseStart_1722397 baseEnd_1722397 := by
    simpa [prefixWord, tailWord_1722397, baseEnd_1722397] using wordTrace_append hprefix tailTrace_1722397
  have hstable : (prefixWord ++ tailWord_1722397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722397).length < 2 ^ (prefixWord ++ tailWord_1722397).sum := by decide
  have hdescent : baseEnd_1722397 < baseStart_1722397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722423 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1722423 : Nat := 118140960795 + 1722423 * 2 ^ 59
def prefixEnd_1722423 : Nat := 4983230072969 + 3 ^ 40 * 1722423 * 2
def baseEnd_1722423 : Nat := 589620592906146497194151

theorem tailTrace_1722423 : CollatzResearch.WordTrace tailWord_1722423 prefixEnd_1722423 589620592906146497194151 := by
  unfold tailWord_1722423
  simp only [CollatzResearch.WordTrace]
  refine ⟨62821927838963112273723923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41881285225975408182482615 62821927838963112273723923)
  ·
    refine ⟨94232891758444668410585885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62821927838963112273723923 94232891758444668410585885)
    ·
      refine ⟨35337334409416750653969707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94232891758444668410585885 35337334409416750653969707)
      ·
        refine ⟨53006001614125125980954561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35337334409416750653969707 53006001614125125980954561)
        ·
          refine ⟨39754501210593844485715921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53006001614125125980954561 39754501210593844485715921)
          ·
            refine ⟨29815875907945383364286941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39754501210593844485715921 29815875907945383364286941)
            ·
              refine ⟨11180953465479518761607603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29815875907945383364286941 11180953465479518761607603)
              ·
                refine ⟨16771430198219278142411405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180953465479518761607603 16771430198219278142411405)
                ·
                  refine ⟨6289286324332229303404277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16771430198219278142411405 6289286324332229303404277)
                  ·
                    refine ⟨589620592906146497194151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6289286324332229303404277 589620592906146497194151)
                    ·
                      rfl

theorem cell22_1722423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1722423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722423 prefixEnd_1722423 := by exact prefixLift 1722423
  have htrace : WordTrace (prefixWord ++ tailWord_1722423) baseStart_1722423 baseEnd_1722423 := by
    simpa [prefixWord, tailWord_1722423, baseEnd_1722423] using wordTrace_append hprefix tailTrace_1722423
  have hstable : (prefixWord ++ tailWord_1722423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722423).length < 2 ^ (prefixWord ++ tailWord_1722423).sum := by decide
  have hdescent : baseEnd_1722423 < baseStart_1722423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722575 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1722575 : Nat := 118140960795 + 1722575 * 2 ^ 59
def prefixEnd_1722575 : Nat := 4983230072969 + 3 ^ 40 * 1722575 * 2
def baseEnd_1722575 : Nat := 589672625612468767393685

theorem tailTrace_1722575 : CollatzResearch.WordTrace tailWord_1722575 prefixEnd_1722575 589672625612468767393685 := by
  unfold tailWord_1722575
  simp only [CollatzResearch.WordTrace]
  refine ⟨62827471734412442233257179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41884981156274961488838119 62827471734412442233257179)
  ·
    refine ⟨94241207601618663349885769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62827471734412442233257179 94241207601618663349885769)
    ·
      refine ⟨70680905701213997512414327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94241207601618663349885769 70680905701213997512414327)
      ·
        refine ⟨106021358551820996268621491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70680905701213997512414327 106021358551820996268621491)
        ·
          refine ⟨159032037827731494402932237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106021358551820996268621491 159032037827731494402932237)
          ·
            refine ⟨59637014185399310401099589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159032037827731494402932237 59637014185399310401099589)
            ·
              refine ⟨11181940159762370700206173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59637014185399310401099589 11181940159762370700206173)
              ·
                refine ⟨4193227559910889012577315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11181940159762370700206173 4193227559910889012577315)
                ·
                  refine ⟨6289841339866333518865973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193227559910889012577315 6289841339866333518865973)
                  ·
                    refine ⟨589672625612468767393685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6289841339866333518865973 589672625612468767393685)
                    ·
                      rfl

theorem cell22_1722575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1722575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722575 prefixEnd_1722575 := by exact prefixLift 1722575
  have htrace : WordTrace (prefixWord ++ tailWord_1722575) baseStart_1722575 baseEnd_1722575 := by
    simpa [prefixWord, tailWord_1722575, baseEnd_1722575] using wordTrace_append hprefix tailTrace_1722575
  have hstable : (prefixWord ++ tailWord_1722575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722575).length < 2 ^ (prefixWord ++ tailWord_1722575).sum := by decide
  have hdescent : baseEnd_1722575 < baseStart_1722575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722605 : List Nat := [1, 5, 1, 2, 13]
def baseStart_1722605 : Nat := 118140960795 + 1722605 * 2 ^ 59
def prefixEnd_1722605 : Nat := 4983230072969 + 3 ^ 40 * 1722605 * 2
def baseEnd_1722605 : Nat := 2426678581175138638451

theorem tailTrace_1722605 : CollatzResearch.WordTrace tailWord_1722605 prefixEnd_1722605 2426678581175138638451 := by
  unfold tailWord_1722605
  simp only [CollatzResearch.WordTrace]
  refine ⟨62828565924303757356849269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41885710616202504904566179 62828565924303757356849269)
  ·
    refine ⟨5890178055403477252204619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62828565924303757356849269 5890178055403477252204619)
    ·
      refine ⟨8835267083105215878306929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890178055403477252204619 8835267083105215878306929)
      ·
        refine ⟨6626450312328911908730197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8835267083105215878306929 6626450312328911908730197)
        ·
          refine ⟨2426678581175138638451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6626450312328911908730197 2426678581175138638451)
          ·
            rfl

theorem cell22_1722605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 13].length) (baseStart_1722605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722605 prefixEnd_1722605 := by exact prefixLift 1722605
  have htrace : WordTrace (prefixWord ++ tailWord_1722605) baseStart_1722605 baseEnd_1722605 := by
    simpa [prefixWord, tailWord_1722605, baseEnd_1722605] using wordTrace_append hprefix tailTrace_1722605
  have hstable : (prefixWord ++ tailWord_1722605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722605).length < 2 ^ (prefixWord ++ tailWord_1722605).sum := by decide
  have hdescent : baseEnd_1722605 < baseStart_1722605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722607 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_1722607 : Nat := 118140960795 + 1722607 * 2 ^ 59
def prefixEnd_1722607 : Nat := 4983230072969 + 3 ^ 40 * 1722607 * 2
def baseEnd_1722607 : Nat := 589683579866431350593587

theorem tailTrace_1722607 : CollatzResearch.WordTrace tailWord_1722607 prefixEnd_1722607 589683579866431350593587 := by
  unfold tailWord_1722607
  simp only [CollatzResearch.WordTrace]
  refine ⟨62828638870296511698422075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41885759246864341132281383 62828638870296511698422075)
  ·
    refine ⟨94242958305444767547633113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62828638870296511698422075 94242958305444767547633113)
    ·
      refine ⟨70682218729083575660724835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94242958305444767547633113 70682218729083575660724835)
      ·
        refine ⟨106023328093625363491087253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70682218729083575660724835 106023328093625363491087253)
        ·
          refine ⟨4969843504388688913644715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106023328093625363491087253 4969843504388688913644715)
          ·
            refine ⟨7454765256583033370467073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969843504388688913644715 7454765256583033370467073)
            ·
              refine ⟨5591073942437275027850305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7454765256583033370467073 5591073942437275027850305)
              ·
                refine ⟨4193305456827956270887729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591073942437275027850305 4193305456827956270887729)
                ·
                  refine ⟨3144979092620967203165797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193305456827956270887729 3144979092620967203165797)
                  ·
                    refine ⟨589683579866431350593587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3144979092620967203165797 589683579866431350593587)
                    ·
                      rfl

theorem cell22_1722607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_1722607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722607 prefixEnd_1722607 := by exact prefixLift 1722607
  have htrace : WordTrace (prefixWord ++ tailWord_1722607) baseStart_1722607 baseEnd_1722607 := by
    simpa [prefixWord, tailWord_1722607, baseEnd_1722607] using wordTrace_append hprefix tailTrace_1722607
  have hstable : (prefixWord ++ tailWord_1722607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722607).length < 2 ^ (prefixWord ++ tailWord_1722607).sum := by decide
  have hdescent : baseEnd_1722607 < baseStart_1722607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722626 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1722626 : Nat := 118140960795 + 1722626 * 2 ^ 59
def prefixEnd_1722626 : Nat := 4983230072969 + 3 ^ 40 * 1722626 * 2
def baseEnd_1722626 : Nat := 589690083954721634368529

theorem tailTrace_1722626 : CollatzResearch.WordTrace tailWord_1722626 prefixEnd_1722626 589690083954721634368529 := by
  unfold tailWord_1722626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707332964306919485840933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41886221238151785295575821 15707332964306919485840933)
  ·
    refine ⟨2945124930807547403595175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15707332964306919485840933 2945124930807547403595175)
    ·
      refine ⟨4417687396211321105392763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945124930807547403595175 4417687396211321105392763)
      ·
        refine ⟨6626531094316981658089145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417687396211321105392763 6626531094316981658089145)
        ·
          refine ⟨4969898320737736243566859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6626531094316981658089145 4969898320737736243566859)
          ·
            refine ⟨7454847481106604365350289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969898320737736243566859 7454847481106604365350289)
            ·
              refine ⟨5591135610829953274012717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7454847481106604365350289 5591135610829953274012717)
              ·
                refine ⟨2096675854061232477754769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5591135610829953274012717 2096675854061232477754769)
                ·
                  refine ⟨1572506890545924358316077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2096675854061232477754769 1572506890545924358316077)
                  ·
                    refine ⟨589690083954721634368529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572506890545924358316077 589690083954721634368529)
                    ·
                      rfl

theorem cell22_1722626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1722626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722626 prefixEnd_1722626 := by exact prefixLift 1722626
  have htrace : WordTrace (prefixWord ++ tailWord_1722626) baseStart_1722626 baseEnd_1722626 := by
    simpa [prefixWord, tailWord_1722626, baseEnd_1722626] using wordTrace_append hprefix tailTrace_1722626
  have hstable : (prefixWord ++ tailWord_1722626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722626).length < 2 ^ (prefixWord ++ tailWord_1722626).sum := by decide
  have hdescent : baseEnd_1722626 < baseStart_1722626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722635 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_1722635 : Nat := 118140960795 + 1722635 * 2 ^ 59
def prefixEnd_1722635 : Nat := 4983230072969 + 3 ^ 40 * 1722635 * 2
def baseEnd_1722635 : Nat := 589693164838648610893501

theorem tailTrace_1722635 : CollatzResearch.WordTrace tailWord_1722635 prefixEnd_1722635 589693164838648610893501 := by
  unfold tailWord_1722635
  simp only [CollatzResearch.WordTrace]
  refine ⟨62829660114195072480441359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41886440076130048320294239 62829660114195072480441359)
  ·
    refine ⟨94244490171292608720662039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62829660114195072480441359 94244490171292608720662039)
    ·
      refine ⟨141366735256938913080993059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94244490171292608720662039 141366735256938913080993059)
      ·
        refine ⟨212050102885408369621489589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141366735256938913080993059 212050102885408369621489589)
        ·
          refine ⟨19879697145507034652014649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212050102885408369621489589 19879697145507034652014649)
          ·
            refine ⟨14909772859130275989010987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19879697145507034652014649 14909772859130275989010987)
            ·
              refine ⟨22364659288695413983516481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14909772859130275989010987 22364659288695413983516481)
              ·
                refine ⟨16773494466521560487637361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22364659288695413983516481 16773494466521560487637361)
                ·
                  refine ⟨12580120849891170365728021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16773494466521560487637361 12580120849891170365728021)
                  ·
                    refine ⟨589693164838648610893501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12580120849891170365728021 589693164838648610893501)
                    ·
                      rfl

theorem cell22_1722635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_1722635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722635 prefixEnd_1722635 := by exact prefixLift 1722635
  have htrace : WordTrace (prefixWord ++ tailWord_1722635) baseStart_1722635 baseEnd_1722635 := by
    simpa [prefixWord, tailWord_1722635, baseEnd_1722635] using wordTrace_append hprefix tailTrace_1722635
  have hstable : (prefixWord ++ tailWord_1722635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722635).length < 2 ^ (prefixWord ++ tailWord_1722635).sum := by decide
  have hdescent : baseEnd_1722635 < baseStart_1722635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722682 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1722682 : Nat := 118140960795 + 1722682 * 2 ^ 59
def prefixEnd_1722682 : Nat := 4983230072969 + 3 ^ 40 * 1722682 * 2
def baseEnd_1722682 : Nat := 589709253899156154968357

theorem tailTrace_1722682 : CollatzResearch.WordTrace tailWord_1722682 prefixEnd_1722682 589709253899156154968357 := by
  unfold tailWord_1722682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707843586256199876850575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41887582896683199671601533 15707843586256199876850575)
  ·
    refine ⟨23561765379384299815275863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707843586256199876850575 23561765379384299815275863)
    ·
      refine ⟨35342648069076449722913795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561765379384299815275863 35342648069076449722913795)
      ·
        refine ⟨53013972103614674584370693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35342648069076449722913795 53013972103614674584370693)
        ·
          refine ⟨9940119769427751484569505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53013972103614674584370693 9940119769427751484569505)
          ·
            refine ⟨7455089827070813613427129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9940119769427751484569505 7455089827070813613427129)
            ·
              refine ⟨5591317370303110210070347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7455089827070813613427129 5591317370303110210070347)
              ·
                refine ⟨8386976055454665315105521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5591317370303110210070347 8386976055454665315105521)
                ·
                  refine ⟨6290232041590998986329141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8386976055454665315105521 6290232041590998986329141)
                  ·
                    refine ⟨589709253899156154968357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6290232041590998986329141 589709253899156154968357)
                    ·
                      rfl

theorem cell22_1722682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1722682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722682 prefixEnd_1722682 := by exact prefixLift 1722682
  have htrace : WordTrace (prefixWord ++ tailWord_1722682) baseStart_1722682 baseEnd_1722682 := by
    simpa [prefixWord, tailWord_1722682, baseEnd_1722682] using wordTrace_append hprefix tailTrace_1722682
  have hstable : (prefixWord ++ tailWord_1722682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722682).length < 2 ^ (prefixWord ++ tailWord_1722682).sum := by decide
  have hdescent : baseEnd_1722682 < baseStart_1722682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722684 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_1722684 : Nat := 118140960795 + 1722684 * 2 ^ 59
def prefixEnd_1722684 : Nat := 4983230072969 + 3 ^ 40 * 1722684 * 2
def baseEnd_1722684 : Nat := 196569979513342938806117

theorem tailTrace_1722684 : CollatzResearch.WordTrace tailWord_1722684 prefixEnd_1722684 196569979513342938806117 := by
  unfold tailWord_1722684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31415723645508776924487553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41887631527345035899316737 31415723645508776924487553)
  ·
    refine ⟨23561792734131582693365665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31415723645508776924487553 23561792734131582693365665)
    ·
      refine ⟨17671344550598687020024249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23561792734131582693365665 17671344550598687020024249)
      ·
        refine ⟨13253508412949015265018187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17671344550598687020024249 13253508412949015265018187)
        ·
          refine ⟨19880262619423522897527281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13253508412949015265018187 19880262619423522897527281)
          ·
            refine ⟨14910196964567642173145461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19880262619423522897527281 14910196964567642173145461)
            ·
              refine ⟨1397830965428216453732387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14910196964567642173145461 1397830965428216453732387)
              ·
                refine ⟨2096746448142324680598581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397830965428216453732387 2096746448142324680598581)
                ·
                  refine ⟨196569979513342938806117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2096746448142324680598581 196569979513342938806117)
                  ·
                    rfl

theorem cell22_1722684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_1722684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722684 prefixEnd_1722684 := by exact prefixLift 1722684
  have htrace : WordTrace (prefixWord ++ tailWord_1722684) baseStart_1722684 baseEnd_1722684 := by
    simpa [prefixWord, tailWord_1722684, baseEnd_1722684] using wordTrace_append hprefix tailTrace_1722684
  have hstable : (prefixWord ++ tailWord_1722684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722684).length < 2 ^ (prefixWord ++ tailWord_1722684).sum := by decide
  have hdescent : baseEnd_1722684 < baseStart_1722684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722759 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1722759 : Nat := 118140960795 + 1722759 * 2 ^ 59
def prefixEnd_1722759 : Nat := 4983230072969 + 3 ^ 40 * 1722759 * 2
def baseEnd_1722759 : Nat := 589735612572753620793121

theorem tailTrace_1722759 : CollatzResearch.WordTrace tailWord_1722759 prefixEnd_1722759 589735612572753620793121 := by
  unfold tailWord_1722759
  simp only [CollatzResearch.WordTrace]
  refine ⟨62834182765745841657955331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41889455177163894438636887 62834182765745841657955331)
  ·
    refine ⟨94251274148618762486932997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62834182765745841657955331 94251274148618762486932997)
    ·
      refine ⟨17672113902866017966299937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94251274148618762486932997 17672113902866017966299937)
      ·
        refine ⟨13254085427149513474724953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17672113902866017966299937 13254085427149513474724953)
        ·
          refine ⟨9940564070362135106043715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13254085427149513474724953 9940564070362135106043715)
          ·
            refine ⟨14910846105543202659065573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9940564070362135106043715 14910846105543202659065573)
            ·
              refine ⟨2795783644789350498574795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14910846105543202659065573 2795783644789350498574795)
              ·
                refine ⟨4193675467184025747862193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795783644789350498574795 4193675467184025747862193)
                ·
                  refine ⟨3145256600388019310896645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193675467184025747862193 3145256600388019310896645)
                  ·
                    refine ⟨589735612572753620793121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3145256600388019310896645 589735612572753620793121)
                    ·
                      rfl

theorem cell22_1722759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1722759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722759 prefixEnd_1722759 := by exact prefixLift 1722759
  have htrace : WordTrace (prefixWord ++ tailWord_1722759) baseStart_1722759 baseEnd_1722759 := by
    simpa [prefixWord, tailWord_1722759, baseEnd_1722759] using wordTrace_append hprefix tailTrace_1722759
  have hstable : (prefixWord ++ tailWord_1722759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722759).length < 2 ^ (prefixWord ++ tailWord_1722759).sum := by decide
  have hdescent : baseEnd_1722759 < baseStart_1722759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722787 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_1722787 : Nat := 118140960795 + 1722787 * 2 ^ 59
def prefixEnd_1722787 : Nat := 4983230072969 + 3 ^ 40 * 1722787 * 2
def baseEnd_1722787 : Nat := 589745197544970881093035

theorem tailTrace_1722787 : CollatzResearch.WordTrace tailWord_1722787 prefixEnd_1722787 589745197544970881093035 := by
  unfold tailWord_1722787
  simp only [CollatzResearch.WordTrace]
  refine ⟨62835204009644402439974615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41890136006429601626649743 62835204009644402439974615)
  ·
    refine ⟨94252806014466603659961923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62835204009644402439974615 94252806014466603659961923)
    ·
      refine ⟨141379209021699905489942885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94252806014466603659961923 141379209021699905489942885)
      ·
        refine ⟨26508601691568732279364291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141379209021699905489942885 26508601691568732279364291)
        ·
          refine ⟨39762902537353098419046437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26508601691568732279364291 39762902537353098419046437)
          ·
            refine ⟨7455544225753705953571207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39762902537353098419046437 7455544225753705953571207)
            ·
              refine ⟨11183316338630558930356811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455544225753705953571207 11183316338630558930356811)
              ·
                refine ⟨16774974507945838395535217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11183316338630558930356811 16774974507945838395535217)
                ·
                  refine ⟨12581230880959378796651413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16774974507945838395535217 12581230880959378796651413)
                  ·
                    refine ⟨589745197544970881093035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12581230880959378796651413 589745197544970881093035)
                    ·
                      rfl

theorem cell22_1722787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_1722787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722787 prefixEnd_1722787 := by exact prefixLift 1722787
  have htrace : WordTrace (prefixWord ++ tailWord_1722787) baseStart_1722787 baseEnd_1722787 := by
    simpa [prefixWord, tailWord_1722787, baseEnd_1722787] using wordTrace_append hprefix tailTrace_1722787
  have hstable : (prefixWord ++ tailWord_1722787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722787).length < 2 ^ (prefixWord ++ tailWord_1722787).sum := by decide
  have hdescent : baseEnd_1722787 < baseStart_1722787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722789 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_1722789 : Nat := 118140960795 + 1722789 * 2 ^ 59
def prefixEnd_1722789 : Nat := 4983230072969 + 3 ^ 40 * 1722789 * 2
def baseEnd_1722789 : Nat := 589745882185843542543029

theorem tailTrace_1722789 : CollatzResearch.WordTrace tailWord_1722789 prefixEnd_1722789 589745882185843542543029 := by
  unfold tailWord_1722789
  simp only [CollatzResearch.WordTrace]
  refine ⟨62835276955637156781547421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41890184637091437854364947 62835276955637156781547421)
  ·
    refine ⟨23563228858363933793080283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62835276955637156781547421 23563228858363933793080283)
    ·
      refine ⟨35344843287545900689620425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23563228858363933793080283 35344843287545900689620425)
      ·
        refine ⟨26508632465659425517215319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35344843287545900689620425 26508632465659425517215319)
        ·
          refine ⟨39762948698489138275822979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26508632465659425517215319 39762948698489138275822979)
          ·
            refine ⟨59644423047733707413734469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39762948698489138275822979 59644423047733707413734469)
            ·
              refine ⟨11183329321450070140075213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59644423047733707413734469 11183329321450070140075213)
              ·
                refine ⟨4193748495543776302528205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11183329321450070140075213 4193748495543776302528205)
                ·
                  refine ⟨1572655685828916113448077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4193748495543776302528205 1572655685828916113448077)
                  ·
                    refine ⟨589745882185843542543029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572655685828916113448077 589745882185843542543029)
                    ·
                      rfl

theorem cell22_1722789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_1722789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722789 prefixEnd_1722789 := by exact prefixLift 1722789
  have htrace : WordTrace (prefixWord ++ tailWord_1722789) baseStart_1722789 baseEnd_1722789 := by
    simpa [prefixWord, tailWord_1722789, baseEnd_1722789] using wordTrace_append hprefix tailTrace_1722789
  have hstable : (prefixWord ++ tailWord_1722789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722789).length < 2 ^ (prefixWord ++ tailWord_1722789).sum := by decide
  have hdescent : baseEnd_1722789 < baseStart_1722789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722823 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 1, 3]
def baseStart_1722823 : Nat := 118140960795 + 1722823 * 2 ^ 59
def prefixEnd_1722823 : Nat := 4983230072969 + 3 ^ 40 * 1722823 * 2
def baseEnd_1722823 : Nat := 589757521080678787192925

theorem tailTrace_1722823 : CollatzResearch.WordTrace tailWord_1722823 prefixEnd_1722823 589757521080678787192925 := by
  unfold tailWord_1722823
  simp only [CollatzResearch.WordTrace]
  refine ⟨62836517037513980588285123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41891011358342653725523415 62836517037513980588285123)
  ·
    refine ⟨94254775556270970882427685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62836517037513980588285123 94254775556270970882427685)
    ·
      refine ⟨17672770416800807040455191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94254775556270970882427685 17672770416800807040455191)
      ·
        refine ⟨26509155625201210560682787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17672770416800807040455191 26509155625201210560682787)
        ·
          refine ⟨39763733437801815841024181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26509155625201210560682787 39763733437801815841024181)
          ·
            refine ⟨3727850009793920235096017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39763733437801815841024181 3727850009793920235096017)
            ·
              refine ⟨2795887507345440176322013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727850009793920235096017 2795887507345440176322013)
              ·
                refine ⟨1048457815254540066120755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2795887507345440176322013 1048457815254540066120755)
                ·
                  refine ⟨1572686722881810099181133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048457815254540066120755 1572686722881810099181133)
                  ·
                    refine ⟨589757521080678787192925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572686722881810099181133 589757521080678787192925)
                    ·
                      rfl

theorem cell22_1722823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_1722823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722823 prefixEnd_1722823 := by exact prefixLift 1722823
  have htrace : WordTrace (prefixWord ++ tailWord_1722823) baseStart_1722823 baseEnd_1722823 := by
    simpa [prefixWord, tailWord_1722823, baseEnd_1722823] using wordTrace_append hprefix tailTrace_1722823
  have hstable : (prefixWord ++ tailWord_1722823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722823).length < 2 ^ (prefixWord ++ tailWord_1722823).sum := by decide
  have hdescent : baseEnd_1722823 < baseStart_1722823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722836 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1722836 : Nat := 118140960795 + 1722836 * 2 ^ 59
def prefixEnd_1722836 : Nat := 4983230072969 + 3 ^ 40 * 1722836 * 2
def baseEnd_1722836 : Nat := 196587323748783695539295

theorem tailTrace_1722836 : CollatzResearch.WordTrace tailWord_1722836 prefixEnd_1722836 196587323748783695539295 := by
  unfold tailWord_1722836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31418495593233441904254181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41891327457644589205672241 31418495593233441904254181)
  ·
    refine ⟨5890967923731270357047659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31418495593233441904254181 5890967923731270357047659)
    ·
      refine ⟨8836451885596905535571489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890967923731270357047659 8836451885596905535571489)
      ·
        refine ⟨6627338914197679151678617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8836451885596905535571489 6627338914197679151678617)
        ·
          refine ⟨4970504185648259363758963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6627338914197679151678617 4970504185648259363758963)
          ·
            refine ⟨7455756278472389045638445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970504185648259363758963 7455756278472389045638445)
            ·
              refine ⟨2795908604427145892114417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7455756278472389045638445 2795908604427145892114417)
              ·
                refine ⟨2096931453320359419085813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795908604427145892114417 2096931453320359419085813)
                ·
                  refine ⟨196587323748783695539295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2096931453320359419085813 196587323748783695539295)
                  ·
                    rfl

theorem cell22_1722836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1722836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722836 prefixEnd_1722836 := by exact prefixLift 1722836
  have htrace : WordTrace (prefixWord ++ tailWord_1722836) baseStart_1722836 baseEnd_1722836 := by
    simpa [prefixWord, tailWord_1722836, baseEnd_1722836] using wordTrace_append hprefix tailTrace_1722836
  have hstable : (prefixWord ++ tailWord_1722836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722836).length < 2 ^ (prefixWord ++ tailWord_1722836).sum := by decide
  have hdescent : baseEnd_1722836 < baseStart_1722836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722853 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 5]
def baseStart_1722853 : Nat := 118140960795 + 1722853 * 2 ^ 59
def prefixEnd_1722853 : Nat := 4983230072969 + 3 ^ 40 * 1722853 * 2
def baseEnd_1722853 : Nat := 196589263564589569647611

theorem tailTrace_1722853 : CollatzResearch.WordTrace tailWord_1722853 prefixEnd_1722853 196589263564589569647611 := by
  unfold tailWord_1722853
  simp only [CollatzResearch.WordTrace]
  refine ⟨62837611227405295711877213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41891740818270197141251475 62837611227405295711877213)
  ·
    refine ⟨23564104210276985891953955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62837611227405295711877213 23564104210276985891953955)
    ·
      refine ⟨35346156315415478837930933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23564104210276985891953955 35346156315415478837930933)
      ·
        refine ⟨3313702154570201141056025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35346156315415478837930933 3313702154570201141056025)
        ·
          refine ⟨2485276615927650855792019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313702154570201141056025 2485276615927650855792019)
          ·
            refine ⟨3727914923891476283688029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485276615927650855792019 3727914923891476283688029)
            ·
              refine ⟨1397968096459303606383011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3727914923891476283688029 1397968096459303606383011)
              ·
                refine ⟨2096952144688955409574517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397968096459303606383011 2096952144688955409574517)
                ·
                  refine ⟨196589263564589569647611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2096952144688955409574517 196589263564589569647611)
                  ·
                    rfl

theorem cell22_1722853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_1722853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722853 prefixEnd_1722853 := by exact prefixLift 1722853
  have htrace : WordTrace (prefixWord ++ tailWord_1722853) baseStart_1722853 baseEnd_1722853 := by
    simpa [prefixWord, tailWord_1722853, baseEnd_1722853] using wordTrace_append hprefix tailTrace_1722853
  have hstable : (prefixWord ++ tailWord_1722853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722853).length < 2 ^ (prefixWord ++ tailWord_1722853).sum := by decide
  have hdescent : baseEnd_1722853 < baseStart_1722853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722879 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 6, 3]
def baseStart_1722879 : Nat := 118140960795 + 1722879 * 2 ^ 59
def prefixEnd_1722879 : Nat := 4983230072969 + 3 ^ 40 * 1722879 * 2
def baseEnd_1722879 : Nat := 589776691025113307792753

theorem tailTrace_1722879 : CollatzResearch.WordTrace tailWord_1722879 prefixEnd_1722879 589776691025113307792753 := by
  unfold tailWord_1722879
  simp only [CollatzResearch.WordTrace]
  refine ⟨62838559525311102152323691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41892373016874068101549127 62838559525311102152323691)
  ·
    refine ⟨94257839287966653228485537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62838559525311102152323691 94257839287966653228485537)
    ·
      refine ⟨70693379465974989921364153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94257839287966653228485537 70693379465974989921364153)
      ·
        refine ⟨53020034599481242441023115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70693379465974989921364153 53020034599481242441023115)
        ·
          refine ⟨79530051899221863661534673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53020034599481242441023115 79530051899221863661534673)
          ·
            refine ⟨59647538924416397746151005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79530051899221863661534673 59647538924416397746151005)
            ·
              refine ⟨22367827096656149154806627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59647538924416397746151005 22367827096656149154806627)
              ·
                refine ⟨33551740644984223732209941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22367827096656149154806627 33551740644984223732209941)
                ·
                  refine ⟨1572737842733635487447341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33551740644984223732209941 1572737842733635487447341)
                  ·
                    refine ⟨589776691025113307792753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572737842733635487447341 589776691025113307792753)
                    ·
                      rfl

theorem cell22_1722879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_1722879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722879 prefixEnd_1722879 := by exact prefixLift 1722879
  have htrace : WordTrace (prefixWord ++ tailWord_1722879) baseStart_1722879 baseEnd_1722879 := by
    simpa [prefixWord, tailWord_1722879, baseEnd_1722879] using wordTrace_append hprefix tailTrace_1722879
  have hstable : (prefixWord ++ tailWord_1722879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722879).length < 2 ^ (prefixWord ++ tailWord_1722879).sum := by decide
  have hdescent : baseEnd_1722879 < baseStart_1722879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722909 : List Nat := [1, 4, 2, 2, 1, 2, 1, 9]
def baseStart_1722909 : Nat := 118140960795 + 1722909 * 2 ^ 59
def prefixEnd_1722909 : Nat := 4983230072969 + 3 ^ 40 * 1722909 * 2
def baseEnd_1722909 : Nat := 65531884515355914393629

theorem tailTrace_1722909 : CollatzResearch.WordTrace tailWord_1722909 prefixEnd_1722909 65531884515355914393629 := by
  unfold tailWord_1722909
  simp only [CollatzResearch.WordTrace]
  refine ⟨62839653715202417275915781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41893102476801611517277187 62839653715202417275915781)
  ·
    refine ⟨11782435071600453239234209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62839653715202417275915781 11782435071600453239234209)
    ·
      refine ⟨8836826303700339929425657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11782435071600453239234209 8836826303700339929425657)
      ·
        refine ⟨6627619727775254947069243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8836826303700339929425657 6627619727775254947069243)
        ·
          refine ⟨9941429591662882420603865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6627619727775254947069243 9941429591662882420603865)
          ·
            refine ⟨7456072193747161815452899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9941429591662882420603865 7456072193747161815452899)
            ·
              refine ⟨11184108290620742723179349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456072193747161815452899 11184108290620742723179349)
              ·
                refine ⟨65531884515355914393629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11184108290620742723179349 65531884515355914393629)
                ·
                  rfl

theorem cell22_1722909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 9].length) (baseStart_1722909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1722909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1722909 prefixEnd_1722909 := by exact prefixLift 1722909
  have htrace : WordTrace (prefixWord ++ tailWord_1722909) baseStart_1722909 baseEnd_1722909 := by
    simpa [prefixWord, tailWord_1722909, baseEnd_1722909] using wordTrace_append hprefix tailTrace_1722909
  have hstable : (prefixWord ++ tailWord_1722909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722909).length < 2 ^ (prefixWord ++ tailWord_1722909).sum := by decide
  have hdescent : baseEnd_1722909 < baseStart_1722909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723005 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 5]
def baseStart_1723005 : Nat := 118140960795 + 1723005 * 2 ^ 59
def prefixEnd_1723005 : Nat := 4983230072969 + 3 ^ 40 * 1723005 * 2
def baseEnd_1723005 : Nat := 196606607800030326380789

theorem tailTrace_1723005 : CollatzResearch.WordTrace tailWord_1723005 prefixEnd_1723005 196606607800030326380789 := by
  unfold tailWord_1723005
  simp only [CollatzResearch.WordTrace]
  refine ⟨62843155122854625671410469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41895436748569750447606979 62843155122854625671410469)
  ·
    refine ⟨11783091585535242313389463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62843155122854625671410469 11783091585535242313389463)
    ·
      refine ⟨17674637378302863470084195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783091585535242313389463 17674637378302863470084195)
      ·
        refine ⟨26511956067454295205126293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17674637378302863470084195 26511956067454295205126293)
        ·
          refine ⟨1242747940661920087740295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26511956067454295205126293 1242747940661920087740295)
          ·
            refine ⟨1864121910992880131610443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242747940661920087740295 1864121910992880131610443)
            ·
              refine ⟨2796182866489320197415665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864121910992880131610443 2796182866489320197415665)
              ·
                refine ⟨2097137149866990148061749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796182866489320197415665 2097137149866990148061749)
                ·
                  refine ⟨196606607800030326380789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097137149866990148061749 196606607800030326380789)
                  ·
                    rfl

theorem cell22_1723005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_1723005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723005 prefixEnd_1723005 := by exact prefixLift 1723005
  have htrace : WordTrace (prefixWord ++ tailWord_1723005) baseStart_1723005 baseEnd_1723005 := by
    simpa [prefixWord, tailWord_1723005, baseEnd_1723005] using wordTrace_append hprefix tailTrace_1723005
  have hstable : (prefixWord ++ tailWord_1723005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723005).length < 2 ^ (prefixWord ++ tailWord_1723005).sum := by decide
  have hdescent : baseEnd_1723005 < baseStart_1723005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723061 : List Nat := [1, 3, 3, 3, 1, 1, 10]
def baseStart_1723061 : Nat := 118140960795 + 1723061 * 2 ^ 59
def prefixEnd_1723061 : Nat := 4983230072969 + 3 ^ 40 * 1723061 * 2
def baseEnd_1723061 : Nat := 21845888642389833323785

theorem tailTrace_1723061 : CollatzResearch.WordTrace tailWord_1723061 prefixEnd_1723061 21845888642389833323785 := by
  unfold tailWord_1723061
  simp only [CollatzResearch.WordTrace]
  refine ⟨62845197610651747235449037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41896798407101164823632691 62845197610651747235449037)
  ·
    refine ⟨23566949103994405213293389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62845197610651747235449037 23566949103994405213293389)
    ·
      refine ⟨8837605913997901954985021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23566949103994405213293389 8837605913997901954985021)
      ·
        refine ⟨3314102217749213233119383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8837605913997901954985021 3314102217749213233119383)
        ·
          refine ⟨4971153326623819849679075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314102217749213233119383 4971153326623819849679075)
          ·
            refine ⟨7456729989935729774518613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971153326623819849679075 7456729989935729774518613)
            ·
              refine ⟨21845888642389833323785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7456729989935729774518613 21845888642389833323785)
              ·
                rfl

theorem cell22_1723061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 10].length) (baseStart_1723061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723061 prefixEnd_1723061 := by exact prefixLift 1723061
  have htrace : WordTrace (prefixWord ++ tailWord_1723061) baseStart_1723061 baseEnd_1723061 := by
    simpa [prefixWord, tailWord_1723061, baseEnd_1723061] using wordTrace_append hprefix tailTrace_1723061
  have hstable : (prefixWord ++ tailWord_1723061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723061).length < 2 ^ (prefixWord ++ tailWord_1723061).sum := by decide
  have hdescent : baseEnd_1723061 < baseStart_1723061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723063 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1723063 : Nat := 118140960795 + 1723063 * 2 ^ 59
def prefixEnd_1723063 : Nat := 4983230072969 + 3 ^ 40 * 1723063 * 2
def baseEnd_1723063 : Nat := 589839677985398161192189

theorem tailTrace_1723063 : CollatzResearch.WordTrace tailWord_1723063 prefixEnd_1723063 589839677985398161192189 := by
  unfold tailWord_1723063
  simp only [CollatzResearch.WordTrace]
  refine ⟨62845270556644501577021843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41896847037763001051347895 62845270556644501577021843)
  ·
    refine ⟨94267905834966752365532765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62845270556644501577021843 94267905834966752365532765)
    ·
      refine ⟨35350464688112532137074787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94267905834966752365532765 35350464688112532137074787)
      ·
        refine ⟨53025697032168798205612181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35350464688112532137074787 53025697032168798205612181)
        ·
          refine ⟨2485579548382912415888071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53025697032168798205612181 2485579548382912415888071)
          ·
            refine ⟨3728369322574368623832107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485579548382912415888071 3728369322574368623832107)
            ·
              refine ⟨5592553983861552935748161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728369322574368623832107 5592553983861552935748161)
              ·
                refine ⟨4194415487896164701811121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592553983861552935748161 4194415487896164701811121)
                ·
                  refine ⟨3145811615922123526358341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4194415487896164701811121 3145811615922123526358341)
                  ·
                    refine ⟨589839677985398161192189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3145811615922123526358341 589839677985398161192189)
                    ·
                      rfl

theorem cell22_1723063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1723063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723063 prefixEnd_1723063 := by exact prefixLift 1723063
  have htrace : WordTrace (prefixWord ++ tailWord_1723063) baseStart_1723063 baseEnd_1723063 := by
    simpa [prefixWord, tailWord_1723063, baseEnd_1723063] using wordTrace_append hprefix tailTrace_1723063
  have hstable : (prefixWord ++ tailWord_1723063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723063).length < 2 ^ (prefixWord ++ tailWord_1723063).sum := by decide
  have hdescent : baseEnd_1723063 < baseStart_1723063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723082 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_1723082 : Nat := 118140960795 + 1723082 * 2 ^ 59
def prefixEnd_1723082 : Nat := 4983230072969 + 3 ^ 40 * 1723082 * 2
def baseEnd_1723082 : Nat := 589846182073688444967131

theorem tailTrace_1723082 : CollatzResearch.WordTrace tailWord_1723082 prefixEnd_1723082 589846182073688444967131 := by
  unfold tailWord_1723082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711490885893916955490875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41897309029050445214642333 15711490885893916955490875)
  ·
    refine ⟨23567236328840875433236313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15711490885893916955490875 23567236328840875433236313)
    ·
      refine ⟨17675427246630656574927235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23567236328840875433236313 17675427246630656574927235)
      ·
        refine ⟨26513140869945984862390853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17675427246630656574927235 26513140869945984862390853)
        ·
          refine ⟨4971213913114872161698285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26513140869945984862390853 4971213913114872161698285)
          ·
            refine ⟨1864205217418077060636857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4971213913114872161698285 1864205217418077060636857)
            ·
              refine ⟨1398153913063557795477643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864205217418077060636857 1398153913063557795477643)
              ·
                refine ⟨2097230869595336693216465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398153913063557795477643 2097230869595336693216465)
                ·
                  refine ⟨1572923152196502519912349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097230869595336693216465 1572923152196502519912349)
                  ·
                    refine ⟨589846182073688444967131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1572923152196502519912349 589846182073688444967131)
                    ·
                      rfl

theorem cell22_1723082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_1723082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723082 prefixEnd_1723082 := by exact prefixLift 1723082
  have htrace : WordTrace (prefixWord ++ tailWord_1723082) baseStart_1723082 baseEnd_1723082 := by
    simpa [prefixWord, tailWord_1723082, baseEnd_1723082] using wordTrace_append hprefix tailTrace_1723082
  have hstable : (prefixWord ++ tailWord_1723082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723082).length < 2 ^ (prefixWord ++ tailWord_1723082).sum := by decide
  have hdescent : baseEnd_1723082 < baseStart_1723082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723121 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1723121 : Nat := 118140960795 + 1723121 * 2 ^ 59
def prefixEnd_1723121 : Nat := 4983230072969 + 3 ^ 40 * 1723121 * 2
def baseEnd_1723121 : Nat := 589859532570705343242011

theorem tailTrace_1723121 : CollatzResearch.WordTrace tailWord_1723121 prefixEnd_1723121 589859532570705343242011 := by
  unfold tailWord_1723121
  simp only [CollatzResearch.WordTrace]
  refine ⟨62847385990434377482633217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41898257326956251655088811 62847385990434377482633217)
  ·
    refine ⟨47135539492825783111974913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62847385990434377482633217 47135539492825783111974913)
    ·
      refine ⟨35351654619619337333981185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47135539492825783111974913 35351654619619337333981185)
      ·
        refine ⟨26513740964714503000485889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35351654619619337333981185 26513740964714503000485889)
        ·
          refine ⟨19885305723535877250364417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26513740964714503000485889 19885305723535877250364417)
          ·
            refine ⟨14913979292651907937773313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885305723535877250364417 14913979292651907937773313)
            ·
              refine ⟨11185484469488930953329985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14913979292651907937773313 11185484469488930953329985)
              ·
                refine ⟨8389113352116698214997489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11185484469488930953329985 8389113352116698214997489)
                ·
                  refine ⟨6291835014087523661248117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8389113352116698214997489 6291835014087523661248117)
                  ·
                    refine ⟨589859532570705343242011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6291835014087523661248117 589859532570705343242011)
                    ·
                      rfl

theorem cell22_1723121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1723121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723121 prefixEnd_1723121 := by exact prefixLift 1723121
  have htrace : WordTrace (prefixWord ++ tailWord_1723121) baseStart_1723121 baseEnd_1723121 := by
    simpa [prefixWord, tailWord_1723121, baseEnd_1723121] using wordTrace_append hprefix tailTrace_1723121
  have hstable : (prefixWord ++ tailWord_1723121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723121).length < 2 ^ (prefixWord ++ tailWord_1723121).sum := by decide
  have hdescent : baseEnd_1723121 < baseStart_1723121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723138 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1723138 : Nat := 118140960795 + 1723138 * 2 ^ 59
def prefixEnd_1723138 : Nat := 4983230072969 + 3 ^ 40 * 1723138 * 2
def baseEnd_1723138 : Nat := 589865352018122965566959

theorem tailTrace_1723138 : CollatzResearch.WordTrace tailWord_1723138 prefixEnd_1723138 589865352018122965566959 := by
  unfold tailWord_1723138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712001507843197346500517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41898670687581859590668045 15712001507843197346500517)
  ·
    refine ⟨2946000282720599502468847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15712001507843197346500517 2946000282720599502468847)
    ·
      refine ⟨4419000424080899253703271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946000282720599502468847 4419000424080899253703271)
      ·
        refine ⟨6628500636121348880554907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419000424080899253703271 6628500636121348880554907)
        ·
          refine ⟨9942750954182023320832361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628500636121348880554907 9942750954182023320832361)
          ·
            refine ⟨7457063215636517490624271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9942750954182023320832361 7457063215636517490624271)
            ·
              refine ⟨11185594823454776235936407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457063215636517490624271 11185594823454776235936407)
              ·
                refine ⟨16778392235182164353904611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11185594823454776235936407 16778392235182164353904611)
                ·
                  refine ⟨25167588352773246530856917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16778392235182164353904611 25167588352773246530856917)
                  ·
                    refine ⟨589865352018122965566959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25167588352773246530856917 589865352018122965566959)
                    ·
                      rfl

theorem cell22_1723138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1723138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723138 prefixEnd_1723138 := by exact prefixLift 1723138
  have htrace : WordTrace (prefixWord ++ tailWord_1723138) baseStart_1723138 baseEnd_1723138 := by
    simpa [prefixWord, tailWord_1723138, baseEnd_1723138] using wordTrace_append hprefix tailTrace_1723138
  have hstable : (prefixWord ++ tailWord_1723138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723138).length < 2 ^ (prefixWord ++ tailWord_1723138).sum := by decide
  have hdescent : baseEnd_1723138 < baseStart_1723138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723151 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 6]
def baseStart_1723151 : Nat := 118140960795 + 1723151 * 2 ^ 59
def prefixEnd_1723151 : Nat := 4983230072969 + 3 ^ 40 * 1723151 * 2
def baseEnd_1723151 : Nat := 196623267394598421663973

theorem tailTrace_1723151 : CollatzResearch.WordTrace tailWord_1723151 prefixEnd_1723151 196623267394598421663973 := by
  unfold tailWord_1723151
  simp only [CollatzResearch.WordTrace]
  refine ⟨62848480180325692606225307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41898986786883795070816871 62848480180325692606225307)
  ·
    refine ⟨94272720270488538909337961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62848480180325692606225307 94272720270488538909337961)
    ·
      refine ⟨70704540202866404182003471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94272720270488538909337961 70704540202866404182003471)
      ·
        refine ⟨106056810304299606273005207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70704540202866404182003471 106056810304299606273005207)
        ·
          refine ⟨159085215456449409409507811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106056810304299606273005207 159085215456449409409507811)
          ·
            refine ⟨238627823184674114114261717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159085215456449409409507811 238627823184674114114261717)
            ·
              refine ⟨5592839605890799549553009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238627823184674114114261717 5592839605890799549553009)
              ·
                refine ⟨4194629704418099662164757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592839605890799549553009 4194629704418099662164757)
                ·
                  refine ⟨196623267394598421663973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4194629704418099662164757 196623267394598421663973)
                  ·
                    rfl

theorem cell22_1723151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_1723151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723151 prefixEnd_1723151 := by exact prefixLift 1723151
  have htrace : WordTrace (prefixWord ++ tailWord_1723151) baseStart_1723151 baseEnd_1723151 := by
    simpa [prefixWord, tailWord_1723151, baseEnd_1723151] using wordTrace_append hprefix tailTrace_1723151
  have hstable : (prefixWord ++ tailWord_1723151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723151).length < 2 ^ (prefixWord ++ tailWord_1723151).sum := by decide
  have hdescent : baseEnd_1723151 < baseStart_1723151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723170 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1723170 : Nat := 118140960795 + 1723170 * 2 ^ 59
def prefixEnd_1723170 : Nat := 4983230072969 + 3 ^ 40 * 1723170 * 2
def baseEnd_1723170 : Nat := 589876306272085548766861

theorem tailTrace_1723170 : CollatzResearch.WordTrace tailWord_1723170 prefixEnd_1723170 589876306272085548766861 := by
  unfold tailWord_1723170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712293291814214712791741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41899448778171239234111309 15712293291814214712791741)
  ·
    refine ⟨5892109984430330517296903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15712293291814214712791741 5892109984430330517296903)
    ·
      refine ⟨8838164976645495775945355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892109984430330517296903 8838164976645495775945355)
      ·
        refine ⟨13257247464968243663918033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8838164976645495775945355 13257247464968243663918033)
        ·
          refine ⟨9942935598726182747938525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13257247464968243663918033 9942935598726182747938525)
          ·
            refine ⟨3728600849522318530476947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9942935598726182747938525 3728600849522318530476947)
            ·
              refine ⟨5592901274283477795715421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728600849522318530476947 5592901274283477795715421)
              ·
                refine ⟨2097337977856304173393283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5592901274283477795715421 2097337977856304173393283)
                ·
                  refine ⟨3146006966784456260089925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097337977856304173393283 3146006966784456260089925)
                  ·
                    refine ⟨589876306272085548766861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146006966784456260089925 589876306272085548766861)
                    ·
                      rfl

theorem cell22_1723170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1723170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723170 prefixEnd_1723170 := by exact prefixLift 1723170
  have htrace : WordTrace (prefixWord ++ tailWord_1723170) baseStart_1723170 baseEnd_1723170 := by
    simpa [prefixWord, tailWord_1723170, baseEnd_1723170] using wordTrace_append hprefix tailTrace_1723170
  have hstable : (prefixWord ++ tailWord_1723170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723170).length < 2 ^ (prefixWord ++ tailWord_1723170).sum := by decide
  have hdescent : baseEnd_1723170 < baseStart_1723170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723196 : List Nat := [2, 2, 2, 2, 1, 1, 1, 11]
def baseStart_1723196 : Nat := 118140960795 + 1723196 * 2 ^ 59
def prefixEnd_1723196 : Nat := 4983230072969 + 3 ^ 40 * 1723196 * 2
def baseEnd_1723196 : Nat := 65542800733714460846309

theorem tailTrace_1723196 : CollatzResearch.WordTrace tailWord_1723196 prefixEnd_1723196 65542800733714460846309 := by
  unfold tailWord_1723196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425060732581332645806721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41900080976775110194408961 31425060732581332645806721)
  ·
    refine ⟨23568795549435999484355041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31425060732581332645806721 23568795549435999484355041)
    ·
      refine ⟨17676596662076999613266281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23568795549435999484355041 17676596662076999613266281)
      ·
        refine ⟨13257447496557749709949711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17676596662076999613266281 13257447496557749709949711)
        ·
          refine ⟨19886171244836624564924567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13257447496557749709949711 19886171244836624564924567)
          ·
            refine ⟨29829256867254936847386851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19886171244836624564924567 29829256867254936847386851)
            ·
              refine ⟨44743885300882405271080277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29829256867254936847386851 44743885300882405271080277)
              ·
                refine ⟨65542800733714460846309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 44743885300882405271080277 65542800733714460846309)
                ·
                  rfl

theorem cell22_1723196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_1723196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723196 prefixEnd_1723196 := by exact prefixLift 1723196
  have htrace : WordTrace (prefixWord ++ tailWord_1723196) baseStart_1723196 baseEnd_1723196 := by
    simpa [prefixWord, tailWord_1723196, baseEnd_1723196] using wordTrace_append hprefix tailTrace_1723196
  have hstable : (prefixWord ++ tailWord_1723196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723196).length < 2 ^ (prefixWord ++ tailWord_1723196).sum := by decide
  have hdescent : baseEnd_1723196 < baseStart_1723196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723204 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1723204 : Nat := 118140960795 + 1723204 * 2 ^ 59
def prefixEnd_1723204 : Nat := 4983230072969 + 3 ^ 40 * 1723204 * 2
def baseEnd_1723204 : Nat := 589887945166920793416757

theorem tailTrace_1723204 : CollatzResearch.WordTrace tailWord_1723204 prefixEnd_1723204 589887945166920793416757 := by
  unfold tailWord_1723204
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425206624566841328952333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41900275499422455105269777 31425206624566841328952333)
  ·
    refine ⟨11784452484212565498357125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31425206624566841328952333 11784452484212565498357125)
    ·
      refine ⟨2209584840789856030941961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11784452484212565498357125 2209584840789856030941961)
      ·
        refine ⟨1657188630592392023206471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2209584840789856030941961 1657188630592392023206471)
        ·
          refine ⟨2485782945888588034809707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657188630592392023206471 2485782945888588034809707)
          ·
            refine ⟨3728674418832882052214561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485782945888588034809707 3728674418832882052214561)
            ·
              refine ⟨2796505814124661539160921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728674418832882052214561 2796505814124661539160921)
              ·
                refine ⟨2097379360593496154370691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796505814124661539160921 2097379360593496154370691)
                ·
                  refine ⟨3146069040890244231556037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097379360593496154370691 3146069040890244231556037)
                  ·
                    refine ⟨589887945166920793416757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146069040890244231556037 589887945166920793416757)
                    ·
                      rfl

theorem cell22_1723204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1723204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723204 prefixEnd_1723204 := by exact prefixLift 1723204
  have htrace : WordTrace (prefixWord ++ tailWord_1723204) baseStart_1723204 baseEnd_1723204 := by
    simpa [prefixWord, tailWord_1723204, baseEnd_1723204] using wordTrace_append hprefix tailTrace_1723204
  have hstable : (prefixWord ++ tailWord_1723204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723204).length < 2 ^ (prefixWord ++ tailWord_1723204).sum := by decide
  have hdescent : baseEnd_1723204 < baseStart_1723204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723292 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_1723292 : Nat := 118140960795 + 1723292 * 2 ^ 59
def prefixEnd_1723292 : Nat := 4983230072969 + 3 ^ 40 * 1723292 * 2
def baseEnd_1723292 : Nat := 196639356455105965738829

theorem tailTrace_1723292 : CollatzResearch.WordTrace tailWord_1723292 prefixEnd_1723292 196639356455105965738829 := by
  unfold tailWord_1723292
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426811436407436843554065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41902415248543249124738753 31426811436407436843554065)
  ·
    refine ⟨23570108577305577632665549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31426811436407436843554065 23570108577305577632665549)
    ·
      refine ⟨8838790716489591612249581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23570108577305577632665549 8838790716489591612249581)
      ·
        refine ⟨3314546518683596854593593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8838790716489591612249581 3314546518683596854593593)
        ·
          refine ⟨2485909889012697640945195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3314546518683596854593593 2485909889012697640945195)
          ·
            refine ⟨3728864833519046461417793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485909889012697640945195 3728864833519046461417793)
            ·
              refine ⟨2796648625139284846063345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728864833519046461417793 2796648625139284846063345)
              ·
                refine ⟨2097486468854463634547509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796648625139284846063345 2097486468854463634547509)
                ·
                  refine ⟨196639356455105965738829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097486468854463634547509 196639356455105965738829)
                  ·
                    rfl

theorem cell22_1723292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_1723292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723292 prefixEnd_1723292 := by exact prefixLift 1723292
  have htrace : WordTrace (prefixWord ++ tailWord_1723292) baseStart_1723292 baseEnd_1723292 := by
    simpa [prefixWord, tailWord_1723292, baseEnd_1723292] using wordTrace_append hprefix tailTrace_1723292
  have hstable : (prefixWord ++ tailWord_1723292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723292).length < 2 ^ (prefixWord ++ tailWord_1723292).sum := by decide
  have hdescent : baseEnd_1723292 < baseStart_1723292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723352 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_1723352 : Nat := 118140960795 + 1723352 * 2 ^ 59
def prefixEnd_1723352 : Nat := 4983230072969 + 3 ^ 40 * 1723352 * 2
def baseEnd_1723352 : Nat := 589938608591497740716303

theorem tailTrace_1723352 : CollatzResearch.WordTrace tailWord_1723352 prefixEnd_1723352 589938608591497740716303 := by
  unfold tailWord_1723352
  simp only [CollatzResearch.WordTrace]
  refine ⟨31427905626298751967146155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41903874168398335956194873 31427905626298751967146155)
  ·
    refine ⟨47141858439448127950719233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31427905626298751967146155 47141858439448127950719233)
    ·
      refine ⟨35356393829586095963039425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47141858439448127950719233 35356393829586095963039425)
      ·
        refine ⟨26517295372189571972279569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35356393829586095963039425 26517295372189571972279569)
        ·
          refine ⟨19887971529142178979209677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26517295372189571972279569 19887971529142178979209677)
          ·
            refine ⟨7457989323428317117203629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19887971529142178979209677 7457989323428317117203629)
            ·
              refine ⟨2796745996285618918951361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7457989323428317117203629 2796745996285618918951361)
              ·
                refine ⟨2097559497214214189213521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796745996285618918951361 2097559497214214189213521)
                ·
                  refine ⟨1573169622910660641910141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097559497214214189213521 1573169622910660641910141)
                  ·
                    refine ⟨589938608591497740716303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573169622910660641910141 589938608591497740716303)
                    ·
                      rfl

theorem cell22_1723352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_1723352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723352 prefixEnd_1723352 := by exact prefixLift 1723352
  have htrace : WordTrace (prefixWord ++ tailWord_1723352) baseStart_1723352 baseEnd_1723352 := by
    simpa [prefixWord, tailWord_1723352, baseEnd_1723352] using wordTrace_append hprefix tailTrace_1723352
  have hstable : (prefixWord ++ tailWord_1723352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723352).length < 2 ^ (prefixWord ++ tailWord_1723352).sum := by decide
  have hdescent : baseEnd_1723352 < baseStart_1723352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723382 : List Nat := [5, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1723382 : Nat := 118140960795 + 1723382 * 2 ^ 59
def prefixEnd_1723382 : Nat := 4983230072969 + 3 ^ 40 * 1723382 * 2
def baseEnd_1723382 : Nat := 65549875356065295829579

theorem tailTrace_1723382 : CollatzResearch.WordTrace tailWord_1723382 prefixEnd_1723382 65549875356065295829579 := by
  unfold tailWord_1723382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928556590155551191117775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41904603628325879371922933 3928556590155551191117775)
  ·
    refine ⟨5892834885233326786676663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928556590155551191117775 5892834885233326786676663)
    ·
      refine ⟨8839252327849990180014995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892834885233326786676663 8839252327849990180014995)
      ·
        refine ⟨13258878491774985270022493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839252327849990180014995 13258878491774985270022493)
        ·
          refine ⟨4972079434415619476258435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13258878491774985270022493 4972079434415619476258435)
          ·
            refine ⟨7458119151623429214387653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972079434415619476258435 7458119151623429214387653)
            ·
              refine ⟨1398397340929392977697685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7458119151623429214387653 1398397340929392977697685)
              ·
                refine ⟨65549875356065295829579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1398397340929392977697685 65549875356065295829579)
                ·
                  rfl

theorem cell22_1723382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1723382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723382 prefixEnd_1723382 := by exact prefixLift 1723382
  have htrace : WordTrace (prefixWord ++ tailWord_1723382) baseStart_1723382 baseEnd_1723382 := by
    simpa [prefixWord, tailWord_1723382, baseEnd_1723382] using wordTrace_append hprefix tailTrace_1723382
  have hstable : (prefixWord ++ tailWord_1723382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723382).length < 2 ^ (prefixWord ++ tailWord_1723382).sum := by decide
  have hdescent : baseEnd_1723382 < baseStart_1723382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723427 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 5]
def baseStart_1723427 : Nat := 118140960795 + 1723427 * 2 ^ 59
def prefixEnd_1723427 : Nat := 4983230072969 + 3 ^ 40 * 1723427 * 2
def baseEnd_1723427 : Nat := 196654760874740848363691

theorem tailTrace_1723427 : CollatzResearch.WordTrace tailWord_1723427 prefixEnd_1723427 196654760874740848363691 := by
  unfold tailWord_1723427
  simp only [CollatzResearch.WordTrace]
  refine ⟨62858546727325791743272535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41905697818217194495515023 62858546727325791743272535)
  ·
    refine ⟨94287820090988687614908803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62858546727325791743272535 94287820090988687614908803)
    ·
      refine ⟨141431730136483031422363205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94287820090988687614908803 141431730136483031422363205)
      ·
        refine ⟨26518449400590568391693101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141431730136483031422363205 26518449400590568391693101)
        ·
          refine ⟨9944418525221463146884913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26518449400590568391693101 9944418525221463146884913)
          ·
            refine ⟨7458313893916097360163685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9944418525221463146884913 7458313893916097360163685)
            ·
              refine ⟨1398433855109268255030691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7458313893916097360163685 1398433855109268255030691)
              ·
                refine ⟨2097650782663902382546037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398433855109268255030691 2097650782663902382546037)
                ·
                  refine ⟨196654760874740848363691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097650782663902382546037 196654760874740848363691)
                  ·
                    rfl

theorem cell22_1723427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 5].length) (baseStart_1723427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723427 prefixEnd_1723427 := by exact prefixLift 1723427
  have htrace : WordTrace (prefixWord ++ tailWord_1723427) baseStart_1723427 baseEnd_1723427 := by
    simpa [prefixWord, tailWord_1723427, baseEnd_1723427] using wordTrace_append hprefix tailTrace_1723427
  have hstable : (prefixWord ++ tailWord_1723427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723427).length < 2 ^ (prefixWord ++ tailWord_1723427).sum := by decide
  have hdescent : baseEnd_1723427 < baseStart_1723427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723440 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_1723440 : Nat := 118140960795 + 1723440 * 2 ^ 59
def prefixEnd_1723440 : Nat := 4983230072969 + 3 ^ 40 * 1723440 * 2
def baseEnd_1723440 : Nat := 589968732789894844516033

theorem tailTrace_1723440 : CollatzResearch.WordTrace tailWord_1723440 prefixEnd_1723440 589968732789894844516033 := by
  unfold tailWord_1723440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429510438139347481747887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41906013917519129975663849 31429510438139347481747887)
  ·
    refine ⟨47144265657209021222621831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31429510438139347481747887 47144265657209021222621831)
    ·
      refine ⟨70716398485813531833932747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47144265657209021222621831 70716398485813531833932747)
      ·
        refine ⟨106074597728720297750899121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70716398485813531833932747 106074597728720297750899121)
        ·
          refine ⟨79555948296540223313174341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106074597728720297750899121 79555948296540223313174341)
          ·
            refine ⟨14916740305601291871220189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79555948296540223313174341 14916740305601291871220189)
            ·
              refine ⟨5593777614600484451707571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14916740305601291871220189 5593777614600484451707571)
              ·
                refine ⟨8390666421900726677561357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593777614600484451707571 8390666421900726677561357)
                ·
                  refine ⟨3146499908212772504085509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8390666421900726677561357 3146499908212772504085509)
                  ·
                    refine ⟨589968732789894844516033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146499908212772504085509 589968732789894844516033)
                    ·
                      rfl

theorem cell22_1723440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_1723440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723440 prefixEnd_1723440 := by exact prefixLift 1723440
  have htrace : WordTrace (prefixWord ++ tailWord_1723440) baseStart_1723440 baseEnd_1723440 := by
    simpa [prefixWord, tailWord_1723440, baseEnd_1723440] using wordTrace_append hprefix tailTrace_1723440
  have hstable : (prefixWord ++ tailWord_1723440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723440).length < 2 ^ (prefixWord ++ tailWord_1723440).sum := by decide
  have hdescent : baseEnd_1723440 < baseStart_1723440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723470 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1723470 : Nat := 118140960795 + 1723470 * 2 ^ 59
def prefixEnd_1723470 : Nat := 4983230072969 + 3 ^ 40 * 1723470 * 2
def baseEnd_1723470 : Nat := 589979002402984766265941

theorem tailTrace_1723470 : CollatzResearch.WordTrace tailWord_1723470 prefixEnd_1723470 589979002402984766265941 := by
  unfold tailWord_1723470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857514383271251260885983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41906743377446673391391909 7857514383271251260885983)
  ·
    refine ⟨11786271574906876891328975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857514383271251260885983 11786271574906876891328975)
    ·
      refine ⟨17679407362360315336993463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11786271574906876891328975 17679407362360315336993463)
      ·
        refine ⟨26519111043540473005490195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17679407362360315336993463 26519111043540473005490195)
        ·
          refine ⟨39778666565310709508235293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26519111043540473005490195 39778666565310709508235293)
          ·
            refine ⟨14916999961991516065588235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39778666565310709508235293 14916999961991516065588235)
            ·
              refine ⟨22375499942987274098382353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14916999961991516065588235 22375499942987274098382353)
              ·
                refine ⟨16781624957240455573786765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22375499942987274098382353 16781624957240455573786765)
                ·
                  refine ⟨6293109358965170840170037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16781624957240455573786765 6293109358965170840170037)
                  ·
                    refine ⟨589979002402984766265941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6293109358965170840170037 589979002402984766265941)
                    ·
                      rfl

theorem cell22_1723470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1723470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723470 prefixEnd_1723470 := by exact prefixLift 1723470
  have htrace : WordTrace (prefixWord ++ tailWord_1723470) baseStart_1723470 baseEnd_1723470 := by
    simpa [prefixWord, tailWord_1723470, baseEnd_1723470] using wordTrace_append hprefix tailTrace_1723470
  have hstable : (prefixWord ++ tailWord_1723470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723470).length < 2 ^ (prefixWord ++ tailWord_1723470).sum := by decide
  have hdescent : baseEnd_1723470 < baseStart_1723470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723487 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 2, 3]
def baseStart_1723487 : Nat := 118140960795 + 1723487 * 2 ^ 59
def prefixEnd_1723487 : Nat := 4983230072969 + 3 ^ 40 * 1723487 * 2
def baseEnd_1723487 : Nat := 589984821850402388590889

theorem tailTrace_1723487 : CollatzResearch.WordTrace tailWord_1723487 prefixEnd_1723487 589984821850402388590889 := by
  unfold tailWord_1723487
  simp only [CollatzResearch.WordTrace]
  refine ⟨62860735107108421990456715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41907156738072281326971143 62860735107108421990456715)
  ·
    refine ⟨94291102660662632985685073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62860735107108421990456715 94291102660662632985685073)
    ·
      refine ⟨70718326995496974739263805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94291102660662632985685073 70718326995496974739263805)
      ·
        refine ⟨26519372623311365527223927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70718326995496974739263805 26519372623311365527223927)
        ·
          refine ⟨39779058934967048290835891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26519372623311365527223927 39779058934967048290835891)
          ·
            refine ⟨59668588402450572436253837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39779058934967048290835891 59668588402450572436253837)
            ·
              refine ⟨22375720650918964663595189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59668588402450572436253837 22375720650918964663595189)
              ·
                refine ⟨2097723811023652937212049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22375720650918964663595189 2097723811023652937212049)
                ·
                  refine ⟨1573292858267739702909037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097723811023652937212049 1573292858267739702909037)
                  ·
                    refine ⟨589984821850402388590889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573292858267739702909037 589984821850402388590889)
                    ·
                      rfl

theorem cell22_1723487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_1723487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723487 prefixEnd_1723487 := by exact prefixLift 1723487
  have htrace : WordTrace (prefixWord ++ tailWord_1723487) baseStart_1723487 baseEnd_1723487 := by
    simpa [prefixWord, tailWord_1723487, baseEnd_1723487] using wordTrace_append hprefix tailTrace_1723487
  have hstable : (prefixWord ++ tailWord_1723487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723487).length < 2 ^ (prefixWord ++ tailWord_1723487).sum := by decide
  have hdescent : baseEnd_1723487 < baseStart_1723487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723502 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1723502 : Nat := 118140960795 + 1723502 * 2 ^ 59
def prefixEnd_1723502 : Nat := 4983230072969 + 3 ^ 40 * 1723502 * 2
def baseEnd_1723502 : Nat := 589989956656947349465843

theorem tailTrace_1723502 : CollatzResearch.WordTrace tailWord_1723502 prefixEnd_1723502 589989956656947349465843 := by
  unfold tailWord_1723502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857660275256759944031595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41907521468036053034835173 7857660275256759944031595)
  ·
    refine ⟨11786490412885139916047393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857660275256759944031595 11786490412885139916047393)
    ·
      refine ⟨8839867809663854937035545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786490412885139916047393 8839867809663854937035545)
      ·
        refine ⟨6629900857247891202776659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8839867809663854937035545 6629900857247891202776659)
        ·
          refine ⟨9944851285871836804164989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629900857247891202776659 9944851285871836804164989)
          ·
            refine ⟨3729319232201938801561871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9944851285871836804164989 3729319232201938801561871)
            ·
              refine ⟨5593978848302908202342807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729319232201938801561871 5593978848302908202342807)
              ·
                refine ⟨8390968272454362303514211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593978848302908202342807 8390968272454362303514211)
                ·
                  refine ⟨12586452408681543455271317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8390968272454362303514211 12586452408681543455271317)
                  ·
                    refine ⟨589989956656947349465843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12586452408681543455271317 589989956656947349465843)
                    ·
                      rfl

theorem cell22_1723502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1723502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723502 prefixEnd_1723502 := by exact prefixLift 1723502
  have htrace : WordTrace (prefixWord ++ tailWord_1723502) baseStart_1723502 baseEnd_1723502 := by
    simpa [prefixWord, tailWord_1723502, baseEnd_1723502] using wordTrace_append hprefix tailTrace_1723502
  have hstable : (prefixWord ++ tailWord_1723502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723502).length < 2 ^ (prefixWord ++ tailWord_1723502).sum := by decide
  have hdescent : baseEnd_1723502 < baseStart_1723502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723521 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1723521 : Nat := 118140960795 + 1723521 * 2 ^ 59
def prefixEnd_1723521 : Nat := 4983230072969 + 3 ^ 40 * 1723521 * 2
def baseEnd_1723521 : Nat := 589996460745237633240785

theorem tailTrace_1723521 : CollatzResearch.WordTrace tailWord_1723521 prefixEnd_1723521 589996460745237633240785 := by
  unfold tailWord_1723521
  simp only [CollatzResearch.WordTrace]
  refine ⟨62861975188985245797194417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41907983459323497198129611 62861975188985245797194417)
  ·
    refine ⟨47146481391738934347895813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62861975188985245797194417 47146481391738934347895813)
    ·
      refine ⟨8839965260951050190230465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47146481391738934347895813 8839965260951050190230465)
      ·
        refine ⟨6629973945713287642672849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8839965260951050190230465 6629973945713287642672849)
        ·
          refine ⟨4972480459284965732004637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6629973945713287642672849 4972480459284965732004637)
          ·
            refine ⟨1864680172231862149501739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4972480459284965732004637 1864680172231862149501739)
            ·
              refine ⟨2797020258347793224252609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864680172231862149501739 2797020258347793224252609)
              ·
                refine ⟨2097765193760844918189457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797020258347793224252609 2097765193760844918189457)
                ·
                  refine ⟨1573323895320633688642093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097765193760844918189457 1573323895320633688642093)
                  ·
                    refine ⟨589996460745237633240785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573323895320633688642093 589996460745237633240785)
                    ·
                      rfl

theorem cell22_1723521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1723521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723521 prefixEnd_1723521 := by exact prefixLift 1723521
  have htrace : WordTrace (prefixWord ++ tailWord_1723521) baseStart_1723521 baseEnd_1723521 := by
    simpa [prefixWord, tailWord_1723521, baseEnd_1723521] using wordTrace_append hprefix tailTrace_1723521
  have hstable : (prefixWord ++ tailWord_1723521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723521).length < 2 ^ (prefixWord ++ tailWord_1723521).sum := by decide
  have hdescent : baseEnd_1723521 < baseStart_1723521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723551 : List Nat := [1, 1, 2, 6, 3, 1, 2, 6]
def baseStart_1723551 : Nat := 118140960795 + 1723551 * 2 ^ 59
def prefixEnd_1723551 : Nat := 4983230072969 + 3 ^ 40 * 1723551 * 2
def baseEnd_1723551 : Nat := 65556303373147506110077

theorem tailTrace_1723551 : CollatzResearch.WordTrace tailWord_1723551 prefixEnd_1723551 65556303373147506110077 := by
  unfold tailWord_1723551
  simp only [CollatzResearch.WordTrace]
  refine ⟨62863069378876560920786507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41908712919251040613857671 62863069378876560920786507)
  ·
    refine ⟨94294604068314841381179761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62863069378876560920786507 94294604068314841381179761)
    ·
      refine ⟨70720953051236131035884821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94294604068314841381179761 70720953051236131035884821)
      ·
        refine ⟨3315044674276693642307101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70720953051236131035884821 3315044674276693642307101)
        ·
          refine ⟨1243141752853760115865163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315044674276693642307101 1243141752853760115865163)
          ·
            refine ⟨1864712629280640173797745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243141752853760115865163 1864712629280640173797745)
            ·
              refine ⟨1398534471960480130348309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864712629280640173797745 1398534471960480130348309)
              ·
                refine ⟨65556303373147506110077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1398534471960480130348309 65556303373147506110077)
                ·
                  rfl

theorem cell22_1723551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 6].length) (baseStart_1723551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723551 prefixEnd_1723551 := by exact prefixLift 1723551
  have htrace : WordTrace (prefixWord ++ tailWord_1723551) baseStart_1723551 baseEnd_1723551 := by
    simpa [prefixWord, tailWord_1723551, baseEnd_1723551] using wordTrace_append hprefix tailTrace_1723551
  have hstable : (prefixWord ++ tailWord_1723551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723551).length < 2 ^ (prefixWord ++ tailWord_1723551).sum := by decide
  have hdescent : baseEnd_1723551 < baseStart_1723551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723624 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_1723624 : Nat := 118140960795 + 1723624 * 2 ^ 59
def prefixEnd_1723624 : Nat := 4983230072969 + 3 ^ 40 * 1723624 * 2
def baseEnd_1723624 : Nat := 196677239916726565971823

theorem tailTrace_1723624 : CollatzResearch.WordTrace tailWord_1723624 prefixEnd_1723624 196677239916726565971823 := by
  unfold tailWord_1723624
  simp only [CollatzResearch.WordTrace]
  refine ⟨31432865953806047194096963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41910487938408062925462617 31432865953806047194096963)
  ·
    refine ⟨47149298930709070791145445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31432865953806047194096963 47149298930709070791145445)
    ·
      refine ⟨8840493549507950773339771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47149298930709070791145445 8840493549507950773339771)
      ·
        refine ⟨13260740324261926160009657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840493549507950773339771 13260740324261926160009657)
        ·
          refine ⟨9945555243196444620007243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13260740324261926160009657 9945555243196444620007243)
          ·
            refine ⟨14918332864794666930010865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9945555243196444620007243 14918332864794666930010865)
            ·
              refine ⟨11188749648596000197508149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14918332864794666930010865 11188749648596000197508149)
              ·
                refine ⟨1048945279555875018516389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11188749648596000197508149 1048945279555875018516389)
                ·
                  refine ⟨196677239916726565971823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048945279555875018516389 196677239916726565971823)
                  ·
                    rfl

theorem cell22_1723624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_1723624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723624 prefixEnd_1723624 := by exact prefixLift 1723624
  have htrace : WordTrace (prefixWord ++ tailWord_1723624) baseStart_1723624 baseEnd_1723624 := by
    simpa [prefixWord, tailWord_1723624, baseEnd_1723624] using wordTrace_append hprefix tailTrace_1723624
  have hstable : (prefixWord ++ tailWord_1723624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723624).length < 2 ^ (prefixWord ++ tailWord_1723624).sum := by decide
  have hdescent : baseEnd_1723624 < baseStart_1723624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723626 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1723626 : Nat := 118140960795 + 1723626 * 2 ^ 59
def prefixEnd_1723626 : Nat := 4983230072969 + 3 ^ 40 * 1723626 * 2
def baseEnd_1723626 : Nat := 590032404391052359365463

theorem tailTrace_1723626 : CollatzResearch.WordTrace tailWord_1723626 prefixEnd_1723626 590032404391052359365463 := by
  unfold tailWord_1723626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15716451213401212182441683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41910536569069899153177821 15716451213401212182441683)
  ·
    refine ⟨23574676820101818273662525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15716451213401212182441683 23574676820101818273662525)
    ·
      refine ⟨8840503807538181852623447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23574676820101818273662525 8840503807538181852623447)
      ·
        refine ⟨13260755711307272778935171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840503807538181852623447 13260755711307272778935171)
        ·
          refine ⟨19891133566960909168402757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260755711307272778935171 19891133566960909168402757)
          ·
            refine ⟨3729587543805170469075517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19891133566960909168402757 3729587543805170469075517)
            ·
              refine ⟨1398595328926938925903319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3729587543805170469075517 1398595328926938925903319)
              ·
                refine ⟨2097892993390408388854979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398595328926938925903319 2097892993390408388854979)
                ·
                  refine ⟨3146839490085612583282469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097892993390408388854979 3146839490085612583282469)
                  ·
                    refine ⟨590032404391052359365463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3146839490085612583282469 590032404391052359365463)
                    ·
                      rfl

theorem cell22_1723626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1723626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723626 prefixEnd_1723626 := by exact prefixLift 1723626
  have htrace : WordTrace (prefixWord ++ tailWord_1723626) baseStart_1723626 baseEnd_1723626 := by
    simpa [prefixWord, tailWord_1723626, baseEnd_1723626] using wordTrace_append hprefix tailTrace_1723626
  have hstable : (prefixWord ++ tailWord_1723626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723626).length < 2 ^ (prefixWord ++ tailWord_1723626).sum := by decide
  have hdescent : baseEnd_1723626 < baseStart_1723626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723635 : List Nat := [1, 1, 1, 2, 2, 15]
def baseStart_1723635 : Nat := 118140960795 + 1723635 * 2 ^ 59
def prefixEnd_1723635 : Nat := 4983230072969 + 3 ^ 40 * 1723635 * 2
def baseEnd_1723635 : Nat := 7284388707098510319635

theorem tailTrace_1723635 : CollatzResearch.WordTrace tailWord_1723635 prefixEnd_1723635 7284388707098510319635 := by
  unfold tailWord_1723635
  simp only [CollatzResearch.WordTrace]
  refine ⟨62866133110572243266844359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41910755407048162177896239 62866133110572243266844359)
  ·
    refine ⟨94299199665858364900266539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62866133110572243266844359 94299199665858364900266539)
    ·
      refine ⟨141448799498787547350399809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94299199665858364900266539 141448799498787547350399809)
      ·
        refine ⟨106086599624090660512799857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141448799498787547350399809 106086599624090660512799857)
        ·
          refine ⟨79564949718067995384599893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106086599624090660512799857 79564949718067995384599893)
          ·
            refine ⟨7284388707098510319635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 79564949718067995384599893 7284388707098510319635)
            ·
              rfl

theorem cell22_1723635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 15].length) (baseStart_1723635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723635 prefixEnd_1723635 := by exact prefixLift 1723635
  have htrace : WordTrace (prefixWord ++ tailWord_1723635) baseStart_1723635 baseEnd_1723635 := by
    simpa [prefixWord, tailWord_1723635, baseEnd_1723635] using wordTrace_append hprefix tailTrace_1723635
  have hstable : (prefixWord ++ tailWord_1723635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723635).length < 2 ^ (prefixWord ++ tailWord_1723635).sum := by decide
  have hdescent : baseEnd_1723635 < baseStart_1723635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723684 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_1723684 : Nat := 118140960795 + 1723684 * 2 ^ 59
def prefixEnd_1723684 : Nat := 4983230072969 + 3 ^ 40 * 1723684 * 2
def baseEnd_1723684 : Nat := 590052258976359541415285

theorem tailTrace_1723684 : CollatzResearch.WordTrace tailWord_1723684 prefixEnd_1723684 590052258976359541415285 := by
  unfold tailWord_1723684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31433960143697362317689053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41911946858263149756918737 31433960143697362317689053)
  ·
    refine ⟨11787735053886510869133395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31433960143697362317689053 11787735053886510869133395)
    ·
      refine ⟨17681602580829766303700093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11787735053886510869133395 17681602580829766303700093)
      ·
        refine ⟨6630600967811162363887535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17681602580829766303700093 6630600967811162363887535)
        ·
          refine ⟨9945901451716743545831303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630600967811162363887535 9945901451716743545831303)
          ·
            refine ⟨14918852177575115318746955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9945901451716743545831303 14918852177575115318746955)
            ·
              refine ⟨22378278266362672978120433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14918852177575115318746955 22378278266362672978120433)
              ·
                refine ⟨16783708699772004733590325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22378278266362672978120433 16783708699772004733590325)
                ·
                  refine ⟨1573472690603625443774093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16783708699772004733590325 1573472690603625443774093)
                  ·
                    refine ⟨590052258976359541415285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573472690603625443774093 590052258976359541415285)
                    ·
                      rfl

theorem cell22_1723684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_1723684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723684 prefixEnd_1723684 := by exact prefixLift 1723684
  have htrace : WordTrace (prefixWord ++ tailWord_1723684) baseStart_1723684 baseEnd_1723684 := by
    simpa [prefixWord, tailWord_1723684, baseEnd_1723684] using wordTrace_append hprefix tailTrace_1723684
  have hstable : (prefixWord ++ tailWord_1723684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723684).length < 2 ^ (prefixWord ++ tailWord_1723684).sum := by decide
  have hdescent : baseEnd_1723684 < baseStart_1723684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723701 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1723701 : Nat := 118140960795 + 1723701 * 2 ^ 59
def prefixEnd_1723701 : Nat := 4983230072969 + 3 ^ 40 * 1723701 * 2
def baseEnd_1723701 : Nat := 590058078423777163740233

theorem tailTrace_1723701 : CollatzResearch.WordTrace tailWord_1723701 prefixEnd_1723701 590058078423777163740233 := by
  unfold tailWord_1723701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62868540328333136538746957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41912360218888757692497971 62868540328333136538746957)
  ·
    refine ⟨23575702623124926202030109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62868540328333136538746957 23575702623124926202030109)
    ·
      refine ⟨8840888483671847325761291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23575702623124926202030109 8840888483671847325761291)
      ·
        refine ⟨13261332725507770988641937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840888483671847325761291 13261332725507770988641937)
        ·
          refine ⟨9945999544130828241481453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13261332725507770988641937 9945999544130828241481453)
          ·
            refine ⟨3729749829049060590555545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9945999544130828241481453 3729749829049060590555545)
            ·
              refine ⟨2797312371786795442916659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3729749829049060590555545 2797312371786795442916659)
              ·
                refine ⟨4195968557680193164374989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797312371786795442916659 4195968557680193164374989)
                ·
                  refine ⟨1573488209130072436640621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4195968557680193164374989 1573488209130072436640621)
                  ·
                    refine ⟨590058078423777163740233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573488209130072436640621 590058078423777163740233)
                    ·
                      rfl

theorem cell22_1723701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1723701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723701 prefixEnd_1723701 := by exact prefixLift 1723701
  have htrace : WordTrace (prefixWord ++ tailWord_1723701) baseStart_1723701 baseEnd_1723701 := by
    simpa [prefixWord, tailWord_1723701, baseEnd_1723701] using wordTrace_append hprefix tailTrace_1723701
  have hstable : (prefixWord ++ tailWord_1723701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723701).length < 2 ^ (prefixWord ++ tailWord_1723701).sum := by decide
  have hdescent : baseEnd_1723701 < baseStart_1723701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723712 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_1723712 : Nat := 118140960795 + 1723712 * 2 ^ 59
def prefixEnd_1723712 : Nat := 4983230072969 + 3 ^ 40 * 1723712 * 2
def baseEnd_1723712 : Nat := 590061843948576801715199

theorem tailTrace_1723712 : CollatzResearch.WordTrace tailWord_1723712 prefixEnd_1723712 590061843948576801715199 := by
  unfold tailWord_1723712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31434470765646642708698695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41912627687528856944931593 31434470765646642708698695)
  ·
    refine ⟨47151706148469964063048043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31434470765646642708698695 47151706148469964063048043)
    ·
      refine ⟨70727559222704946094572065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47151706148469964063048043 70727559222704946094572065)
      ·
        refine ⟨53045669417028709570929049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70727559222704946094572065 53045669417028709570929049)
        ·
          refine ⟨39784252062771532178196787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53045669417028709570929049 39784252062771532178196787)
          ·
            refine ⟨59676378094157298267295181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39784252062771532178196787 59676378094157298267295181)
            ·
              refine ⟨22378641785308986850235693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59676378094157298267295181 22378641785308986850235693)
              ·
                refine ⟨8391990669490870068838385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22378641785308986850235693 8391990669490870068838385)
                ·
                  refine ⟨6293993002118152551628789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391990669490870068838385 6293993002118152551628789)
                  ·
                    refine ⟨590061843948576801715199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6293993002118152551628789 590061843948576801715199)
                    ·
                      rfl

theorem cell22_1723712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_1723712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723712 prefixEnd_1723712 := by exact prefixLift 1723712
  have htrace : WordTrace (prefixWord ++ tailWord_1723712) baseStart_1723712 baseEnd_1723712 := by
    simpa [prefixWord, tailWord_1723712, baseEnd_1723712] using wordTrace_append hprefix tailTrace_1723712
  have hstable : (prefixWord ++ tailWord_1723712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723712).length < 2 ^ (prefixWord ++ tailWord_1723712).sum := by decide
  have hdescent : baseEnd_1723712 < baseStart_1723712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1723727 : Nat := 118140960795 + 1723727 * 2 ^ 59
def prefixEnd_1723727 : Nat := 4983230072969 + 3 ^ 40 * 1723727 * 2
def baseEnd_1723727 : Nat := 590066978755121762590153

theorem tailTrace_1723727 : CollatzResearch.WordTrace tailWord_1723727 prefixEnd_1723727 590066978755121762590153 := by
  unfold tailWord_1723727
  simp only [CollatzResearch.WordTrace]
  refine ⟨62869488626238942979193435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41912992417492628652795623 62869488626238942979193435)
  ·
    refine ⟨94304232939358414468790153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62869488626238942979193435 94304232939358414468790153)
    ·
      refine ⟨70728174704518810851592615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94304232939358414468790153 70728174704518810851592615)
      ·
        refine ⟨106092262056778216277388923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70728174704518810851592615 106092262056778216277388923)
        ·
          refine ⟨159138393085167324416083385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106092262056778216277388923 159138393085167324416083385)
          ·
            refine ⟨119353794813875493312062539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159138393085167324416083385 119353794813875493312062539)
            ·
              refine ⟨179030692220813239968093809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119353794813875493312062539 179030692220813239968093809)
              ·
                refine ⟨134273019165609929976070357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179030692220813239968093809 134273019165609929976070357)
                ·
                  refine ⟨3147023886693982733814149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134273019165609929976070357 3147023886693982733814149)
                  ·
                    refine ⟨590066978755121762590153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147023886693982733814149 590066978755121762590153)
                    ·
                      rfl

theorem cell22_1723727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1723727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723727 prefixEnd_1723727 := by exact prefixLift 1723727
  have htrace : WordTrace (prefixWord ++ tailWord_1723727) baseStart_1723727 baseEnd_1723727 := by
    simpa [prefixWord, tailWord_1723727, baseEnd_1723727] using wordTrace_append hprefix tailTrace_1723727
  have hstable : (prefixWord ++ tailWord_1723727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723727).length < 2 ^ (prefixWord ++ tailWord_1723727).sum := by decide
  have hdescent : baseEnd_1723727 < baseStart_1723727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723765 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 5]
def baseStart_1723765 : Nat := 118140960795 + 1723765 * 2 ^ 59
def prefixEnd_1723765 : Nat := 4983230072969 + 3 ^ 40 * 1723765 * 2
def baseEnd_1723765 : Nat := 196693328977234110046679

theorem tailTrace_1723765 : CollatzResearch.WordTrace tailWord_1723765 prefixEnd_1723765 196693328977234110046679 := by
  unfold tailWord_1723765
  simp only [CollatzResearch.WordTrace]
  refine ⟨62870874600101275469076749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41913916400067516979384499 62870874600101275469076749)
  ·
    refine ⟨23576577975037978300903781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62870874600101275469076749 23576577975037978300903781)
    ·
      refine ⟨4420608370319620931419459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23576577975037978300903781 4420608370319620931419459)
      ·
        refine ⟨6630912555479431397129189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420608370319620931419459 6630912555479431397129189)
        ·
          refine ⟨1243296104152393386961723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6630912555479431397129189 1243296104152393386961723)
          ·
            refine ⟨1864944156228590080442585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243296104152393386961723 1864944156228590080442585)
            ·
              refine ⟨1398708117171442560331939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864944156228590080442585 1398708117171442560331939)
              ·
                refine ⟨2098062175757163840497909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398708117171442560331939 2098062175757163840497909)
                ·
                  refine ⟨196693328977234110046679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098062175757163840497909 196693328977234110046679)
                  ·
                    rfl

theorem cell22_1723765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_1723765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723765 prefixEnd_1723765 := by exact prefixLift 1723765
  have htrace : WordTrace (prefixWord ++ tailWord_1723765) baseStart_1723765 baseEnd_1723765 := by
    simpa [prefixWord, tailWord_1723765, baseEnd_1723765] using wordTrace_append hprefix tailTrace_1723765
  have hstable : (prefixWord ++ tailWord_1723765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723765).length < 2 ^ (prefixWord ++ tailWord_1723765).sum := by decide
  have hdescent : baseEnd_1723765 < baseStart_1723765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723778 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1723778 : Nat := 118140960795 + 1723778 * 2 ^ 59
def prefixEnd_1723778 : Nat := 4983230072969 + 3 ^ 40 * 1723778 * 2
def baseEnd_1723778 : Nat := 590084437097374629564997

theorem tailTrace_1723778 : CollatzResearch.WordTrace tailWord_1723778 prefixEnd_1723778 590084437097374629564997 := by
  unfold tailWord_1723778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717837187263544672324997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41914232499369452459533325 15717837187263544672324997)
  ·
    refine ⟨2947094472611914626060937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15717837187263544672324997 2947094472611914626060937)
    ·
      refine ⟨2210320854458935969545703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947094472611914626060937 2210320854458935969545703)
      ·
        refine ⟨3315481281688403954318555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210320854458935969545703 3315481281688403954318555)
        ·
          refine ⟨4973221922532605931477833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315481281688403954318555 4973221922532605931477833)
          ·
            refine ⟨3729916441899454448608375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4973221922532605931477833 3729916441899454448608375)
            ·
              refine ⟨5594874662849181672912563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729916441899454448608375 5594874662849181672912563)
              ·
                refine ⟨8392311994273772509368845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594874662849181672912563 8392311994273772509368845)
                ·
                  refine ⟨3147116997852664691013317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8392311994273772509368845 3147116997852664691013317)
                  ·
                    refine ⟨590084437097374629564997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147116997852664691013317 590084437097374629564997)
                    ·
                      rfl

theorem cell22_1723778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1723778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723778 prefixEnd_1723778 := by exact prefixLift 1723778
  have htrace : WordTrace (prefixWord ++ tailWord_1723778) baseStart_1723778 baseEnd_1723778 := by
    simpa [prefixWord, tailWord_1723778, baseEnd_1723778] using wordTrace_append hprefix tailTrace_1723778
  have hstable : (prefixWord ++ tailWord_1723778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723778).length < 2 ^ (prefixWord ++ tailWord_1723778).sum := by decide
  have hdescent : baseEnd_1723778 < baseStart_1723778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723787 : List Nat := [1, 1, 1, 1, 4, 3, 1, 10]
def baseStart_1723787 : Nat := 118140960795 + 1723787 * 2 ^ 59
def prefixEnd_1723787 : Nat := 4983230072969 + 3 ^ 40 * 1723787 * 2
def baseEnd_1723787 : Nat := 65565279775700178454441

theorem tailTrace_1723787 : CollatzResearch.WordTrace tailWord_1723787 prefixEnd_1723787 65565279775700178454441 := by
  unfold tailWord_1723787
  simp only [CollatzResearch.WordTrace]
  refine ⟨62871677006021573226377615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41914451337347715484251743 62871677006021573226377615)
  ·
    refine ⟨94307515509032359839566423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62871677006021573226377615 94307515509032359839566423)
    ·
      refine ⟨141461273263548539759349635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94307515509032359839566423 141461273263548539759349635)
      ·
        refine ⟨212191909895322809639024453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141461273263548539759349635 212191909895322809639024453)
        ·
          refine ⟨39785983105373026807317085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212191909895322809639024453 39785983105373026807317085)
          ·
            refine ⟨14919743664514885052743907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39785983105373026807317085 14919743664514885052743907)
            ·
              refine ⟨22379615496772327579115861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14919743664514885052743907 22379615496772327579115861)
              ·
                refine ⟨65565279775700178454441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22379615496772327579115861 65565279775700178454441)
                ·
                  rfl

theorem cell22_1723787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 10].length) (baseStart_1723787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723787 prefixEnd_1723787 := by exact prefixLift 1723787
  have htrace : WordTrace (prefixWord ++ tailWord_1723787) baseStart_1723787 baseEnd_1723787 := by
    simpa [prefixWord, tailWord_1723787, baseEnd_1723787] using wordTrace_append hprefix tailTrace_1723787
  have hstable : (prefixWord ++ tailWord_1723787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723787).length < 2 ^ (prefixWord ++ tailWord_1723787).sum := by decide
  have hdescent : baseEnd_1723787 < baseStart_1723787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723804 : List Nat := [2, 2, 3, 4, 11]
def baseStart_1723804 : Nat := 118140960795 + 1723804 * 2 ^ 59
def prefixEnd_1723804 : Nat := 4983230072969 + 3 ^ 40 * 1723804 * 2
def baseEnd_1723804 : Nat := 2428367643739585302119

theorem tailTrace_1723804 : CollatzResearch.WordTrace tailWord_1723804 prefixEnd_1723804 2428367643739585302119 := by
  unfold tailWord_1723804
  simp only [CollatzResearch.WordTrace]
  refine ⟨31436148523479992564873233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41914864697973323419830977 31436148523479992564873233)
  ·
    refine ⟨23577111392609994423654925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31436148523479992564873233 23577111392609994423654925)
    ·
      refine ⟨8841416772228747908870597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23577111392609994423654925 8841416772228747908870597)
      ·
        refine ⟨1657765644792890232913237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8841416772228747908870597 1657765644792890232913237)
        ·
          refine ⟨2428367643739585302119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1657765644792890232913237 2428367643739585302119)
          ·
            rfl

theorem cell22_1723804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 11].length) (baseStart_1723804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723804 prefixEnd_1723804 := by exact prefixLift 1723804
  have htrace : WordTrace (prefixWord ++ tailWord_1723804) baseStart_1723804 baseEnd_1723804 := by
    simpa [prefixWord, tailWord_1723804, baseEnd_1723804] using wordTrace_append hprefix tailTrace_1723804
  have hstable : (prefixWord ++ tailWord_1723804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723804).length < 2 ^ (prefixWord ++ tailWord_1723804).sum := by decide
  have hdescent : baseEnd_1723804 < baseStart_1723804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723810 : List Nat := [3, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1723810 : Nat := 118140960795 + 1723810 * 2 ^ 59
def prefixEnd_1723810 : Nat := 4983230072969 + 3 ^ 40 * 1723810 * 2
def baseEnd_1723810 : Nat := 196698463783779070921633

theorem tailTrace_1723810 : CollatzResearch.WordTrace tailWord_1723810 prefixEnd_1723810 196698463783779070921633 := by
  unfold tailWord_1723810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718128971234562038616221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41915010589958832102976589 15718128971234562038616221)
  ·
    refine ⟨5894298364212960764481083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15718128971234562038616221 5894298364212960764481083)
    ·
      refine ⟨8841447546319441146721625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894298364212960764481083 8841447546319441146721625)
      ·
        refine ⟨6631085659739580860041219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8841447546319441146721625 6631085659739580860041219)
        ·
          refine ⟨9946628489609371290061829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631085659739580860041219 9946628489609371290061829)
          ·
            refine ⟨1864992841801757116886593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9946628489609371290061829 1864992841801757116886593)
            ·
              refine ⟨1398744631351317837664945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864992841801757116886593 1398744631351317837664945)
              ·
                refine ⟨1049058473513488378248709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398744631351317837664945 1049058473513488378248709)
                ·
                  refine ⟨196698463783779070921633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049058473513488378248709 196698463783779070921633)
                  ·
                    rfl

theorem cell22_1723810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1723810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723810 prefixEnd_1723810 := by exact prefixLift 1723810
  have htrace : WordTrace (prefixWord ++ tailWord_1723810) baseStart_1723810 baseEnd_1723810 := by
    simpa [prefixWord, tailWord_1723810, baseEnd_1723810] using wordTrace_append hprefix tailTrace_1723810
  have hstable : (prefixWord ++ tailWord_1723810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723810).length < 2 ^ (prefixWord ++ tailWord_1723810).sum := by decide
  have hdescent : baseEnd_1723810 < baseStart_1723810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723821 : List Nat := [1, 5, 2, 2, 1, 1, 3, 7]
def baseStart_1723821 : Nat := 118140960795 + 1723821 * 2 ^ 59
def prefixEnd_1723821 : Nat := 4983230072969 + 3 ^ 40 * 1723821 * 2
def baseEnd_1723821 : Nat := 65566572986237427859985

theorem tailTrace_1723821 : CollatzResearch.WordTrace tailWord_1723821 prefixEnd_1723821 65566572986237427859985 := by
  unfold tailWord_1723821
  simp only [CollatzResearch.WordTrace]
  refine ⟨62872917087898397033115317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41915278058598931355410211 62872917087898397033115317)
  ·
    refine ⟨5894335976990474721854561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62872917087898397033115317 5894335976990474721854561)
    ·
      refine ⟨4420751982742856041390921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5894335976990474721854561 4420751982742856041390921)
      ·
        refine ⟨3315563987057142031043191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420751982742856041390921 3315563987057142031043191)
        ·
          refine ⟨4973345980585713046564787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315563987057142031043191 4973345980585713046564787)
          ·
            refine ⟨7460018970878569569847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973345980585713046564787 7460018970878569569847181)
            ·
              refine ⟨2797507114079463588692693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460018970878569569847181 2797507114079463588692693)
              ·
                refine ⟨65566572986237427859985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2797507114079463588692693 65566572986237427859985)
                ·
                  rfl

theorem cell22_1723821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 7].length) (baseStart_1723821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723821 prefixEnd_1723821 := by exact prefixLift 1723821
  have htrace : WordTrace (prefixWord ++ tailWord_1723821) baseStart_1723821 baseEnd_1723821 := by
    simpa [prefixWord, tailWord_1723821, baseEnd_1723821] using wordTrace_append hprefix tailTrace_1723821
  have hstable : (prefixWord ++ tailWord_1723821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723821).length < 2 ^ (prefixWord ++ tailWord_1723821).sum := by decide
  have hdescent : baseEnd_1723821 < baseStart_1723821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723864 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1723864 : Nat := 118140960795 + 1723864 * 2 ^ 59
def prefixEnd_1723864 : Nat := 4983230072969 + 3 ^ 40 * 1723864 * 2
def baseEnd_1723864 : Nat := 590113876654899071914733

theorem tailTrace_1723864 : CollatzResearch.WordTrace tailWord_1723864 prefixEnd_1723864 590113876654899071914733 := by
  unfold tailWord_1723864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437242713371307688465323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41916323617828410251287097 31437242713371307688465323)
  ·
    refine ⟨47155864070056961532697985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31437242713371307688465323 47155864070056961532697985)
    ·
      refine ⟨35366898052542721149523489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47155864070056961532697985 35366898052542721149523489)
      ·
        refine ⟨26525173539407040862142617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35366898052542721149523489 26525173539407040862142617)
        ·
          refine ⟨19893880154555280646606963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26525173539407040862142617 19893880154555280646606963)
          ·
            refine ⟨29840820231832920969910445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19893880154555280646606963 29840820231832920969910445)
            ·
              refine ⟨11190307586937345363716417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29840820231832920969910445 11190307586937345363716417)
              ·
                refine ⟨8392730690203009022787313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11190307586937345363716417 8392730690203009022787313)
                ·
                  refine ⟨6294548017652256767090485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8392730690203009022787313 6294548017652256767090485)
                  ·
                    refine ⟨590113876654899071914733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294548017652256767090485 590113876654899071914733)
                    ·
                      rfl

theorem cell22_1723864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1723864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723864 prefixEnd_1723864 := by exact prefixLift 1723864
  have htrace : WordTrace (prefixWord ++ tailWord_1723864) baseStart_1723864 baseEnd_1723864 := by
    simpa [prefixWord, tailWord_1723864, baseEnd_1723864] using wordTrace_append hprefix tailTrace_1723864
  have hstable : (prefixWord ++ tailWord_1723864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723864).length < 2 ^ (prefixWord ++ tailWord_1723864).sum := by decide
  have hdescent : baseEnd_1723864 < baseStart_1723864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723866 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_1723866 : Nat := 118140960795 + 1723866 * 2 ^ 59
def prefixEnd_1723866 : Nat := 4983230072969 + 3 ^ 40 * 1723866 * 2
def baseEnd_1723866 : Nat := 196704853765257244454909

theorem tailTrace_1723866 : CollatzResearch.WordTrace tailWord_1723866 prefixEnd_1723866 196704853765257244454909 := by
  unfold tailWord_1723866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718639593183842429625863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41916372248490246479002301 15718639593183842429625863)
  ·
    refine ⟨23577959389775763644438795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15718639593183842429625863 23577959389775763644438795)
    ·
      refine ⟨35366939084663645466658193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23577959389775763644438795 35366939084663645466658193)
      ·
        refine ⟨26525204313497734099993645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35366939084663645466658193 26525204313497734099993645)
        ·
          refine ⟨9946951617561650287497617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26525204313497734099993645 9946951617561650287497617)
          ·
            refine ⟨7460213713171237715623213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9946951617561650287497617 7460213713171237715623213)
            ·
              refine ⟨2797580142439214143358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460213713171237715623213 2797580142439214143358705)
              ·
                refine ⟨2098185106829410607519029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797580142439214143358705 2098185106829410607519029)
                ·
                  refine ⟨196704853765257244454909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098185106829410607519029 196704853765257244454909)
                  ·
                    rfl

theorem cell22_1723866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_1723866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723866 prefixEnd_1723866 := by exact prefixLift 1723866
  have htrace : WordTrace (prefixWord ++ tailWord_1723866) baseStart_1723866 baseEnd_1723866 := by
    simpa [prefixWord, tailWord_1723866, baseEnd_1723866] using wordTrace_append hprefix tailTrace_1723866
  have hstable : (prefixWord ++ tailWord_1723866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723866).length < 2 ^ (prefixWord ++ tailWord_1723866).sum := by decide
  have hdescent : baseEnd_1723866 < baseStart_1723866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723896 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_1723896 : Nat := 118140960795 + 1723896 * 2 ^ 59
def prefixEnd_1723896 : Nat := 4983230072969 + 3 ^ 40 * 1723896 * 2
def baseEnd_1723896 : Nat := 590124830908861655114635

theorem tailTrace_1723896 : CollatzResearch.WordTrace tailWord_1723896 prefixEnd_1723896 590124830908861655114635 := by
  unfold tailWord_1723896
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437826281313342421047771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41917101708417789894730361 31437826281313342421047771)
  ·
    refine ⟨47156739421970013631571657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31437826281313342421047771 47156739421970013631571657)
    ·
      refine ⟨35367554566477510223678743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47156739421970013631571657 35367554566477510223678743)
      ·
        refine ⟨53051331849716265335518115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35367554566477510223678743 53051331849716265335518115)
        ·
          refine ⟨79576997774574398003277173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53051331849716265335518115 79576997774574398003277173)
          ·
            refine ⟨7460343541366349812807235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79576997774574398003277173 7460343541366349812807235)
            ·
              refine ⟨11190515312049524719210853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460343541366349812807235 11190515312049524719210853)
              ·
                refine ⟨2098221621009285884852035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11190515312049524719210853 2098221621009285884852035)
                ·
                  refine ⟨3147332431513928827278053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098221621009285884852035 3147332431513928827278053)
                  ·
                    refine ⟨590124830908861655114635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147332431513928827278053 590124830908861655114635)
                    ·
                      rfl

theorem cell22_1723896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_1723896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723896 prefixEnd_1723896 := by exact prefixLift 1723896
  have htrace : WordTrace (prefixWord ++ tailWord_1723896) baseStart_1723896 baseEnd_1723896 := by
    simpa [prefixWord, tailWord_1723896, baseEnd_1723896] using wordTrace_append hprefix tailTrace_1723896
  have hstable : (prefixWord ++ tailWord_1723896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723896).length < 2 ^ (prefixWord ++ tailWord_1723896).sum := by decide
  have hdescent : baseEnd_1723896 < baseStart_1723896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723909 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1723909 : Nat := 118140960795 + 1723909 * 2 ^ 59
def prefixEnd_1723909 : Nat := 4983230072969 + 3 ^ 40 * 1723909 * 2
def baseEnd_1723909 : Nat := 590129281074533954539595

theorem tailTrace_1723909 : CollatzResearch.WordTrace tailWord_1723909 prefixEnd_1723909 590129281074533954539595 := by
  unfold tailWord_1723909
  simp only [CollatzResearch.WordTrace]
  refine ⟨62876126711579588062318781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41917417807719725374879187 62876126711579588062318781)
  ·
    refine ⟨23578547516842345523369543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62876126711579588062318781 23578547516842345523369543)
    ·
      refine ⟨35367821275263518285054315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23578547516842345523369543 35367821275263518285054315)
      ·
        refine ⟨53051731912895277427581473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35367821275263518285054315 53051731912895277427581473)
        ·
          refine ⟨39788798934671458070686105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53051731912895277427581473 39788798934671458070686105)
          ·
            refine ⟨29841599201003593553014579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39788798934671458070686105 29841599201003593553014579)
            ·
              refine ⟨44762398801505390329521869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29841599201003593553014579 44762398801505390329521869)
              ·
                refine ⟨16785899550564521373570701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44762398801505390329521869 16785899550564521373570701)
                ·
                  refine ⟨6294712331461695515089013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16785899550564521373570701 6294712331461695515089013)
                  ·
                    refine ⟨590129281074533954539595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294712331461695515089013 590129281074533954539595)
                    ·
                      rfl

theorem cell22_1723909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1723909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723909 prefixEnd_1723909 := by exact prefixLift 1723909
  have htrace : WordTrace (prefixWord ++ tailWord_1723909) baseStart_1723909 baseEnd_1723909 := by
    simpa [prefixWord, tailWord_1723909, baseEnd_1723909] using wordTrace_append hprefix tailTrace_1723909
  have hstable : (prefixWord ++ tailWord_1723909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723909).length < 2 ^ (prefixWord ++ tailWord_1723909).sum := by decide
  have hdescent : baseEnd_1723909 < baseStart_1723909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723928 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_1723928 : Nat := 118140960795 + 1723928 * 2 ^ 59
def prefixEnd_1723928 : Nat := 4983230072969 + 3 ^ 40 * 1723928 * 2
def baseEnd_1723928 : Nat := 196711928387608079438179

theorem tailTrace_1723928 : CollatzResearch.WordTrace tailWord_1723928 prefixEnd_1723928 196711928387608079438179 := by
  unfold tailWord_1723928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31438409849255377153630219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41917879799007169538173625 31438409849255377153630219)
  ·
    refine ⟨47157614773883065730445329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31438409849255377153630219 47157614773883065730445329)
    ·
      refine ⟨35368211080412299297833997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47157614773883065730445329 35368211080412299297833997)
      ·
        refine ⟨13263079155154612236687749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35368211080412299297833997 13263079155154612236687749)
        ·
          refine ⟨2486827341591489794378953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13263079155154612236687749 2486827341591489794378953)
          ·
            refine ⟨1865120506193617345784215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486827341591489794378953 1865120506193617345784215)
            ·
              refine ⟨2797680759290426018676323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865120506193617345784215 2797680759290426018676323)
              ·
                refine ⟨4196521138935639028014485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797680759290426018676323 4196521138935639028014485)
                ·
                  refine ⟨196711928387608079438179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4196521138935639028014485 196711928387608079438179)
                  ·
                    rfl

theorem cell22_1723928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_1723928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723928 prefixEnd_1723928 := by exact prefixLift 1723928
  have htrace : WordTrace (prefixWord ++ tailWord_1723928) baseStart_1723928 baseEnd_1723928 := by
    simpa [prefixWord, tailWord_1723928, baseEnd_1723928] using wordTrace_append hprefix tailTrace_1723928
  have hstable : (prefixWord ++ tailWord_1723928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723928).length < 2 ^ (prefixWord ++ tailWord_1723928).sum := by decide
  have hdescent : baseEnd_1723928 < baseStart_1723928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723986 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1723986 : Nat := 118140960795 + 1723986 * 2 ^ 59
def prefixEnd_1723986 : Nat := 4983230072969 + 3 ^ 40 * 1723986 * 2
def baseEnd_1723986 : Nat := 590155639748131420364359

theorem tailTrace_1723986 : CollatzResearch.WordTrace tailWord_1723986 prefixEnd_1723986 590155639748131420364359 := by
  unfold tailWord_1723986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719733783075157553217953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41919290088200420141914541 15719733783075157553217953)
  ·
    refine ⟨11789800337306368164913465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15719733783075157553217953 11789800337306368164913465)
    ·
      refine ⟨8842350252979776123685099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11789800337306368164913465 8842350252979776123685099)
      ·
        refine ⟨13263525379469664185527649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842350252979776123685099 13263525379469664185527649)
        ·
          refine ⟨9947644034602248139145737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13263525379469664185527649 9947644034602248139145737)
          ·
            refine ⟨7460733025951686104359303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9947644034602248139145737 7460733025951686104359303)
            ·
              refine ⟨11191099538927529156538955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460733025951686104359303 11191099538927529156538955)
              ·
                refine ⟨16786649308391293734808433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11191099538927529156538955 16786649308391293734808433)
                ·
                  refine ⟨12589986981293470301106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16786649308391293734808433 12589986981293470301106325)
                  ·
                    refine ⟨590155639748131420364359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12589986981293470301106325 590155639748131420364359)
                    ·
                      rfl

theorem cell22_1723986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1723986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723986 prefixEnd_1723986 := by exact prefixLift 1723986
  have htrace : WordTrace (prefixWord ++ tailWord_1723986) baseStart_1723986 baseEnd_1723986 := by
    simpa [prefixWord, tailWord_1723986, baseEnd_1723986] using wordTrace_append hprefix tailTrace_1723986
  have hstable : (prefixWord ++ tailWord_1723986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723986).length < 2 ^ (prefixWord ++ tailWord_1723986).sum := by decide
  have hdescent : baseEnd_1723986 < baseStart_1723986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723988 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1723988 : Nat := 118140960795 + 1723988 * 2 ^ 59
def prefixEnd_1723988 : Nat := 4983230072969 + 3 ^ 40 * 1723988 * 2
def baseEnd_1723988 : Nat := 590156324389004081814353

theorem tailTrace_1723988 : CollatzResearch.WordTrace tailWord_1723988 prefixEnd_1723988 590156324389004081814353 := by
  unfold tailWord_1723988
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439504039146692277222309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41919338718862256369629745 31439504039146692277222309)
  ·
    refine ⟨5894907007340004801979183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31439504039146692277222309 5894907007340004801979183)
    ·
      refine ⟨8842360511010007202968775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894907007340004801979183 8842360511010007202968775)
      ·
        refine ⟨13263540766515010804453163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842360511010007202968775 13263540766515010804453163)
        ·
          refine ⟨19895311149772516206679745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263540766515010804453163 19895311149772516206679745)
          ·
            refine ⟨14921483362329387155009809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19895311149772516206679745 14921483362329387155009809)
            ·
              refine ⟨11191112521747040366257357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14921483362329387155009809 11191112521747040366257357)
              ·
                refine ⟨4196667195655140137346509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11191112521747040366257357 4196667195655140137346509)
                ·
                  refine ⟨1573750198370677551504941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4196667195655140137346509 1573750198370677551504941)
                  ·
                    refine ⟨590156324389004081814353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573750198370677551504941 590156324389004081814353)
                    ·
                      rfl

theorem cell22_1723988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1723988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1723988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1723988 prefixEnd_1723988 := by exact prefixLift 1723988
  have htrace : WordTrace (prefixWord ++ tailWord_1723988) baseStart_1723988 baseEnd_1723988 := by
    simpa [prefixWord, tailWord_1723988, baseEnd_1723988] using wordTrace_append hprefix tailTrace_1723988
  have hstable : (prefixWord ++ tailWord_1723988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723988).length < 2 ^ (prefixWord ++ tailWord_1723988).sum := by decide
  have hdescent : baseEnd_1723988 < baseStart_1723988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724001 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 5]
def baseStart_1724001 : Nat := 118140960795 + 1724001 * 2 ^ 59
def prefixEnd_1724001 : Nat := 4983230072969 + 3 ^ 40 * 1724001 * 2
def baseEnd_1724001 : Nat := 196720258184892127079771

theorem tailTrace_1724001 : CollatzResearch.WordTrace tailWord_1724001 prefixEnd_1724001 196720258184892127079771 := by
  unfold tailWord_1724001
  simp only [CollatzResearch.WordTrace]
  refine ⟨62879482227246287774667857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41919654818164191849778571 62879482227246287774667857)
  ·
    refine ⟨47159611670434715831000893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62879482227246287774667857 47159611670434715831000893)
    ·
      refine ⟨17684854376413018436625335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47159611670434715831000893 17684854376413018436625335)
      ·
        refine ⟨26527281564619527654938003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17684854376413018436625335 26527281564619527654938003)
        ·
          refine ⟨39790922346929291482407005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26527281564619527654938003 39790922346929291482407005)
          ·
            refine ⟨14921595880098484305902627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39790922346929291482407005 14921595880098484305902627)
            ·
              refine ⟨22382393820147726458853941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921595880098484305902627 22382393820147726458853941)
              ·
                refine ⟨2098349420638849355517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22382393820147726458853941 2098349420638849355517557)
                ·
                  refine ⟨196720258184892127079771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098349420638849355517557 196720258184892127079771)
                  ·
                    rfl

theorem cell22_1724001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_1724001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724001 prefixEnd_1724001 := by exact prefixLift 1724001
  have htrace : WordTrace (prefixWord ++ tailWord_1724001) baseStart_1724001 baseEnd_1724001 := by
    simpa [prefixWord, tailWord_1724001, baseEnd_1724001] using wordTrace_append hprefix tailTrace_1724001
  have hstable : (prefixWord ++ tailWord_1724001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724001).length < 2 ^ (prefixWord ++ tailWord_1724001).sum := by decide
  have hdescent : baseEnd_1724001 < baseStart_1724001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724022 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_1724022 : Nat := 118140960795 + 1724022 * 2 ^ 59
def prefixEnd_1724022 : Nat := 4983230072969 + 3 ^ 40 * 1724022 * 2
def baseEnd_1724022 : Nat := 590167963283839326464249

theorem tailTrace_1724022 : CollatzResearch.WordTrace tailWord_1724022 prefixEnd_1724022 590167963283839326464249 := by
  unfold tailWord_1724022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930015510010638022573895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41920165440113472240788213 3930015510010638022573895)
  ·
    refine ⟨5895023265015957033860843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930015510010638022573895 5895023265015957033860843)
    ·
      refine ⟨8842534897523935550791265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895023265015957033860843 8842534897523935550791265)
      ·
        refine ⟨6631901173142951663093449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8842534897523935550791265 6631901173142951663093449)
        ·
          refine ⟨4973925879857213747320087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631901173142951663093449 4973925879857213747320087)
          ·
            refine ⟨7460888819785820620980131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973925879857213747320087 7460888819785820620980131)
            ·
              refine ⟨11191333229678730931470197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460888819785820620980131 11191333229678730931470197)
              ·
                refine ⟨1049187490282381024825331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11191333229678730931470197 1049187490282381024825331)
                ·
                  refine ⟨1573781235423571537237997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049187490282381024825331 1573781235423571537237997)
                  ·
                    refine ⟨590167963283839326464249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573781235423571537237997 590167963283839326464249)
                    ·
                      rfl

theorem cell22_1724022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_1724022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724022 prefixEnd_1724022 := by exact prefixLift 1724022
  have htrace : WordTrace (prefixWord ++ tailWord_1724022) baseStart_1724022 baseEnd_1724022 := by
    simpa [prefixWord, tailWord_1724022, baseEnd_1724022] using wordTrace_append hprefix tailTrace_1724022
  have hstable : (prefixWord ++ tailWord_1724022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724022).length < 2 ^ (prefixWord ++ tailWord_1724022).sum := by decide
  have hdescent : baseEnd_1724022 < baseStart_1724022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724052 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1724052 : Nat := 118140960795 + 1724052 * 2 ^ 59
def prefixEnd_1724052 : Nat := 4983230072969 + 3 ^ 40 * 1724052 * 2
def baseEnd_1724052 : Nat := 196726077632309749404719

theorem tailTrace_1724052 : CollatzResearch.WordTrace tailWord_1724052 prefixEnd_1724052 196726077632309749404719 := by
  unfold tailWord_1724052
  simp only [CollatzResearch.WordTrace]
  refine ⟨31440671175030761742387205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41920894900041015656516273 31440671175030761742387205)
  ·
    refine ⟨5895125845318267826697601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31440671175030761742387205 5895125845318267826697601)
    ·
      refine ⟨4421344383988700870023201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5895125845318267826697601 4421344383988700870023201)
      ·
        refine ⟨3316008287991525652517401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4421344383988700870023201 3316008287991525652517401)
        ·
          refine ⟨2487006215993644239388051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316008287991525652517401 2487006215993644239388051)
          ·
            refine ⟨3730509323990466359082077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487006215993644239388051 3730509323990466359082077)
            ·
              refine ⟨1398940996496424884655779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3730509323990466359082077 1398940996496424884655779)
              ·
                refine ⟨2098411494744637326983669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398940996496424884655779 2098411494744637326983669)
                ·
                  refine ⟨196726077632309749404719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098411494744637326983669 196726077632309749404719)
                  ·
                    rfl

theorem cell22_1724052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1724052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724052 prefixEnd_1724052 := by exact prefixLift 1724052
  have htrace : WordTrace (prefixWord ++ tailWord_1724052) baseStart_1724052 baseEnd_1724052 := by
    simpa [prefixWord, tailWord_1724052, baseEnd_1724052] using wordTrace_append hprefix tailTrace_1724052
  have hstable : (prefixWord ++ tailWord_1724052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724052).length < 2 ^ (prefixWord ++ tailWord_1724052).sum := by decide
  have hdescent : baseEnd_1724052 < baseStart_1724052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724065 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1724065 : Nat := 118140960795 + 1724065 * 2 ^ 59
def prefixEnd_1724065 : Nat := 4983230072969 + 3 ^ 40 * 1724065 * 2
def baseEnd_1724065 : Nat := 590182683062601547639117

theorem tailTrace_1724065 : CollatzResearch.WordTrace tailWord_1724065 prefixEnd_1724065 590182683062601547639117 := by
  unfold tailWord_1724065
  simp only [CollatzResearch.WordTrace]
  refine ⟨62881816499014426704997649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41921210999342951136665099 62881816499014426704997649)
  ·
    refine ⟨47161362374260820028748237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62881816499014426704997649 47161362374260820028748237)
    ·
      refine ⟨17685510890347807510780589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47161362374260820028748237 17685510890347807510780589)
      ·
        refine ⟨6632066583880427816542721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17685510890347807510780589 6632066583880427816542721)
        ·
          refine ⟨4974049937910320862407041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6632066583880427816542721 4974049937910320862407041)
          ·
            refine ⟨3730537453432740646805281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4974049937910320862407041 3730537453432740646805281)
            ·
              refine ⟨2797903090074555485103961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730537453432740646805281 2797903090074555485103961)
              ·
                refine ⟨2098427317555916613827971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797903090074555485103961 2098427317555916613827971)
                ·
                  refine ⟨3147640976333874920741957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098427317555916613827971 3147640976333874920741957)
                  ·
                    refine ⟨590182683062601547639117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147640976333874920741957 590182683062601547639117)
                    ·
                      rfl

theorem cell22_1724065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1724065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724065 prefixEnd_1724065 := by exact prefixLift 1724065
  have htrace : WordTrace (prefixWord ++ tailWord_1724065) baseStart_1724065 baseEnd_1724065 := by
    simpa [prefixWord, tailWord_1724065, baseEnd_1724065] using wordTrace_append hprefix tailTrace_1724065
  have hstable : (prefixWord ++ tailWord_1724065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724065).length < 2 ^ (prefixWord ++ tailWord_1724065).sum := by decide
  have hdescent : baseEnd_1724065 < baseStart_1724065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724076 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_1724076 : Nat := 118140960795 + 1724076 * 2 ^ 59
def prefixEnd_1724076 : Nat := 4983230072969 + 3 ^ 40 * 1724076 * 2
def baseEnd_1724076 : Nat := 590186448587401185614083

theorem tailTrace_1724076 : CollatzResearch.WordTrace tailWord_1724076 prefixEnd_1724076 590186448587401185614083 := by
  unfold tailWord_1724076
  simp only [CollatzResearch.WordTrace]
  refine ⟨31441108850987287791824041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41921478467983050389098721 31441108850987287791824041)
  ·
    refine ⟨23580831638240465843868031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31441108850987287791824041 23580831638240465843868031)
    ·
      refine ⟨35371247457360698765802047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23580831638240465843868031 35371247457360698765802047)
      ·
        refine ⟨53056871186041048148703071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35371247457360698765802047 53056871186041048148703071)
        ·
          refine ⟨79585306779061572223054607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53056871186041048148703071 79585306779061572223054607)
          ·
            refine ⟨119377960168592358334581911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79585306779061572223054607 119377960168592358334581911)
            ·
              refine ⟨179066940252888537501872867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119377960168592358334581911 179066940252888537501872867)
              ·
                refine ⟨268600410379332806252809301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179066940252888537501872867 268600410379332806252809301)
                ·
                  refine ⟨3147661059132806323275109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 268600410379332806252809301 3147661059132806323275109)
                  ·
                    refine ⟨590186448587401185614083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147661059132806323275109 590186448587401185614083)
                    ·
                      rfl

theorem cell22_1724076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_1724076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724076 prefixEnd_1724076 := by exact prefixLift 1724076
  have htrace : WordTrace (prefixWord ++ tailWord_1724076) baseStart_1724076 baseEnd_1724076 := by
    simpa [prefixWord, tailWord_1724076, baseEnd_1724076] using wordTrace_append hprefix tailTrace_1724076
  have hstable : (prefixWord ++ tailWord_1724076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724076).length < 2 ^ (prefixWord ++ tailWord_1724076).sum := by decide
  have hdescent : baseEnd_1724076 < baseStart_1724076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724093 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1724093 : Nat := 118140960795 + 1724093 * 2 ^ 59
def prefixEnd_1724093 : Nat := 4983230072969 + 3 ^ 40 * 1724093 * 2
def baseEnd_1724093 : Nat := 590192268034818807939031

theorem tailTrace_1724093 : CollatzResearch.WordTrace tailWord_1724093 prefixEnd_1724093 590192268034818807939031 := by
  unfold tailWord_1724093
  simp only [CollatzResearch.WordTrace]
  refine ⟨62882837742912987487016933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41921891828608658324677955 62882837742912987487016933)
  ·
    refine ⟨11790532076796185153815675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62882837742912987487016933 11790532076796185153815675)
    ·
      refine ⟨17685798115194277730723513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790532076796185153815675 17685798115194277730723513)
      ·
        refine ⟨13264348586395708298042635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17685798115194277730723513 13264348586395708298042635)
        ·
          refine ⟨19896522879593562447063953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13264348586395708298042635 19896522879593562447063953)
          ·
            refine ⟨14922392159695171835297965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19896522879593562447063953 14922392159695171835297965)
            ·
              refine ⟨5595897059885689438236737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14922392159695171835297965 5595897059885689438236737)
              ·
                refine ⟨4196922794914267078677553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595897059885689438236737 4196922794914267078677553)
                ·
                  refine ⟨3147692096185700309008165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196922794914267078677553 3147692096185700309008165)
                  ·
                    refine ⟨590192268034818807939031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147692096185700309008165 590192268034818807939031)
                    ·
                      rfl

theorem cell22_1724093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1724093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724093 prefixEnd_1724093 := by exact prefixLift 1724093
  have htrace : WordTrace (prefixWord ++ tailWord_1724093) baseStart_1724093 baseEnd_1724093 := by
    simpa [prefixWord, tailWord_1724093, baseEnd_1724093] using wordTrace_append hprefix tailTrace_1724093
  have hstable : (prefixWord ++ tailWord_1724093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724093).length < 2 ^ (prefixWord ++ tailWord_1724093).sum := by decide
  have hdescent : baseEnd_1724093 < baseStart_1724093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724168 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1724168 : Nat := 118140960795 + 1724168 * 2 ^ 59
def prefixEnd_1724168 : Nat := 4983230072969 + 3 ^ 40 * 1724168 * 2
def baseEnd_1724168 : Nat := 590217942067543612313801

theorem tailTrace_1724168 : CollatzResearch.WordTrace tailWord_1724168 prefixEnd_1724168 590217942067543612313801 := by
  unfold tailWord_1724168
  simp only [CollatzResearch.WordTrace]
  refine ⟨31442786608820637647998579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41923715478427516863998105 31442786608820637647998579)
  ·
    refine ⟨47164179913230956471997869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31442786608820637647998579 47164179913230956471997869)
    ·
      refine ⟨17686567467461608676999201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47164179913230956471997869 17686567467461608676999201)
      ·
        refine ⟨13264925600596206507749401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17686567467461608676999201 13264925600596206507749401)
        ·
          refine ⟨9948694200447154880812051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13264925600596206507749401 9948694200447154880812051)
          ·
            refine ⟨14923041300670732321218077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9948694200447154880812051 14923041300670732321218077)
            ·
              refine ⟨5596140487751524620456779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14923041300670732321218077 5596140487751524620456779)
              ·
                refine ⟨8394210731627286930685169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596140487751524620456779 8394210731627286930685169)
                ·
                  refine ⟨6295658048720465198013877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8394210731627286930685169 6295658048720465198013877)
                  ·
                    refine ⟨590217942067543612313801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6295658048720465198013877 590217942067543612313801)
                    ·
                      rfl

theorem cell22_1724168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1724168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724168 prefixEnd_1724168 := by exact prefixLift 1724168
  have htrace : WordTrace (prefixWord ++ tailWord_1724168) baseStart_1724168 baseEnd_1724168 := by
    simpa [prefixWord, tailWord_1724168, baseEnd_1724168] using wordTrace_append hprefix tailTrace_1724168
  have hstable : (prefixWord ++ tailWord_1724168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724168).length < 2 ^ (prefixWord ++ tailWord_1724168).sum := by decide
  have hdescent : baseEnd_1724168 < baseStart_1724168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724260 : List Nat := [2, 3, 1, 1, 5, 2, 8]
def baseStart_1724260 : Nat := 118140960795 + 1724260 * 2 ^ 59
def prefixEnd_1724260 : Nat := 4983230072969 + 3 ^ 40 * 1724260 * 2
def baseEnd_1724260 : Nat := 21861090205469853296797

theorem tailTrace_1724260 : CollatzResearch.WordTrace tailWord_1724260 prefixEnd_1724260 21861090205469853296797 := by
  unfold tailWord_1724260
  simp only [CollatzResearch.WordTrace]
  refine ⟨31444464366653987504173117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41925952488871983338897489 31444464366653987504173117)
  ·
    refine ⟨11791674137495245314064919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31444464366653987504173117 11791674137495245314064919)
    ·
      refine ⟨17687511206242867971097379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11791674137495245314064919 17687511206242867971097379)
      ·
        refine ⟨26531266809364301956646069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17687511206242867971097379 26531266809364301956646069)
        ·
          refine ⟨2487306263377903308435569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26531266809364301956646069 2487306263377903308435569)
          ·
            refine ⟨1865479697533427481326677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2487306263377903308435569 1865479697533427481326677)
            ·
              refine ⟨21861090205469853296797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1865479697533427481326677 21861090205469853296797)
              ·
                rfl

theorem cell22_1724260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 8].length) (baseStart_1724260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724260 prefixEnd_1724260 := by exact prefixLift 1724260
  have htrace : WordTrace (prefixWord ++ tailWord_1724260) baseStart_1724260 baseEnd_1724260 := by
    simpa [prefixWord, tailWord_1724260, baseEnd_1724260] using wordTrace_append hprefix tailTrace_1724260
  have hstable : (prefixWord ++ tailWord_1724260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724260).length < 2 ^ (prefixWord ++ tailWord_1724260).sum := by decide
  have hdescent : baseEnd_1724260 < baseStart_1724260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724266 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_1724266 : Nat := 118140960795 + 1724266 * 2 ^ 59
def prefixEnd_1724266 : Nat := 4983230072969 + 3 ^ 40 * 1724266 * 2
def baseEnd_1724266 : Nat := 196750496490101341121167

theorem tailTrace_1724266 : CollatzResearch.WordTrace tailWord_1724266 prefixEnd_1724266 196750496490101341121167 := by
  unfold tailWord_1724266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722286892821559508266163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41926098380857492022043101 15722286892821559508266163)
  ·
    refine ⟨23583430339232339262399245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15722286892821559508266163 23583430339232339262399245)
    ·
      refine ⟨8843786377212127223399717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23583430339232339262399245 8843786377212127223399717)
      ·
        refine ⟨1658209945727273854387447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8843786377212127223399717 1658209945727273854387447)
        ·
          refine ⟨2487314918590910781581171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658209945727273854387447 2487314918590910781581171)
          ·
            refine ⟨3730972377886366172371757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487314918590910781581171 3730972377886366172371757)
            ·
              refine ⟨1399114641707387314639409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3730972377886366172371757 1399114641707387314639409)
              ·
                refine ⟨1049335981280540485979557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399114641707387314639409 1049335981280540485979557)
                ·
                  refine ⟨196750496490101341121167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049335981280540485979557 196750496490101341121167)
                  ·
                    rfl

theorem cell22_1724266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_1724266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724266 prefixEnd_1724266 := by exact prefixLift 1724266
  have htrace : WordTrace (prefixWord ++ tailWord_1724266) baseStart_1724266 baseEnd_1724266 := by
    simpa [prefixWord, tailWord_1724266, baseEnd_1724266] using wordTrace_append hprefix tailTrace_1724266
  have hstable : (prefixWord ++ tailWord_1724266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724266).length < 2 ^ (prefixWord ++ tailWord_1724266).sum := by decide
  have hdescent : baseEnd_1724266 < baseStart_1724266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724273 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1724273 : Nat := 118140960795 + 1724273 * 2 ^ 59
def prefixEnd_1724273 : Nat := 4983230072969 + 3 ^ 40 * 1724273 * 2
def baseEnd_1724273 : Nat := 590253885713358338438479

theorem tailTrace_1724273 : CollatzResearch.WordTrace tailWord_1724273 prefixEnd_1724273 590253885713358338438479 := by
  unfold tailWord_1724273
  simp only [CollatzResearch.WordTrace]
  refine ⟨62889402882260878228569473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41926268588173918819046315 62889402882260878228569473)
  ·
    refine ⟨47167052161695658671427105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62889402882260878228569473 47167052161695658671427105)
    ·
      refine ⟨35375289121271744003570329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47167052161695658671427105 35375289121271744003570329)
      ·
        refine ⟨26531466840953808002677747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35375289121271744003570329 26531466840953808002677747)
        ·
          refine ⟨39797200261430712004016621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26531466840953808002677747 39797200261430712004016621)
          ·
            refine ⟨14923950098036517001506233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39797200261430712004016621 14923950098036517001506233)
            ·
              refine ⟨11192962573527387751129675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14923950098036517001506233 11192962573527387751129675)
              ·
                refine ⟨16789443860291081626694513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192962573527387751129675 16789443860291081626694513)
                ·
                  refine ⟨12592082895218311220020885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16789443860291081626694513 12592082895218311220020885)
                  ·
                    refine ⟨590253885713358338438479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12592082895218311220020885 590253885713358338438479)
                    ·
                      rfl

theorem cell22_1724273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1724273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724273 prefixEnd_1724273 := by exact prefixLift 1724273
  have htrace : WordTrace (prefixWord ++ tailWord_1724273) baseStart_1724273 baseEnd_1724273 := by
    simpa [prefixWord, tailWord_1724273, baseEnd_1724273] using wordTrace_append hprefix tailTrace_1724273
  have hstable : (prefixWord ++ tailWord_1724273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724273).length < 2 ^ (prefixWord ++ tailWord_1724273).sum := by decide
  have hdescent : baseEnd_1724273 < baseStart_1724273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724350 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1724350 : Nat := 118140960795 + 1724350 * 2 ^ 59
def prefixEnd_1724350 : Nat := 4983230072969 + 3 ^ 40 * 1724350 * 2
def baseEnd_1724350 : Nat := 196760081462318601421081

theorem tailTrace_1724350 : CollatzResearch.WordTrace tailWord_1724350 prefixEnd_1724350 196760081462318601421081 := by
  unfold tailWord_1724350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861526412872740047390313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41928140868654613586081669 7861526412872740047390313)
  ·
    refine ⟨5896144809654555035542735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7861526412872740047390313 5896144809654555035542735)
    ·
      refine ⟨8844217214481832553314103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896144809654555035542735 8844217214481832553314103)
      ·
        refine ⟨13266325821722748829971155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844217214481832553314103 13266325821722748829971155)
        ·
          refine ⟨19899488732584123244956733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13266325821722748829971155 19899488732584123244956733)
          ·
            refine ⟨7462308274719046216858775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19899488732584123244956733 7462308274719046216858775)
            ·
              refine ⟨11193462412078569325288163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462308274719046216858775 11193462412078569325288163)
              ·
                refine ⟨16790193618117853987932245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193462412078569325288163 16790193618117853987932245)
                ·
                  refine ⟨196760081462318601421081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16790193618117853987932245 196760081462318601421081)
                  ·
                    rfl

theorem cell22_1724350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1724350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724350 prefixEnd_1724350 := by exact prefixLift 1724350
  have htrace : WordTrace (prefixWord ++ tailWord_1724350) baseStart_1724350 baseEnd_1724350 := by
    simpa [prefixWord, tailWord_1724350, baseEnd_1724350] using wordTrace_append hprefix tailTrace_1724350
  have hstable : (prefixWord ++ tailWord_1724350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724350).length < 2 ^ (prefixWord ++ tailWord_1724350).sum := by decide
  have hdescent : baseEnd_1724350 < baseStart_1724350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724367 : List Nat := [1, 1, 2, 1, 1, 5, 4, 3, 4]
def baseStart_1724367 : Nat := 118140960795 + 1724367 * 2 ^ 59
def prefixEnd_1724367 : Nat := 4983230072969 + 3 ^ 40 * 1724367 * 2
def baseEnd_1724367 : Nat := 196762021278124475529397

theorem tailTrace_1724367 : CollatzResearch.WordTrace tailWord_1724367 prefixEnd_1724367 196762021278124475529397 := by
  unfold tailWord_1724367
  simp only [CollatzResearch.WordTrace]
  refine ⟨62892831343920332282491355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41928554229280221521660903 62892831343920332282491355)
  ·
    refine ⟨94339247015880498423737033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62892831343920332282491355 94339247015880498423737033)
    ·
      refine ⟨70754435261910373817802775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94339247015880498423737033 70754435261910373817802775)
      ·
        refine ⟨106131652892865560726704163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70754435261910373817802775 106131652892865560726704163)
        ·
          refine ⟨159197479339298341090056245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106131652892865560726704163 159197479339298341090056245)
          ·
            refine ⟨14924763688059219477192773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159197479339298341090056245 14924763688059219477192773)
            ·
              refine ⟨2798393191511103651973645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14924763688059219477192773 2798393191511103651973645)
              ·
                refine ⟨1049397446816663869490117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2798393191511103651973645 1049397446816663869490117)
                ·
                  refine ⟨196762021278124475529397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049397446816663869490117 196762021278124475529397)
                  ·
                    rfl

theorem cell22_1724367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 4].length) (baseStart_1724367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724367 prefixEnd_1724367 := by exact prefixLift 1724367
  have htrace : WordTrace (prefixWord ++ tailWord_1724367) baseStart_1724367 baseEnd_1724367 := by
    simpa [prefixWord, tailWord_1724367, baseEnd_1724367] using wordTrace_append hprefix tailTrace_1724367
  have hstable : (prefixWord ++ tailWord_1724367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724367).length < 2 ^ (prefixWord ++ tailWord_1724367).sum := by decide
  have hdescent : baseEnd_1724367 < baseStart_1724367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724399 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 2, 3]
def baseStart_1724399 : Nat := 118140960795 + 1724399 * 2 ^ 59
def prefixEnd_1724399 : Nat := 4983230072969 + 3 ^ 40 * 1724399 * 2
def baseEnd_1724399 : Nat := 590297018088336009788093

theorem tailTrace_1724399 : CollatzResearch.WordTrace tailWord_1724399 prefixEnd_1724399 590297018088336009788093 := by
  unfold tailWord_1724399
  simp only [CollatzResearch.WordTrace]
  refine ⟨62893998479804401747656251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41929332319869601165104167 62893998479804401747656251)
  ·
    refine ⟨94340997719706602621484377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62893998479804401747656251 94340997719706602621484377)
    ·
      refine ⟨70755748289779951966113283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94340997719706602621484377 70755748289779951966113283)
      ·
        refine ⟨106133622434669927949169925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70755748289779951966113283 106133622434669927949169925)
        ·
          refine ⟨19900054206500611490469361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106133622434669927949169925 19900054206500611490469361)
          ·
            refine ⟨14925040654875458617852021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19900054206500611490469361 14925040654875458617852021)
            ·
              refine ⟨1399222561394574245423627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14925040654875458617852021 1399222561394574245423627)
              ·
                refine ⟨2098833842091861368135441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399222561394574245423627 2098833842091861368135441)
                ·
                  refine ⟨1574125381568896026101581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2098833842091861368135441 1574125381568896026101581)
                  ·
                    refine ⟨590297018088336009788093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574125381568896026101581 590297018088336009788093)
                    ·
                      rfl

theorem cell22_1724399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_1724399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724399 prefixEnd_1724399 := by exact prefixLift 1724399
  have htrace : WordTrace (prefixWord ++ tailWord_1724399) baseStart_1724399 baseEnd_1724399 := by
    simpa [prefixWord, tailWord_1724399, baseEnd_1724399] using wordTrace_append hprefix tailTrace_1724399
  have hstable : (prefixWord ++ tailWord_1724399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724399).length < 2 ^ (prefixWord ++ tailWord_1724399).sum := by decide
  have hdescent : baseEnd_1724399 < baseStart_1724399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724440 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_1724440 : Nat := 118140960795 + 1724440 * 2 ^ 59
def prefixEnd_1724440 : Nat := 4983230072969 + 3 ^ 40 * 1724440 * 2
def baseEnd_1724440 : Nat := 196770351075408523170989

theorem tailTrace_1724440 : CollatzResearch.WordTrace tailWord_1724440 prefixEnd_1724440 196770351075408523170989 := by
  unfold tailWord_1724440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447746936327932874949387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41930329248437243833265849 31447746936327932874949387)
  ·
    refine ⟨47171620404491899312424081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31447746936327932874949387 47171620404491899312424081)
    ·
      refine ⟨35378715303368924484318061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47171620404491899312424081 35378715303368924484318061)
      ·
        refine ⟨13267018238763346681619273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35378715303368924484318061 13267018238763346681619273)
        ·
          refine ⟨9950263679072510011214455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13267018238763346681619273 9950263679072510011214455)
          ·
            refine ⟨14925395518608765016821683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9950263679072510011214455 14925395518608765016821683)
            ·
              refine ⟨22388093277913147525232525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14925395518608765016821683 22388093277913147525232525)
              ·
                refine ⟨8395534979217430321962197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22388093277913147525232525 8395534979217430321962197)
                ·
                  refine ⟨196770351075408523170989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8395534979217430321962197 196770351075408523170989)
                  ·
                    rfl

theorem cell22_1724440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_1724440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724440 prefixEnd_1724440 := by exact prefixLift 1724440
  have htrace : WordTrace (prefixWord ++ tailWord_1724440) baseStart_1724440 baseEnd_1724440 := by
    simpa [prefixWord, tailWord_1724440, baseEnd_1724440] using wordTrace_append hprefix tailTrace_1724440
  have hstable : (prefixWord ++ tailWord_1724440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724440).length < 2 ^ (prefixWord ++ tailWord_1724440).sum := by decide
  have hdescent : baseEnd_1724440 < baseStart_1724440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724444 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1724444 : Nat := 118140960795 + 1724444 * 2 ^ 59
def prefixEnd_1724444 : Nat := 4983230072969 + 3 ^ 40 * 1724444 * 2
def baseEnd_1724444 : Nat := 590312422507970892412955

theorem tailTrace_1724444 : CollatzResearch.WordTrace tailWord_1724444 prefixEnd_1724444 590312422507970892412955 := by
  unfold tailWord_1724444
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447819882320687216522193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41930426509760916288696257 31447819882320687216522193)
  ·
    refine ⟨23585864911740515412391645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31447819882320687216522193 23585864911740515412391645)
    ·
      refine ⟨8844699341902693279646867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23585864911740515412391645 8844699341902693279646867)
      ·
        refine ⟨13267049012854039919470301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844699341902693279646867 13267049012854039919470301)
        ·
          refine ⟨4975143379820264969801363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13267049012854039919470301 4975143379820264969801363)
          ·
            refine ⟨7462715069730397454702045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975143379820264969801363 7462715069730397454702045)
            ·
              refine ⟨2798518151148899045513267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7462715069730397454702045 2798518151148899045513267)
              ·
                refine ⟨4197777226723348568269901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798518151148899045513267 4197777226723348568269901)
                ·
                  refine ⟨1574166460021255713101213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4197777226723348568269901 1574166460021255713101213)
                  ·
                    refine ⟨590312422507970892412955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574166460021255713101213 590312422507970892412955)
                    ·
                      rfl

theorem cell22_1724444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1724444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724444 prefixEnd_1724444 := by exact prefixLift 1724444
  have htrace : WordTrace (prefixWord ++ tailWord_1724444) baseStart_1724444 baseEnd_1724444 := by
    simpa [prefixWord, tailWord_1724444, baseEnd_1724444] using wordTrace_append hprefix tailTrace_1724444
  have hstable : (prefixWord ++ tailWord_1724444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724444).length < 2 ^ (prefixWord ++ tailWord_1724444).sum := by decide
  have hdescent : baseEnd_1724444 < baseStart_1724444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724517 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_1724517 : Nat := 118140960795 + 1724517 * 2 ^ 59
def prefixEnd_1724517 : Nat := 4983230072969 + 3 ^ 40 * 1724517 * 2
def baseEnd_1724517 : Nat := 590337411899823035337731

theorem tailTrace_1724517 : CollatzResearch.WordTrace tailWord_1724517 prefixEnd_1724517 590337411899823035337731 := by
  unfold tailWord_1724517
  simp only [CollatzResearch.WordTrace]
  refine ⟨62898302293376907900451805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41932201528917938600301203 62898302293376907900451805)
  ·
    refine ⟨23586863360016340462669427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62898302293376907900451805 23586863360016340462669427)
    ·
      refine ⟨35380295040024510694004141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23586863360016340462669427 35380295040024510694004141)
      ·
        refine ⟨13267610640009191510251553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35380295040024510694004141 13267610640009191510251553)
        ·
          refine ⟨9950707980006893632688665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13267610640009191510251553 9950707980006893632688665)
          ·
            refine ⟨7463030985005170224516499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9950707980006893632688665 7463030985005170224516499)
            ·
              refine ⟨11194546477507755336774749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7463030985005170224516499 11194546477507755336774749)
              ·
                refine ⟨4197954929065408251290531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11194546477507755336774749 4197954929065408251290531)
                ·
                  refine ⟨6296932393598112376935797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197954929065408251290531 6296932393598112376935797)
                  ·
                    refine ⟨590337411899823035337731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6296932393598112376935797 590337411899823035337731)
                    ·
                      rfl

theorem cell22_1724517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_1724517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724517 prefixEnd_1724517 := by exact prefixLift 1724517
  have htrace : WordTrace (prefixWord ++ tailWord_1724517) baseStart_1724517 baseEnd_1724517 := by
    simpa [prefixWord, tailWord_1724517, baseEnd_1724517] using wordTrace_append hprefix tailTrace_1724517
  have hstable : (prefixWord ++ tailWord_1724517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724517).length < 2 ^ (prefixWord ++ tailWord_1724517).sum := by decide
  have hdescent : baseEnd_1724517 < baseStart_1724517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724534 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1724534 : Nat := 118140960795 + 1724534 * 2 ^ 59
def prefixEnd_1724534 : Nat := 4983230072969 + 3 ^ 40 * 1724534 * 2
def baseEnd_1724534 : Nat := 590343231347240657662679

theorem tailTrace_1724534 : CollatzResearch.WordTrace tailWord_1724534 prefixEnd_1724534 590343231347240657662679 := by
  unfold tailWord_1724534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931182645894707487738791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41932614889543546535880437 3931182645894707487738791)
  ·
    refine ⟨5896773968842061231608187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3931182645894707487738791 5896773968842061231608187)
    ·
      refine ⟨8845160953263091847412281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896773968842061231608187 8845160953263091847412281)
      ·
        refine ⟨6633870714947318885559211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8845160953263091847412281 6633870714947318885559211)
        ·
          refine ⟨9950806072420978328338817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633870714947318885559211 9950806072420978328338817)
          ·
            refine ⟨7463104554315733746254113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9950806072420978328338817 7463104554315733746254113)
            ·
              refine ⟨5597328415736800309690585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7463104554315733746254113 5597328415736800309690585)
              ·
                refine ⟨4197996311802600232267939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597328415736800309690585 4197996311802600232267939)
                ·
                  refine ⟨6296994467703900348401909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197996311802600232267939 6296994467703900348401909)
                  ·
                    refine ⟨590343231347240657662679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6296994467703900348401909 590343231347240657662679)
                    ·
                      rfl

theorem cell22_1724534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1724534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724534 prefixEnd_1724534 := by exact prefixLift 1724534
  have htrace : WordTrace (prefixWord ++ tailWord_1724534) baseStart_1724534 baseEnd_1724534 := by
    simpa [prefixWord, tailWord_1724534, baseEnd_1724534] using wordTrace_append hprefix tailTrace_1724534
  have hstable : (prefixWord ++ tailWord_1724534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724534).length < 2 ^ (prefixWord ++ tailWord_1724534).sum := by decide
  have hdescent : baseEnd_1724534 < baseStart_1724534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724568 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_1724568 : Nat := 118140960795 + 1724568 * 2 ^ 59
def prefixEnd_1724568 : Nat := 4983230072969 + 3 ^ 40 * 1724568 * 2
def baseEnd_1724568 : Nat := 590354870242075902312575

theorem tailTrace_1724568 : CollatzResearch.WordTrace tailWord_1724568 prefixEnd_1724568 590354870242075902312575 := by
  unfold tailWord_1724568
  simp only [CollatzResearch.WordTrace]
  refine ⟨31450081208096071805279179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41933441610794762407038905 31450081208096071805279179)
  ·
    refine ⟨47175121812144107707918769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31450081208096071805279179 47175121812144107707918769)
    ·
      refine ⟨35381341359108080780939077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47175121812144107707918769 35381341359108080780939077)
      ·
        refine ⟨6634001504832765146426077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35381341359108080780939077 6634001504832765146426077)
        ·
          refine ⟨2487750564312286929909779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6634001504832765146426077 2487750564312286929909779)
          ·
            refine ⟨3731625846468430394864669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487750564312286929909779 3731625846468430394864669)
            ·
              refine ⟨1399359692425661398074251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3731625846468430394864669 1399359692425661398074251)
              ·
                refine ⟨2099039538638492097111377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399359692425661398074251 2099039538638492097111377)
                ·
                  refine ⟨1574279653978869072833533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099039538638492097111377 1574279653978869072833533)
                  ·
                    refine ⟨590354870242075902312575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574279653978869072833533 590354870242075902312575)
                    ·
                      rfl

theorem cell22_1724568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_1724568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724568 prefixEnd_1724568 := by exact prefixLift 1724568
  have htrace : WordTrace (prefixWord ++ tailWord_1724568) baseStart_1724568 baseEnd_1724568 := by
    simpa [prefixWord, tailWord_1724568, baseEnd_1724568] using wordTrace_append hprefix tailTrace_1724568
  have hstable : (prefixWord ++ tailWord_1724568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724568).length < 2 ^ (prefixWord ++ tailWord_1724568).sum := by decide
  have hdescent : baseEnd_1724568 < baseStart_1724568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724626 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1724626 : Nat := 118140960795 + 1724626 * 2 ^ 59
def prefixEnd_1724626 : Nat := 4983230072969 + 3 ^ 40 * 1724626 * 2
def baseEnd_1724626 : Nat := 196791574942461028120799

theorem tailTrace_1724626 : CollatzResearch.WordTrace tailWord_1724626 prefixEnd_1724626 196791574942461028120799 := by
  unfold tailWord_1724626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725569462495504879042433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41934851899988013010779821 15725569462495504879042433)
  ·
    refine ⟨11794177096871628659281825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15725569462495504879042433 11794177096871628659281825)
    ·
      refine ⟨8845632822653721494461369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11794177096871628659281825 8845632822653721494461369)
      ·
        refine ⟨6634224616990291120846027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8845632822653721494461369 6634224616990291120846027)
        ·
          refine ⟨9951336925485436681269041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634224616990291120846027 9951336925485436681269041)
          ·
            refine ⟨7463502694114077510951781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9951336925485436681269041 7463502694114077510951781)
            ·
              refine ⟨1399406755146389533303459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7463502694114077510951781 1399406755146389533303459)
              ·
                refine ⟨2099110132719584299955189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399406755146389533303459 2099110132719584299955189)
                ·
                  refine ⟨196791574942461028120799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099110132719584299955189 196791574942461028120799)
                  ·
                    rfl

theorem cell22_1724626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1724626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724626 prefixEnd_1724626 := by exact prefixLift 1724626
  have htrace : WordTrace (prefixWord ++ tailWord_1724626) baseStart_1724626 baseEnd_1724626 := by
    simpa [prefixWord, tailWord_1724626, baseEnd_1724626] using wordTrace_append hprefix tailTrace_1724626
  have hstable : (prefixWord ++ tailWord_1724626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724626).length < 2 ^ (prefixWord ++ tailWord_1724626).sum := by decide
  have hdescent : baseEnd_1724626 < baseStart_1724626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724669 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_1724669 : Nat := 118140960795 + 1724669 * 2 ^ 59
def prefixEnd_1724669 : Nat := 4983230072969 + 3 ^ 40 * 1724669 * 2
def baseEnd_1724669 : Nat := 590389444606145305537265

theorem tailTrace_1724669 : CollatzResearch.WordTrace tailWord_1724669 prefixEnd_1724669 590389444606145305537265 := by
  unfold tailWord_1724669
  simp only [CollatzResearch.WordTrace]
  refine ⟨62903846188826237859985061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41935897459217491906656707 62903846188826237859985061)
  ·
    refine ⟨11794471160404919598747199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62903846188826237859985061 11794471160404919598747199)
    ·
      refine ⟨17691706740607379398120799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794471160404919598747199 17691706740607379398120799)
      ·
        refine ⟨26537560110911069097181199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691706740607379398120799 26537560110911069097181199)
        ·
          refine ⟨39806340166366603645771799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26537560110911069097181199 39806340166366603645771799)
          ·
            refine ⟨59709510249549905468657699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39806340166366603645771799 59709510249549905468657699)
            ·
              refine ⟨89564265374324858202986549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59709510249549905468657699 89564265374324858202986549)
              ·
                refine ⟨8396649878842955456529989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89564265374324858202986549 8396649878842955456529989)
                ·
                  refine ⟨1574371852283054148099373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8396649878842955456529989 1574371852283054148099373)
                  ·
                    refine ⟨590389444606145305537265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574371852283054148099373 590389444606145305537265)
                    ·
                      rfl

theorem cell22_1724669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_1724669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724669 prefixEnd_1724669 := by exact prefixLift 1724669
  have htrace : WordTrace (prefixWord ++ tailWord_1724669) baseStart_1724669 baseEnd_1724669 := by
    simpa [prefixWord, tailWord_1724669, baseEnd_1724669] using wordTrace_append hprefix tailTrace_1724669
  have hstable : (prefixWord ++ tailWord_1724669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724669).length < 2 ^ (prefixWord ++ tailWord_1724669).sum := by decide
  have hdescent : baseEnd_1724669 < baseStart_1724669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724686 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1724686 : Nat := 118140960795 + 1724686 * 2 ^ 59
def prefixEnd_1724686 : Nat := 4983230072969 + 3 ^ 40 * 1724686 * 2
def baseEnd_1724686 : Nat := 590395264053562927862213

theorem tailTrace_1724686 : CollatzResearch.WordTrace tailWord_1724686 prefixEnd_1724686 590395264053562927862213 := by
  unfold tailWord_1724686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863058278720581220419239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41936310819843099842235941 7863058278720581220419239)
  ·
    refine ⟨11794587418080871830628859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863058278720581220419239 11794587418080871830628859)
    ·
      refine ⟨17691881127121307745943289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794587418080871830628859 17691881127121307745943289)
      ·
        refine ⟨13268910845340980809457467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17691881127121307745943289 13268910845340980809457467)
        ·
          refine ⟨19903366268011471214186201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13268910845340980809457467 19903366268011471214186201)
          ·
            refine ⟨14927524701008603410639651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903366268011471214186201 14927524701008603410639651)
            ·
              refine ⟨22391287051512905115959477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14927524701008603410639651 22391287051512905115959477)
              ·
                refine ⟨2099183161079334854621201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22391287051512905115959477 2099183161079334854621201)
                ·
                  refine ⟨1574387370809501140965901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099183161079334854621201 1574387370809501140965901)
                  ·
                    refine ⟨590395264053562927862213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574387370809501140965901 590395264053562927862213)
                    ·
                      rfl

theorem cell22_1724686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1724686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724686 prefixEnd_1724686 := by exact prefixLift 1724686
  have htrace : WordTrace (prefixWord ++ tailWord_1724686) baseStart_1724686 baseEnd_1724686 := by
    simpa [prefixWord, tailWord_1724686, baseEnd_1724686] using wordTrace_append hprefix tailTrace_1724686
  have hstable : (prefixWord ++ tailWord_1724686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724686).length < 2 ^ (prefixWord ++ tailWord_1724686).sum := by decide
  have hdescent : baseEnd_1724686 < baseStart_1724686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724701 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1724701 : Nat := 118140960795 + 1724701 * 2 ^ 59
def prefixEnd_1724701 : Nat := 4983230072969 + 3 ^ 40 * 1724701 * 2
def baseEnd_1724701 : Nat := 590400398860107888737167

theorem tailTrace_1724701 : CollatzResearch.WordTrace tailWord_1724701 prefixEnd_1724701 590400398860107888737167 := by
  unfold tailWord_1724701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62905013324710307325149957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41936675549806871550099971 62905013324710307325149957)
  ·
    refine ⟨11794689998383182623465617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62905013324710307325149957 11794689998383182623465617)
    ·
      refine ⟨8846017498787386967599213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11794689998383182623465617 8846017498787386967599213)
      ·
        refine ⟨3317256562045270112849705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8846017498787386967599213 3317256562045270112849705)
        ·
          refine ⟨2487942421533952584637279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3317256562045270112849705 2487942421533952584637279)
          ·
            refine ⟨3731913632300928876955919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487942421533952584637279 3731913632300928876955919)
            ·
              refine ⟨5597870448451393315433879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731913632300928876955919 5597870448451393315433879)
              ·
                refine ⟨8396805672677089973150819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597870448451393315433879 8396805672677089973150819)
                ·
                  refine ⟨12595208509015634959726229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396805672677089973150819 12595208509015634959726229)
                  ·
                    refine ⟨590400398860107888737167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12595208509015634959726229 590400398860107888737167)
                    ·
                      rfl

theorem cell22_1724701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1724701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724701 prefixEnd_1724701 := by exact prefixLift 1724701
  have htrace : WordTrace (prefixWord ++ tailWord_1724701) baseStart_1724701 baseEnd_1724701 := by
    simpa [prefixWord, tailWord_1724701, baseEnd_1724701] using wordTrace_append hprefix tailTrace_1724701
  have hstable : (prefixWord ++ tailWord_1724701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724701).length < 2 ^ (prefixWord ++ tailWord_1724701).sum := by decide
  have hdescent : baseEnd_1724701 < baseStart_1724701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724744 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_1724744 : Nat := 118140960795 + 1724744 * 2 ^ 59
def prefixEnd_1724744 : Nat := 4983230072969 + 3 ^ 40 * 1724744 * 2
def baseEnd_1724744 : Nat := 196805039546290036637345

theorem tailTrace_1724744 : CollatzResearch.WordTrace tailWord_1724744 prefixEnd_1724744 196805039546290036637345 := by
  unfold tailWord_1724744
  simp only [CollatzResearch.WordTrace]
  refine ⟨31453290831777262834482643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41937721109036350445976857 31453290831777262834482643)
  ·
    refine ⟨47179936247665894251723965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31453290831777262834482643 47179936247665894251723965)
    ·
      refine ⟨17692476092874710344396487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47179936247665894251723965 17692476092874710344396487)
      ·
        refine ⟨26538714139312065516594731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17692476092874710344396487 26538714139312065516594731)
        ·
          refine ⟨39808071208968098274892097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26538714139312065516594731 39808071208968098274892097)
          ·
            refine ⟨29856053406726073706169073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39808071208968098274892097 29856053406726073706169073)
            ·
              refine ⟨22392040055044555279626805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29856053406726073706169073 22392040055044555279626805)
              ·
                refine ⟨2099253755160427057465013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22392040055044555279626805 2099253755160427057465013)
                ·
                  refine ⟨196805039546290036637345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099253755160427057465013 196805039546290036637345)
                  ·
                    rfl

theorem cell22_1724744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_1724744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724744 prefixEnd_1724744 := by exact prefixLift 1724744
  have htrace : WordTrace (prefixWord ++ tailWord_1724744) baseStart_1724744 baseEnd_1724744 := by
    simpa [prefixWord, tailWord_1724744, baseEnd_1724744] using wordTrace_append hprefix tailTrace_1724744
  have hstable : (prefixWord ++ tailWord_1724744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724744).length < 2 ^ (prefixWord ++ tailWord_1724744).sum := by decide
  have hdescent : baseEnd_1724744 < baseStart_1724744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724836 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1724836 : Nat := 118140960795 + 1724836 * 2 ^ 59
def prefixEnd_1724836 : Nat := 4983230072969 + 3 ^ 40 * 1724836 * 2
def baseEnd_1724836 : Nat := 590446612119012536611753

theorem tailTrace_1724836 : CollatzResearch.WordTrace tailWord_1724836 prefixEnd_1724836 590446612119012536611753 := by
  unfold tailWord_1724836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31454968589610612690657181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41939958119480816920876241 31454968589610612690657181)
  ·
    refine ⟨11795613221103979758996443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31454968589610612690657181 11795613221103979758996443)
    ·
      refine ⟨17693419831655969638494665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795613221103979758996443 17693419831655969638494665)
      ·
        refine ⟨13270064873741977228870999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17693419831655969638494665 13270064873741977228870999)
        ·
          refine ⟨19905097310612965843306499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13270064873741977228870999 19905097310612965843306499)
          ·
            refine ⟨29857645965919448764959749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19905097310612965843306499 29857645965919448764959749)
            ·
              refine ⟨5598308618609896643429953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29857645965919448764959749 5598308618609896643429953)
              ·
                refine ⟨4198731463957422482572465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598308618609896643429953 4198731463957422482572465)
                ·
                  refine ⟨3149048597968066861929349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198731463957422482572465 3149048597968066861929349)
                  ·
                    refine ⟨590446612119012536611753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149048597968066861929349 590446612119012536611753)
                    ·
                      rfl

theorem cell22_1724836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1724836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724836 prefixEnd_1724836 := by exact prefixLift 1724836
  have htrace : WordTrace (prefixWord ++ tailWord_1724836) baseStart_1724836 baseEnd_1724836 := by
    simpa [prefixWord, tailWord_1724836, baseEnd_1724836] using wordTrace_append hprefix tailTrace_1724836
  have hstable : (prefixWord ++ tailWord_1724836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724836).length < 2 ^ (prefixWord ++ tailWord_1724836).sum := by decide
  have hdescent : baseEnd_1724836 < baseStart_1724836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724840 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_1724840 : Nat := 118140960795 + 1724840 * 2 ^ 59
def prefixEnd_1724840 : Nat := 4983230072969 + 3 ^ 40 * 1724840 * 2
def baseEnd_1724840 : Nat := 196815993800252619837247

theorem tailTrace_1724840 : CollatzResearch.WordTrace tailWord_1724840 prefixEnd_1724840 196815993800252619837247 := by
  unfold tailWord_1724840
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455041535603367032229987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41940055380804489376306649 31455041535603367032229987)
  ·
    refine ⟨47182562303405050548344981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31455041535603367032229987 47182562303405050548344981)
    ·
      refine ⟨2211682607972111744453671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47182562303405050548344981 2211682607972111744453671)
      ·
        refine ⟨3317523911958167616680507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211682607972111744453671 3317523911958167616680507)
        ·
          refine ⟨4976285867937251425020761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317523911958167616680507 4976285867937251425020761)
          ·
            refine ⟨3732214400952938568765571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976285867937251425020761 3732214400952938568765571)
            ·
              refine ⟨5598321601429407853148357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3732214400952938568765571 5598321601429407853148357)
              ·
                refine ⟨1049685300268013972465317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5598321601429407853148357 1049685300268013972465317)
                ·
                  refine ⟨196815993800252619837247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049685300268013972465317 196815993800252619837247)
                  ·
                    rfl

theorem cell22_1724840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_1724840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724840 prefixEnd_1724840 := by exact prefixLift 1724840
  have htrace : WordTrace (prefixWord ++ tailWord_1724840) baseStart_1724840 baseEnd_1724840 := by
    simpa [prefixWord, tailWord_1724840, baseEnd_1724840] using wordTrace_append hprefix tailTrace_1724840
  have hstable : (prefixWord ++ tailWord_1724840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724840).length < 2 ^ (prefixWord ++ tailWord_1724840).sum := by decide
  have hdescent : baseEnd_1724840 < baseStart_1724840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724864 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_1724864 : Nat := 118140960795 + 1724864 * 2 ^ 59
def prefixEnd_1724864 : Nat := 4983230072969 + 3 ^ 40 * 1724864 * 2
def baseEnd_1724864 : Nat := 590456197091229796911667

theorem tailTrace_1724864 : CollatzResearch.WordTrace tailWord_1724864 prefixEnd_1724864 590456197091229796911667 := by
  unfold tailWord_1724864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455479211559893081666823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41940638948746524108889097 31455479211559893081666823)
  ·
    refine ⟨47183218817339839622500235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31455479211559893081666823 47183218817339839622500235)
    ·
      refine ⟨70774828226009759433750353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47183218817339839622500235 70774828226009759433750353)
      ·
        refine ⟨53081121169507319575312765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70774828226009759433750353 53081121169507319575312765)
        ·
          refine ⟨19905420438565244840742287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53081121169507319575312765 19905420438565244840742287)
          ·
            refine ⟨29858130657847867261113431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19905420438565244840742287 29858130657847867261113431)
            ·
              refine ⟨44787195986771800891670147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29858130657847867261113431 44787195986771800891670147)
              ·
                refine ⟨67180793980157701337505221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44787195986771800891670147 67180793980157701337505221)
                ·
                  refine ⟨12596398871279569000782229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67180793980157701337505221 12596398871279569000782229)
                  ·
                    refine ⟨590456197091229796911667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12596398871279569000782229 590456197091229796911667)
                    ·
                      rfl

theorem cell22_1724864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_1724864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724864 prefixEnd_1724864 := by exact prefixLift 1724864
  have htrace : WordTrace (prefixWord ++ tailWord_1724864) baseStart_1724864 baseEnd_1724864 := by
    simpa [prefixWord, tailWord_1724864, baseEnd_1724864] using wordTrace_append hprefix tailTrace_1724864
  have hstable : (prefixWord ++ tailWord_1724864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724864).length < 2 ^ (prefixWord ++ tailWord_1724864).sum := by decide
  have hdescent : baseEnd_1724864 < baseStart_1724864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724879 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 7]
def baseStart_1724879 : Nat := 118140960795 + 1724879 * 2 ^ 59
def prefixEnd_1724879 : Nat := 4983230072969 + 3 ^ 40 * 1724879 * 2
def baseEnd_1724879 : Nat := 196820443965924919262207

theorem tailTrace_1724879 : CollatzResearch.WordTrace tailWord_1724879 prefixEnd_1724879 196820443965924919262207 := by
  unfold tailWord_1724879
  simp only [CollatzResearch.WordTrace]
  refine ⟨62911505518065443725129691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41941003678710295816753127 62911505518065443725129691)
  ·
    refine ⟨94367258277098165587694537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62911505518065443725129691 94367258277098165587694537)
    ·
      refine ⟨70775443707823624190770903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94367258277098165587694537 70775443707823624190770903)
      ·
        refine ⟨106163165561735436286156355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70775443707823624190770903 106163165561735436286156355)
        ·
          refine ⟨159244748342603154429234533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106163165561735436286156355 159244748342603154429234533)
          ·
            refine ⟨29858390314238091455481475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159244748342603154429234533 29858390314238091455481475)
            ·
              refine ⟨44787585471357137183222213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29858390314238091455481475 44787585471357137183222213)
              ·
                refine ⟨8397672275879463221854165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44787585471357137183222213 8397672275879463221854165)
                ·
                  refine ⟨196820443965924919262207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8397672275879463221854165 196820443965924919262207)
                  ·
                    rfl

theorem cell22_1724879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_1724879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724879 prefixEnd_1724879 := by exact prefixLift 1724879
  have htrace : WordTrace (prefixWord ++ tailWord_1724879) baseStart_1724879 baseEnd_1724879 := by
    simpa [prefixWord, tailWord_1724879, baseEnd_1724879] using wordTrace_append hprefix tailTrace_1724879
  have hstable : (prefixWord ++ tailWord_1724879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724879).length < 2 ^ (prefixWord ++ tailWord_1724879).sum := by decide
  have hdescent : baseEnd_1724879 < baseStart_1724879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724913 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 5]
def baseStart_1724913 : Nat := 118140960795 + 1724913 * 2 ^ 59
def prefixEnd_1724913 : Nat := 4983230072969 + 3 ^ 40 * 1724913 * 2
def baseEnd_1724913 : Nat := 196824323597536667478839

theorem tailTrace_1724913 : CollatzResearch.WordTrace tailWord_1724913 prefixEnd_1724913 196824323597536667478839 := by
  unfold tailWord_1724913
  simp only [CollatzResearch.WordTrace]
  refine ⟨62912745599942267531867393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41941830399961511687911595 62912745599942267531867393)
  ·
    refine ⟨47184559199956700648900545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62912745599942267531867393 47184559199956700648900545)
    ·
      refine ⟨35388419399967525486675409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47184559199956700648900545 35388419399967525486675409)
      ·
        refine ⟨26541314549975644115006557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35388419399967525486675409 26541314549975644115006557)
        ·
          refine ⟨9952992956240866543127459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26541314549975644115006557 9952992956240866543127459)
          ·
            refine ⟨14929489434361299814691189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952992956240866543127459 14929489434361299814691189)
            ·
              refine ⟨1399639634471371857627299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14929489434361299814691189 1399639634471371857627299)
              ·
                refine ⟨2099459451707057786440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399639634471371857627299 2099459451707057786440949)
                ·
                  refine ⟨196824323597536667478839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099459451707057786440949 196824323597536667478839)
                  ·
                    rfl

theorem cell22_1724913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_1724913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724913 prefixEnd_1724913 := by exact prefixLift 1724913
  have htrace : WordTrace (prefixWord ++ tailWord_1724913) baseStart_1724913 baseEnd_1724913 := by
    simpa [prefixWord, tailWord_1724913, baseEnd_1724913] using wordTrace_append hprefix tailTrace_1724913
  have hstable : (prefixWord ++ tailWord_1724913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724913).length < 2 ^ (prefixWord ++ tailWord_1724913).sum := by decide
  have hdescent : baseEnd_1724913 < baseStart_1724913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724964 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_1724964 : Nat := 118140960795 + 1724964 * 2 ^ 59
def prefixEnd_1724964 : Nat := 4983230072969 + 3 ^ 40 * 1724964 * 2
def baseEnd_1724964 : Nat := 196830143044954289803787

theorem tailTrace_1724964 : CollatzResearch.WordTrace tailWord_1724964 prefixEnd_1724964 196830143044954289803787 := by
  unfold tailWord_1724964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457302861378751620986973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41943070481838335494649297 31457302861378751620986973)
  ·
    refine ⟨11796488573017031857870115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31457302861378751620986973 11796488573017031857870115)
    ·
      refine ⟨17694732859525547786805173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11796488573017031857870115 17694732859525547786805173)
      ·
        refine ⟨1658881205580520105012985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17694732859525547786805173 1658881205580520105012985)
        ·
          refine ⟨1244160904185390078759739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658881205580520105012985 1244160904185390078759739)
          ·
            refine ⟨1866241356278085118139609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244160904185390078759739 1866241356278085118139609)
            ·
              refine ⟨1399681017208563838604707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866241356278085118139609 1399681017208563838604707)
              ·
                refine ⟨2099521525812845757907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399681017208563838604707 2099521525812845757907061)
                ·
                  refine ⟨196830143044954289803787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099521525812845757907061 196830143044954289803787)
                  ·
                    rfl

theorem cell22_1724964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_1724964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724964 prefixEnd_1724964 := by exact prefixLift 1724964
  have htrace : WordTrace (prefixWord ++ tailWord_1724964) baseStart_1724964 baseEnd_1724964 := by
    simpa [prefixWord, tailWord_1724964, baseEnd_1724964] using wordTrace_append hprefix tailTrace_1724964
  have hstable : (prefixWord ++ tailWord_1724964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724964).length < 2 ^ (prefixWord ++ tailWord_1724964).sum := by decide
  have hdescent : baseEnd_1724964 < baseStart_1724964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724986 : List Nat := [3, 1, 1, 1, 3, 3, 2, 8]
def baseStart_1724986 : Nat := 118140960795 + 1724986 * 2 ^ 59
def prefixEnd_1724986 : Nat := 4983230072969 + 3 ^ 40 * 1724986 * 2
def baseEnd_1724986 : Nat := 65610884464940238373477

theorem tailTrace_1724986 : CollatzResearch.WordTrace tailWord_1724986 prefixEnd_1724986 65610884464940238373477 := by
  unfold tailWord_1724986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728852032169450249818703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41943605419118533999516541 15728852032169450249818703)
  ·
    refine ⟨23593278048254175374728055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15728852032169450249818703 23593278048254175374728055)
    ·
      refine ⟨35389917072381263062092083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23593278048254175374728055 35389917072381263062092083)
      ·
        refine ⟨53084875608571894593138125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35389917072381263062092083 53084875608571894593138125)
        ·
          refine ⟨19906828353214460472426797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53084875608571894593138125 19906828353214460472426797)
          ·
            refine ⟨7465060632455422677160049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19906828353214460472426797 7465060632455422677160049)
            ·
              refine ⟨5598795474341567007870037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465060632455422677160049 5598795474341567007870037)
              ·
                refine ⟨65610884464940238373477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5598795474341567007870037 65610884464940238373477)
                ·
                  rfl

theorem cell22_1724986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_1724986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724986 prefixEnd_1724986 := by exact prefixLift 1724986
  have htrace : WordTrace (prefixWord ++ tailWord_1724986) baseStart_1724986 baseEnd_1724986 := by
    simpa [prefixWord, tailWord_1724986, baseEnd_1724986] using wordTrace_append hprefix tailTrace_1724986
  have hstable : (prefixWord ++ tailWord_1724986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724986).length < 2 ^ (prefixWord ++ tailWord_1724986).sum := by decide
  have hdescent : baseEnd_1724986 < baseStart_1724986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724988 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1724988 : Nat := 118140960795 + 1724988 * 2 ^ 59
def prefixEnd_1724988 : Nat := 4983230072969 + 3 ^ 40 * 1724988 * 2
def baseEnd_1724988 : Nat := 590498644825334806811287

theorem tailTrace_1724988 : CollatzResearch.WordTrace tailWord_1724988 prefixEnd_1724988 590498644825334806811287 := by
  unfold tailWord_1724988
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457740537335277670423809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41943654049780370227231745 31457740537335277670423809)
  ·
    refine ⟨23593305403001458252817857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31457740537335277670423809 23593305403001458252817857)
    ·
      refine ⟨17694979052251093689613393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23593305403001458252817857 17694979052251093689613393)
      ·
        refine ⟨13271234289188320267210045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17694979052251093689613393 13271234289188320267210045)
        ·
          refine ⟨4976712858445620100203767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13271234289188320267210045 4976712858445620100203767)
          ·
            refine ⟨7465069287668430150305651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976712858445620100203767 7465069287668430150305651)
            ·
              refine ⟨11197603931502645225458477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465069287668430150305651 11197603931502645225458477)
              ·
                refine ⟨4199101474313491959546929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11197603931502645225458477 4199101474313491959546929)
                ·
                  refine ⟨3149326105735118969660197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199101474313491959546929 3149326105735118969660197)
                  ·
                    refine ⟨590498644825334806811287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149326105735118969660197 590498644825334806811287)
                    ·
                      rfl

theorem cell22_1724988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1724988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1724988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1724988 prefixEnd_1724988 := by exact prefixLift 1724988
  have htrace : WordTrace (prefixWord ++ tailWord_1724988) baseStart_1724988 baseEnd_1724988 := by
    simpa [prefixWord, tailWord_1724988, baseEnd_1724988] using wordTrace_append hprefix tailTrace_1724988
  have hstable : (prefixWord ++ tailWord_1724988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724988).length < 2 ^ (prefixWord ++ tailWord_1724988).sum := by decide
  have hdescent : baseEnd_1724988 < baseStart_1724988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725005 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1725005 : Nat := 118140960795 + 1725005 * 2 ^ 59
def prefixEnd_1725005 : Nat := 4983230072969 + 3 ^ 40 * 1725005 * 2
def baseEnd_1725005 : Nat := 590504464272752429136235

theorem tailTrace_1725005 : CollatzResearch.WordTrace tailWord_1725005 prefixEnd_1725005 590504464272752429136235 := by
  unfold tailWord_1725005
  simp only [CollatzResearch.WordTrace]
  refine ⟨62916101115608967244216469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41944067410405978162810979 62916101115608967244216469)
  ·
    refine ⟨2949192239794170339572647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62916101115608967244216469 2949192239794170339572647)
    ·
      refine ⟨4423788359691255509358971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2949192239794170339572647 4423788359691255509358971)
      ·
        refine ⟨6635682539536883264038457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423788359691255509358971 6635682539536883264038457)
        ·
          refine ⟨4976761904652662448028843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635682539536883264038457 4976761904652662448028843)
          ·
            refine ⟨7465142856978993672043265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976761904652662448028843 7465142856978993672043265)
            ·
              refine ⟨5598857142734245254032449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465142856978993672043265 5598857142734245254032449)
              ·
                refine ⟨4199142857050683940524337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598857142734245254032449 4199142857050683940524337)
                ·
                  refine ⟨3149357142788012955393253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199142857050683940524337 3149357142788012955393253)
                  ·
                    refine ⟨590504464272752429136235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149357142788012955393253 590504464272752429136235)
                    ·
                      rfl

theorem cell22_1725005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1725005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725005 prefixEnd_1725005 := by exact prefixLift 1725005
  have htrace : WordTrace (prefixWord ++ tailWord_1725005) baseStart_1725005 baseEnd_1725005 := by
    simpa [prefixWord, tailWord_1725005, baseEnd_1725005] using wordTrace_append hprefix tailTrace_1725005
  have hstable : (prefixWord ++ tailWord_1725005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725005).length < 2 ^ (prefixWord ++ tailWord_1725005).sum := by decide
  have hdescent : baseEnd_1725005 < baseStart_1725005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725016 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1725016 : Nat := 118140960795 + 1725016 * 2 ^ 59
def prefixEnd_1725016 : Nat := 4983230072969 + 3 ^ 40 * 1725016 * 2
def baseEnd_1725016 : Nat := 590508229797552067111201

theorem tailTrace_1725016 : CollatzResearch.WordTrace tailWord_1725016 prefixEnd_1725016 590508229797552067111201 := by
  unfold tailWord_1725016
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458251159284558061433451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41944334879046077415244601 31458251159284558061433451)
  ·
    refine ⟨47187376738926837092150177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31458251159284558061433451 47187376738926837092150177)
    ·
      refine ⟨35390532554195127819112633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47187376738926837092150177 35390532554195127819112633)
      ·
        refine ⟨26542899415646345864334475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35390532554195127819112633 26542899415646345864334475)
        ·
          refine ⟨39814349123469518796501713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26542899415646345864334475 39814349123469518796501713)
          ·
            refine ⟨29860761842602139097376285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39814349123469518796501713 29860761842602139097376285)
            ·
              refine ⟨11197785690975802161516107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29860761842602139097376285 11197785690975802161516107)
              ·
                refine ⟨16796678536463703242274161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197785690975802161516107 16796678536463703242274161)
                ·
                  refine ⟨12597508902347777431705621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16796678536463703242274161 12597508902347777431705621)
                  ·
                    refine ⟨590508229797552067111201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12597508902347777431705621 590508229797552067111201)
                    ·
                      rfl

theorem cell22_1725016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1725016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725016 prefixEnd_1725016 := by exact prefixLift 1725016
  have htrace : WordTrace (prefixWord ++ tailWord_1725016) baseStart_1725016 baseEnd_1725016 := by
    simpa [prefixWord, tailWord_1725016, baseEnd_1725016] using wordTrace_append hprefix tailTrace_1725016
  have hstable : (prefixWord ++ tailWord_1725016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725016).length < 2 ^ (prefixWord ++ tailWord_1725016).sum := by decide
  have hdescent : baseEnd_1725016 < baseStart_1725016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725020 : List Nat := [2, 2, 4, 1, 3, 2, 1, 7]
def baseStart_1725020 : Nat := 118140960795 + 1725020 * 2 ^ 59
def prefixEnd_1725020 : Nat := 4983230072969 + 3 ^ 40 * 1725020 * 2
def baseEnd_1725020 : Nat := 65612177675477487779021

theorem tailTrace_1725020 : CollatzResearch.WordTrace tailWord_1725020 prefixEnd_1725020 65612177675477487779021 := by
  unfold tailWord_1725020
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458324105277312403006257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41944432140369749870675009 31458324105277312403006257)
  ·
    refine ⟨23593743078957984302254693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31458324105277312403006257 23593743078957984302254693)
    ·
      refine ⟨4423826827304622056672755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23593743078957984302254693 4423826827304622056672755)
      ·
        refine ⟨6635740240956933085009133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423826827304622056672755 6635740240956933085009133)
        ·
          refine ⟨2488402590358849906878425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6635740240956933085009133 2488402590358849906878425)
          ·
            refine ⟨1866301942769137430158819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488402590358849906878425 1866301942769137430158819)
            ·
              refine ⟨2799452914153706145238229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866301942769137430158819 2799452914153706145238229)
              ·
                refine ⟨65612177675477487779021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2799452914153706145238229 65612177675477487779021)
                ·
                  rfl

theorem cell22_1725020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_1725020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725020 prefixEnd_1725020 := by exact prefixLift 1725020
  have htrace : WordTrace (prefixWord ++ tailWord_1725020) baseStart_1725020 baseEnd_1725020 := by
    simpa [prefixWord, tailWord_1725020, baseEnd_1725020] using wordTrace_append hprefix tailTrace_1725020
  have hstable : (prefixWord ++ tailWord_1725020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725020).length < 2 ^ (prefixWord ++ tailWord_1725020).sum := by decide
  have hdescent : baseEnd_1725020 < baseStart_1725020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725031 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 9]
def baseStart_1725031 : Nat := 118140960795 + 1725031 * 2 ^ 59
def prefixEnd_1725031 : Nat := 4983230072969 + 3 ^ 40 * 1725031 * 2
def baseEnd_1725031 : Nat := 196837788201365675995385

theorem tailTrace_1725031 : CollatzResearch.WordTrace tailWord_1725031 prefixEnd_1725031 196837788201365675995385 := by
  unfold tailWord_1725031
  simp only [CollatzResearch.WordTrace]
  refine ⟨62917049413514773684662947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41944699609009849123108631 62917049413514773684662947)
  ·
    refine ⟨94375574120272160526994421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62917049413514773684662947 94375574120272160526994421)
    ·
      refine ⟨8847710073775515049405727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94375574120272160526994421 8847710073775515049405727)
      ·
        refine ⟨13271565110663272574108591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8847710073775515049405727 13271565110663272574108591)
        ·
          refine ⟨19907347665994908861162887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13271565110663272574108591 19907347665994908861162887)
          ·
            refine ⟨29861021498992363291744331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19907347665994908861162887 29861021498992363291744331)
            ·
              refine ⟨44791532248488544937616497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29861021498992363291744331 44791532248488544937616497)
              ·
                refine ⟨33593649186366408703212373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44791532248488544937616497 33593649186366408703212373)
                ·
                  refine ⟨196837788201365675995385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33593649186366408703212373 196837788201365675995385)
                  ·
                    rfl

theorem cell22_1725031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_1725031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725031 prefixEnd_1725031 := by exact prefixLift 1725031
  have htrace : WordTrace (prefixWord ++ tailWord_1725031) baseStart_1725031 baseEnd_1725031 := by
    simpa [prefixWord, tailWord_1725031, baseEnd_1725031] using wordTrace_append hprefix tailTrace_1725031
  have hstable : (prefixWord ++ tailWord_1725031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725031).length < 2 ^ (prefixWord ++ tailWord_1725031).sum := by decide
  have hdescent : baseEnd_1725031 < baseStart_1725031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725058 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1725058 : Nat := 118140960795 + 1725058 * 2 ^ 59
def prefixEnd_1725058 : Nat := 4983230072969 + 3 ^ 40 * 1725058 * 2
def baseEnd_1725058 : Nat := 590522607255877957561073

theorem tailTrace_1725058 : CollatzResearch.WordTrace tailWord_1725058 prefixEnd_1725058 590522607255877957561073 := by
  unfold tailWord_1725058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15729508546104239323973957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41945356122944638197263885 15729508546104239323973957)
  ·
    refine ⟨2949282852394544873245117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15729508546104239323973957 2949282852394544873245117)
    ·
      refine ⟨1105981069647954327466919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2949282852394544873245117 1105981069647954327466919)
      ·
        refine ⟨1658971604471931491200379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105981069647954327466919 1658971604471931491200379)
        ·
          refine ⟨2488457406707897236800569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658971604471931491200379 2488457406707897236800569)
          ·
            refine ⟨1866343055030922927600427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488457406707897236800569 1866343055030922927600427)
            ·
              refine ⟨2799514582546384391400641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866343055030922927600427 2799514582546384391400641)
              ·
                refine ⟨2099635936909788293550481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799514582546384391400641 2099635936909788293550481)
                ·
                  refine ⟨1574726952682341220162861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099635936909788293550481 1574726952682341220162861)
                  ·
                    refine ⟨590522607255877957561073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1574726952682341220162861 590522607255877957561073)
                    ·
                      rfl

theorem cell22_1725058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1725058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725058 prefixEnd_1725058 := by exact prefixLift 1725058
  have htrace : WordTrace (prefixWord ++ tailWord_1725058) baseStart_1725058 baseEnd_1725058 := by
    simpa [prefixWord, tailWord_1725058, baseEnd_1725058] using wordTrace_append hprefix tailTrace_1725058
  have hstable : (prefixWord ++ tailWord_1725058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725058).length < 2 ^ (prefixWord ++ tailWord_1725058).sum := by decide
  have hdescent : baseEnd_1725058 < baseStart_1725058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725172 : List Nat := [2, 6, 1, 1, 2, 10]
def baseStart_1725172 : Nat := 118140960795 + 1725172 * 2 ^ 59
def prefixEnd_1725172 : Nat := 4983230072969 + 3 ^ 40 * 1725172 * 2
def baseEnd_1725172 : Nat := 7290884343032341484083

theorem tailTrace_1725172 : CollatzResearch.WordTrace tailWord_1725172 prefixEnd_1725172 7290884343032341484083 := by
  unfold tailWord_1725172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31461096053001977382772885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41948128070669303177030513 31461096053001977382772885)
  ·
    refine ⟨1474738877484467689817479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31461096053001977382772885 1474738877484467689817479)
    ·
      refine ⟨2212108316226701534726219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474738877484467689817479 2212108316226701534726219)
      ·
        refine ⟨3318162474340052302089329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212108316226701534726219 3318162474340052302089329)
        ·
          refine ⟨2488621855755039226566997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3318162474340052302089329 2488621855755039226566997)
          ·
            refine ⟨7290884343032341484083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2488621855755039226566997 7290884343032341484083)
            ·
              rfl

theorem cell22_1725172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 10].length) (baseStart_1725172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725172 prefixEnd_1725172 := by exact prefixLift 1725172
  have htrace : WordTrace (prefixWord ++ tailWord_1725172) baseStart_1725172 baseEnd_1725172 := by
    simpa [prefixWord, tailWord_1725172, baseEnd_1725172] using wordTrace_append hprefix tailTrace_1725172
  have hstable : (prefixWord ++ tailWord_1725172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725172).length < 2 ^ (prefixWord ++ tailWord_1725172).sum := by decide
  have hdescent : baseEnd_1725172 < baseStart_1725172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725228 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_1725228 : Nat := 118140960795 + 1725228 * 2 ^ 59
def prefixEnd_1725228 : Nat := 4983230072969 + 3 ^ 40 * 1725228 * 2
def baseEnd_1725228 : Nat := 196860267243351393603517

theorem tailTrace_1725228 : CollatzResearch.WordTrace tailWord_1725228 prefixEnd_1725228 196860267243351393603517 := by
  unfold tailWord_1725228
  simp only [CollatzResearch.WordTrace]
  refine ⟨31462117296900538164792169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41949489729200717553056225 31462117296900538164792169)
  ·
    refine ⟨23596587972675403623594127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31462117296900538164792169 23596587972675403623594127)
    ·
      refine ⟨35394881959013105435391191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23596587972675403623594127 35394881959013105435391191)
      ·
        refine ⟨53092322938519658153086787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35394881959013105435391191 53092322938519658153086787)
        ·
          refine ⟨79638484407779487229630181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53092322938519658153086787 79638484407779487229630181)
          ·
            refine ⟨14932215826458653855555659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79638484407779487229630181 14932215826458653855555659)
            ·
              refine ⟨22398323739687980783333489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14932215826458653855555659 22398323739687980783333489)
              ·
                refine ⟨16798742804765985587500117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22398323739687980783333489 16798742804765985587500117)
                ·
                  refine ⟨196860267243351393603517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16798742804765985587500117 196860267243351393603517)
                  ·
                    rfl

theorem cell22_1725228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_1725228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725228 prefixEnd_1725228 := by exact prefixLift 1725228
  have htrace : WordTrace (prefixWord ++ tailWord_1725228) baseStart_1725228 baseEnd_1725228 := by
    simpa [prefixWord, tailWord_1725228, baseEnd_1725228] using wordTrace_append hprefix tailTrace_1725228
  have hstable : (prefixWord ++ tailWord_1725228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725228).length < 2 ^ (prefixWord ++ tailWord_1725228).sum := by decide
  have hdescent : baseEnd_1725228 < baseStart_1725228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725455 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1725455 : Nat := 118140960795 + 1725455 * 2 ^ 59
def prefixEnd_1725455 : Nat := 4983230072969 + 3 ^ 40 * 1725455 * 2
def baseEnd_1725455 : Nat := 590658508469101255384855

theorem tailTrace_1725455 : CollatzResearch.WordTrace tailWord_1725455 prefixEnd_1725455 590658508469101255384855 := by
  unfold tailWord_1725455
  simp only [CollatzResearch.WordTrace]
  refine ⟨62932513963978694098097819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41955009309319129398731879 62932513963978694098097819)
  ·
    refine ⟨94398770945968041147146729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62932513963978694098097819 94398770945968041147146729)
    ·
      refine ⟨70799078209476030860360047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94398770945968041147146729 70799078209476030860360047)
      ·
        refine ⟨106198617314214046290540071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70799078209476030860360047 106198617314214046290540071)
        ·
          refine ⟨159297925971321069435810107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106198617314214046290540071 159297925971321069435810107)
          ·
            refine ⟨238946888956981604153715161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159297925971321069435810107 238946888956981604153715161)
            ·
              refine ⟨179210166717736203115286371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238946888956981604153715161 179210166717736203115286371)
              ·
                refine ⟨268815250076604304672929557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179210166717736203115286371 268815250076604304672929557)
                ·
                  refine ⟨12600714847340826781543573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268815250076604304672929557 12600714847340826781543573)
                  ·
                    refine ⟨590658508469101255384855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12600714847340826781543573 590658508469101255384855)
                    ·
                      rfl

theorem cell22_1725455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1725455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725455 prefixEnd_1725455 := by exact prefixLift 1725455
  have htrace : WordTrace (prefixWord ++ tailWord_1725455) baseStart_1725455 baseEnd_1725455 := by
    simpa [prefixWord, tailWord_1725455, baseEnd_1725455] using wordTrace_append hprefix tailTrace_1725455
  have hstable : (prefixWord ++ tailWord_1725455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725455).length < 2 ^ (prefixWord ++ tailWord_1725455).sum := by decide
  have hdescent : baseEnd_1725455 < baseStart_1725455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725457 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_1725457 : Nat := 118140960795 + 1725457 * 2 ^ 59
def prefixEnd_1725457 : Nat := 4983230072969 + 3 ^ 40 * 1725457 * 2
def baseEnd_1725457 : Nat := 590659193109973916834849

theorem tailTrace_1725457 : CollatzResearch.WordTrace tailWord_1725457 prefixEnd_1725457 590659193109973916834849 := by
  unfold tailWord_1725457
  simp only [CollatzResearch.WordTrace]
  refine ⟨62932586909971448439670625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41955057939980965626447083 62932586909971448439670625)
  ·
    refine ⟨47199440182478586329752969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62932586909971448439670625 47199440182478586329752969)
    ·
      refine ⟨35399580136858939747314727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47199440182478586329752969 35399580136858939747314727)
      ·
        refine ⟨53099370205288409620972091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35399580136858939747314727 53099370205288409620972091)
        ·
          refine ⟨79649055307932614431458137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53099370205288409620972091 79649055307932614431458137)
          ·
            refine ⟨59736791480949460823593603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79649055307932614431458137 59736791480949460823593603)
            ·
              refine ⟨89605187221424191235390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59736791480949460823593603 89605187221424191235390405)
              ·
                refine ⟨16800972604017035856635701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89605187221424191235390405 16800972604017035856635701)
                ·
                  refine ⟨1575091181626597111559597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16800972604017035856635701 1575091181626597111559597)
                  ·
                    refine ⟨590659193109973916834849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575091181626597111559597 590659193109973916834849)
                    ·
                      rfl

theorem cell22_1725457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_1725457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725457 prefixEnd_1725457 := by exact prefixLift 1725457
  have htrace : WordTrace (prefixWord ++ tailWord_1725457) baseStart_1725457 baseEnd_1725457 := by
    simpa [prefixWord, tailWord_1725457, baseEnd_1725457] using wordTrace_append hprefix tailTrace_1725457
  have hstable : (prefixWord ++ tailWord_1725457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725457).length < 2 ^ (prefixWord ++ tailWord_1725457).sum := by decide
  have hdescent : baseEnd_1725457 < baseStart_1725457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725549 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1725549 : Nat := 118140960795 + 1725549 * 2 ^ 59
def prefixEnd_1725549 : Nat := 4983230072969 + 3 ^ 40 * 1725549 * 2
def baseEnd_1725549 : Nat := 196896895530038781178189

theorem tailTrace_1725549 : CollatzResearch.WordTrace tailWord_1725549 prefixEnd_1725549 196896895530038781178189 := by
  unfold tailWord_1725549
  simp only [CollatzResearch.WordTrace]
  refine ⟨62935942425638148152019701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41957294950425432101346467 62935942425638148152019701)
  ·
    refine ⟨5900244602403576389251847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62935942425638148152019701 5900244602403576389251847)
    ·
      refine ⟨8850366903605364583877771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5900244602403576389251847 8850366903605364583877771)
      ·
        refine ⟨13275550355408046875816657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8850366903605364583877771 13275550355408046875816657)
        ·
          refine ⟨9956662766556035156862493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13275550355408046875816657 9956662766556035156862493)
          ·
            refine ⟨3733748537458513183823435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9956662766556035156862493 3733748537458513183823435)
            ·
              refine ⟨5600622806187769775735153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733748537458513183823435 5600622806187769775735153)
              ·
                refine ⟨4200467104640827331801365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5600622806187769775735153 4200467104640827331801365)
                ·
                  refine ⟨196896895530038781178189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4200467104640827331801365 196896895530038781178189)
                  ·
                    rfl

theorem cell22_1725549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1725549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725549 prefixEnd_1725549 := by exact prefixLift 1725549
  have htrace : WordTrace (prefixWord ++ tailWord_1725549) baseStart_1725549 baseEnd_1725549 := by
    simpa [prefixWord, tailWord_1725549, baseEnd_1725549] using wordTrace_append hprefix tailTrace_1725549
  have hstable : (prefixWord ++ tailWord_1725549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725549).length < 2 ^ (prefixWord ++ tailWord_1725549).sum := by decide
  have hdescent : baseEnd_1725549 < baseStart_1725549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725564 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1725564 : Nat := 118140960795 + 1725564 * 2 ^ 59
def prefixEnd_1725564 : Nat := 4983230072969 + 3 ^ 40 * 1725564 * 2
def baseEnd_1725564 : Nat := 590695821396661304409521

theorem tailTrace_1725564 : CollatzResearch.WordTrace tailWord_1725564 prefixEnd_1725564 590695821396661304409521 := by
  unfold tailWord_1725564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31468244760291902856907873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41957659680389203809210497 31468244760291902856907873)
  ·
    refine ⟨23601183570218927142680905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31468244760291902856907873 23601183570218927142680905)
    ·
      refine ⟨17700887677664195357010679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23601183570218927142680905 17700887677664195357010679)
      ·
        refine ⟨26551331516496293035516019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17700887677664195357010679 26551331516496293035516019)
        ·
          refine ⟨39826997274744439553274029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26551331516496293035516019 39826997274744439553274029)
          ·
            refine ⟨14935123978029164832477761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39826997274744439553274029 14935123978029164832477761)
            ·
              refine ⟨11201342983521873624358321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14935123978029164832477761 11201342983521873624358321)
              ·
                refine ⟨8401007237641405218268741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11201342983521873624358321 8401007237641405218268741)
                ·
                  refine ⟨1575188857057763478425389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8401007237641405218268741 1575188857057763478425389)
                  ·
                    refine ⟨590695821396661304409521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575188857057763478425389 590695821396661304409521)
                    ·
                      rfl

theorem cell22_1725564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1725564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725564 prefixEnd_1725564 := by exact prefixLift 1725564
  have htrace : WordTrace (prefixWord ++ tailWord_1725564) baseStart_1725564 baseEnd_1725564 := by
    simpa [prefixWord, tailWord_1725564, baseEnd_1725564] using wordTrace_append hprefix tailTrace_1725564
  have hstable : (prefixWord ++ tailWord_1725564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725564).length < 2 ^ (prefixWord ++ tailWord_1725564).sum := by decide
  have hdescent : baseEnd_1725564 < baseStart_1725564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725577 : List Nat := [1, 2, 1, 1, 4, 4, 9]
def baseStart_1725577 : Nat := 118140960795 + 1725577 * 2 ^ 59
def prefixEnd_1725577 : Nat := 4983230072969 + 3 ^ 40 * 1725577 * 2
def baseEnd_1725577 : Nat := 21877787835641985327203

theorem tailTrace_1725577 : CollatzResearch.WordTrace tailWord_1725577 prefixEnd_1725577 21877787835641985327203 := by
  unfold tailWord_1725577
  simp only [CollatzResearch.WordTrace]
  refine ⟨62936963669536708934038985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41957975779691139289359323 62936963669536708934038985)
  ·
    refine ⟨47202722752152531700529239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62936963669536708934038985 47202722752152531700529239)
    ·
      refine ⟨70804084128228797550793859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47202722752152531700529239 70804084128228797550793859)
      ·
        refine ⟨106206126192343196326190789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70804084128228797550793859 106206126192343196326190789)
        ·
          refine ⟨19913648661064349311160773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106206126192343196326190789 19913648661064349311160773)
          ·
            refine ⟨3733809123949565495842645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19913648661064349311160773 3733809123949565495842645)
            ·
              refine ⟨21877787835641985327203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3733809123949565495842645 21877787835641985327203)
              ·
                rfl

theorem cell22_1725577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 9].length) (baseStart_1725577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725577 prefixEnd_1725577 := by exact prefixLift 1725577
  have htrace : WordTrace (prefixWord ++ tailWord_1725577) baseStart_1725577 baseEnd_1725577 := by
    simpa [prefixWord, tailWord_1725577, baseEnd_1725577] using wordTrace_append hprefix tailTrace_1725577
  have hstable : (prefixWord ++ tailWord_1725577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725577).length < 2 ^ (prefixWord ++ tailWord_1725577).sum := by decide
  have hdescent : baseEnd_1725577 < baseStart_1725577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725598 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1725598 : Nat := 118140960795 + 1725598 * 2 ^ 59
def prefixEnd_1725598 : Nat := 4983230072969 + 3 ^ 40 * 1725598 * 2
def baseEnd_1725598 : Nat := 590707460291496549059417

theorem tailTrace_1725598 : CollatzResearch.WordTrace tailWord_1725598 prefixEnd_1725598 590707460291496549059417 := by
  unfold tailWord_1725598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867216200307578690069181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41958486401640419680368965 7867216200307578690069181)
  ·
    refine ⟨2950206075115342008775943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7867216200307578690069181 2950206075115342008775943)
    ·
      refine ⟨4425309112673013013163915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950206075115342008775943 4425309112673013013163915)
      ·
        refine ⟨6637963669009519519745873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425309112673013013163915 6637963669009519519745873)
        ·
          refine ⟨4978472751757139639809405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637963669009519519745873 4978472751757139639809405)
          ·
            refine ⟨1866927281908927364928527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4978472751757139639809405 1866927281908927364928527)
            ·
              refine ⟨2800390922863391047392791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866927281908927364928527 2800390922863391047392791)
              ·
                refine ⟨4200586384295086571089187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800390922863391047392791 4200586384295086571089187)
                ·
                  refine ⟨6300879576442629856633781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200586384295086571089187 6300879576442629856633781)
                  ·
                    refine ⟨590707460291496549059417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6300879576442629856633781 590707460291496549059417)
                    ·
                      rfl

theorem cell22_1725598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1725598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725598 prefixEnd_1725598 := by exact prefixLift 1725598
  have htrace : WordTrace (prefixWord ++ tailWord_1725598) baseStart_1725598 baseEnd_1725598 := by
    simpa [prefixWord, tailWord_1725598, baseEnd_1725598] using wordTrace_append hprefix tailTrace_1725598
  have hstable : (prefixWord ++ tailWord_1725598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725598).length < 2 ^ (prefixWord ++ tailWord_1725598).sum := by decide
  have hdescent : baseEnd_1725598 < baseStart_1725598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725656 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_1725656 : Nat := 118140960795 + 1725656 * 2 ^ 59
def prefixEnd_1725656 : Nat := 4983230072969 + 3 ^ 40 * 1725656 * 2
def baseEnd_1725656 : Nat := 196909104958934577036413

theorem tailTrace_1725656 : CollatzResearch.WordTrace tailWord_1725656 prefixEnd_1725656 196909104958934577036413 := by
  unfold tailWord_1725656
  simp only [CollatzResearch.WordTrace]
  refine ⟨31469922518125252713082411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41959896690833670284109881 31469922518125252713082411)
  ·
    refine ⟨47204883777187879069623617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31469922518125252713082411 47204883777187879069623617)
    ·
      refine ⟨35403662832890909302217713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47204883777187879069623617 35403662832890909302217713)
      ·
        refine ⟨26552747124668181976663285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35403662832890909302217713 26552747124668181976663285)
        ·
          refine ⟨2489320042937642060312183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26552747124668181976663285 2489320042937642060312183)
          ·
            refine ⟨3733980064406463090468275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489320042937642060312183 3733980064406463090468275)
            ·
              refine ⟨5600970096609694635702413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733980064406463090468275 5600970096609694635702413)
              ·
                refine ⟨2100363786228635488388405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5600970096609694635702413 2100363786228635488388405)
                ·
                  refine ⟨196909104958934577036413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2100363786228635488388405 196909104958934577036413)
                  ·
                    rfl

theorem cell22_1725656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_1725656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725656 prefixEnd_1725656 := by exact prefixLift 1725656
  have htrace : WordTrace (prefixWord ++ tailWord_1725656) baseStart_1725656 baseEnd_1725656 := by
    simpa [prefixWord, tailWord_1725656, baseEnd_1725656] using wordTrace_append hprefix tailTrace_1725656
  have hstable : (prefixWord ++ tailWord_1725656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725656).length < 2 ^ (prefixWord ++ tailWord_1725656).sum := by decide
  have hdescent : baseEnd_1725656 < baseStart_1725656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725701 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 4]
def baseStart_1725701 : Nat := 118140960795 + 1725701 * 2 ^ 59
def prefixEnd_1725701 : Nat := 4983230072969 + 3 ^ 40 * 1725701 * 2
def baseEnd_1725701 : Nat := 196914239765479537911367

theorem tailTrace_1725701 : CollatzResearch.WordTrace tailWord_1725701 prefixEnd_1725701 196914239765479537911367 := by
  unfold tailWord_1725701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62941486321087478111552957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41960990880724985407701971 62941486321087478111552957)
  ·
    refine ⟨23603057370407804291832359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62941486321087478111552957 23603057370407804291832359)
    ·
      refine ⟨35404586055611706437748539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603057370407804291832359 35404586055611706437748539)
      ·
        refine ⟨53106879083417559656622809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35404586055611706437748539 53106879083417559656622809)
        ·
          refine ⟨39830159312563169742467107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53106879083417559656622809 39830159312563169742467107)
          ·
            refine ⟨59745238968844754613700661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39830159312563169742467107 59745238968844754613700661)
            ·
              refine ⟨5601116153329195745034437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59745238968844754613700661 5601116153329195745034437)
              ·
                refine ⟨1050209278749224202193957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5601116153329195745034437 1050209278749224202193957)
                ·
                  refine ⟨196914239765479537911367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050209278749224202193957 196914239765479537911367)
                  ·
                    rfl

theorem cell22_1725701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_1725701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725701 prefixEnd_1725701 := by exact prefixLift 1725701
  have htrace : WordTrace (prefixWord ++ tailWord_1725701) baseStart_1725701 baseEnd_1725701 := by
    simpa [prefixWord, tailWord_1725701, baseEnd_1725701] using wordTrace_append hprefix tailTrace_1725701
  have hstable : (prefixWord ++ tailWord_1725701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725701).length < 2 ^ (prefixWord ++ tailWord_1725701).sum := by decide
  have hdescent : baseEnd_1725701 < baseStart_1725701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725731 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 2, 4]
def baseStart_1725731 : Nat := 118140960795 + 1725731 * 2 ^ 59
def prefixEnd_1725731 : Nat := 4983230072969 + 3 ^ 40 * 1725731 * 2
def baseEnd_1725731 : Nat := 590752988909528535484009

theorem tailTrace_1725731 : CollatzResearch.WordTrace tailWord_1725731 prefixEnd_1725731 590752988909528535484009 := by
  unfold tailWord_1725731
  simp only [CollatzResearch.WordTrace]
  refine ⟨62942580510978793235145047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41961720340652528823430031 62942580510978793235145047)
  ·
    refine ⟨94413870766468189852717571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62942580510978793235145047 94413870766468189852717571)
    ·
      refine ⟨141620806149702284779076357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94413870766468189852717571 141620806149702284779076357)
      ·
        refine ⟨26553901153069178396076817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141620806149702284779076357 26553901153069178396076817)
        ·
          refine ⟨19915425864801883797057613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26553901153069178396076817 19915425864801883797057613)
          ·
            refine ⟨7468284699300706423896605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19915425864801883797057613 7468284699300706423896605)
            ·
              refine ⟨2800606762237764908961227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7468284699300706423896605 2800606762237764908961227)
              ·
                refine ⟨4200910143356647363441841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800606762237764908961227 4200910143356647363441841)
                ·
                  refine ⟨3150682607517485522581381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200910143356647363441841 3150682607517485522581381)
                  ·
                    refine ⟨590752988909528535484009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3150682607517485522581381 590752988909528535484009)
                    ·
                      rfl

theorem cell22_1725731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_1725731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725731 prefixEnd_1725731 := by exact prefixLift 1725731
  have htrace : WordTrace (prefixWord ++ tailWord_1725731) baseStart_1725731 baseEnd_1725731 := by
    simpa [prefixWord, tailWord_1725731, baseEnd_1725731] using wordTrace_append hprefix tailTrace_1725731
  have hstable : (prefixWord ++ tailWord_1725731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725731).length < 2 ^ (prefixWord ++ tailWord_1725731).sum := by decide
  have hdescent : baseEnd_1725731 < baseStart_1725731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725795 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 1, 3]
def baseStart_1725795 : Nat := 118140960795 + 1725795 * 2 ^ 59
def prefixEnd_1725795 : Nat := 4983230072969 + 3 ^ 40 * 1725795 * 2
def baseEnd_1725795 : Nat := 590774897417453701883813

theorem tailTrace_1725795 : CollatzResearch.WordTrace tailWord_1725795 prefixEnd_1725795 590774897417453701883813 := by
  unfold tailWord_1725795
  simp only [CollatzResearch.WordTrace]
  refine ⟨62944914782746932165474839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41963276521831288110316559 62944914782746932165474839)
  ·
    refine ⟨94417372174120398248212259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62944914782746932165474839 94417372174120398248212259)
    ·
      refine ⟨141626058261180597372318389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94417372174120398248212259 141626058261180597372318389)
      ·
        refine ⟨13277442961985681003654849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141626058261180597372318389 13277442961985681003654849)
        ·
          refine ⟨9958082221489260752741137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13277442961985681003654849 9958082221489260752741137)
          ·
            refine ⟨7468561666116945564555853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958082221489260752741137 7468561666116945564555853)
            ·
              refine ⟨2800710624793854586708445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7468561666116945564555853 2800710624793854586708445)
              ·
                refine ⟨1050266484297695470015667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2800710624793854586708445 1050266484297695470015667)
                ·
                  refine ⟨1575399726446543205023501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050266484297695470015667 1575399726446543205023501)
                  ·
                    refine ⟨590774897417453701883813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575399726446543205023501 590774897417453701883813)
                    ·
                      rfl

theorem cell22_1725795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 3].length) (baseStart_1725795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725795 prefixEnd_1725795 := by exact prefixLift 1725795
  have htrace : WordTrace (prefixWord ++ tailWord_1725795) baseStart_1725795 baseEnd_1725795 := by
    simpa [prefixWord, tailWord_1725795, baseEnd_1725795] using wordTrace_append hprefix tailTrace_1725795
  have hstable : (prefixWord ++ tailWord_1725795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725795).length < 2 ^ (prefixWord ++ tailWord_1725795).sum := by decide
  have hdescent : baseEnd_1725795 < baseStart_1725795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725821 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1725821 : Nat := 118140960795 + 1725821 * 2 ^ 59
def prefixEnd_1725821 : Nat := 4983230072969 + 3 ^ 40 * 1725821 * 2
def baseEnd_1725821 : Nat := 590783797748798300733733

theorem tailTrace_1725821 : CollatzResearch.WordTrace tailWord_1725821 prefixEnd_1725821 590783797748798300733733 := by
  unfold tailWord_1725821
  simp only [CollatzResearch.WordTrace]
  refine ⟨62945863080652738605921317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41963908720435159070614211 62945863080652738605921317)
  ·
    refine ⟨11802349327622388488610247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62945863080652738605921317 11802349327622388488610247)
    ·
      refine ⟨17703523991433582732915371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11802349327622388488610247 17703523991433582732915371)
      ·
        refine ⟨26555285987150374099373057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17703523991433582732915371 26555285987150374099373057)
        ·
          refine ⟨19916464490362780574529793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26555285987150374099373057 19916464490362780574529793)
          ·
            refine ⟨14937348367772085430897345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19916464490362780574529793 14937348367772085430897345)
            ·
              refine ⟨11203011275829064073173009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14937348367772085430897345 11203011275829064073173009)
              ·
                refine ⟨8402258456871798054879757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11203011275829064073173009 8402258456871798054879757)
                ·
                  refine ⟨3150846921326924270579909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8402258456871798054879757 3150846921326924270579909)
                  ·
                    refine ⟨590783797748798300733733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3150846921326924270579909 590783797748798300733733)
                    ·
                      rfl

theorem cell22_1725821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1725821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725821 prefixEnd_1725821 := by exact prefixLift 1725821
  have htrace : WordTrace (prefixWord ++ tailWord_1725821) baseStart_1725821 baseEnd_1725821 := by
    simpa [prefixWord, tailWord_1725821, baseEnd_1725821] using wordTrace_append hprefix tailTrace_1725821
  have hstable : (prefixWord ++ tailWord_1725821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725821).length < 2 ^ (prefixWord ++ tailWord_1725821).sum := by decide
  have hdescent : baseEnd_1725821 < baseStart_1725821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725855 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 1, 4]
def baseStart_1725855 : Nat := 118140960795 + 1725855 * 2 ^ 59
def prefixEnd_1725855 : Nat := 4983230072969 + 3 ^ 40 * 1725855 * 2
def baseEnd_1725855 : Nat := 590795436643633545383629

theorem tailTrace_1725855 : CollatzResearch.WordTrace tailWord_1725855 prefixEnd_1725855 590795436643633545383629 := by
  unfold tailWord_1725855
  simp only [CollatzResearch.WordTrace]
  refine ⟨62947103162529562412659019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41964735441686374941772679 62947103162529562412659019)
  ·
    refine ⟨94420654743794343618988529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62947103162529562412659019 94420654743794343618988529)
    ·
      refine ⟨70815491057845757714241397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94420654743794343618988529 70815491057845757714241397)
      ·
        refine ⟨6638952286673039785710131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70815491057845757714241397 6638952286673039785710131)
        ·
          refine ⟨9958428430009559678565197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638952286673039785710131 9958428430009559678565197)
          ·
            refine ⟨3734410661253584879461949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9958428430009559678565197 3734410661253584879461949)
            ·
              refine ⟨1400403997970094329798231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734410661253584879461949 1400403997970094329798231)
              ·
                refine ⟨2100605996955141494697347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400403997970094329798231 2100605996955141494697347)
                ·
                  refine ⟨3150908995432712242046021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100605996955141494697347 3150908995432712242046021)
                  ·
                    refine ⟨590795436643633545383629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3150908995432712242046021 590795436643633545383629)
                    ·
                      rfl

theorem cell22_1725855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_1725855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725855 prefixEnd_1725855 := by exact prefixLift 1725855
  have htrace : WordTrace (prefixWord ++ tailWord_1725855) baseStart_1725855 baseEnd_1725855 := by
    simpa [prefixWord, tailWord_1725855, baseEnd_1725855] using wordTrace_append hprefix tailTrace_1725855
  have hstable : (prefixWord ++ tailWord_1725855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725855).length < 2 ^ (prefixWord ++ tailWord_1725855).sum := by decide
  have hdescent : baseEnd_1725855 < baseStart_1725855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725868 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_1725868 : Nat := 118140960795 + 1725868 * 2 ^ 59
def prefixEnd_1725868 : Nat := 4983230072969 + 3 ^ 40 * 1725868 * 2
def baseEnd_1725868 : Nat := 590799886809305844808589

theorem tailTrace_1725868 : CollatzResearch.WordTrace tailWord_1725868 prefixEnd_1725868 590799886809305844808589 := by
  unfold tailWord_1725868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31473788655741232816441129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41965051540988310421921505 31473788655741232816441129)
  ·
    refine ⟨23605341491805924612330847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31473788655741232816441129 23605341491805924612330847)
    ·
      refine ⟨35408012237708886918496271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23605341491805924612330847 35408012237708886918496271)
      ·
        refine ⟨53112018356563330377744407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35408012237708886918496271 53112018356563330377744407)
        ·
          refine ⟨79668027534844995566616611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53112018356563330377744407 79668027534844995566616611)
          ·
            refine ⟨119502041302267493349924917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79668027534844995566616611 119502041302267493349924917)
            ·
              refine ⟨11203316372087577501555461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119502041302267493349924917 11203316372087577501555461)
              ·
                refine ⟨2100621819766420781541649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11203316372087577501555461 2100621819766420781541649)
                ·
                  refine ⟨1575466364824815586156237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100621819766420781541649 1575466364824815586156237)
                  ·
                    refine ⟨590799886809305844808589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575466364824815586156237 590799886809305844808589)
                    ·
                      rfl

theorem cell22_1725868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_1725868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725868 prefixEnd_1725868 := by exact prefixLift 1725868
  have htrace : WordTrace (prefixWord ++ tailWord_1725868) baseStart_1725868 baseEnd_1725868 := by
    simpa [prefixWord, tailWord_1725868, baseEnd_1725868] using wordTrace_append hprefix tailTrace_1725868
  have hstable : (prefixWord ++ tailWord_1725868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725868).length < 2 ^ (prefixWord ++ tailWord_1725868).sum := by decide
  have hdescent : baseEnd_1725868 < baseStart_1725868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725898 : List Nat := [3, 1, 2, 1, 2, 4, 3, 6]
def baseStart_1725898 : Nat := 118140960795 + 1725898 * 2 ^ 59
def prefixEnd_1725898 : Nat := 4983230072969 + 3 ^ 40 * 1725898 * 2
def baseEnd_1725898 : Nat := 65645572935821751839833

theorem tailTrace_1725898 : CollatzResearch.WordTrace tailWord_1725898 prefixEnd_1725898 65645572935821751839833 := by
  unfold tailWord_1725898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15737167875343445189118587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41965781000915853837649565 15737167875343445189118587)
  ·
    refine ⟨23605751813015167783677881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15737167875343445189118587 23605751813015167783677881)
    ·
      refine ⟨17704313859761375837758411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23605751813015167783677881 17704313859761375837758411)
      ·
        refine ⟨26556470789642063756637617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17704313859761375837758411 26556470789642063756637617)
        ·
          refine ⟨19917353092231547817478213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26556470789642063756637617 19917353092231547817478213)
          ·
            refine ⟨3734503704793415215777165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19917353092231547817478213 3734503704793415215777165)
            ·
              refine ⟨1400438889297530705916437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734503704793415215777165 1400438889297530705916437)
              ·
                refine ⟨65645572935821751839833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1400438889297530705916437 65645572935821751839833)
                ·
                  rfl

theorem cell22_1725898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_1725898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725898 prefixEnd_1725898 := by exact prefixLift 1725898
  have htrace : WordTrace (prefixWord ++ tailWord_1725898) baseStart_1725898 baseEnd_1725898 := by
    simpa [prefixWord, tailWord_1725898, baseEnd_1725898] using wordTrace_append hprefix tailTrace_1725898
  have hstable : (prefixWord ++ tailWord_1725898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725898).length < 2 ^ (prefixWord ++ tailWord_1725898).sum := by decide
  have hdescent : baseEnd_1725898 < baseStart_1725898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725900 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_1725900 : Nat := 118140960795 + 1725900 * 2 ^ 59
def prefixEnd_1725900 : Nat := 4983230072969 + 3 ^ 40 * 1725900 * 2
def baseEnd_1725900 : Nat := 590810841063268428008491

theorem tailTrace_1725900 : CollatzResearch.WordTrace tailWord_1725900 prefixEnd_1725900 590810841063268428008491 := by
  unfold tailWord_1725900
  simp only [CollatzResearch.WordTrace]
  refine ⟨31474372223683267549023577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41965829631577690065364769 31474372223683267549023577)
  ·
    refine ⟨23605779167762450661767683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31474372223683267549023577 23605779167762450661767683)
    ·
      refine ⟨35408668751643675992651525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23605779167762450661767683 35408668751643675992651525)
      ·
        refine ⟨6639125390933189248622161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35408668751643675992651525 6639125390933189248622161)
        ·
          refine ⟨4979344043199891936466621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6639125390933189248622161 4979344043199891936466621)
          ·
            refine ⟨1867254016199959476174983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4979344043199891936466621 1867254016199959476174983)
            ·
              refine ⟨2800881024299939214262475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867254016199959476174983 2800881024299939214262475)
              ·
                refine ⟨4201321536449908821393713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800881024299939214262475 4201321536449908821393713)
                ·
                  refine ⟨3150991152337431616045285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4201321536449908821393713 3150991152337431616045285)
                  ·
                    refine ⟨590810841063268428008491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3150991152337431616045285 590810841063268428008491)
                    ·
                      rfl

theorem cell22_1725900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_1725900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725900 prefixEnd_1725900 := by exact prefixLift 1725900
  have htrace : WordTrace (prefixWord ++ tailWord_1725900) baseStart_1725900 baseEnd_1725900 := by
    simpa [prefixWord, tailWord_1725900, baseEnd_1725900] using wordTrace_append hprefix tailTrace_1725900
  have hstable : (prefixWord ++ tailWord_1725900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725900).length < 2 ^ (prefixWord ++ tailWord_1725900).sum := by decide
  have hdescent : baseEnd_1725900 < baseStart_1725900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725964 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_1725964 : Nat := 118140960795 + 1725964 * 2 ^ 59
def prefixEnd_1725964 : Nat := 4983230072969 + 3 ^ 40 * 1725964 * 2
def baseEnd_1725964 : Nat := 590832749571193594408295

theorem tailTrace_1725964 : CollatzResearch.WordTrace tailWord_1725964 prefixEnd_1725964 590832749571193594408295 := by
  unfold tailWord_1725964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31475539359567337014188473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41967385812756449352251297 31475539359567337014188473)
  ·
    refine ⟨23606654519675502760641355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31475539359567337014188473 23606654519675502760641355)
    ·
      refine ⟨35409981779513254140962033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23606654519675502760641355 35409981779513254140962033)
      ·
        refine ⟨26557486334634940605721525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35409981779513254140962033 26557486334634940605721525)
        ·
          refine ⟨2489764343872025681786393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26557486334634940605721525 2489764343872025681786393)
          ·
            refine ⟨1867323257904019261339795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489764343872025681786393 1867323257904019261339795)
            ·
              refine ⟨2800984886856028892009693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867323257904019261339795 2800984886856028892009693)
              ·
                refine ⟨1050369332571010834503635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2800984886856028892009693 1050369332571010834503635)
                ·
                  refine ⟨1575553998856516251755453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050369332571010834503635 1575553998856516251755453)
                  ·
                    refine ⟨590832749571193594408295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575553998856516251755453 590832749571193594408295)
                    ·
                      rfl

theorem cell22_1725964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_1725964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1725964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1725964 prefixEnd_1725964 := by exact prefixLift 1725964
  have htrace : WordTrace (prefixWord ++ tailWord_1725964) baseStart_1725964 baseEnd_1725964 := by
    simpa [prefixWord, tailWord_1725964, baseEnd_1725964] using wordTrace_append hprefix tailTrace_1725964
  have hstable : (prefixWord ++ tailWord_1725964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725964).length < 2 ^ (prefixWord ++ tailWord_1725964).sum := by decide
  have hdescent : baseEnd_1725964 < baseStart_1725964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726112 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_1726112 : Nat := 118140960795 + 1726112 * 2 ^ 59
def prefixEnd_1726112 : Nat := 4983230072969 + 3 ^ 40 * 1726112 * 2
def baseEnd_1726112 : Nat := 196961137665256847235947

theorem tailTrace_1726112 : CollatzResearch.WordTrace tailWord_1726112 prefixEnd_1726112 196961137665256847235947 := by
  unfold tailWord_1726112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31478238361299247652382295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41970984481732330203176393 31478238361299247652382295)
  ·
    refine ⟨47217357541948871478573443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31478238361299247652382295 47217357541948871478573443)
    ·
      refine ⟨70826036312923307217860165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47217357541948871478573443 70826036312923307217860165)
      ·
        refine ⟨13279881808673120103348781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70826036312923307217860165 13279881808673120103348781)
        ·
          refine ⟨4979955678252420038755793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13279881808673120103348781 4979955678252420038755793)
          ·
            refine ⟨3734966758689315029066845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4979955678252420038755793 3734966758689315029066845)
            ·
              refine ⟨1400612534508493135900067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734966758689315029066845 1400612534508493135900067)
              ·
                refine ⟨2100918801762739703850101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400612534508493135900067 2100918801762739703850101)
                ·
                  refine ⟨196961137665256847235947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2100918801762739703850101 196961137665256847235947)
                  ·
                    rfl

theorem cell22_1726112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_1726112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726112 prefixEnd_1726112 := by exact prefixLift 1726112
  have htrace : WordTrace (prefixWord ++ tailWord_1726112) baseStart_1726112 baseEnd_1726112 := by
    simpa [prefixWord, tailWord_1726112, baseEnd_1726112] using wordTrace_append hprefix tailTrace_1726112
  have hstable : (prefixWord ++ tailWord_1726112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726112).length < 2 ^ (prefixWord ++ tailWord_1726112).sum := by decide
  have hdescent : baseEnd_1726112 < baseStart_1726112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726133 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1726133 : Nat := 118140960795 + 1726133 * 2 ^ 59
def prefixEnd_1726133 : Nat := 4983230072969 + 3 ^ 40 * 1726133 * 2
def baseEnd_1726133 : Nat := 590890601724933486932777

theorem tailTrace_1726133 : CollatzResearch.WordTrace tailWord_1726133 prefixEnd_1726133 590890601724933486932777 := by
  unfold tailWord_1726133
  simp only [CollatzResearch.WordTrace]
  refine ⟨62957242655522415891279053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41971495103681610594186035 62957242655522415891279053)
  ·
    refine ⟨23608965995820905959229645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62957242655522415891279053 23608965995820905959229645)
    ·
      refine ⟨8853362248432839734711117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23608965995820905959229645 8853362248432839734711117)
      ·
        refine ⟨3320010843162314900516669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8853362248432839734711117 3320010843162314900516669)
        ·
          refine ⟨1245004066185868087693751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3320010843162314900516669 1245004066185868087693751)
          ·
            refine ⟨1867506099278802131540627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245004066185868087693751 1867506099278802131540627)
            ·
              refine ⟨2801259148918203197310941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867506099278802131540627 2801259148918203197310941)
              ·
                refine ⟨1050472180844326198991603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2801259148918203197310941 1050472180844326198991603)
                ·
                  refine ⟨1575708271266489298487405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050472180844326198991603 1575708271266489298487405)
                  ·
                    refine ⟨590890601724933486932777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575708271266489298487405 590890601724933486932777)
                    ·
                      rfl

theorem cell22_1726133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1726133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726133 prefixEnd_1726133 := by exact prefixLift 1726133
  have htrace : WordTrace (prefixWord ++ tailWord_1726133) baseStart_1726133 baseEnd_1726133 := by
    simpa [prefixWord, tailWord_1726133, baseEnd_1726133] using wordTrace_append hprefix tailTrace_1726133
  have hstable : (prefixWord ++ tailWord_1726133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726133).length < 2 ^ (prefixWord ++ tailWord_1726133).sum := by decide
  have hdescent : baseEnd_1726133 < baseStart_1726133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726142 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1726142 : Nat := 118140960795 + 1726142 * 2 ^ 59
def prefixEnd_1726142 : Nat := 4983230072969 + 3 ^ 40 * 1726142 * 2
def baseEnd_1726142 : Nat := 590893682608860463457749

theorem tailTrace_1726142 : CollatzResearch.WordTrace tailWord_1726142 prefixEnd_1726142 590893682608860463457749 := by
  unfold tailWord_1726142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869696364061226303544585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41971713941659873618904453 7869696364061226303544585)
  ·
    refine ⟨5902272273045919727658439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7869696364061226303544585 5902272273045919727658439)
    ·
      refine ⟨8853408409568879591487659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902272273045919727658439 8853408409568879591487659)
      ·
        refine ⟨13280112614353319387231489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853408409568879591487659 13280112614353319387231489)
        ·
          refine ⟨9960084460764989540423617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13280112614353319387231489 9960084460764989540423617)
          ·
            refine ⟨7470063345573742155317713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9960084460764989540423617 7470063345573742155317713)
            ·
              refine ⟨5602547509180306616488285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470063345573742155317713 5602547509180306616488285)
              ·
                refine ⟨2100955315942614981183107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5602547509180306616488285 2100955315942614981183107)
                ·
                  refine ⟨3151432973913922471774661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100955315942614981183107 3151432973913922471774661)
                  ·
                    refine ⟨590893682608860463457749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151432973913922471774661 590893682608860463457749)
                    ·
                      rfl

theorem cell22_1726142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1726142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726142 prefixEnd_1726142 := by exact prefixLift 1726142
  have htrace : WordTrace (prefixWord ++ tailWord_1726142) baseStart_1726142 baseEnd_1726142 := by
    simpa [prefixWord, tailWord_1726142, baseEnd_1726142] using wordTrace_append hprefix tailTrace_1726142
  have hstable : (prefixWord ++ tailWord_1726142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726142).length < 2 ^ (prefixWord ++ tailWord_1726142).sum := by decide
  have hdescent : baseEnd_1726142 < baseStart_1726142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726150 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1726150 : Nat := 118140960795 + 1726150 * 2 ^ 59
def prefixEnd_1726150 : Nat := 4983230072969 + 3 ^ 40 * 1726150 * 2
def baseEnd_1726150 : Nat := 590896421172351109257725

theorem tailTrace_1726150 : CollatzResearch.WordTrace tailWord_1726150 prefixEnd_1726150 590896421172351109257725 := by
  unfold tailWord_1726150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967433209264400868582747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41971908464307218529765269 1967433209264400868582747)
  ·
    refine ⟨2951149813896601302874121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967433209264400868582747 2951149813896601302874121)
    ·
      refine ⟨2213362360422450977155591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951149813896601302874121 2213362360422450977155591)
      ·
        refine ⟨3320043540633676465733387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213362360422450977155591 3320043540633676465733387)
        ·
          refine ⟨4980065310950514698600081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320043540633676465733387 4980065310950514698600081)
          ·
            refine ⟨3735048983212886023950061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980065310950514698600081 3735048983212886023950061)
            ·
              refine ⟨1400643368704832258981273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3735048983212886023950061 1400643368704832258981273)
              ·
                refine ⟨1050482526528624194235955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400643368704832258981273 1050482526528624194235955)
                ·
                  refine ⟨1575723789792936291353933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050482526528624194235955 1575723789792936291353933)
                  ·
                    refine ⟨590896421172351109257725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575723789792936291353933 590896421172351109257725)
                    ·
                      rfl

theorem cell22_1726150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1726150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726150 prefixEnd_1726150 := by exact prefixLift 1726150
  have htrace : WordTrace (prefixWord ++ tailWord_1726150) baseStart_1726150 baseEnd_1726150 := by
    simpa [prefixWord, tailWord_1726150, baseEnd_1726150] using wordTrace_append hprefix tailTrace_1726150
  have hstable : (prefixWord ++ tailWord_1726150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726150).length < 2 ^ (prefixWord ++ tailWord_1726150).sum := by decide
  have hdescent : baseEnd_1726150 < baseStart_1726150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726200 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_1726200 : Nat := 118140960795 + 1726200 * 2 ^ 59
def prefixEnd_1726200 : Nat := 4983230072969 + 3 ^ 40 * 1726200 * 2
def baseEnd_1726200 : Nat := 590913537194167645507571

theorem tailTrace_1726200 : CollatzResearch.WordTrace tailWord_1726200 prefixEnd_1726200 590913537194167645507571 := by
  unfold tailWord_1726200
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479843173139843166984027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41973124230853124222645369 31479843173139843166984027)
  ·
    refine ⟨47219764759709764750476041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31479843173139843166984027 47219764759709764750476041)
    ·
      refine ⟨35414823569782323562857031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47219764759709764750476041 35414823569782323562857031)
      ·
        refine ⟨53122235354673485344285547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35414823569782323562857031 53122235354673485344285547)
        ·
          refine ⟨79683353032010228016428321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53122235354673485344285547 79683353032010228016428321)
          ·
            refine ⟨59762514774007671012321241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79683353032010228016428321 59762514774007671012321241)
            ·
              refine ⟨44821886080505753259240931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59762514774007671012321241 44821886080505753259240931)
              ·
                refine ⟨67232829120758629888861397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44821886080505753259240931 67232829120758629888861397)
                ·
                  refine ⟨1575769432517780388020189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 67232829120758629888861397 1575769432517780388020189)
                  ·
                    refine ⟨590913537194167645507571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575769432517780388020189 590913537194167645507571)
                    ·
                      rfl

theorem cell22_1726200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_1726200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726200 prefixEnd_1726200 := by exact prefixLift 1726200
  have htrace : WordTrace (prefixWord ++ tailWord_1726200) baseStart_1726200 baseEnd_1726200 := by
    simpa [prefixWord, tailWord_1726200, baseEnd_1726200] using wordTrace_append hprefix tailTrace_1726200
  have hstable : (prefixWord ++ tailWord_1726200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726200).length < 2 ^ (prefixWord ++ tailWord_1726200).sum := by decide
  have hdescent : baseEnd_1726200 < baseStart_1726200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726206 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1726206 : Nat := 118140960795 + 1726206 * 2 ^ 59
def prefixEnd_1726206 : Nat := 4983230072969 + 3 ^ 40 * 1726206 * 2
def baseEnd_1726206 : Nat := 590915591116785629857553

theorem tailTrace_1726206 : CollatzResearch.WordTrace tailWord_1726206 prefixEnd_1726206 590915591116785629857553 := by
  unfold tailWord_1726206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869988148032243669835809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41973270122838632905790981 7869988148032243669835809)
  ·
    refine ⟨5902491111024182752376857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7869988148032243669835809 5902491111024182752376857)
    ·
      refine ⟨4426868333268137064282643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5902491111024182752376857 4426868333268137064282643)
      ·
        refine ⟨6640302499902205596423965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426868333268137064282643 6640302499902205596423965)
        ·
          refine ⟨2490113437463327098658987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6640302499902205596423965 2490113437463327098658987)
          ·
            refine ⟨3735170156194990647988481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490113437463327098658987 3735170156194990647988481)
            ·
              refine ⟨2801377617146242985991361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735170156194990647988481 2801377617146242985991361)
              ·
                refine ⟨2101033212859682239493521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801377617146242985991361 2101033212859682239493521)
                ·
                  refine ⟨1575774909644761679620141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2101033212859682239493521 1575774909644761679620141)
                  ·
                    refine ⟨590915591116785629857553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1575774909644761679620141 590915591116785629857553)
                    ·
                      rfl

theorem cell22_1726206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1726206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726206 prefixEnd_1726206 := by exact prefixLift 1726206
  have htrace : WordTrace (prefixWord ++ tailWord_1726206) baseStart_1726206 baseEnd_1726206 := by
    simpa [prefixWord, tailWord_1726206, baseEnd_1726206] using wordTrace_append hprefix tailTrace_1726206
  have hstable : (prefixWord ++ tailWord_1726206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726206).length < 2 ^ (prefixWord ++ tailWord_1726206).sum := by decide
  have hdescent : baseEnd_1726206 < baseStart_1726206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726238 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1726238 : Nat := 118140960795 + 1726238 * 2 ^ 59
def prefixEnd_1726238 : Nat := 4983230072969 + 3 ^ 40 * 1726238 * 2
def baseEnd_1726238 : Nat := 590926545370748213057455

theorem tailTrace_1726238 : CollatzResearch.WordTrace tailWord_1726238 prefixEnd_1726238 590926545370748213057455 := by
  unfold tailWord_1726238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870134040017752352981421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41974048213428012549234245 7870134040017752352981421)
  ·
    refine ⟨2951300265006657132368033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7870134040017752352981421 2951300265006657132368033)
    ·
      refine ⟨2213475198754992849276025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951300265006657132368033 2213475198754992849276025)
      ·
        refine ⟨1660106399066244636957019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2213475198754992849276025 1660106399066244636957019)
        ·
          refine ⟨2490159598599366955435529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660106399066244636957019 2490159598599366955435529)
          ·
            refine ⟨1867619698949525216576647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490159598599366955435529 1867619698949525216576647)
            ·
              refine ⟨2801429548424287824864971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867619698949525216576647 2801429548424287824864971)
              ·
                refine ⟨4202144322636431737297457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801429548424287824864971 4202144322636431737297457)
                ·
                  refine ⟨3151608241977323802973093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202144322636431737297457 3151608241977323802973093)
                  ·
                    refine ⟨590926545370748213057455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151608241977323802973093 590926545370748213057455)
                    ·
                      rfl

theorem cell22_1726238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1726238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726238 prefixEnd_1726238 := by exact prefixLift 1726238
  have htrace : WordTrace (prefixWord ++ tailWord_1726238) baseStart_1726238 baseEnd_1726238 := by
    simpa [prefixWord, tailWord_1726238, baseEnd_1726238] using wordTrace_append hprefix tailTrace_1726238
  have hstable : (prefixWord ++ tailWord_1726238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726238).length < 2 ^ (prefixWord ++ tailWord_1726238).sum := by decide
  have hdescent : baseEnd_1726238 < baseStart_1726238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726275 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 6]
def baseStart_1726275 : Nat := 118140960795 + 1726275 * 2 ^ 59
def prefixEnd_1726275 : Nat := 4983230072969 + 3 ^ 40 * 1726275 * 2
def baseEnd_1726275 : Nat := 196979737075630816627447

theorem tailTrace_1726275 : CollatzResearch.WordTrace tailWord_1726275 prefixEnd_1726275 196979737075630816627447 := by
  unfold tailWord_1726275
  simp only [CollatzResearch.WordTrace]
  refine ⟨62962421821007974142948279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41974947880671982761965519 62962421821007974142948279)
  ·
    refine ⟨94443632731511961214422419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62962421821007974142948279 94443632731511961214422419)
    ·
      refine ⟨141665449097267941821633629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94443632731511961214422419 141665449097267941821633629)
      ·
        refine ⟨53124543411475478183112611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141665449097267941821633629 53124543411475478183112611)
        ·
          refine ⟨79686815117213217274668917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53124543411475478183112611 79686815117213217274668917)
          ·
            refine ⟨7470638917238739119500211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79686815117213217274668917 7470638917238739119500211)
            ·
              refine ⟨11205958375858108679250317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470638917238739119500211 11205958375858108679250317)
              ·
                refine ⟨4202234390946790754718869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11205958375858108679250317 4202234390946790754718869)
                ·
                  refine ⟨196979737075630816627447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4202234390946790754718869 196979737075630816627447)
                  ·
                    rfl

theorem cell22_1726275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_1726275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726275 prefixEnd_1726275 := by exact prefixLift 1726275
  have htrace : WordTrace (prefixWord ++ tailWord_1726275) baseStart_1726275 baseEnd_1726275 := by
    simpa [prefixWord, tailWord_1726275, baseEnd_1726275] using wordTrace_append hprefix tailTrace_1726275
  have hstable : (prefixWord ++ tailWord_1726275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726275).length < 2 ^ (prefixWord ++ tailWord_1726275).sum := by decide
  have hdescent : baseEnd_1726275 < baseStart_1726275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726292 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1726292 : Nat := 118140960795 + 1726292 * 2 ^ 59
def prefixEnd_1726292 : Nat := 4983230072969 + 3 ^ 40 * 1726292 * 2
def baseEnd_1726292 : Nat := 196981676891436690735763

theorem tailTrace_1726292 : CollatzResearch.WordTrace tailWord_1726292 prefixEnd_1726292 196981676891436690735763 := by
  unfold tailWord_1726292
  simp only [CollatzResearch.WordTrace]
  refine ⟨31481520930973193023158565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41975361241297590697544753 31481520930973193023158565)
  ·
    refine ⟨5902785174557473691842231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31481520930973193023158565 5902785174557473691842231)
    ·
      refine ⟨8854177761836210537763347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902785174557473691842231 8854177761836210537763347)
      ·
        refine ⟨13281266642754315806645021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854177761836210537763347 13281266642754315806645021)
        ·
          refine ⟨4980474991032868427491883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13281266642754315806645021 4980474991032868427491883)
          ·
            refine ⟨7470712486549302641237825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980474991032868427491883 7470712486549302641237825)
            ·
              refine ⟨5603034364911976980928369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470712486549302641237825 5603034364911976980928369)
              ·
                refine ⟨4202275773683982735696277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603034364911976980928369 4202275773683982735696277)
                ·
                  refine ⟨196981676891436690735763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4202275773683982735696277 196981676891436690735763)
                  ·
                    rfl

theorem cell22_1726292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1726292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726292 prefixEnd_1726292 := by exact prefixLift 1726292
  have htrace : WordTrace (prefixWord ++ tailWord_1726292) baseStart_1726292 baseEnd_1726292 := by
    simpa [prefixWord, tailWord_1726292, baseEnd_1726292] using wordTrace_append hprefix tailTrace_1726292
  have hstable : (prefixWord ++ tailWord_1726292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726292).length < 2 ^ (prefixWord ++ tailWord_1726292).sum := by decide
  have hdescent : baseEnd_1726292 < baseStart_1726292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726305 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1726305 : Nat := 118140960795 + 1726305 * 2 ^ 59
def prefixEnd_1726305 : Nat := 4983230072969 + 3 ^ 40 * 1726305 * 2
def baseEnd_1726305 : Nat := 590949480839982371632249

theorem tailTrace_1726305 : CollatzResearch.WordTrace tailWord_1726305 prefixEnd_1726305 590949480839982371632249 := by
  unfold tailWord_1726305
  simp only [CollatzResearch.WordTrace]
  refine ⟨62963516010899289266540369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41975677340599526177693579 62963516010899289266540369)
  ·
    refine ⟨47222637008174466949905277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62963516010899289266540369 47222637008174466949905277)
    ·
      refine ⟨17708488878065425106214479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47222637008174466949905277 17708488878065425106214479)
      ·
        refine ⟨26562733317098137659321719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17708488878065425106214479 26562733317098137659321719)
        ·
          refine ⟨39844099975647206488982579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26562733317098137659321719 39844099975647206488982579)
          ·
            refine ⟨59766149963470809733473869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39844099975647206488982579 59766149963470809733473869)
            ·
              refine ⟨22412306236301553650052701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59766149963470809733473869 22412306236301553650052701)
              ·
                refine ⟨8404614838613082618769763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22412306236301553650052701 8404614838613082618769763)
                ·
                  refine ⟨12606922257919623928154645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404614838613082618769763 12606922257919623928154645)
                  ·
                    refine ⟨590949480839982371632249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12606922257919623928154645 590949480839982371632249)
                    ·
                      rfl

theorem cell22_1726305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1726305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726305 prefixEnd_1726305 := by exact prefixLift 1726305
  have htrace : WordTrace (prefixWord ++ tailWord_1726305) baseStart_1726305 baseEnd_1726305 := by
    simpa [prefixWord, tailWord_1726305, baseEnd_1726305] using wordTrace_append hprefix tailTrace_1726305
  have hstable : (prefixWord ++ tailWord_1726305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726305).length < 2 ^ (prefixWord ++ tailWord_1726305).sum := by decide
  have hdescent : baseEnd_1726305 < baseStart_1726305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726326 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_1726326 : Nat := 118140960795 + 1726326 * 2 ^ 59
def prefixEnd_1726326 : Nat := 4983230072969 + 3 ^ 40 * 1726326 * 2
def baseEnd_1726326 : Nat := 196985556523048438952395

theorem tailTrace_1726326 : CollatzResearch.WordTrace tailWord_1726326 prefixEnd_1726326 196985556523048438952395 := by
  unfold tailWord_1726326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935267621488950615815927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41976187962548806568703221 3935267621488950615815927)
  ·
    refine ⟨5902901432233425923723891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935267621488950615815927 5902901432233425923723891)
    ·
      refine ⟨8854352148350138885585837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902901432233425923723891 8854352148350138885585837)
      ·
        refine ⟨3320382055631302082094689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8854352148350138885585837 3320382055631302082094689)
        ·
          refine ⟨2490286541723476561571017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320382055631302082094689 2490286541723476561571017)
          ·
            refine ⟨1867714906292607421178263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490286541723476561571017 1867714906292607421178263)
            ·
              refine ⟨2801572359438911131767395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867714906292607421178263 2801572359438911131767395)
              ·
                refine ⟨4202358539158366697651093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801572359438911131767395 4202358539158366697651093)
                ·
                  refine ⟨196985556523048438952395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4202358539158366697651093 196985556523048438952395)
                  ·
                    rfl

theorem cell22_1726326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_1726326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726326 prefixEnd_1726326 := by exact prefixLift 1726326
  have htrace : WordTrace (prefixWord ++ tailWord_1726326) baseStart_1726326 baseEnd_1726326 := by
    simpa [prefixWord, tailWord_1726326, baseEnd_1726326] using wordTrace_append hprefix tailTrace_1726326
  have hstable : (prefixWord ++ tailWord_1726326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726326).length < 2 ^ (prefixWord ++ tailWord_1726326).sum := by decide
  have hdescent : baseEnd_1726326 < baseStart_1726326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726358 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1726358 : Nat := 118140960795 + 1726358 * 2 ^ 59
def prefixEnd_1726358 : Nat := 4983230072969 + 3 ^ 40 * 1726358 * 2
def baseEnd_1726358 : Nat := 590967623823107900057087

theorem tailTrace_1726358 : CollatzResearch.WordTrace tailWord_1726358 prefixEnd_1726358 590967623823107900057087 := by
  unfold tailWord_1726358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935340567481704957388733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41976966053138186212146485 3935340567481704957388733)
  ·
    refine ⟨1475752712805639359020775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3935340567481704957388733 1475752712805639359020775)
    ·
      refine ⟨2213629069208459038531163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475752712805639359020775 2213629069208459038531163)
      ·
        refine ⟨3320443603812688557796745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213629069208459038531163 3320443603812688557796745)
        ·
          refine ⟨2490332702859516418347559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320443603812688557796745 2490332702859516418347559)
          ·
            refine ⟨3735499054289274627521339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490332702859516418347559 3735499054289274627521339)
            ·
              refine ⟨5603248581433911941282009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735499054289274627521339 5603248581433911941282009)
              ·
                refine ⟨4202436436075433955961507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603248581433911941282009 4202436436075433955961507)
                ·
                  refine ⟨6303654654113150933942261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202436436075433955961507 6303654654113150933942261)
                  ·
                    refine ⟨590967623823107900057087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6303654654113150933942261 590967623823107900057087)
                    ·
                      rfl

theorem cell22_1726358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1726358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726358 prefixEnd_1726358 := by exact prefixLift 1726358
  have htrace : WordTrace (prefixWord ++ tailWord_1726358) baseStart_1726358 baseEnd_1726358 := by
    simpa [prefixWord, tailWord_1726358, baseEnd_1726358] using wordTrace_append hprefix tailTrace_1726358
  have hstable : (prefixWord ++ tailWord_1726358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726358).length < 2 ^ (prefixWord ++ tailWord_1726358).sum := by decide
  have hdescent : baseEnd_1726358 < baseStart_1726358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726388 : List Nat := [2, 5, 2, 1, 3, 1, 1, 7]
def baseStart_1726388 : Nat := 118140960795 + 1726388 * 2 ^ 59
def prefixEnd_1726388 : Nat := 4983230072969 + 3 ^ 40 * 1726388 * 2
def baseEnd_1726388 : Nat := 65664210381799757978555

theorem tailTrace_1726388 : CollatzResearch.WordTrace tailWord_1726388 prefixEnd_1726388 65664210381799757978555 := by
  unfold tailWord_1726388
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483271634799297220905909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41977695513065729627874545 31483271634799297220905909)
  ·
    refine ⟨2951556715762434114459929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31483271634799297220905909 2951556715762434114459929)
    ·
      refine ⟨2213667536821825585844947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951556715762434114459929 2213667536821825585844947)
      ·
        refine ⟨3320501305232738378767421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213667536821825585844947 3320501305232738378767421)
        ·
          refine ⟨1245187989462276892037783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3320501305232738378767421 1245187989462276892037783)
          ·
            refine ⟨1867781984193415338056675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245187989462276892037783 1867781984193415338056675)
            ·
              refine ⟨2801672976290123007085013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867781984193415338056675 2801672976290123007085013)
              ·
                refine ⟨65664210381799757978555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2801672976290123007085013 65664210381799757978555)
                ·
                  rfl

theorem cell22_1726388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_1726388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726388 prefixEnd_1726388 := by exact prefixLift 1726388
  have htrace : WordTrace (prefixWord ++ tailWord_1726388) baseStart_1726388 baseEnd_1726388 := by
    simpa [prefixWord, tailWord_1726388, baseEnd_1726388] using wordTrace_append hprefix tailTrace_1726388
  have hstable : (prefixWord ++ tailWord_1726388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726388).length < 2 ^ (prefixWord ++ tailWord_1726388).sum := by decide
  have hdescent : baseEnd_1726388 < baseStart_1726388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726395 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_1726395 : Nat := 118140960795 + 1726395 * 2 ^ 59
def prefixEnd_1726395 : Nat := 4983230072969 + 3 ^ 40 * 1726395 * 2
def baseEnd_1726395 : Nat := 590980289679252136881973

theorem tailTrace_1726395 : CollatzResearch.WordTrace tailWord_1726395 prefixEnd_1726395 590980289679252136881973 := by
  unfold tailWord_1726395
  simp only [CollatzResearch.WordTrace]
  refine ⟨62966798580573234637316639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41977865720382156424877759 62966798580573234637316639)
  ·
    refine ⟨94450197870859851955974959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62966798580573234637316639 94450197870859851955974959)
    ·
      refine ⟨141675296806289777933962439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94450197870859851955974959 141675296806289777933962439)
      ·
        refine ⟨212512945209434666900943659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141675296806289777933962439 212512945209434666900943659)
        ·
          refine ⟨318769417814152000351415489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212512945209434666900943659 318769417814152000351415489)
          ·
            refine ⟨239077063360614000263561617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318769417814152000351415489 239077063360614000263561617)
            ·
              refine ⟨179307797520460500197671213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239077063360614000263561617 179307797520460500197671213)
              ·
                refine ⟨67240424070172687574126705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179307797520460500197671213 67240424070172687574126705)
                ·
                  refine ⟨50430318052629515680595029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67240424070172687574126705 50430318052629515680595029)
                  ·
                    refine ⟨590980289679252136881973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50430318052629515680595029 590980289679252136881973)
                    ·
                      rfl

theorem cell22_1726395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_1726395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726395 prefixEnd_1726395 := by exact prefixLift 1726395
  have htrace : WordTrace (prefixWord ++ tailWord_1726395) baseStart_1726395 baseEnd_1726395 := by
    simpa [prefixWord, tailWord_1726395, baseEnd_1726395] using wordTrace_append hprefix tailTrace_1726395
  have hstable : (prefixWord ++ tailWord_1726395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726395).length < 2 ^ (prefixWord ++ tailWord_1726395).sum := by decide
  have hdescent : baseEnd_1726395 < baseStart_1726395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726397 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1726397 : Nat := 118140960795 + 1726397 * 2 ^ 59
def prefixEnd_1726397 : Nat := 4983230072969 + 3 ^ 40 * 1726397 * 2
def baseEnd_1726397 : Nat := 590980974320124798331967

theorem tailTrace_1726397 : CollatzResearch.WordTrace tailWord_1726397 prefixEnd_1726397 590980974320124798331967 := by
  unfold tailWord_1726397
  simp only [CollatzResearch.WordTrace]
  refine ⟨62966871526565988978889445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41977914351043992652592963 62966871526565988978889445)
  ·
    refine ⟨11806288411231122933541771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62966871526565988978889445 11806288411231122933541771)
    ·
      refine ⟨17709432616846684400312657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11806288411231122933541771 17709432616846684400312657)
      ·
        refine ⟨13282074462635013300234493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17709432616846684400312657 13282074462635013300234493)
        ·
          refine ⟨4980777923488129987587935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13282074462635013300234493 4980777923488129987587935)
          ·
            refine ⟨7471166885232194981381903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980777923488129987587935 7471166885232194981381903)
            ·
              refine ⟨11206750327848292472072855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471166885232194981381903 11206750327848292472072855)
              ·
                refine ⟨16810125491772438708109283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206750327848292472072855 16810125491772438708109283)
                ·
                  refine ⟨25215188237658658062163925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16810125491772438708109283 25215188237658658062163925)
                  ·
                    refine ⟨590980974320124798331967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25215188237658658062163925 590980974320124798331967)
                    ·
                      rfl

theorem cell22_1726397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1726397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726397 prefixEnd_1726397 := by exact prefixLift 1726397
  have htrace : WordTrace (prefixWord ++ tailWord_1726397) baseStart_1726397 baseEnd_1726397 := by
    simpa [prefixWord, tailWord_1726397, baseEnd_1726397] using wordTrace_append hprefix tailTrace_1726397
  have hstable : (prefixWord ++ tailWord_1726397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726397).length < 2 ^ (prefixWord ++ tailWord_1726397).sum := by decide
  have hdescent : baseEnd_1726397 < baseStart_1726397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726457 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_1726457 : Nat := 118140960795 + 1726457 * 2 ^ 59
def prefixEnd_1726457 : Nat := 4983230072969 + 3 ^ 40 * 1726457 * 2
def baseEnd_1726457 : Nat := 591001513546304641831783

theorem tailTrace_1726457 : CollatzResearch.WordTrace tailWord_1726457 prefixEnd_1726457 591001513546304641831783 := by
  unfold tailWord_1726457
  simp only [CollatzResearch.WordTrace]
  refine ⟨62969059906348619226073625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41979373270899079484049083 62969059906348619226073625)
  ·
    refine ⟨47226794929761464419555219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62969059906348619226073625 47226794929761464419555219)
    ·
      refine ⟨70840192394642196629332829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47226794929761464419555219 70840192394642196629332829)
      ·
        refine ⟨26565072147990823735999811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70840192394642196629332829 26565072147990823735999811)
        ·
          refine ⟨39847608221986235603999717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26565072147990823735999811 39847608221986235603999717)
          ·
            refine ⟨7471426541622419175749947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39847608221986235603999717 7471426541622419175749947)
            ·
              refine ⟨11207139812433628763624921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471426541622419175749947 11207139812433628763624921)
              ·
                refine ⟨8405354859325221572718691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11207139812433628763624921 8405354859325221572718691)
                ·
                  refine ⟨12608032288987832359078037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8405354859325221572718691 12608032288987832359078037)
                  ·
                    refine ⟨591001513546304641831783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12608032288987832359078037 591001513546304641831783)
                    ·
                      rfl

theorem cell22_1726457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_1726457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726457 prefixEnd_1726457 := by exact prefixLift 1726457
  have htrace : WordTrace (prefixWord ++ tailWord_1726457) baseStart_1726457 baseEnd_1726457 := by
    simpa [prefixWord, tailWord_1726457, baseEnd_1726457] using wordTrace_append hprefix tailTrace_1726457
  have hstable : (prefixWord ++ tailWord_1726457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726457).length < 2 ^ (prefixWord ++ tailWord_1726457).sum := by decide
  have hdescent : baseEnd_1726457 < baseStart_1726457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726459 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 2, 3]
def baseStart_1726459 : Nat := 118140960795 + 1726459 * 2 ^ 59
def prefixEnd_1726459 : Nat := 4983230072969 + 3 ^ 40 * 1726459 * 2
def baseEnd_1726459 : Nat := 591002198187177303281777

theorem tailTrace_1726459 : CollatzResearch.WordTrace tailWord_1726459 prefixEnd_1726459 591002198187177303281777 := by
  unfold tailWord_1726459
  simp only [CollatzResearch.WordTrace]
  refine ⟨62969132852341373567646431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41979421901560915711764287 62969132852341373567646431)
  ·
    refine ⟨94453699278512060351469647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62969132852341373567646431 94453699278512060351469647)
    ·
      refine ⟨141680548917768090527204471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94453699278512060351469647 141680548917768090527204471)
      ·
        refine ⟨212520823376652135790806707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141680548917768090527204471 212520823376652135790806707)
        ·
          refine ⟨318781235064978203686210061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212520823376652135790806707 318781235064978203686210061)
          ·
            refine ⟨119542963149366826382328773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318781235064978203686210061 119542963149366826382328773)
            ·
              refine ⟨22414305590506279946686645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119542963149366826382328773 22414305590506279946686645)
              ·
                refine ⟨2101341149109963745001873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22414305590506279946686645 2101341149109963745001873)
                ·
                  refine ⟨1576005861832472808751405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2101341149109963745001873 1576005861832472808751405)
                  ·
                    refine ⟨591002198187177303281777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576005861832472808751405 591002198187177303281777)
                    ·
                      rfl

theorem cell22_1726459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 3].length) (baseStart_1726459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726459 prefixEnd_1726459 := by exact prefixLift 1726459
  have htrace : WordTrace (prefixWord ++ tailWord_1726459) baseStart_1726459 baseEnd_1726459 := by
    simpa [prefixWord, tailWord_1726459, baseEnd_1726459] using wordTrace_append hprefix tailTrace_1726459
  have hstable : (prefixWord ++ tailWord_1726459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726459).length < 2 ^ (prefixWord ++ tailWord_1726459).sum := by decide
  have hdescent : baseEnd_1726459 < baseStart_1726459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726472 : List Nat := [2, 1, 3, 2, 1, 2, 3, 8]
def baseStart_1726472 : Nat := 118140960795 + 1726472 * 2 ^ 59
def prefixEnd_1726472 : Nat := 4983230072969 + 3 ^ 40 * 1726472 * 2
def baseEnd_1726472 : Nat := 65667405372538844745193

theorem tailTrace_1726472 : CollatzResearch.WordTrace tailWord_1726472 prefixEnd_1726472 65667405372538844745193 := by
  unfold tailWord_1726472
  simp only [CollatzResearch.WordTrace]
  refine ⟨31484803500647138393934835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41979738000862851191913113 31484803500647138393934835)
  ·
    refine ⟨47227205250970707590902253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31484803500647138393934835 47227205250970707590902253)
    ·
      refine ⟨17710201969114015346588345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47227205250970707590902253 17710201969114015346588345)
      ·
        refine ⟨13282651476835511509941259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17710201969114015346588345 13282651476835511509941259)
        ·
          refine ⟨19923977215253267264911889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13282651476835511509941259 19923977215253267264911889)
          ·
            refine ⟨14942982911439950448683917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19923977215253267264911889 14942982911439950448683917)
            ·
              refine ⟨5603618591789981418256469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14942982911439950448683917 5603618591789981418256469)
              ·
                refine ⟨65667405372538844745193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5603618591789981418256469 65667405372538844745193)
                ·
                  rfl

theorem cell22_1726472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_1726472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726472 prefixEnd_1726472 := by exact prefixLift 1726472
  have htrace : WordTrace (prefixWord ++ tailWord_1726472) baseStart_1726472 baseEnd_1726472 := by
    simpa [prefixWord, tailWord_1726472, baseEnd_1726472] using wordTrace_append hprefix tailTrace_1726472
  have hstable : (prefixWord ++ tailWord_1726472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726472).length < 2 ^ (prefixWord ++ tailWord_1726472).sum := by decide
  have hdescent : baseEnd_1726472 < baseStart_1726472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726510 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1726510 : Nat := 118140960795 + 1726510 * 2 ^ 59
def prefixEnd_1726510 : Nat := 4983230072969 + 3 ^ 40 * 1726510 * 2
def baseEnd_1726510 : Nat := 591019656529430170256621

theorem tailTrace_1726510 : CollatzResearch.WordTrace tailWord_1726510 prefixEnd_1726510 591019656529430170256621 := by
  unfold tailWord_1726510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7871374121894576159719123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41980661983437739518501989 7871374121894576159719123)
  ·
    refine ⟨11807061182841864239578685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7871374121894576159719123 11807061182841864239578685)
    ·
      refine ⟨4427647943565699089842007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11807061182841864239578685 4427647943565699089842007)
      ·
        refine ⟨6641471915348548634763011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427647943565699089842007 6641471915348548634763011)
        ·
          refine ⟨9962207873022822952144517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641471915348548634763011 9962207873022822952144517)
          ·
            refine ⟨1867913976191779303527097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9962207873022822952144517 1867913976191779303527097)
            ·
              refine ⟨1400935482143834477645323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867913976191779303527097 1400935482143834477645323)
              ·
                refine ⟨2101403223215751716467985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400935482143834477645323 2101403223215751716467985)
                ·
                  refine ⟨1576052417411813787350989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2101403223215751716467985 1576052417411813787350989)
                  ·
                    refine ⟨591019656529430170256621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576052417411813787350989 591019656529430170256621)
                    ·
                      rfl

theorem cell22_1726510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1726510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726510 prefixEnd_1726510 := by exact prefixLift 1726510
  have htrace : WordTrace (prefixWord ++ tailWord_1726510) baseStart_1726510 baseEnd_1726510 := by
    simpa [prefixWord, tailWord_1726510, baseEnd_1726510] using wordTrace_append hprefix tailTrace_1726510
  have hstable : (prefixWord ++ tailWord_1726510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726510).length < 2 ^ (prefixWord ++ tailWord_1726510).sum := by decide
  have hdescent : baseEnd_1726510 < baseStart_1726510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726564 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1726564 : Nat := 118140960795 + 1726564 * 2 ^ 59
def prefixEnd_1726564 : Nat := 4983230072969 + 3 ^ 40 * 1726564 * 2
def baseEnd_1726564 : Nat := 591038141832992029406455

theorem tailTrace_1726564 : CollatzResearch.WordTrace tailWord_1726564 prefixEnd_1726564 591038141832992029406455 := by
  unfold tailWord_1726564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31486481258480488250109373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41981975011307317666812497 31486481258480488250109373)
  ·
    refine ⟨11807430471930183093791015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31486481258480488250109373 11807430471930183093791015)
    ·
      refine ⟨17711145707895274640686523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807430471930183093791015 17711145707895274640686523)
      ·
        refine ⟨26566718561842911961029785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17711145707895274640686523 26566718561842911961029785)
        ·
          refine ⟨19925038921382183970772339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26566718561842911961029785 19925038921382183970772339)
          ·
            refine ⟨29887558382073275956158509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19925038921382183970772339 29887558382073275956158509)
            ·
              refine ⟨11207834393277478483559441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29887558382073275956158509 11207834393277478483559441)
              ·
                refine ⟨8405875794958108862669581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11207834393277478483559441 8405875794958108862669581)
                ·
                  refine ⟨3152203423109290823501093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8405875794958108862669581 3152203423109290823501093)
                  ·
                    refine ⟨591038141832992029406455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152203423109290823501093 591038141832992029406455)
                    ·
                      rfl

theorem cell22_1726564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1726564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726564 prefixEnd_1726564 := by exact prefixLift 1726564
  have htrace : WordTrace (prefixWord ++ tailWord_1726564) baseStart_1726564 baseEnd_1726564 := by
    simpa [prefixWord, tailWord_1726564, baseEnd_1726564] using wordTrace_append hprefix tailTrace_1726564
  have hstable : (prefixWord ++ tailWord_1726564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726564).length < 2 ^ (prefixWord ++ tailWord_1726564).sum := by decide
  have hdescent : baseEnd_1726564 < baseStart_1726564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726626 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1726626 : Nat := 118140960795 + 1726626 * 2 ^ 59
def prefixEnd_1726626 : Nat := 4983230072969 + 3 ^ 40 * 1726626 * 2
def baseEnd_1726626 : Nat := 591059365700044534356265

theorem tailTrace_1726626 : CollatzResearch.WordTrace tailWord_1726626 prefixEnd_1726626 591059365700044534356265 := by
  unfold tailWord_1726626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743805960684090272243933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41983482561824240725983821 15743805960684090272243933)
  ·
    refine ⟨5903927235256533852091475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15743805960684090272243933 5903927235256533852091475)
    ·
      refine ⟨8855890852884800778137213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903927235256533852091475 8855890852884800778137213)
      ·
        refine ⟨3320959069831800291801455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8855890852884800778137213 3320959069831800291801455)
        ·
          refine ⟨4981438604747700437702183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320959069831800291801455 4981438604747700437702183)
          ·
            refine ⟨7472157907121550656553275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981438604747700437702183 7472157907121550656553275)
            ·
              refine ⟨11208236860682325984829913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472157907121550656553275 11208236860682325984829913)
              ·
                refine ⟨8406177645511744488622435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11208236860682325984829913 8406177645511744488622435)
                ·
                  refine ⟨12609266468267616732933653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406177645511744488622435 12609266468267616732933653)
                  ·
                    refine ⟨591059365700044534356265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12609266468267616732933653 591059365700044534356265)
                    ·
                      rfl

theorem cell22_1726626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1726626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726626 prefixEnd_1726626 := by exact prefixLift 1726626
  have htrace : WordTrace (prefixWord ++ tailWord_1726626) baseStart_1726626 baseEnd_1726626 := by
    simpa [prefixWord, tailWord_1726626, baseEnd_1726626] using wordTrace_append hprefix tailTrace_1726626
  have hstable : (prefixWord ++ tailWord_1726626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726626).length < 2 ^ (prefixWord ++ tailWord_1726626).sum := by decide
  have hdescent : baseEnd_1726626 < baseStart_1726626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726628 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1726628 : Nat := 118140960795 + 1726628 * 2 ^ 59
def prefixEnd_1726628 : Nat := 4983230072969 + 3 ^ 40 * 1726628 * 2
def baseEnd_1726628 : Nat := 591060050340917195806259

theorem tailTrace_1726628 : CollatzResearch.WordTrace tailWord_1726628 prefixEnd_1726628 591060050340917195806259 := by
  unfold tailWord_1726628
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487648394364557715274269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41983531192486076953699025 31487648394364557715274269)
  ·
    refine ⟨11807868147886709143227851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31487648394364557715274269 11807868147886709143227851)
    ·
      refine ⟨17711802221830063714841777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807868147886709143227851 17711802221830063714841777)
      ·
        refine ⟨13283851666372547786131333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17711802221830063714841777 13283851666372547786131333)
        ·
          refine ⟨2490722187444852709899625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13283851666372547786131333 2490722187444852709899625)
          ·
            refine ⟨1868041640583639532424719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490722187444852709899625 1868041640583639532424719)
            ·
              refine ⟨2802062460875459298637079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868041640583639532424719 2802062460875459298637079)
              ·
                refine ⟨4203093691313188947955619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802062460875459298637079 4203093691313188947955619)
                ·
                  refine ⟨6304640536969783421933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203093691313188947955619 6304640536969783421933429)
                  ·
                    refine ⟨591060050340917195806259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6304640536969783421933429 591060050340917195806259)
                    ·
                      rfl

theorem cell22_1726628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1726628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726628 prefixEnd_1726628 := by exact prefixLift 1726628
  have htrace : WordTrace (prefixWord ++ tailWord_1726628) baseStart_1726628 baseEnd_1726628 := by
    simpa [prefixWord, tailWord_1726628, baseEnd_1726628] using wordTrace_append hprefix tailTrace_1726628
  have hstable : (prefixWord ++ tailWord_1726628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726628).length < 2 ^ (prefixWord ++ tailWord_1726628).sum := by decide
  have hdescent : baseEnd_1726628 < baseStart_1726628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726641 : List Nat := [1, 2, 2, 5, 2, 1, 1, 8]
def baseStart_1726641 : Nat := 118140960795 + 1726641 * 2 ^ 59
def prefixEnd_1726641 : Nat := 4983230072969 + 3 ^ 40 * 1726641 * 2
def baseEnd_1726641 : Nat := 65673833389621055025691

theorem tailTrace_1726641 : CollatzResearch.WordTrace tailWord_1726641 prefixEnd_1726641 65673833389621055025691 := by
  unfold tailWord_1726641
  simp only [CollatzResearch.WordTrace]
  refine ⟨62975770937682018650771777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41983847291788012433847851 62975770937682018650771777)
  ·
    refine ⟨47231828203261513988078833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62975770937682018650771777 47231828203261513988078833)
    ·
      refine ⟨35423871152446135491059125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47231828203261513988078833 35423871152446135491059125)
      ·
        refine ⟨3320987920541825202286793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35423871152446135491059125 3320987920541825202286793)
        ·
          refine ⟨2490740940406368901715095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320987920541825202286793 2490740940406368901715095)
          ·
            refine ⟨3736111410609553352572643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490740940406368901715095 3736111410609553352572643)
            ·
              refine ⟨5604167115914330028858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736111410609553352572643 5604167115914330028858965)
              ·
                refine ⟨65673833389621055025691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5604167115914330028858965 65673833389621055025691)
                ·
                  rfl

theorem cell22_1726641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 8].length) (baseStart_1726641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726641 prefixEnd_1726641 := by exact prefixLift 1726641
  have htrace : WordTrace (prefixWord ++ tailWord_1726641) baseStart_1726641 baseEnd_1726641 := by
    simpa [prefixWord, tailWord_1726641, baseEnd_1726641] using wordTrace_append hprefix tailTrace_1726641
  have hstable : (prefixWord ++ tailWord_1726641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726641).length < 2 ^ (prefixWord ++ tailWord_1726641).sum := by decide
  have hdescent : baseEnd_1726641 < baseStart_1726641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726658 : List Nat := [3, 5, 1, 1, 1, 1, 10]
def baseStart_1726658 : Nat := 118140960795 + 1726658 * 2 ^ 59
def prefixEnd_1726658 : Nat := 4983230072969 + 3 ^ 40 * 1726658 * 2
def baseEnd_1726658 : Nat := 21891493331629893242821

theorem tailTrace_1726658 : CollatzResearch.WordTrace tailWord_1726658 prefixEnd_1726658 21891493331629893242821 := by
  unfold tailWord_1726658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744097744655107638535157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41984260652413620369427085 15744097744655107638535157)
  ·
    refine ⟨1476009163561416341112671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15744097744655107638535157 1476009163561416341112671)
    ·
      refine ⟨2214013745342124511669007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476009163561416341112671 2214013745342124511669007)
      ·
        refine ⟨3321020618013186767503511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214013745342124511669007 3321020618013186767503511)
        ·
          refine ⟨4981530927019780151255267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321020618013186767503511 4981530927019780151255267)
          ·
            refine ⟨7472296390529670226882901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981530927019780151255267 7472296390529670226882901)
            ·
              refine ⟨21891493331629893242821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7472296390529670226882901 21891493331629893242821)
              ·
                rfl

theorem cell22_1726658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 10].length) (baseStart_1726658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726658 prefixEnd_1726658 := by exact prefixLift 1726658
  have htrace : WordTrace (prefixWord ++ tailWord_1726658) baseStart_1726658 baseEnd_1726658 := by
    simpa [prefixWord, tailWord_1726658, baseEnd_1726658] using wordTrace_append hprefix tailTrace_1726658
  have hstable : (prefixWord ++ tailWord_1726658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726658).length < 2 ^ (prefixWord ++ tailWord_1726658).sum := by decide
  have hdescent : baseEnd_1726658 < baseStart_1726658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726673 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 1, 3]
def baseStart_1726673 : Nat := 118140960795 + 1726673 * 2 ^ 59
def prefixEnd_1726673 : Nat := 4983230072969 + 3 ^ 40 * 1726673 * 2
def baseEnd_1726673 : Nat := 591075454760552078431121

theorem tailTrace_1726673 : CollatzResearch.WordTrace tailWord_1726673 prefixEnd_1726673 591075454760552078431121 := by
  unfold tailWord_1726673
  simp only [CollatzResearch.WordTrace]
  refine ⟨62976938073566088115936673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41984625382377392077291115 62976938073566088115936673)
  ·
    refine ⟨47232703555174566086952505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62976938073566088115936673 47232703555174566086952505)
    ·
      refine ⟨35424527666380924565214379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47232703555174566086952505 35424527666380924565214379)
      ·
        refine ⟨53136791499571386847821569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35424527666380924565214379 53136791499571386847821569)
        ·
          refine ⟨39852593624678540135866177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53136791499571386847821569 39852593624678540135866177)
          ·
            refine ⟨29889445218508905101899633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39852593624678540135866177 29889445218508905101899633)
            ·
              refine ⟨22417083913881678826424725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29889445218508905101899633 22417083913881678826424725)
              ·
                refine ⟨1050800808463203694988659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22417083913881678826424725 1050800808463203694988659)
                ·
                  refine ⟨1576201212694805542482989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050800808463203694988659 1576201212694805542482989)
                  ·
                    refine ⟨591075454760552078431121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576201212694805542482989 591075454760552078431121)
                    ·
                      rfl

theorem cell22_1726673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_1726673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726673 prefixEnd_1726673 := by exact prefixLift 1726673
  have htrace : WordTrace (prefixWord ++ tailWord_1726673) baseStart_1726673 baseEnd_1726673 := by
    simpa [prefixWord, tailWord_1726673, baseEnd_1726673] using wordTrace_append hprefix tailTrace_1726673
  have hstable : (prefixWord ++ tailWord_1726673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726673).length < 2 ^ (prefixWord ++ tailWord_1726673).sum := by decide
  have hdescent : baseEnd_1726673 < baseStart_1726673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726724 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1726724 : Nat := 118140960795 + 1726724 * 2 ^ 59
def prefixEnd_1726724 : Nat := 4983230072969 + 3 ^ 40 * 1726724 * 2
def baseEnd_1726724 : Nat := 591092913102804945405965

theorem tailTrace_1726724 : CollatzResearch.WordTrace tailWord_1726724 prefixEnd_1726724 591092913102804945405965 := by
  unfold tailWord_1726724
  simp only [CollatzResearch.WordTrace]
  refine ⟨31489399098190661913021613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41985865464254215884028817 31489399098190661913021613)
  ·
    refine ⟨11808524661821498217383105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31489399098190661913021613 11808524661821498217383105)
    ·
      refine ⟨8856393496366123663037329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11808524661821498217383105 8856393496366123663037329)
      ·
        refine ⟨6642295122274592747277997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8856393496366123663037329 6642295122274592747277997)
        ·
          refine ⟨2490860670852972280229249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6642295122274592747277997 2490860670852972280229249)
          ·
            refine ⟨1868145503139729210171937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490860670852972280229249 1868145503139729210171937)
            ·
              refine ⟨1401109127354796907628953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868145503139729210171937 1401109127354796907628953)
              ·
                refine ⟨1050831845516097680721715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401109127354796907628953 1050831845516097680721715)
                ·
                  refine ⟨1576247768274146521082573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050831845516097680721715 1576247768274146521082573)
                  ·
                    refine ⟨591092913102804945405965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576247768274146521082573 591092913102804945405965)
                    ·
                      rfl

theorem cell22_1726724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1726724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726724 prefixEnd_1726724 := by exact prefixLift 1726724
  have htrace : WordTrace (prefixWord ++ tailWord_1726724) baseStart_1726724 baseEnd_1726724 := by
    simpa [prefixWord, tailWord_1726724, baseEnd_1726724] using wordTrace_append hprefix tailTrace_1726724
  have hstable : (prefixWord ++ tailWord_1726724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726724).length < 2 ^ (prefixWord ++ tailWord_1726724).sum := by decide
  have hdescent : baseEnd_1726724 < baseStart_1726724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726750 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1726750 : Nat := 118140960795 + 1726750 * 2 ^ 59
def prefixEnd_1726750 : Nat := 4983230072969 + 3 ^ 40 * 1726750 * 2
def baseEnd_1726750 : Nat := 591101813434149544255885

theorem tailTrace_1726750 : CollatzResearch.WordTrace tailWord_1726750 prefixEnd_1726750 591101813434149544255885 := by
  unfold tailWord_1726750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7872468311785891283311213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41986497662858086844326469 7872468311785891283311213)
  ·
    refine ⟨2952175616919709231241705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7872468311785891283311213 2952175616919709231241705)
    ·
      refine ⟨2214131712689781923431279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2952175616919709231241705 2214131712689781923431279)
      ·
        refine ⟨3321197569034672885146919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214131712689781923431279 3321197569034672885146919)
        ·
          refine ⟨4981796353552009327720379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321197569034672885146919 4981796353552009327720379)
          ·
            refine ⟨7472694530328013991580569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981796353552009327720379 7472694530328013991580569)
            ·
              refine ⟨5604520897746010493685427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472694530328013991580569 5604520897746010493685427)
              ·
                refine ⟨8406781346619015740528141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604520897746010493685427 8406781346619015740528141)
                ·
                  refine ⟨3152543004982130902698053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8406781346619015740528141 3152543004982130902698053)
                  ·
                    refine ⟨591101813434149544255885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152543004982130902698053 591101813434149544255885)
                    ·
                      rfl

theorem cell22_1726750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1726750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726750 prefixEnd_1726750 := by exact prefixLift 1726750
  have htrace : WordTrace (prefixWord ++ tailWord_1726750) baseStart_1726750 baseEnd_1726750 := by
    simpa [prefixWord, tailWord_1726750, baseEnd_1726750] using wordTrace_append hprefix tailTrace_1726750
  have hstable : (prefixWord ++ tailWord_1726750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726750).length < 2 ^ (prefixWord ++ tailWord_1726750).sum := by decide
  have hdescent : baseEnd_1726750 < baseStart_1726750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726821 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 7]
def baseStart_1726821 : Nat := 118140960795 + 1726821 * 2 ^ 59
def prefixEnd_1726821 : Nat := 4983230072969 + 3 ^ 40 * 1726821 * 2
def baseEnd_1726821 : Nat := 197042039395043008576889

theorem tailTrace_1726821 : CollatzResearch.WordTrace tailWord_1726821 prefixEnd_1726821 197042039395043008576889 := by
  unfold tailWord_1726821
  simp only [CollatzResearch.WordTrace]
  refine ⟨62982336077029909392324317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41988224051353272928216211 62982336077029909392324317)
  ·
    refine ⟨23618376028886216022121619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62982336077029909392324317 23618376028886216022121619)
    ·
      refine ⟨35427564043329324033182429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23618376028886216022121619 35427564043329324033182429)
      ·
        refine ⟨13285336516248496512443411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35427564043329324033182429 13285336516248496512443411)
        ·
          refine ⟨19928004774372744768665117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13285336516248496512443411 19928004774372744768665117)
          ·
            refine ⟨7473001790389779288249419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19928004774372744768665117 7473001790389779288249419)
            ·
              refine ⟨11209502685584668932374129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473001790389779288249419 11209502685584668932374129)
              ·
                refine ⟨8407127014188501699280597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209502685584668932374129 8407127014188501699280597)
                ·
                  refine ⟨197042039395043008576889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8407127014188501699280597 197042039395043008576889)
                  ·
                    rfl

theorem cell22_1726821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_1726821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726821 prefixEnd_1726821 := by exact prefixLift 1726821
  have htrace : WordTrace (prefixWord ++ tailWord_1726821) baseStart_1726821 baseEnd_1726821 := by
    simpa [prefixWord, tailWord_1726821, baseEnd_1726821] using wordTrace_append hprefix tailTrace_1726821
  have hstable : (prefixWord ++ tailWord_1726821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726821).length < 2 ^ (prefixWord ++ tailWord_1726821).sum := by decide
  have hdescent : baseEnd_1726821 < baseStart_1726821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726885 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_1726885 : Nat := 118140960795 + 1726885 * 2 ^ 59
def prefixEnd_1726885 : Nat := 4983230072969 + 3 ^ 40 * 1726885 * 2
def baseEnd_1726885 : Nat := 591148026693054192130471

theorem tailTrace_1726885 : CollatzResearch.WordTrace tailWord_1726885 prefixEnd_1726885 591148026693054192130471 := by
  unfold tailWord_1726885
  simp only [CollatzResearch.WordTrace]
  refine ⟨62984670348798048322654109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41989780232532032215102739 62984670348798048322654109)
  ·
    refine ⟨23619251380799268120995291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62984670348798048322654109 23619251380799268120995291)
    ·
      refine ⟨35428877071198902181492937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23619251380799268120995291 35428877071198902181492937)
      ·
        refine ⟨26571657803399176636119703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35428877071198902181492937 26571657803399176636119703)
        ·
          refine ⟨39857486705098764954179555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26571657803399176636119703 39857486705098764954179555)
          ·
            refine ⟨59786230057648147431269333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39857486705098764954179555 59786230057648147431269333)
            ·
              refine ⟨1401239766976128455420375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59786230057648147431269333 1401239766976128455420375)
              ·
                refine ⟨2101859650464192683130563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401239766976128455420375 2101859650464192683130563)
                ·
                  refine ⟨3152789475696289024695845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101859650464192683130563 3152789475696289024695845)
                  ·
                    refine ⟨591148026693054192130471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152789475696289024695845 591148026693054192130471)
                    ·
                      rfl

theorem cell22_1726885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_1726885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726885 prefixEnd_1726885 := by exact prefixLift 1726885
  have htrace : WordTrace (prefixWord ++ tailWord_1726885) baseStart_1726885 baseEnd_1726885 := by
    simpa [prefixWord, tailWord_1726885, baseEnd_1726885] using wordTrace_append hprefix tailTrace_1726885
  have hstable : (prefixWord ++ tailWord_1726885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726885).length < 2 ^ (prefixWord ++ tailWord_1726885).sum := by decide
  have hdescent : baseEnd_1726885 < baseStart_1726885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726893 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1726893 : Nat := 118140960795 + 1726893 * 2 ^ 59
def prefixEnd_1726893 : Nat := 4983230072969 + 3 ^ 40 * 1726893 * 2
def baseEnd_1726893 : Nat := 591150765256544837930447

theorem tailTrace_1726893 : CollatzResearch.WordTrace tailWord_1726893 prefixEnd_1726893 591150765256544837930447 := by
  unfold tailWord_1726893
  simp only [CollatzResearch.WordTrace]
  refine ⟨62984962132769065688945333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41989974755179377125963555 62984962132769065688945333)
  ·
    refine ⟨5904840199947099908338625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62984962132769065688945333 5904840199947099908338625)
    ·
      refine ⟨4428630149960324931253969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5904840199947099908338625 4428630149960324931253969)
      ·
        refine ⟨3321472612470243698440477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4428630149960324931253969 3321472612470243698440477)
        ·
          refine ⟨1245552229676341386915179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3321472612470243698440477 1245552229676341386915179)
          ·
            refine ⟨1868328344514512080372769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245552229676341386915179 1868328344514512080372769)
            ·
              refine ⟨1401246258385884060279577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868328344514512080372769 1401246258385884060279577)
              ·
                refine ⟨1050934693789413045209683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401246258385884060279577 1050934693789413045209683)
                ·
                  refine ⟨1576402040684119567814525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050934693789413045209683 1576402040684119567814525)
                  ·
                    refine ⟨591150765256544837930447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576402040684119567814525 591150765256544837930447)
                    ·
                      rfl

theorem cell22_1726893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1726893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726893 prefixEnd_1726893 := by exact prefixLift 1726893
  have htrace : WordTrace (prefixWord ++ tailWord_1726893) baseStart_1726893 baseEnd_1726893 := by
    simpa [prefixWord, tailWord_1726893, baseEnd_1726893] using wordTrace_append hprefix tailTrace_1726893
  have hstable : (prefixWord ++ tailWord_1726893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726893).length < 2 ^ (prefixWord ++ tailWord_1726893).sum := by decide
  have hdescent : baseEnd_1726893 < baseStart_1726893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726949 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_1726949 : Nat := 118140960795 + 1726949 * 2 ^ 59
def prefixEnd_1726949 : Nat := 4983230072969 + 3 ^ 40 * 1726949 * 2
def baseEnd_1726949 : Nat := 591169935200979358530275

theorem tailTrace_1726949 : CollatzResearch.WordTrace tailWord_1726949 prefixEnd_1726949 591169935200979358530275 := by
  unfold tailWord_1726949
  simp only [CollatzResearch.WordTrace]
  refine ⟨62987004620566187252983901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41991336413710791501989267 62987004620566187252983901)
  ·
    refine ⟨23620126732712320219868963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62987004620566187252983901 23620126732712320219868963)
    ·
      refine ⟨35430190099068480329803445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23620126732712320219868963 35430190099068480329803445)
      ·
        refine ⟨3321580321787670030919073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35430190099068480329803445 3321580321787670030919073)
        ·
          refine ⟨2491185241340752523189305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3321580321787670030919073 2491185241340752523189305)
          ·
            refine ⟨1868388931005564392391979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491185241340752523189305 1868388931005564392391979)
            ·
              refine ⟨2802583396508346588587969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868388931005564392391979 2802583396508346588587969)
              ·
                refine ⟨2101937547381259941440977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802583396508346588587969 2101937547381259941440977)
                ·
                  refine ⟨1576453160535944956080733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2101937547381259941440977 1576453160535944956080733)
                  ·
                    refine ⟨591169935200979358530275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576453160535944956080733 591169935200979358530275)
                    ·
                      rfl

theorem cell22_1726949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_1726949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726949 prefixEnd_1726949 := by exact prefixLift 1726949
  have htrace : WordTrace (prefixWord ++ tailWord_1726949) baseStart_1726949 baseEnd_1726949 := by
    simpa [prefixWord, tailWord_1726949, baseEnd_1726949] using wordTrace_append hprefix tailTrace_1726949
  have hstable : (prefixWord ++ tailWord_1726949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726949).length < 2 ^ (prefixWord ++ tailWord_1726949).sum := by decide
  have hdescent : baseEnd_1726949 < baseStart_1726949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726960 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_1726960 : Nat := 118140960795 + 1726960 * 2 ^ 59
def prefixEnd_1726960 : Nat := 4983230072969 + 3 ^ 40 * 1726960 * 2
def baseEnd_1726960 : Nat := 591173700725778996505241

theorem tailTrace_1726960 : CollatzResearch.WordTrace tailWord_1726960 prefixEnd_1726960 591173700725778996505241 := by
  unfold tailWord_1726960
  simp only [CollatzResearch.WordTrace]
  refine ⟨31493702911763168065817167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41991603882350890754422889 31493702911763168065817167)
  ·
    refine ⟨47240554367644752098725751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31493702911763168065817167 47240554367644752098725751)
    ·
      refine ⟨70860831551467128148088627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47240554367644752098725751 70860831551467128148088627)
      ·
        refine ⟨106291247327200692222132941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70860831551467128148088627 106291247327200692222132941)
        ·
          refine ⟨39859217747700259583299853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106291247327200692222132941 39859217747700259583299853)
          ·
            refine ⟨14947206655387597343737445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39859217747700259583299853 14947206655387597343737445)
            ·
              refine ⟨2802601247885174501950771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14947206655387597343737445 2802601247885174501950771)
              ·
                refine ⟨4203901871827761752926157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802601247885174501950771 4203901871827761752926157)
                ·
                  refine ⟨1576463201935410657347309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4203901871827761752926157 1576463201935410657347309)
                  ·
                    refine ⟨591173700725778996505241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576463201935410657347309 591173700725778996505241)
                    ·
                      rfl

theorem cell22_1726960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_1726960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1726960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1726960 prefixEnd_1726960 := by exact prefixLift 1726960
  have htrace : WordTrace (prefixWord ++ tailWord_1726960) baseStart_1726960 baseEnd_1726960 := by
    simpa [prefixWord, tailWord_1726960, baseEnd_1726960] using wordTrace_append hprefix tailTrace_1726960
  have hstable : (prefixWord ++ tailWord_1726960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726960).length < 2 ^ (prefixWord ++ tailWord_1726960).sum := by decide
  have hdescent : baseEnd_1726960 < baseStart_1726960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727037 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1727037 : Nat := 118140960795 + 1727037 * 2 ^ 59
def prefixEnd_1727037 : Nat := 4983230072969 + 3 ^ 40 * 1727037 * 2
def baseEnd_1727037 : Nat := 591200059399376462330005

theorem tailTrace_1727037 : CollatzResearch.WordTrace tailWord_1727037 prefixEnd_1727037 591200059399376462330005 := by
  unfold tailWord_1727037
  simp only [CollatzResearch.WordTrace]
  refine ⟨62990214244247378282187365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41993476162831585521458243 62990214244247378282187365)
  ·
    refine ⟨11810665170796383427910131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62990214244247378282187365 11810665170796383427910131)
    ·
      refine ⟨17715997756194575141865197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11810665170796383427910131 17715997756194575141865197)
      ·
        refine ⟨6643499158572965678199449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17715997756194575141865197 6643499158572965678199449)
        ·
          refine ⟨4982624368929724258649587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6643499158572965678199449 4982624368929724258649587)
          ·
            refine ⟨7473936553394586387974381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982624368929724258649587 7473936553394586387974381)
            ·
              refine ⟨2802726207522969895490393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7473936553394586387974381 2802726207522969895490393)
              ·
                refine ⟨2102044655642227421617795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802726207522969895490393 2102044655642227421617795)
                ·
                  refine ⟨3153066983463341132426693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102044655642227421617795 3153066983463341132426693)
                  ·
                    refine ⟨591200059399376462330005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153066983463341132426693 591200059399376462330005)
                    ·
                      rfl

theorem cell22_1727037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1727037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727037 prefixEnd_1727037 := by exact prefixLift 1727037
  have htrace : WordTrace (prefixWord ++ tailWord_1727037) baseStart_1727037 baseEnd_1727037 := by
    simpa [prefixWord, tailWord_1727037, baseEnd_1727037] using wordTrace_append hprefix tailTrace_1727037
  have hstable : (prefixWord ++ tailWord_1727037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727037).length < 2 ^ (prefixWord ++ tailWord_1727037).sum := by decide
  have hdescent : baseEnd_1727037 < baseStart_1727037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727048 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1727048 : Nat := 118140960795 + 1727048 * 2 ^ 59
def prefixEnd_1727048 : Nat := 4983230072969 + 3 ^ 40 * 1727048 * 2
def baseEnd_1727048 : Nat := 591203824924176100304971

theorem tailTrace_1727048 : CollatzResearch.WordTrace tailWord_1727048 prefixEnd_1727048 591203824924176100304971 := by
  unfold tailWord_1727048
  simp only [CollatzResearch.WordTrace]
  refine ⟨31495307723603763580418899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41993743631471684773891865 31495307723603763580418899)
  ·
    refine ⟨47242961585405645370628349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31495307723603763580418899 47242961585405645370628349)
    ·
      refine ⟨17716110594527117013985631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47242961585405645370628349 17716110594527117013985631)
      ·
        refine ⟨26574165891790675520978447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17716110594527117013985631 26574165891790675520978447)
        ·
          refine ⟨39861248837686013281467671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26574165891790675520978447 39861248837686013281467671)
          ·
            refine ⟨59791873256529019922201507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39861248837686013281467671 59791873256529019922201507)
            ·
              refine ⟨89687809884793529883302261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59791873256529019922201507 89687809884793529883302261)
              ·
                refine ⟨8408232176699393426559587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89687809884793529883302261 8408232176699393426559587)
                ·
                  refine ⟨12612348265049090139839381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8408232176699393426559587 12612348265049090139839381)
                  ·
                    refine ⟨591203824924176100304971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12612348265049090139839381 591203824924176100304971)
                    ·
                      rfl

theorem cell22_1727048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1727048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727048 prefixEnd_1727048 := by exact prefixLift 1727048
  have htrace : WordTrace (prefixWord ++ tailWord_1727048) baseStart_1727048 baseEnd_1727048 := by
    simpa [prefixWord, tailWord_1727048, baseEnd_1727048] using wordTrace_append hprefix tailTrace_1727048
  have hstable : (prefixWord ++ tailWord_1727048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727048).length < 2 ^ (prefixWord ++ tailWord_1727048).sum := by decide
  have hdescent : baseEnd_1727048 < baseStart_1727048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727050 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1727050 : Nat := 118140960795 + 1727050 * 2 ^ 59
def prefixEnd_1727050 : Nat := 4983230072969 + 3 ^ 40 * 1727050 * 2
def baseEnd_1727050 : Nat := 591204509565048761754965

theorem tailTrace_1727050 : CollatzResearch.WordTrace tailWord_1727050 prefixEnd_1727050 591204509565048761754965 := by
  unfold tailWord_1727050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15747672098300070375602651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41993792262133521001607069 15747672098300070375602651)
  ·
    refine ⟨23621508147450105563403977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15747672098300070375602651 23621508147450105563403977)
    ·
      refine ⟨17716131110587579172552983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23621508147450105563403977 17716131110587579172552983)
      ·
        refine ⟨26574196665881368758829475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17716131110587579172552983 26574196665881368758829475)
        ·
          refine ⟨39861294998822053138244213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26574196665881368758829475 39861294998822053138244213)
          ·
            refine ⟨3736996406139567481710395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39861294998822053138244213 3736996406139567481710395)
            ·
              refine ⟨5605494609209351222565593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736996406139567481710395 5605494609209351222565593)
              ·
                refine ⟨4204120956907013416924195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605494609209351222565593 4204120956907013416924195)
                ·
                  refine ⟨6306181435360520125386293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204120956907013416924195 6306181435360520125386293)
                  ·
                    refine ⟨591204509565048761754965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6306181435360520125386293 591204509565048761754965)
                    ·
                      rfl

theorem cell22_1727050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1727050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727050 prefixEnd_1727050 := by exact prefixLift 1727050
  have htrace : WordTrace (prefixWord ++ tailWord_1727050) baseStart_1727050 baseEnd_1727050 := by
    simpa [prefixWord, tailWord_1727050, baseEnd_1727050] using wordTrace_append hprefix tailTrace_1727050
  have hstable : (prefixWord ++ tailWord_1727050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727050).length < 2 ^ (prefixWord ++ tailWord_1727050).sum := by decide
  have hdescent : baseEnd_1727050 < baseStart_1727050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727095 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 5, 3]
def baseStart_1727095 : Nat := 118140960795 + 1727095 * 2 ^ 59
def prefixEnd_1727095 : Nat := 4983230072969 + 3 ^ 40 * 1727095 * 2
def baseEnd_1727095 : Nat := 591219913984683644379827

theorem tailTrace_1727095 : CollatzResearch.WordTrace tailWord_1727095 prefixEnd_1727095 591219913984683644379827 := by
  unfold tailWord_1727095
  simp only [CollatzResearch.WordTrace]
  refine ⟨62992329678037254187798739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41994886452024836125199159 62992329678037254187798739)
  ·
    refine ⟨94488494517055881281698109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62992329678037254187798739 94488494517055881281698109)
    ·
      refine ⟨35433185443895955480636791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94488494517055881281698109 35433185443895955480636791)
      ·
        refine ⟨53149778165843933220955187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35433185443895955480636791 53149778165843933220955187)
        ·
          refine ⟨79724667248765899831432781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53149778165843933220955187 79724667248765899831432781)
          ·
            refine ⟨29896750218287212436787293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79724667248765899831432781 29896750218287212436787293)
            ·
              refine ⟨11211281331857704663795235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29896750218287212436787293 11211281331857704663795235)
              ·
                refine ⟨16816921997786556995692853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11211281331857704663795235 16816921997786556995692853)
                ·
                  refine ⟨1576586437292489718346205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16816921997786556995692853 1576586437292489718346205)
                  ·
                    refine ⟨591219913984683644379827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576586437292489718346205 591219913984683644379827)
                    ·
                      rfl

theorem cell22_1727095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_1727095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727095 prefixEnd_1727095 := by exact prefixLift 1727095
  have htrace : WordTrace (prefixWord ++ tailWord_1727095) baseStart_1727095 baseEnd_1727095 := by
    simpa [prefixWord, tailWord_1727095, baseEnd_1727095] using wordTrace_append hprefix tailTrace_1727095
  have hstable : (prefixWord ++ tailWord_1727095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727095).length < 2 ^ (prefixWord ++ tailWord_1727095).sum := by decide
  have hdescent : baseEnd_1727095 < baseStart_1727095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727123 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_1727123 : Nat := 118140960795 + 1727123 * 2 ^ 59
def prefixEnd_1727123 : Nat := 4983230072969 + 3 ^ 40 * 1727123 * 2
def baseEnd_1727123 : Nat := 591229498956900904679741

theorem tailTrace_1727123 : CollatzResearch.WordTrace tailWord_1727123 prefixEnd_1727123 591229498956900904679741 := by
  unfold tailWord_1727123
  simp only [CollatzResearch.WordTrace]
  refine ⟨62993350921935814969818023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41995567281290543313212015 62993350921935814969818023)
  ·
    refine ⟨94490026382903722454727035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62993350921935814969818023 94490026382903722454727035)
    ·
      refine ⟨141735039574355583682090553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94490026382903722454727035 141735039574355583682090553)
      ·
        refine ⟨106301279680766687761567915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141735039574355583682090553 106301279680766687761567915)
        ·
          refine ⟨159451919521150031642351873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106301279680766687761567915 159451919521150031642351873)
          ·
            refine ⟨119588939640862523731763905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159451919521150031642351873 119588939640862523731763905)
            ·
              refine ⟨89691704730646892798822929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119588939640862523731763905 89691704730646892798822929)
              ·
                refine ⟨67268778547985169599117197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89691704730646892798822929 67268778547985169599117197)
                ·
                  refine ⟨25225791955494438599668949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67268778547985169599117197 25225791955494438599668949)
                  ·
                    refine ⟨591229498956900904679741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25225791955494438599668949 591229498956900904679741)
                    ·
                      rfl

theorem cell22_1727123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_1727123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727123 prefixEnd_1727123 := by exact prefixLift 1727123
  have htrace : WordTrace (prefixWord ++ tailWord_1727123) baseStart_1727123 baseEnd_1727123 := by
    simpa [prefixWord, tailWord_1727123, baseEnd_1727123] using wordTrace_append hprefix tailTrace_1727123
  have hstable : (prefixWord ++ tailWord_1727123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727123).length < 2 ^ (prefixWord ++ tailWord_1727123).sum := by decide
  have hdescent : baseEnd_1727123 < baseStart_1727123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727140 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1727140 : Nat := 118140960795 + 1727140 * 2 ^ 59
def prefixEnd_1727140 : Nat := 4983230072969 + 3 ^ 40 * 1727140 * 2
def baseEnd_1727140 : Nat := 591235318404318527004689

theorem tailTrace_1727140 : CollatzResearch.WordTrace tailWord_1727140 prefixEnd_1727140 591235318404318527004689 := by
  unfold tailWord_1727140
  simp only [CollatzResearch.WordTrace]
  refine ⟨31496985481437113436593437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41995980641916151248791249 31496985481437113436593437)
  ·
    refine ⟨11811369555538917538722539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31496985481437113436593437 11811369555538917538722539)
    ·
      refine ⟨17717054333308376308083809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11811369555538917538722539 17717054333308376308083809)
      ·
        refine ⟨13287790749981282231062857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17717054333308376308083809 13287790749981282231062857)
        ·
          refine ⟨9965843062485961673297143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13287790749981282231062857 9965843062485961673297143)
          ·
            refine ⟨14948764593728942509945715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9965843062485961673297143 14948764593728942509945715)
            ·
              refine ⟨22423146890593413764918573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14948764593728942509945715 22423146890593413764918573)
              ·
                refine ⟨8408680083972530161844465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22423146890593413764918573 8408680083972530161844465)
                ·
                  refine ⟨6306510062979397621383349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8408680083972530161844465 6306510062979397621383349)
                  ·
                    refine ⟨591235318404318527004689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6306510062979397621383349 591235318404318527004689)
                    ·
                      rfl

theorem cell22_1727140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1727140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727140 prefixEnd_1727140 := by exact prefixLift 1727140
  have htrace : WordTrace (prefixWord ++ tailWord_1727140) baseStart_1727140 baseEnd_1727140 := by
    simpa [prefixWord, tailWord_1727140, baseEnd_1727140] using wordTrace_append hprefix tailTrace_1727140
  have hstable : (prefixWord ++ tailWord_1727140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727140).length < 2 ^ (prefixWord ++ tailWord_1727140).sum := by decide
  have hdescent : baseEnd_1727140 < baseStart_1727140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727200 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_1727200 : Nat := 118140960795 + 1727200 * 2 ^ 59
def prefixEnd_1727200 : Nat := 4983230072969 + 3 ^ 40 * 1727200 * 2
def baseEnd_1727200 : Nat := 591255857630498370504505

theorem tailTrace_1727200 : CollatzResearch.WordTrace tailWord_1727200 prefixEnd_1727200 591255857630498370504505 := by
  unfold tailWord_1727200
  simp only [CollatzResearch.WordTrace]
  refine ⟨31498079671328428560185527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41997439561771238080247369 31498079671328428560185527)
  ·
    refine ⟨47247119506992642840278291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31498079671328428560185527 47247119506992642840278291)
    ·
      refine ⟨70870679260488964260417437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47247119506992642840278291 70870679260488964260417437)
      ·
        refine ⟨26576504722683361597656539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70870679260488964260417437 26576504722683361597656539)
        ·
          refine ⟨39864757084025042396484809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26576504722683361597656539 39864757084025042396484809)
          ·
            refine ⟨29898567813018781797363607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39864757084025042396484809 29898567813018781797363607)
            ·
              refine ⟨44847851719528172696045411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29898567813018781797363607 44847851719528172696045411)
              ·
                refine ⟨67271777579292259044068117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44847851719528172696045411 67271777579292259044068117)
                ·
                  refine ⟨3153364574029324642690693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67271777579292259044068117 3153364574029324642690693)
                  ·
                    refine ⟨591255857630498370504505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153364574029324642690693 591255857630498370504505)
                    ·
                      rfl

theorem cell22_1727200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_1727200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727200 prefixEnd_1727200 := by exact prefixLift 1727200
  have htrace : WordTrace (prefixWord ++ tailWord_1727200) baseStart_1727200 baseEnd_1727200 := by
    simpa [prefixWord, tailWord_1727200, baseEnd_1727200] using wordTrace_append hprefix tailTrace_1727200
  have hstable : (prefixWord ++ tailWord_1727200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727200).length < 2 ^ (prefixWord ++ tailWord_1727200).sum := by decide
  have hdescent : baseEnd_1727200 < baseStart_1727200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727215 : List Nat := [1, 1, 2, 1, 5, 2, 2, 8]
def baseStart_1727215 : Nat := 118140960795 + 1727215 * 2 ^ 59
def prefixEnd_1727215 : Nat := 4983230072969 + 3 ^ 40 * 1727215 * 2
def baseEnd_1727215 : Nat := 65695665826338147931051

theorem tailTrace_1727215 : CollatzResearch.WordTrace tailWord_1727215 prefixEnd_1727215 65695665826338147931051 := by
  unfold tailWord_1727215
  simp only [CollatzResearch.WordTrace]
  refine ⟨62996706437602514682167099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41997804291735009788111399 62996706437602514682167099)
  ·
    refine ⟨94495059656403772023250649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62996706437602514682167099 94495059656403772023250649)
    ·
      refine ⟨70871294742302829017437987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94495059656403772023250649 70871294742302829017437987)
      ·
        refine ⟨106306942113454243526156981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70871294742302829017437987 106306942113454243526156981)
        ·
          refine ⟨9966275823136335330577217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106306942113454243526156981 9966275823136335330577217)
          ·
            refine ⟨7474706867352251497932913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9966275823136335330577217 7474706867352251497932913)
            ·
              refine ⟨5606030150514188623449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7474706867352251497932913 5606030150514188623449685)
              ·
                refine ⟨65695665826338147931051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5606030150514188623449685 65695665826338147931051)
                ·
                  rfl

theorem cell22_1727215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 8].length) (baseStart_1727215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727215 prefixEnd_1727215 := by exact prefixLift 1727215
  have htrace : WordTrace (prefixWord ++ tailWord_1727215) baseStart_1727215 baseEnd_1727215 := by
    simpa [prefixWord, tailWord_1727215, baseEnd_1727215] using wordTrace_append hprefix tailTrace_1727215
  have hstable : (prefixWord ++ tailWord_1727215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727215).length < 2 ^ (prefixWord ++ tailWord_1727215).sum := by decide
  have hdescent : baseEnd_1727215 < baseStart_1727215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727217 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1727217 : Nat := 118140960795 + 1727217 * 2 ^ 59
def prefixEnd_1727217 : Nat := 4983230072969 + 3 ^ 40 * 1727217 * 2
def baseEnd_1727217 : Nat := 591261677077915992829453

theorem tailTrace_1727217 : CollatzResearch.WordTrace tailWord_1727217 prefixEnd_1727217 591261677077915992829453 := by
  unfold tailWord_1727217
  simp only [CollatzResearch.WordTrace]
  refine ⟨62996779383595269023739905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41997852922396846015826603 62996779383595269023739905)
  ·
    refine ⟨47247584537696451767804929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62996779383595269023739905 47247584537696451767804929)
    ·
      refine ⟨35435688403272338825853697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47247584537696451767804929 35435688403272338825853697)
      ·
        refine ⟨26576766302454254119390273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35435688403272338825853697 26576766302454254119390273)
        ·
          refine ⟨19932574726840690589542705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26576766302454254119390273 19932574726840690589542705)
          ·
            refine ⟨14949431045130517942157029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19932574726840690589542705 14949431045130517942157029)
            ·
              refine ⟨2803018320961972114154443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14949431045130517942157029 2803018320961972114154443)
              ·
                refine ⟨4204527481442958171231665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803018320961972114154443 4204527481442958171231665)
                ·
                  refine ⟨3153395611082218628423749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204527481442958171231665 3153395611082218628423749)
                  ·
                    refine ⟨591261677077915992829453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153395611082218628423749 591261677077915992829453)
                    ·
                      rfl

theorem cell22_1727217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1727217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727217 prefixEnd_1727217 := by exact prefixLift 1727217
  have htrace : WordTrace (prefixWord ++ tailWord_1727217) baseStart_1727217 baseEnd_1727217 := by
    simpa [prefixWord, tailWord_1727217, baseEnd_1727217] using wordTrace_append hprefix tailTrace_1727217
  have hstable : (prefixWord ++ tailWord_1727217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727217).length < 2 ^ (prefixWord ++ tailWord_1727217).sum := by decide
  have hdescent : baseEnd_1727217 < baseStart_1727217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727234 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1727234 : Nat := 118140960795 + 1727234 * 2 ^ 59
def prefixEnd_1727234 : Nat := 4983230072969 + 3 ^ 40 * 1727234 * 2
def baseEnd_1727234 : Nat := 591267496525333615154401

theorem tailTrace_1727234 : CollatzResearch.WordTrace tailWord_1727234 prefixEnd_1727234 591267496525333615154401 := by
  unfold tailWord_1727234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749349856133420231777189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41998266283022453951405837 15749349856133420231777189)
  ·
    refine ⟨2953003098025016293458223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15749349856133420231777189 2953003098025016293458223)
    ·
      refine ⟨4429504647037524440187335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2953003098025016293458223 4429504647037524440187335)
      ·
        refine ⟨6644256970556286660281003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4429504647037524440187335 6644256970556286660281003)
        ·
          refine ⟨9966385455834429990421505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644256970556286660281003 9966385455834429990421505)
          ·
            refine ⟨7474789091875822492816129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9966385455834429990421505 7474789091875822492816129)
            ·
              refine ⟨5606091818906866869612097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7474789091875822492816129 5606091818906866869612097)
              ·
                refine ⟨4204568864180150152209073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606091818906866869612097 4204568864180150152209073)
                ·
                  refine ⟨3153426648135112614156805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204568864180150152209073 3153426648135112614156805)
                  ·
                    refine ⟨591267496525333615154401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153426648135112614156805 591267496525333615154401)
                    ·
                      rfl

theorem cell22_1727234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1727234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727234 prefixEnd_1727234 := by exact prefixLift 1727234
  have htrace : WordTrace (prefixWord ++ tailWord_1727234) baseStart_1727234 baseEnd_1727234 := by
    simpa [prefixWord, tailWord_1727234, baseEnd_1727234] using wordTrace_append hprefix tailTrace_1727234
  have hstable : (prefixWord ++ tailWord_1727234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727234).length < 2 ^ (prefixWord ++ tailWord_1727234).sum := by decide
  have hdescent : baseEnd_1727234 < baseStart_1727234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727247 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 3, 3]
def baseStart_1727247 : Nat := 118140960795 + 1727247 * 2 ^ 59
def prefixEnd_1727247 : Nat := 4983230072969 + 3 ^ 40 * 1727247 * 2
def baseEnd_1727247 : Nat := 591271946691005914579361

theorem tailTrace_1727247 : CollatzResearch.WordTrace tailWord_1727247 prefixEnd_1727247 591271946691005914579361 := by
  unfold tailWord_1727247
  simp only [CollatzResearch.WordTrace]
  refine ⟨62997873573486584147331995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41998582382324389431554663 62997873573486584147331995)
  ·
    refine ⟨94496810360229876220997993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62997873573486584147331995 94496810360229876220997993)
    ·
      refine ⟨70872607770172407165748495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94496810360229876220997993 70872607770172407165748495)
      ·
        refine ⟨106308911655258610748622743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70872607770172407165748495 106308911655258610748622743)
        ·
          refine ⟨159463367482887916122934115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106308911655258610748622743 159463367482887916122934115)
          ·
            refine ⟨239195051224331874184401173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159463367482887916122934115 239195051224331874184401173)
            ·
              refine ⟨11212268026140556602393805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239195051224331874184401173 11212268026140556602393805)
              ·
                refine ⟨4204600509802708725897677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11212268026140556602393805 4204600509802708725897677)
                ·
                  refine ⟨1576725191176015772211629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4204600509802708725897677 1576725191176015772211629)
                  ·
                    refine ⟨591271946691005914579361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576725191176015772211629 591271946691005914579361)
                    ·
                      rfl

theorem cell22_1727247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_1727247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727247 prefixEnd_1727247 := by exact prefixLift 1727247
  have htrace : WordTrace (prefixWord ++ tailWord_1727247) baseStart_1727247 baseEnd_1727247 := by
    simpa [prefixWord, tailWord_1727247, baseEnd_1727247] using wordTrace_append hprefix tailTrace_1727247
  have hstable : (prefixWord ++ tailWord_1727247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727247).length < 2 ^ (prefixWord ++ tailWord_1727247).sum := by decide
  have hdescent : baseEnd_1727247 < baseStart_1727247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727264 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_1727264 : Nat := 118140960795 + 1727264 * 2 ^ 59
def prefixEnd_1727264 : Nat := 4983230072969 + 3 ^ 40 * 1727264 * 2
def baseEnd_1727264 : Nat := 591277766138423536904309

theorem tailTrace_1727264 : CollatzResearch.WordTrace tailWord_1727264 prefixEnd_1727264 591277766138423536904309 := by
  unfold tailWord_1727264
  simp only [CollatzResearch.WordTrace]
  refine ⟨31499246807212498025350423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41998995742949997367133897 31499246807212498025350423)
  ·
    refine ⟨47248870210818747038025635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31499246807212498025350423 47248870210818747038025635)
    ·
      refine ⟨70873305316228120557038453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47248870210818747038025635 70873305316228120557038453)
      ·
        refine ⟨6644372373396386302222355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70873305316228120557038453 6644372373396386302222355)
        ·
          refine ⟨9966558560094579453333533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644372373396386302222355 9966558560094579453333533)
          ·
            refine ⟨3737459460035467295000075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9966558560094579453333533 3737459460035467295000075)
            ·
              refine ⟨5606189190053200942500113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737459460035467295000075 5606189190053200942500113)
              ·
                refine ⟨4204641892539900706875085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606189190053200942500113 4204641892539900706875085)
                ·
                  refine ⟨1576740709702462765078157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4204641892539900706875085 1576740709702462765078157)
                  ·
                    refine ⟨591277766138423536904309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576740709702462765078157 591277766138423536904309)
                    ·
                      rfl

theorem cell22_1727264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_1727264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727264 prefixEnd_1727264 := by exact prefixLift 1727264
  have htrace : WordTrace (prefixWord ++ tailWord_1727264) baseStart_1727264 baseEnd_1727264 := by
    simpa [prefixWord, tailWord_1727264, baseEnd_1727264] using wordTrace_append hprefix tailTrace_1727264
  have hstable : (prefixWord ++ tailWord_1727264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727264).length < 2 ^ (prefixWord ++ tailWord_1727264).sum := by decide
  have hdescent : baseEnd_1727264 < baseStart_1727264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727275 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_1727275 : Nat := 118140960795 + 1727275 * 2 ^ 59
def prefixEnd_1727275 : Nat := 4983230072969 + 3 ^ 40 * 1727275 * 2
def baseEnd_1727275 : Nat := 591281531663223174879275

theorem tailTrace_1727275 : CollatzResearch.WordTrace tailWord_1727275 prefixEnd_1727275 591281531663223174879275 := by
  unfold tailWord_1727275
  simp only [CollatzResearch.WordTrace]
  refine ⟨62998894817385144929351279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41999263211590096619567519 62998894817385144929351279)
  ·
    refine ⟨94498342226077717394026919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62998894817385144929351279 94498342226077717394026919)
    ·
      refine ⟨141747513339116576091040379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94498342226077717394026919 141747513339116576091040379)
      ·
        refine ⟨212621270008674864136560569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141747513339116576091040379 212621270008674864136560569)
        ·
          refine ⟨159465952506506148102420427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212621270008674864136560569 159465952506506148102420427)
          ·
            refine ⟨239198928759759222153630641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159465952506506148102420427 239198928759759222153630641)
            ·
              refine ⟨179399196569819416615222981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239198928759759222153630641 179399196569819416615222981)
              ·
                refine ⟨33637349356841140615354309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179399196569819416615222981 33637349356841140615354309)
                ·
                  refine ⟨6307003004407713865378933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33637349356841140615354309 6307003004407713865378933)
                  ·
                    refine ⟨591281531663223174879275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6307003004407713865378933 591281531663223174879275)
                    ·
                      rfl

theorem cell22_1727275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_1727275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727275 prefixEnd_1727275 := by exact prefixLift 1727275
  have htrace : WordTrace (prefixWord ++ tailWord_1727275) baseStart_1727275 baseEnd_1727275 := by
    simpa [prefixWord, tailWord_1727275, baseEnd_1727275] using wordTrace_append hprefix tailTrace_1727275
  have hstable : (prefixWord ++ tailWord_1727275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727275).length < 2 ^ (prefixWord ++ tailWord_1727275).sum := by decide
  have hdescent : baseEnd_1727275 < baseStart_1727275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727281 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 1, 3]
def baseStart_1727281 : Nat := 118140960795 + 1727281 * 2 ^ 59
def prefixEnd_1727281 : Nat := 4983230072969 + 3 ^ 40 * 1727281 * 2
def baseEnd_1727281 : Nat := 591283585585841159229257

theorem tailTrace_1727281 : CollatzResearch.WordTrace tailWord_1727281 prefixEnd_1727281 591283585585841159229257 := by
  unfold tailWord_1727281
  simp only [CollatzResearch.WordTrace]
  refine ⟨62999113655363407954069697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41999409103575605302713131 62999113655363407954069697)
  ·
    refine ⟨47249335241522555965552273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62999113655363407954069697 47249335241522555965552273)
    ·
      refine ⟨35437001431141916974164205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47249335241522555965552273 35437001431141916974164205)
      ·
        refine ⟨13288875536678218865311577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35437001431141916974164205 13288875536678218865311577)
        ·
          refine ⟨9966656652508664148983683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13288875536678218865311577 9966656652508664148983683)
          ·
            refine ⟨14949984978762996223475525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966656652508664148983683 14949984978762996223475525)
            ·
              refine ⟨2803122183518061791901661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14949984978762996223475525 2803122183518061791901661)
              ·
                refine ⟨1051170818819273171963123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2803122183518061791901661 1051170818819273171963123)
                ·
                  refine ⟨1576756228228909757944685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051170818819273171963123 1576756228228909757944685)
                  ·
                    refine ⟨591283585585841159229257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576756228228909757944685 591283585585841159229257)
                    ·
                      rfl

theorem cell22_1727281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_1727281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727281 prefixEnd_1727281 := by exact prefixLift 1727281
  have htrace : WordTrace (prefixWord ++ tailWord_1727281) baseStart_1727281 baseEnd_1727281 := by
    simpa [prefixWord, tailWord_1727281, baseEnd_1727281] using wordTrace_append hprefix tailTrace_1727281
  have hstable : (prefixWord ++ tailWord_1727281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727281).length < 2 ^ (prefixWord ++ tailWord_1727281).sum := by decide
  have hdescent : baseEnd_1727281 < baseStart_1727281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727294 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1727294 : Nat := 118140960795 + 1727294 * 2 ^ 59
def prefixEnd_1727294 : Nat := 4983230072969 + 3 ^ 40 * 1727294 * 2
def baseEnd_1727294 : Nat := 197096011917171152884739

theorem tailTrace_1727294 : CollatzResearch.WordTrace tailWord_1727294 prefixEnd_1727294 197096011917171152884739 := by
  unfold tailWord_1727294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874948475539538896786617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41999725202877540782861957 7874948475539538896786617)
  ·
    refine ⟨5906211356654654172589963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7874948475539538896786617 5906211356654654172589963)
    ·
      refine ⟨8859317034981981258884945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906211356654654172589963 8859317034981981258884945)
      ·
        refine ⟨6644487776236485944163709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859317034981981258884945 6644487776236485944163709)
        ·
          refine ⟨2491682916088682229061391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6644487776236485944163709 2491682916088682229061391)
          ·
            refine ⟨3737524374133023343592087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491682916088682229061391 3737524374133023343592087)
            ·
              refine ⟨5606286561199535015388131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737524374133023343592087 5606286561199535015388131)
              ·
                refine ⟨8409429841799302523082197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606286561199535015388131 8409429841799302523082197)
                ·
                  refine ⟨197096011917171152884739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8409429841799302523082197 197096011917171152884739)
                  ·
                    rfl

theorem cell22_1727294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1727294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727294 prefixEnd_1727294 := by exact prefixLift 1727294
  have htrace : WordTrace (prefixWord ++ tailWord_1727294) baseStart_1727294 baseEnd_1727294 := by
    simpa [prefixWord, tailWord_1727294, baseEnd_1727294] using wordTrace_append hprefix tailTrace_1727294
  have hstable : (prefixWord ++ tailWord_1727294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727294).length < 2 ^ (prefixWord ++ tailWord_1727294).sum := by decide
  have hdescent : baseEnd_1727294 < baseStart_1727294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727322 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_1727322 : Nat := 118140960795 + 1727322 * 2 ^ 59
def prefixEnd_1727322 : Nat := 4983230072969 + 3 ^ 40 * 1727322 * 2
def baseEnd_1727322 : Nat := 197099206907910239651377

theorem tailTrace_1727322 : CollatzResearch.WordTrace tailWord_1727322 prefixEnd_1727322 197099206907910239651377 := by
  unfold tailWord_1727322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750152262053717989078055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42000406032143247970874813 15750152262053717989078055)
  ·
    refine ⟨23625228393080576983617083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15750152262053717989078055 23625228393080576983617083)
    ·
      refine ⟨35437842589620865475425625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23625228393080576983617083 35437842589620865475425625)
      ·
        refine ⟨26578381942215649106569219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35437842589620865475425625 26578381942215649106569219)
        ·
          refine ⟨39867572913323473659853829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26578381942215649106569219 39867572913323473659853829)
          ·
            refine ⟨7475169921248151311222593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39867572913323473659853829 7475169921248151311222593)
            ·
              refine ⟨5606377440936113483416945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7475169921248151311222593 5606377440936113483416945)
              ·
                refine ⟨4204783080702085112562709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606377440936113483416945 4204783080702085112562709)
                ·
                  refine ⟨197099206907910239651377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4204783080702085112562709 197099206907910239651377)
                  ·
                    rfl

theorem cell22_1727322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_1727322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727322 prefixEnd_1727322 := by exact prefixLift 1727322
  have htrace : WordTrace (prefixWord ++ tailWord_1727322) baseStart_1727322 baseEnd_1727322 := by
    simpa [prefixWord, tailWord_1727322, baseEnd_1727322] using wordTrace_append hprefix tailTrace_1727322
  have hstable : (prefixWord ++ tailWord_1727322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727322).length < 2 ^ (prefixWord ++ tailWord_1727322).sum := by decide
  have hdescent : baseEnd_1727322 < baseStart_1727322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727339 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 4]
def baseStart_1727339 : Nat := 118140960795 + 1727339 * 2 ^ 59
def prefixEnd_1727339 : Nat := 4983230072969 + 3 ^ 40 * 1727339 * 2
def baseEnd_1727339 : Nat := 197101146723716113759693

theorem tailTrace_1727339 : CollatzResearch.WordTrace tailWord_1727339 prefixEnd_1727339 197101146723716113759693 := by
  unfold tailWord_1727339
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001229089153283859681071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42000819392768855906454047 63001229089153283859681071)
  ·
    refine ⟨94501843633729925789521607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63001229089153283859681071 94501843633729925789521607)
    ·
      refine ⟨141752765450594888684282411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94501843633729925789521607 141752765450594888684282411)
      ·
        refine ⟨212629148175892333026423617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141752765450594888684282411 212629148175892333026423617)
        ·
          refine ⟨159471861131919249769817713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212629148175892333026423617 159471861131919249769817713)
          ·
            refine ⟨119603895848939437327363285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159471861131919249769817713 119603895848939437327363285)
            ·
              refine ⟨2803216308959518062360077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119603895848939437327363285 2803216308959518062360077)
              ·
                refine ⟨1051206115859819273385029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2803216308959518062360077 1051206115859819273385029)
                ·
                  refine ⟨197101146723716113759693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051206115859819273385029 197101146723716113759693)
                  ·
                    rfl

theorem cell22_1727339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 4].length) (baseStart_1727339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727339 prefixEnd_1727339 := by exact prefixLift 1727339
  have htrace : WordTrace (prefixWord ++ tailWord_1727339) baseStart_1727339 baseEnd_1727339 := by
    simpa [prefixWord, tailWord_1727339, baseEnd_1727339] using wordTrace_append hprefix tailTrace_1727339
  have hstable : (prefixWord ++ tailWord_1727339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727339).length < 2 ^ (prefixWord ++ tailWord_1727339).sum := by decide
  have hdescent : baseEnd_1727339 < baseStart_1727339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727354 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_1727354 : Nat := 118140960795 + 1727354 * 2 ^ 59
def prefixEnd_1727354 : Nat := 4983230072969 + 3 ^ 40 * 1727354 * 2
def baseEnd_1727354 : Nat := 591308574977693302154033

theorem tailTrace_1727354 : CollatzResearch.WordTrace tailWord_1727354 prefixEnd_1727354 591308574977693302154033 := by
  unfold tailWord_1727354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750444046024735355369279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42001184122732627614318077 15750444046024735355369279)
  ·
    refine ⟨23625666069037103033053919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15750444046024735355369279 23625666069037103033053919)
    ·
      refine ⟨35438499103555654549580879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23625666069037103033053919 35438499103555654549580879)
      ·
        refine ⟨53157748655333481824371319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35438499103555654549580879 53157748655333481824371319)
        ·
          refine ⟨79736622983000222736556979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53157748655333481824371319 79736622983000222736556979)
          ·
            refine ⟨119604934474500334104835469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79736622983000222736556979 119604934474500334104835469)
            ·
              refine ⟨44851850427937625289313301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119604934474500334104835469 44851850427937625289313301)
              ·
                refine ⟨2102430488809576185436561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44851850427937625289313301 2102430488809576185436561)
                ·
                  refine ⟨1576822866607182139077421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102430488809576185436561 1576822866607182139077421)
                  ·
                    refine ⟨591308574977693302154033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576822866607182139077421 591308574977693302154033)
                    ·
                      rfl

theorem cell22_1727354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_1727354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727354 prefixEnd_1727354 := by exact prefixLift 1727354
  have htrace : WordTrace (prefixWord ++ tailWord_1727354) baseStart_1727354 baseEnd_1727354 := by
    simpa [prefixWord, tailWord_1727354, baseEnd_1727354] using wordTrace_append hprefix tailTrace_1727354
  have hstable : (prefixWord ++ tailWord_1727354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727354).length < 2 ^ (prefixWord ++ tailWord_1727354).sum := by decide
  have hdescent : baseEnd_1727354 < baseStart_1727354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727362 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1727362 : Nat := 118140960795 + 1727362 * 2 ^ 59
def prefixEnd_1727362 : Nat := 4983230072969 + 3 ^ 40 * 1727362 * 2
def baseEnd_1727362 : Nat := 197103771180394649318003

theorem tailTrace_1727362 : CollatzResearch.WordTrace tailWord_1727362 prefixEnd_1727362 197103771180394649318003 := by
  unfold tailWord_1727362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750516992017489696942085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42001378645379972525178893 15750516992017489696942085)
  ·
    refine ⟨2953221936003279318176641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15750516992017489696942085 2953221936003279318176641)
    ·
      refine ⟨2214916452002459488632481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2953221936003279318176641 2214916452002459488632481)
      ·
        refine ⟨1661187339001844616474361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2214916452002459488632481 1661187339001844616474361)
        ·
          refine ⟨1245890504251383462355771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661187339001844616474361 1245890504251383462355771)
          ·
            refine ⟨1868835756377075193533657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245890504251383462355771 1868835756377075193533657)
            ·
              refine ⟨1401626817282806395150243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868835756377075193533657 1401626817282806395150243)
              ·
                refine ⟨2102440225924209592725365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401626817282806395150243 2102440225924209592725365)
                ·
                  refine ⟨197103771180394649318003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2102440225924209592725365 197103771180394649318003)
                  ·
                    rfl

theorem cell22_1727362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1727362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727362 prefixEnd_1727362 := by exact prefixLift 1727362
  have htrace : WordTrace (prefixWord ++ tailWord_1727362) baseStart_1727362 baseEnd_1727362 := by
    simpa [prefixWord, tailWord_1727362, baseEnd_1727362] using wordTrace_append hprefix tailTrace_1727362
  have hstable : (prefixWord ++ tailWord_1727362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727362).length < 2 ^ (prefixWord ++ tailWord_1727362).sum := by decide
  have hdescent : baseEnd_1727362 < baseStart_1727362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727367 : List Nat := [1, 1, 4, 2, 3, 1, 1, 9]
def baseStart_1727367 : Nat := 118140960795 + 1727367 * 2 ^ 59
def prefixEnd_1727367 : Nat := 4983230072969 + 3 ^ 40 * 1727367 * 2
def baseEnd_1727367 : Nat := 65701447238151733508777

theorem tailTrace_1727367 : CollatzResearch.WordTrace tailWord_1727367 prefixEnd_1727367 65701447238151733508777 := by
  unfold tailWord_1727367
  simp only [CollatzResearch.WordTrace]
  refine ⟨63002250333051844641700355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42001500222034563094466903 63002250333051844641700355)
  ·
    refine ⟨94503375499577766962550533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63002250333051844641700355 94503375499577766962550533)
    ·
      refine ⟨17719382906170831305478225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94503375499577766962550533 17719382906170831305478225)
      ·
        refine ⟨13289537179628123479108669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17719382906170831305478225 13289537179628123479108669)
        ·
          refine ⟨4983576442360546304665751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13289537179628123479108669 4983576442360546304665751)
          ·
            refine ⟨7475364663540819456998627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983576442360546304665751 7475364663540819456998627)
            ·
              refine ⟨11213046995311229185497941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475364663540819456998627 11213046995311229185497941)
              ·
                refine ⟨65701447238151733508777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11213046995311229185497941 65701447238151733508777)
                ·
                  rfl

theorem cell22_1727367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 9].length) (baseStart_1727367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727367 prefixEnd_1727367 := by exact prefixLift 1727367
  have htrace : WordTrace (prefixWord ++ tailWord_1727367) baseStart_1727367 baseEnd_1727367 := by
    simpa [prefixWord, tailWord_1727367, baseEnd_1727367] using wordTrace_append hprefix tailTrace_1727367
  have hstable : (prefixWord ++ tailWord_1727367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727367).length < 2 ^ (prefixWord ++ tailWord_1727367).sum := by decide
  have hdescent : baseEnd_1727367 < baseStart_1727367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727371 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 2, 3]
def baseStart_1727371 : Nat := 118140960795 + 1727371 * 2 ^ 59
def prefixEnd_1727371 : Nat := 4983230072969 + 3 ^ 40 * 1727371 * 2
def baseEnd_1727371 : Nat := 591314394425110924478981

theorem tailTrace_1727371 : CollatzResearch.WordTrace tailWord_1727371 prefixEnd_1727371 591314394425110924478981 := by
  unfold tailWord_1727371
  simp only [CollatzResearch.WordTrace]
  refine ⟨63002396225037353324845967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42001597483358235549897311 63002396225037353324845967)
  ·
    refine ⟨94503594337556029987268951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63002396225037353324845967 94503594337556029987268951)
    ·
      refine ⟨141755391506334044980903427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94503594337556029987268951 141755391506334044980903427)
      ·
        refine ⟨212633087259501067471355141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141755391506334044980903427 212633087259501067471355141)
        ·
          refine ⟨39868703861156450150879089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212633087259501067471355141 39868703861156450150879089)
          ·
            refine ⟨29901527895867337613159317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39868703861156450150879089 29901527895867337613159317)
            ·
              refine ⟨1401634120118781450616843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29901527895867337613159317 1401634120118781450616843)
              ·
                refine ⟨2102451180178172175925265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401634120118781450616843 2102451180178172175925265)
                ·
                  refine ⟨1576838385133629131943949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102451180178172175925265 1576838385133629131943949)
                  ·
                    refine ⟨591314394425110924478981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576838385133629131943949 591314394425110924478981)
                    ·
                      rfl

theorem cell22_1727371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 3].length) (baseStart_1727371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727371 prefixEnd_1727371 := by exact prefixLift 1727371
  have htrace : WordTrace (prefixWord ++ tailWord_1727371) baseStart_1727371 baseEnd_1727371 := by
    simpa [prefixWord, tailWord_1727371, baseEnd_1727371] using wordTrace_append hprefix tailTrace_1727371
  have hstable : (prefixWord ++ tailWord_1727371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727371).length < 2 ^ (prefixWord ++ tailWord_1727371).sum := by decide
  have hdescent : baseEnd_1727371 < baseStart_1727371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727386 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1727386 : Nat := 118140960795 + 1727386 * 2 ^ 59
def prefixEnd_1727386 : Nat := 4983230072969 + 3 ^ 40 * 1727386 * 2
def baseEnd_1727386 : Nat := 591319529231655885353935

theorem tailTrace_1727386 : CollatzResearch.WordTrace tailWord_1727386 prefixEnd_1727386 591319529231655885353935 := by
  unfold tailWord_1727386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750735829995752721660503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42001962213322007257761341 15750735829995752721660503)
  ·
    refine ⟨23626103744993629082490755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15750735829995752721660503 23626103744993629082490755)
    ·
      refine ⟨35439155617490443623736133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23626103744993629082490755 35439155617490443623736133)
      ·
        refine ⟨6644841678279458179450525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35439155617490443623736133 6644841678279458179450525)
        ·
          refine ⟨2491815629354796817293947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6644841678279458179450525 2491815629354796817293947)
          ·
            refine ⟨3737723444032195225940921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491815629354796817293947 3737723444032195225940921)
            ·
              refine ⟨2803292583024146419455691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3737723444032195225940921 2803292583024146419455691)
              ·
                refine ⟨4204938874536219629183537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803292583024146419455691 4204938874536219629183537)
                ·
                  refine ⟨3153704155902164721887653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204938874536219629183537 3153704155902164721887653)
                  ·
                    refine ⟨591319529231655885353935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153704155902164721887653 591319529231655885353935)
                    ·
                      rfl

theorem cell22_1727386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1727386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727386 prefixEnd_1727386 := by exact prefixLift 1727386
  have htrace : WordTrace (prefixWord ++ tailWord_1727386) baseStart_1727386 baseEnd_1727386 := by
    simpa [prefixWord, tailWord_1727386, baseEnd_1727386] using wordTrace_append hprefix tailTrace_1727386
  have hstable : (prefixWord ++ tailWord_1727386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727386).length < 2 ^ (prefixWord ++ tailWord_1727386).sum := by decide
  have hdescent : baseEnd_1727386 < baseStart_1727386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727405 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1727405 : Nat := 118140960795 + 1727405 * 2 ^ 59
def prefixEnd_1727405 : Nat := 4983230072969 + 3 ^ 40 * 1727405 * 2
def baseEnd_1727405 : Nat := 591326033319946169128877

theorem tailTrace_1727405 : CollatzResearch.WordTrace tailWord_1727405 prefixEnd_1727405 591326033319946169128877 := by
  unfold tailWord_1727405
  simp only [CollatzResearch.WordTrace]
  refine ⟨63003636306914177131583669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42002424204609451421055779 63003636306914177131583669)
  ·
    refine ⟨5906590903773204106085969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63003636306914177131583669 5906590903773204106085969)
    ·
      refine ⟨4429943177829903079564477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5906590903773204106085969 4429943177829903079564477)
      ·
        refine ⟨1661228691686213654836679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4429943177829903079564477 1661228691686213654836679)
        ·
          refine ⟨2491843037529320482255019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661228691686213654836679 2491843037529320482255019)
          ·
            refine ⟨3737764556293980723382529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491843037529320482255019 3737764556293980723382529)
            ·
              refine ⟨2803323417220485542536897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3737764556293980723382529 2803323417220485542536897)
              ·
                refine ⟨2102492562915364156902673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803323417220485542536897 2102492562915364156902673)
                ·
                  refine ⟨1576869422186523117677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102492562915364156902673 1576869422186523117677005)
                  ·
                    refine ⟨591326033319946169128877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576869422186523117677005 591326033319946169128877)
                    ·
                      rfl

theorem cell22_1727405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1727405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727405 prefixEnd_1727405 := by exact prefixLift 1727405
  have htrace : WordTrace (prefixWord ++ tailWord_1727405) baseStart_1727405 baseEnd_1727405 := by
    simpa [prefixWord, tailWord_1727405, baseEnd_1727405] using wordTrace_append hprefix tailTrace_1727405
  have hstable : (prefixWord ++ tailWord_1727405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727405).length < 2 ^ (prefixWord ++ tailWord_1727405).sum := by decide
  have hdescent : baseEnd_1727405 < baseStart_1727405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_1727427 : Nat := 118140960795 + 1727427 * 2 ^ 59
def prefixEnd_1727427 : Nat := 4983230072969 + 3 ^ 40 * 1727427 * 2
def baseEnd_1727427 : Nat := 591333564369545445078809

theorem tailTrace_1727427 : CollatzResearch.WordTrace tailWord_1727427 prefixEnd_1727427 591333564369545445078809 := by
  unfold tailWord_1727427
  simp only [CollatzResearch.WordTrace]
  refine ⟨63004438712834474888884535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42002959141889649925923023 63004438712834474888884535)
  ·
    refine ⟨94506658069251712333326803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63004438712834474888884535 94506658069251712333326803)
    ·
      refine ⟨141759987103877568499990205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94506658069251712333326803 141759987103877568499990205)
      ·
        refine ⟨53159995163954088187496327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141759987103877568499990205 53159995163954088187496327)
        ·
          refine ⟨79739992745931132281244491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53159995163954088187496327 79739992745931132281244491)
          ·
            refine ⟨119609989118896698421866737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79739992745931132281244491 119609989118896698421866737)
            ·
              refine ⟨89707491839172523816400053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119609989118896698421866737 89707491839172523816400053)
              ·
                refine ⟨8410077359922424107787505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89707491839172523816400053 8410077359922424107787505)
                ·
                  refine ⟨6307558019941818080840629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8410077359922424107787505 6307558019941818080840629)
                  ·
                    refine ⟨591333564369545445078809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6307558019941818080840629 591333564369545445078809)
                    ·
                      rfl

theorem cell22_1727427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_1727427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727427 prefixEnd_1727427 := by exact prefixLift 1727427
  have htrace : WordTrace (prefixWord ++ tailWord_1727427) baseStart_1727427 baseEnd_1727427 := by
    simpa [prefixWord, tailWord_1727427, baseEnd_1727427] using wordTrace_append hprefix tailTrace_1727427
  have hstable : (prefixWord ++ tailWord_1727427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727427).length < 2 ^ (prefixWord ++ tailWord_1727427).sum := by decide
  have hdescent : baseEnd_1727427 < baseStart_1727427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727437 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1727437 : Nat := 118140960795 + 1727437 * 2 ^ 59
def prefixEnd_1727437 : Nat := 4983230072969 + 3 ^ 40 * 1727437 * 2
def baseEnd_1727437 : Nat := 591336987573908752328779

theorem tailTrace_1727437 : CollatzResearch.WordTrace tailWord_1727437 prefixEnd_1727437 591336987573908752328779 := by
  unfold tailWord_1727437
  simp only [CollatzResearch.WordTrace]
  refine ⟨63004803442798246596748565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42003202295198831064499043 63004803442798246596748565)
  ·
    refine ⟨2953350161381167809222589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63004803442798246596748565 2953350161381167809222589)
    ·
      refine ⟨1107506310517937928458471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2953350161381167809222589 1107506310517937928458471)
      ·
        refine ⟨1661259465776906892687707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107506310517937928458471 1661259465776906892687707)
        ·
          refine ⟨2491889198665360339031561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661259465776906892687707 2491889198665360339031561)
          ·
            refine ⟨1868916898999020254273671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491889198665360339031561 1868916898999020254273671)
            ·
              refine ⟨2803375348498530381410507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868916898999020254273671 2803375348498530381410507)
              ·
                refine ⟨4205063022747795572115761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803375348498530381410507 4205063022747795572115761)
                ·
                  refine ⟨3153797267060846679086821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205063022747795572115761 3153797267060846679086821)
                  ·
                    refine ⟨591336987573908752328779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153797267060846679086821 591336987573908752328779)
                    ·
                      rfl

theorem cell22_1727437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1727437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727437 prefixEnd_1727437 := by exact prefixLift 1727437
  have htrace : WordTrace (prefixWord ++ tailWord_1727437) baseStart_1727437 baseEnd_1727437 := by
    simpa [prefixWord, tailWord_1727437, baseEnd_1727437] using wordTrace_append hprefix tailTrace_1727437
  have hstable : (prefixWord ++ tailWord_1727437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727437).length < 2 ^ (prefixWord ++ tailWord_1727437).sum := by decide
  have hdescent : baseEnd_1727437 < baseStart_1727437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727457 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 10]
def baseStart_1727457 : Nat := 118140960795 + 1727457 * 2 ^ 59
def prefixEnd_1727457 : Nat := 4983230072969 + 3 ^ 40 * 1727457 * 2
def baseEnd_1727457 : Nat := 197114611327545122276239

theorem tailTrace_1727457 : CollatzResearch.WordTrace tailWord_1727457 prefixEnd_1727457 197114611327545122276239 := by
  unfold tailWord_1727457
  simp only [CollatzResearch.WordTrace]
  refine ⟨63005532902725790012476625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42003688601817193341651083 63005532902725790012476625)
  ·
    refine ⟨47254149677044342509357469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63005532902725790012476625 47254149677044342509357469)
    ·
      refine ⟨17720306128891628441009051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47254149677044342509357469 17720306128891628441009051)
      ·
        refine ⟨26580459193337442661513577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17720306128891628441009051 26580459193337442661513577)
        ·
          refine ⟨19935344395003081996135183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26580459193337442661513577 19935344395003081996135183)
          ·
            refine ⟨29903016592504622994202775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19935344395003081996135183 29903016592504622994202775)
            ·
              refine ⟨44854524888756934491304163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29903016592504622994202775 44854524888756934491304163)
              ·
                refine ⟨67281787333135401736956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44854524888756934491304163 67281787333135401736956245)
                ·
                  refine ⟨197114611327545122276239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67281787333135401736956245 197114611327545122276239)
                  ·
                    rfl

theorem cell22_1727457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_1727457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727457 prefixEnd_1727457 := by exact prefixLift 1727457
  have htrace : WordTrace (prefixWord ++ tailWord_1727457) baseStart_1727457 baseEnd_1727457 := by
    simpa [prefixWord, tailWord_1727457, baseEnd_1727457] using wordTrace_append hprefix tailTrace_1727457
  have hstable : (prefixWord ++ tailWord_1727457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727457).length < 2 ^ (prefixWord ++ tailWord_1727457).sum := by decide
  have hdescent : baseEnd_1727457 < baseStart_1727457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727519 : List Nat := [1, 1, 2, 4, 1, 5, 8]
def baseStart_1727519 : Nat := 118140960795 + 1727519 * 2 ^ 59
def prefixEnd_1727519 : Nat := 4983230072969 + 3 ^ 40 * 1727519 * 2
def baseEnd_1727519 : Nat := 21902409549988439695501

theorem tailTrace_1727519 : CollatzResearch.WordTrace tailWord_1727519 prefixEnd_1727519 21902409549988439695501 := by
  unfold tailWord_1727519
  simp only [CollatzResearch.WordTrace]
  refine ⟨63007794228501174601233611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42005196152334116400822407 63007794228501174601233611)
  ·
    refine ⟨94511691342751761901850417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63007794228501174601233611 94511691342751761901850417)
    ·
      refine ⟨70883768507063821426387813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94511691342751761901850417 70883768507063821426387813)
      ·
        refine ⟨13290706595074466517447715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70883768507063821426387813 13290706595074466517447715)
        ·
          refine ⟨19936059892611699776171573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13290706595074466517447715 19936059892611699776171573)
          ·
            refine ⟨1869005614932346854016085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19936059892611699776171573 1869005614932346854016085)
            ·
              refine ⟨21902409549988439695501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1869005614932346854016085 21902409549988439695501)
              ·
                rfl

theorem cell22_1727519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 8].length) (baseStart_1727519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727519 prefixEnd_1727519 := by exact prefixLift 1727519
  have htrace : WordTrace (prefixWord ++ tailWord_1727519) baseStart_1727519 baseEnd_1727519 := by
    simpa [prefixWord, tailWord_1727519, baseEnd_1727519] using wordTrace_append hprefix tailTrace_1727519
  have hstable : (prefixWord ++ tailWord_1727519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727519).length < 2 ^ (prefixWord ++ tailWord_1727519).sum := by decide
  have hdescent : baseEnd_1727519 < baseStart_1727519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727521 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1727521 : Nat := 118140960795 + 1727521 * 2 ^ 59
def prefixEnd_1727521 : Nat := 4983230072969 + 3 ^ 40 * 1727521 * 2
def baseEnd_1727521 : Nat := 591365742490560533228521

theorem tailTrace_1727521 : CollatzResearch.WordTrace tailWord_1727521 prefixEnd_1727521 591365742490560533228521 := by
  unfold tailWord_1727521
  simp only [CollatzResearch.WordTrace]
  refine ⟨63007867174493928942806417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42005244782995952628537611 63007867174493928942806417)
  ·
    refine ⟨47255900380870446707104813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63007867174493928942806417 47255900380870446707104813)
    ·
      refine ⟨17720962642826417515164305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47255900380870446707104813 17720962642826417515164305)
      ·
        refine ⟨13290721982119813136373229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17720962642826417515164305 13290721982119813136373229)
        ·
          refine ⟨4984020743294929926139961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13290721982119813136373229 4984020743294929926139961)
          ·
            refine ⟨3738015557471197444604971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984020743294929926139961 3738015557471197444604971)
            ·
              refine ⟨5607023336206796166907457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738015557471197444604971 5607023336206796166907457)
              ·
                refine ⟨4205267502155097125180593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607023336206796166907457 4205267502155097125180593)
                ·
                  refine ⟨3153950626616322843885445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205267502155097125180593 3153950626616322843885445)
                  ·
                    refine ⟨591365742490560533228521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153950626616322843885445 591365742490560533228521)
                    ·
                      rfl

theorem cell22_1727521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1727521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727521 prefixEnd_1727521 := by exact prefixLift 1727521
  have htrace : WordTrace (prefixWord ++ tailWord_1727521) baseStart_1727521 baseEnd_1727521 := by
    simpa [prefixWord, tailWord_1727521, baseEnd_1727521] using wordTrace_append hprefix tailTrace_1727521
  have hstable : (prefixWord ++ tailWord_1727521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727521).length < 2 ^ (prefixWord ++ tailWord_1727521).sum := by decide
  have hdescent : baseEnd_1727521 < baseStart_1727521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727540 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1727540 : Nat := 118140960795 + 1727540 * 2 ^ 59
def prefixEnd_1727540 : Nat := 4983230072969 + 3 ^ 40 * 1727540 * 2
def baseEnd_1727540 : Nat := 591372246578850817003463

theorem tailTrace_1727540 : CollatzResearch.WordTrace tailWord_1727540 prefixEnd_1727540 591372246578850817003463 := by
  unfold tailWord_1727540
  simp only [CollatzResearch.WordTrace]
  refine ⟨31504280080712547593874037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42005706774283396791832049 31504280080712547593874037)
  ·
    refine ⟨2953526257566801336925691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31504280080712547593874037 2953526257566801336925691)
    ·
      refine ⟨4430289386350202005388537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2953526257566801336925691 4430289386350202005388537)
      ·
        refine ⟨3322717039762651504041403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430289386350202005388537 3322717039762651504041403)
        ·
          refine ⟨4984075559643977256062105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322717039762651504041403 4984075559643977256062105)
          ·
            refine ⟨3738056669732982942046579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984075559643977256062105 3738056669732982942046579)
            ·
              refine ⟨5607085004599474413069869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738056669732982942046579 5607085004599474413069869)
              ·
                refine ⟨2102656876724802904901201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5607085004599474413069869 2102656876724802904901201)
                ·
                  refine ⟨1576992657543602178675901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102656876724802904901201 1576992657543602178675901)
                  ·
                    refine ⟨591372246578850817003463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1576992657543602178675901 591372246578850817003463)
                    ·
                      rfl

theorem cell22_1727540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1727540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727540 prefixEnd_1727540 := by exact prefixLift 1727540
  have htrace : WordTrace (prefixWord ++ tailWord_1727540) baseStart_1727540 baseEnd_1727540 := by
    simpa [prefixWord, tailWord_1727540, baseEnd_1727540] using wordTrace_append hprefix tailTrace_1727540
  have hstable : (prefixWord ++ tailWord_1727540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727540).length < 2 ^ (prefixWord ++ tailWord_1727540).sum := by decide
  have hdescent : baseEnd_1727540 < baseStart_1727540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727585 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 1, 3]
def baseStart_1727585 : Nat := 118140960795 + 1727585 * 2 ^ 59
def prefixEnd_1727585 : Nat := 4983230072969 + 3 ^ 40 * 1727585 * 2
def baseEnd_1727585 : Nat := 591387650998485699628325

theorem tailTrace_1727585 : CollatzResearch.WordTrace tailWord_1727585 prefixEnd_1727585 591387650998485699628325 := by
  unfold tailWord_1727585
  simp only [CollatzResearch.WordTrace]
  refine ⟨63010201446262067873136209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42006800964174711915424139 63010201446262067873136209)
  ·
    refine ⟨47257651084696550904852157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63010201446262067873136209 47257651084696550904852157)
    ·
      refine ⟨17721619156761206589319559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47257651084696550904852157 17721619156761206589319559)
      ·
        refine ⟨26582428735141809883979339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17721619156761206589319559 26582428735141809883979339)
        ·
          refine ⟨39873643102712714825969009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26582428735141809883979339 39873643102712714825969009)
          ·
            refine ⟨29905232327034536119476757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39873643102712714825969009 29905232327034536119476757)
            ·
              refine ⟨1401807765329743880600473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29905232327034536119476757 1401807765329743880600473)
              ·
                refine ⟨1051355823997307910450355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401807765329743880600473 1051355823997307910450355)
                ·
                  refine ⟨1577033735995961865675533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051355823997307910450355 1577033735995961865675533)
                  ·
                    refine ⟨591387650998485699628325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577033735995961865675533 591387650998485699628325)
                    ·
                      rfl

theorem cell22_1727585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_1727585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727585 prefixEnd_1727585 := by exact prefixLift 1727585
  have htrace : WordTrace (prefixWord ++ tailWord_1727585) baseStart_1727585 baseEnd_1727585 := by
    simpa [prefixWord, tailWord_1727585, baseEnd_1727585] using wordTrace_append hprefix tailTrace_1727585
  have hstable : (prefixWord ++ tailWord_1727585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727585).length < 2 ^ (prefixWord ++ tailWord_1727585).sum := by decide
  have hdescent : baseEnd_1727585 < baseStart_1727585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727703 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 3, 3]
def baseStart_1727703 : Nat := 118140960795 + 1727703 * 2 ^ 59
def prefixEnd_1727703 : Nat := 4983230072969 + 3 ^ 40 * 1727703 * 2
def baseEnd_1727703 : Nat := 591428044809972725177963

theorem tailTrace_1727703 : CollatzResearch.WordTrace tailWord_1727703 prefixEnd_1727703 591428044809972725177963 := by
  unfold tailWord_1727703
  simp only [CollatzResearch.WordTrace]
  refine ⟨63014505259834574025931763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42009670173223049350621175 63014505259834574025931763)
  ·
    refine ⟨94521757889751861038897645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63014505259834574025931763 94521757889751861038897645)
    ·
      refine ⟨35445659208656947889586617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94521757889751861038897645 35445659208656947889586617)
      ·
        refine ⟨26584244406492710917189963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35445659208656947889586617 26584244406492710917189963)
        ·
          refine ⟨39876366609739066375784945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26584244406492710917189963 39876366609739066375784945)
          ·
            refine ⟨29907274957304299781838709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39876366609739066375784945 29907274957304299781838709)
            ·
              refine ⟨2803807027247278104547379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29907274957304299781838709 2803807027247278104547379)
              ·
                refine ⟨4205710540870917156821069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803807027247278104547379 4205710540870917156821069)
                ·
                  refine ⟨1577141452826593933807901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4205710540870917156821069 1577141452826593933807901)
                  ·
                    refine ⟨591428044809972725177963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577141452826593933807901 591428044809972725177963)
                    ·
                      rfl

theorem cell22_1727703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_1727703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727703 prefixEnd_1727703 := by exact prefixLift 1727703
  have htrace : WordTrace (prefixWord ++ tailWord_1727703) baseStart_1727703 baseEnd_1727703 := by
    simpa [prefixWord, tailWord_1727703, baseEnd_1727703] using wordTrace_append hprefix tailTrace_1727703
  have hstable : (prefixWord ++ tailWord_1727703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727703).length < 2 ^ (prefixWord ++ tailWord_1727703).sum := by decide
  have hdescent : baseEnd_1727703 < baseStart_1727703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727709 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1727709 : Nat := 118140960795 + 1727709 * 2 ^ 59
def prefixEnd_1727709 : Nat := 4983230072969 + 3 ^ 40 * 1727709 * 2
def baseEnd_1727709 : Nat := 591430098732590709527945

theorem tailTrace_1727709 : CollatzResearch.WordTrace tailWord_1727709 prefixEnd_1727709 591430098732590709527945 := by
  unfold tailWord_1727709
  simp only [CollatzResearch.WordTrace]
  refine ⟨63014724097812837050650181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42009816065208558033766787 63014724097812837050650181)
  ·
    refine ⟨11815260768339906946996909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63014724097812837050650181 11815260768339906946996909)
    ·
      refine ⟨4430722788127465105123841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11815260768339906946996909 4430722788127465105123841)
      ·
        refine ⟨3323042091095598828842881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430722788127465105123841 3323042091095598828842881)
        ·
          refine ⟨2492281568321699121632161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323042091095598828842881 2492281568321699121632161)
          ·
            refine ⟨1869211176241274341224121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492281568321699121632161 1869211176241274341224121)
            ·
              refine ⟨1401908382180955755918091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869211176241274341224121 1401908382180955755918091)
              ·
                refine ⟨2102862573271433633877137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401908382180955755918091 2102862573271433633877137)
                ·
                  refine ⟨1577146929953575225407853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102862573271433633877137 1577146929953575225407853)
                  ·
                    refine ⟨591430098732590709527945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1577146929953575225407853 591430098732590709527945)
                    ·
                      rfl

theorem cell22_1727709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1727709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727709 prefixEnd_1727709 := by exact prefixLift 1727709
  have htrace : WordTrace (prefixWord ++ tailWord_1727709) baseStart_1727709 baseEnd_1727709 := by
    simpa [prefixWord, tailWord_1727709, baseEnd_1727709] using wordTrace_append hprefix tailTrace_1727709
  have hstable : (prefixWord ++ tailWord_1727709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727709).length < 2 ^ (prefixWord ++ tailWord_1727709).sum := by decide
  have hdescent : baseEnd_1727709 < baseStart_1727709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727761 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 6]
def baseStart_1727761 : Nat := 118140960795 + 1727761 * 2 ^ 59
def prefixEnd_1727761 : Nat := 4983230072969 + 3 ^ 40 * 1727761 * 2
def baseEnd_1727761 : Nat := 197149299798426635742595

theorem tailTrace_1727761 : CollatzResearch.WordTrace tailWord_1727761 prefixEnd_1727761 197149299798426635742595 := by
  unfold tailWord_1727761
  simp only [CollatzResearch.WordTrace]
  refine ⟨63016620693624449931543137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42011080462416299954362091 63016620693624449931543137)
  ·
    refine ⟨47262465520218337448657353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63016620693624449931543137 47262465520218337448657353)
    ·
      refine ⟨35446849140163753086493015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47262465520218337448657353 35446849140163753086493015)
      ·
        refine ⟨53170273710245629629739523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35446849140163753086493015 53170273710245629629739523)
        ·
          refine ⟨79755410565368444444609285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53170273710245629629739523 79755410565368444444609285)
          ·
            refine ⟨14954139481006583333364241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79755410565368444444609285 14954139481006583333364241)
            ·
              refine ⟨11215604610754937500023181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14954139481006583333364241 11215604610754937500023181)
              ·
                refine ⟨4205851729033101562508693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11215604610754937500023181 4205851729033101562508693)
                ·
                  refine ⟨197149299798426635742595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4205851729033101562508693 197149299798426635742595)
                  ·
                    rfl

theorem cell22_1727761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_1727761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727761 prefixEnd_1727761 := by exact prefixLift 1727761
  have htrace : WordTrace (prefixWord ++ tailWord_1727761) baseStart_1727761 baseEnd_1727761 := by
    simpa [prefixWord, tailWord_1727761, baseEnd_1727761] using wordTrace_append hprefix tailTrace_1727761
  have hstable : (prefixWord ++ tailWord_1727761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727761).length < 2 ^ (prefixWord ++ tailWord_1727761).sum := by decide
  have hdescent : baseEnd_1727761 < baseStart_1727761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727793 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1727793 : Nat := 118140960795 + 1727793 * 2 ^ 59
def prefixEnd_1727793 : Nat := 4983230072969 + 3 ^ 40 * 1727793 * 2
def baseEnd_1727793 : Nat := 591458853649242490427687

theorem tailTrace_1727793 : CollatzResearch.WordTrace tailWord_1727793 prefixEnd_1727793 591458853649242490427687 := by
  unfold tailWord_1727793
  simp only [CollatzResearch.WordTrace]
  refine ⟨63017787829508519396708033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42011858553005679597805355 63017787829508519396708033)
  ·
    refine ⟨47263340872131389547531025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63017787829508519396708033 47263340872131389547531025)
    ·
      refine ⟨35447505654098542160648269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47263340872131389547531025 35447505654098542160648269)
      ·
        refine ⟨13292814620286953310243101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35447505654098542160648269 13292814620286953310243101)
        ·
          refine ⟨4984805482607607491341163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13292814620286953310243101 4984805482607607491341163)
          ·
            refine ⟨7477208223911411237011745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984805482607607491341163 7477208223911411237011745)
            ·
              refine ⟨5607906167933558427758809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477208223911411237011745 5607906167933558427758809)
              ·
                refine ⟨4205929625950168820819107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607906167933558427758809 4205929625950168820819107)
                ·
                  refine ⟨6308894438925253231228661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4205929625950168820819107 6308894438925253231228661)
                  ·
                    refine ⟨591458853649242490427687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6308894438925253231228661 591458853649242490427687)
                    ·
                      rfl

theorem cell22_1727793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1727793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727793 prefixEnd_1727793 := by exact prefixLift 1727793
  have htrace : WordTrace (prefixWord ++ tailWord_1727793) baseStart_1727793 baseEnd_1727793 := by
    simpa [prefixWord, tailWord_1727793, baseEnd_1727793] using wordTrace_append hprefix tailTrace_1727793
  have hstable : (prefixWord ++ tailWord_1727793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727793).length < 2 ^ (prefixWord ++ tailWord_1727793).sum := by decide
  have hdescent : baseEnd_1727793 < baseStart_1727793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727795 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 4]
def baseStart_1727795 : Nat := 118140960795 + 1727795 * 2 ^ 59
def prefixEnd_1727795 : Nat := 4983230072969 + 3 ^ 40 * 1727795 * 2
def baseEnd_1727795 : Nat := 197153179430038383959227

theorem tailTrace_1727795 : CollatzResearch.WordTrace tailWord_1727795 prefixEnd_1727795 197153179430038383959227 := by
  unfold tailWord_1727795
  simp only [CollatzResearch.WordTrace]
  refine ⟨63017860775501273738280839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42011907183667515825520559 63017860775501273738280839)
  ·
    refine ⟨94526791163251910607421259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63017860775501273738280839 94526791163251910607421259)
    ·
      refine ⟨141790186744877865911131889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94526791163251910607421259 141790186744877865911131889)
      ·
        refine ⟨106342640058658399433348917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141790186744877865911131889 106342640058658399433348917)
        ·
          refine ⟨9969622505499224946876461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106342640058658399433348917 9969622505499224946876461)
          ·
            refine ⟨3738608439562209355078673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9969622505499224946876461 3738608439562209355078673)
            ·
              refine ⟨2803956329671657016309005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3738608439562209355078673 2803956329671657016309005)
              ·
                refine ⟨1051483623626871381115877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2803956329671657016309005 1051483623626871381115877)
                ·
                  refine ⟨197153179430038383959227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051483623626871381115877 197153179430038383959227)
                  ·
                    rfl

theorem cell22_1727795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 4].length) (baseStart_1727795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727795 prefixEnd_1727795 := by exact prefixLift 1727795
  have htrace : WordTrace (prefixWord ++ tailWord_1727795) baseStart_1727795 baseEnd_1727795 := by
    simpa [prefixWord, tailWord_1727795, baseEnd_1727795] using wordTrace_append hprefix tailTrace_1727795
  have hstable : (prefixWord ++ tailWord_1727795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727795).length < 2 ^ (prefixWord ++ tailWord_1727795).sum := by decide
  have hdescent : baseEnd_1727795 < baseStart_1727795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727797 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1727797 : Nat := 118140960795 + 1727797 * 2 ^ 59
def prefixEnd_1727797 : Nat := 4983230072969 + 3 ^ 40 * 1727797 * 2
def baseEnd_1727797 : Nat := 591460222930987813327675

theorem tailTrace_1727797 : CollatzResearch.WordTrace tailWord_1727797 prefixEnd_1727797 591460222930987813327675 := by
  unfold tailWord_1727797
  simp only [CollatzResearch.WordTrace]
  refine ⟨63017933721494028079853645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42011955814329352053235763 63017933721494028079853645)
  ·
    refine ⟨23631725145560260529945117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63017933721494028079853645 23631725145560260529945117)
    ·
      refine ⟨8861896929585097698729419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23631725145560260529945117 8861896929585097698729419)
      ·
        refine ⟨13292845394377646548094129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861896929585097698729419 13292845394377646548094129)
        ·
          refine ⟨9969634045783234911070597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13292845394377646548094129 9969634045783234911070597)
          ·
            refine ⟨1869306383584356545825737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9969634045783234911070597 1869306383584356545825737)
            ·
              refine ⟨1401979787688267409369303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869306383584356545825737 1401979787688267409369303)
              ·
                refine ⟨2102969681532401114053955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401979787688267409369303 2102969681532401114053955)
                ·
                  refine ⟨3154454522298601671080933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102969681532401114053955 3154454522298601671080933)
                  ·
                    refine ⟨591460222930987813327675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154454522298601671080933 591460222930987813327675)
                    ·
                      rfl

theorem cell22_1727797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1727797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727797 prefixEnd_1727797 := by exact prefixLift 1727797
  have htrace : WordTrace (prefixWord ++ tailWord_1727797) baseStart_1727797 baseEnd_1727797 := by
    simpa [prefixWord, tailWord_1727797, baseEnd_1727797] using wordTrace_append hprefix tailTrace_1727797
  have hstable : (prefixWord ++ tailWord_1727797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727797).length < 2 ^ (prefixWord ++ tailWord_1727797).sum := by decide
  have hdescent : baseEnd_1727797 < baseStart_1727797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727812 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1727812 : Nat := 118140960795 + 1727812 * 2 ^ 59
def prefixEnd_1727812 : Nat := 4983230072969 + 3 ^ 40 * 1727812 * 2
def baseEnd_1727812 : Nat := 197155119245844258067543

theorem tailTrace_1727812 : CollatzResearch.WordTrace tailWord_1727812 prefixEnd_1727812 197155119245844258067543 := by
  unfold tailWord_1727812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31509240408219842820824845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42012320544293123761099793 31509240408219842820824845)
  ·
    refine ⟨11815965153082441057809317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31509240408219842820824845 11815965153082441057809317)
    ·
      refine ⟨2215493466202957698339247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11815965153082441057809317 2215493466202957698339247)
      ·
        refine ⟨3323240199304436547508871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215493466202957698339247 3323240199304436547508871)
        ·
          refine ⟨4984860298956654821263307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323240199304436547508871 4984860298956654821263307)
          ·
            refine ⟨7477290448434982231894961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4984860298956654821263307 7477290448434982231894961)
            ·
              refine ⟨5607967836326236673921221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477290448434982231894961 5607967836326236673921221)
              ·
                refine ⟨1051493969311169376360229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5607967836326236673921221 1051493969311169376360229)
                ·
                  refine ⟨197155119245844258067543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051493969311169376360229 197155119245844258067543)
                  ·
                    rfl

theorem cell22_1727812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1727812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727812 prefixEnd_1727812 := by exact prefixLift 1727812
  have htrace : WordTrace (prefixWord ++ tailWord_1727812) baseStart_1727812 baseEnd_1727812 := by
    simpa [prefixWord, tailWord_1727812, baseEnd_1727812] using wordTrace_append hprefix tailTrace_1727812
  have hstable : (prefixWord ++ tailWord_1727812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727812).length < 2 ^ (prefixWord ++ tailWord_1727812).sum := by decide
  have hdescent : baseEnd_1727812 < baseStart_1727812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727840 : List Nat := [2, 1, 1, 3, 4, 3, 2, 6]
def baseStart_1727840 : Nat := 118140960795 + 1727840 * 2 ^ 59
def prefixEnd_1727840 : Nat := 4983230072969 + 3 ^ 40 * 1727840 * 2
def baseEnd_1727840 : Nat := 65719438078861114944727

theorem tailTrace_1727840 : CollatzResearch.WordTrace tailWord_1727840 prefixEnd_1727840 65719438078861114944727 := by
  unfold tailWord_1727840
  simp only [CollatzResearch.WordTrace]
  refine ⟨31509751030169123211834487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42013001373558830949112649 31509751030169123211834487)
  ·
    refine ⟨47264626545253684817751731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31509751030169123211834487 47264626545253684817751731)
    ·
      refine ⟨70896939817880527226627597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47264626545253684817751731 70896939817880527226627597)
      ·
        refine ⟨26586352431705197709985349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70896939817880527226627597 26586352431705197709985349)
        ·
          refine ⟨4984941080944724570622253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26586352431705197709985349 4984941080944724570622253)
          ·
            refine ⟨1869352905354271713983345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4984941080944724570622253 1869352905354271713983345)
            ·
              refine ⟨1402014679015703785487509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869352905354271713983345 1402014679015703785487509)
              ·
                refine ⟨65719438078861114944727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1402014679015703785487509 65719438078861114944727)
                ·
                  rfl

theorem cell22_1727840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_1727840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727840 prefixEnd_1727840 := by exact prefixLift 1727840
  have htrace : WordTrace (prefixWord ++ tailWord_1727840) baseStart_1727840 baseEnd_1727840 := by
    simpa [prefixWord, tailWord_1727840, baseEnd_1727840] using wordTrace_append hprefix tailTrace_1727840
  have hstable : (prefixWord ++ tailWord_1727840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727840).length < 2 ^ (prefixWord ++ tailWord_1727840).sum := by decide
  have hdescent : baseEnd_1727840 < baseStart_1727840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727868 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_1727868 : Nat := 118140960795 + 1727868 * 2 ^ 59
def prefixEnd_1727868 : Nat := 4983230072969 + 3 ^ 40 * 1727868 * 2
def baseEnd_1727868 : Nat := 197161509227322431600819

theorem tailTrace_1727868 : CollatzResearch.WordTrace tailWord_1727868 prefixEnd_1727868 197161509227322431600819 := by
  unfold tailWord_1727868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31510261652118403602844129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42013682202824538137125505 31510261652118403602844129)
  ·
    refine ⟨23632696239088802702133097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31510261652118403602844129 23632696239088802702133097)
    ·
      refine ⟨17724522179316602026599823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23632696239088802702133097 17724522179316602026599823)
      ·
        refine ⟨26586783268974903039899735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17724522179316602026599823 26586783268974903039899735)
        ·
          refine ⟨39880174903462354559849603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26586783268974903039899735 39880174903462354559849603)
          ·
            refine ⟨59820262355193531839774405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39880174903462354559849603 59820262355193531839774405)
            ·
              refine ⟨11216299191598787219957701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59820262355193531839774405 11216299191598787219957701)
              ·
                refine ⟨2103056098424772603742069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11216299191598787219957701 2103056098424772603742069)
                ·
                  refine ⟨197161509227322431600819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103056098424772603742069 197161509227322431600819)
                  ·
                    rfl

theorem cell22_1727868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_1727868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727868 prefixEnd_1727868 := by exact prefixLift 1727868
  have htrace : WordTrace (prefixWord ++ tailWord_1727868) baseStart_1727868 baseEnd_1727868 := by
    simpa [prefixWord, tailWord_1727868, baseEnd_1727868] using wordTrace_append hprefix tailTrace_1727868
  have hstable : (prefixWord ++ tailWord_1727868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727868).length < 2 ^ (prefixWord ++ tailWord_1727868).sum := by decide
  have hdescent : baseEnd_1727868 < baseStart_1727868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727943 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1727943 : Nat := 118140960795 + 1727943 * 2 ^ 59
def prefixEnd_1727943 : Nat := 4983230072969 + 3 ^ 40 * 1727943 * 2
def baseEnd_1727943 : Nat := 591510201714692099177227

theorem tailTrace_1727943 : CollatzResearch.WordTrace tailWord_1727943 prefixEnd_1727943 591510201714692099177227 := by
  unfold tailWord_1727943
  simp only [CollatzResearch.WordTrace]
  refine ⟨63023258778965095014668483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42015505852643396676445655 63023258778965095014668483)
  ·
    refine ⟨94534888168447642522002725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63023258778965095014668483 94534888168447642522002725)
    ·
      refine ⟨17725291531583932972875511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94534888168447642522002725 17725291531583932972875511)
      ·
        refine ⟨26587937297375899459313267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17725291531583932972875511 26587937297375899459313267)
        ·
          refine ⟨39881905946063849188969901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26587937297375899459313267 39881905946063849188969901)
          ·
            refine ⟨14955714729773943445863713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39881905946063849188969901 14955714729773943445863713)
            ·
              refine ⟨11216786047330457584397785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14955714729773943445863713 11216786047330457584397785)
              ·
                refine ⟨8412589535497843188298339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11216786047330457584397785 8412589535497843188298339)
                ·
                  refine ⟨12618884303246764782447509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412589535497843188298339 12618884303246764782447509)
                  ·
                    refine ⟨591510201714692099177227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12618884303246764782447509 591510201714692099177227)
                    ·
                      rfl

theorem cell22_1727943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1727943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727943 prefixEnd_1727943 := by exact prefixLift 1727943
  have htrace : WordTrace (prefixWord ++ tailWord_1727943) baseStart_1727943 baseEnd_1727943 := by
    simpa [prefixWord, tailWord_1727943, baseEnd_1727943] using wordTrace_append hprefix tailTrace_1727943
  have hstable : (prefixWord ++ tailWord_1727943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727943).length < 2 ^ (prefixWord ++ tailWord_1727943).sum := by decide
  have hdescent : baseEnd_1727943 < baseStart_1727943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1727960 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_1727960 : Nat := 118140960795 + 1727960 * 2 ^ 59
def prefixEnd_1727960 : Nat := 4983230072969 + 3 ^ 40 * 1727960 * 2
def baseEnd_1727960 : Nat := 591516021162109721502175

theorem tailTrace_1727960 : CollatzResearch.WordTrace tailWord_1727960 prefixEnd_1727960 591516021162109721502175 := by
  unfold tailWord_1727960
  simp only [CollatzResearch.WordTrace]
  refine ⟨31511939409951753459018667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42015919213269004612024889 31511939409951753459018667)
  ·
    refine ⟨47267909114927630188528001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31511939409951753459018667 47267909114927630188528001)
    ·
      refine ⟨35450931836195722641396001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47267909114927630188528001 35450931836195722641396001)
      ·
        refine ⟨26588198877146791981047001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35450931836195722641396001 26588198877146791981047001)
        ·
          refine ⟨19941149157860093985785251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26588198877146791981047001 19941149157860093985785251)
          ·
            refine ⟨29911723736790140978677877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19941149157860093985785251 29911723736790140978677877)
            ·
              refine ⟨2804224100324075716751051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29911723736790140978677877 2804224100324075716751051)
              ·
                refine ⟨4206336150486113575126577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804224100324075716751051 4206336150486113575126577)
                ·
                  refine ⟨3154752112864585181344933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4206336150486113575126577 3154752112864585181344933)
                  ·
                    refine ⟨591516021162109721502175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3154752112864585181344933 591516021162109721502175)
                    ·
                      rfl

theorem cell22_1727960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_1727960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1727960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1727960 prefixEnd_1727960 := by exact prefixLift 1727960
  have htrace : WordTrace (prefixWord ++ tailWord_1727960) baseStart_1727960 baseEnd_1727960 := by
    simpa [prefixWord, tailWord_1727960, baseEnd_1727960] using wordTrace_append hprefix tailTrace_1727960
  have hstable : (prefixWord ++ tailWord_1727960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1727960).length < 2 ^ (prefixWord ++ tailWord_1727960).sum := by decide
  have hdescent : baseEnd_1727960 < baseStart_1727960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1727960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
