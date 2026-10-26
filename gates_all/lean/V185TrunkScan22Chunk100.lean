import V185TrunkScan22Chunk099

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_897185 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 4]
def baseStart_897185 : Nat := 118140960795 + 897185 * 2 ^ 59
def prefixEnd_897185 : Nat := 4983230072969 + 3 ^ 40 * 897185 * 2
def baseEnd_897185 : Nat := 102374920223150554058095

theorem tailTrace_897185 : CollatzResearch.WordTrace tailWord_897185 prefixEnd_897185 102374920223150554058095 := by
  unfold tailWord_897185
  simp only [CollatzResearch.WordTrace]
  refine ⟨32723025254659446844085009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21815350169772964562723339 32723025254659446844085009)
  ·
    refine ⟨24542268940994585133063757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32723025254659446844085009 24542268940994585133063757)
    ·
      refine ⟨9203350852872969424898909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24542268940994585133063757 9203350852872969424898909)
      ·
        refine ⟨3451256569827363534337091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9203350852872969424898909 3451256569827363534337091)
        ·
          refine ⟨5176884854741045301505637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451256569827363534337091 5176884854741045301505637)
          ·
            refine ⟨970665910263945994032307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5176884854741045301505637 970665910263945994032307)
            ·
              refine ⟨1455998865395918991048461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970665910263945994032307 1455998865395918991048461)
              ·
                refine ⟨545999574523469621643173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1455998865395918991048461 545999574523469621643173)
                ·
                  refine ⟨102374920223150554058095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545999574523469621643173 102374920223150554058095)
                  ·
                    rfl

theorem cell22_897185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_897185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897185 prefixEnd_897185 := by exact prefixLift 897185
  have htrace : WordTrace (prefixWord ++ tailWord_897185) baseStart_897185 baseEnd_897185 := by
    simpa [prefixWord, tailWord_897185, baseEnd_897185] using wordTrace_append hprefix tailTrace_897185
  have hstable : (prefixWord ++ tailWord_897185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897185).length < 2 ^ (prefixWord ++ tailWord_897185).sum := by decide
  have hdescent : baseEnd_897185 < baseStart_897185 := by decide
  rcases family_descends (prefixWord ++ tailWord_897185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897217 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_897217 : Nat := 118140960795 + 897217 * 2 ^ 59
def prefixEnd_897217 : Nat := 4983230072969 + 3 ^ 40 * 897217 * 2
def baseEnd_897217 : Nat := 307135714923414245374187

theorem tailTrace_897217 : CollatzResearch.WordTrace tailWord_897217 prefixEnd_897217 307135714923414245374187 := by
  unfold tailWord_897217
  simp only [CollatzResearch.WordTrace]
  refine ⟨32724192390543516309249905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21816128260362344206166603 32724192390543516309249905)
  ·
    refine ⟨24543144292907637231937429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32724192390543516309249905 24543144292907637231937429)
    ·
      refine ⟨1150459888730045495247067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24543144292907637231937429 1150459888730045495247067)
      ·
        refine ⟨1725689833095068242870601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150459888730045495247067 1725689833095068242870601)
        ·
          refine ⟨1294267374821301182152951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725689833095068242870601 1294267374821301182152951)
          ·
            refine ⟨1941401062231951773229427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294267374821301182152951 1941401062231951773229427)
            ·
              refine ⟨2912101593347927659844141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941401062231951773229427 2912101593347927659844141)
              ·
                refine ⟨1092038097505472872441553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2912101593347927659844141 1092038097505472872441553)
                ·
                  refine ⟨819028573129104654331165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092038097505472872441553 819028573129104654331165)
                  ·
                    refine ⟨307135714923414245374187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819028573129104654331165 307135714923414245374187)
                    ·
                      rfl

theorem cell22_897217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_897217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897217 prefixEnd_897217 := by exact prefixLift 897217
  have htrace : WordTrace (prefixWord ++ tailWord_897217) baseStart_897217 baseEnd_897217 := by
    simpa [prefixWord, tailWord_897217, baseEnd_897217] using wordTrace_append hprefix tailTrace_897217
  have hstable : (prefixWord ++ tailWord_897217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897217).length < 2 ^ (prefixWord ++ tailWord_897217).sum := by decide
  have hdescent : baseEnd_897217 < baseStart_897217 := by decide
  rcases family_descends (prefixWord ++ tailWord_897217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897258 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_897258 : Nat := 118140960795 + 897258 * 2 ^ 59
def prefixEnd_897258 : Nat := 4983230072969 + 3 ^ 40 * 897258 * 2
def baseEnd_897258 : Nat := 102383250020434601699687

theorem tailTrace_897258 : CollatzResearch.WordTrace tailWord_897258 prefixEnd_897258 102383250020434601699687 := by
  unfold tailWord_897258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181421945848745077873107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21817125188929986874328285 8181421945848745077873107)
  ·
    refine ⟨12272132918773117616809661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8181421945848745077873107 12272132918773117616809661)
    ·
      refine ⟨4602049844539919106303623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12272132918773117616809661 4602049844539919106303623)
      ·
        refine ⟨6903074766809878659455435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602049844539919106303623 6903074766809878659455435)
        ·
          refine ⟨10354612150214817989183153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903074766809878659455435 10354612150214817989183153)
          ·
            refine ⟨7765959112661113491887365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10354612150214817989183153 7765959112661113491887365)
            ·
              refine ⟨1456117333623958779728881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7765959112661113491887365 1456117333623958779728881)
              ·
                refine ⟨1092088000217969084796661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456117333623958779728881 1092088000217969084796661)
                ·
                  refine ⟨102383250020434601699687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092088000217969084796661 102383250020434601699687)
                  ·
                    rfl

theorem cell22_897258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_897258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897258 prefixEnd_897258 := by exact prefixLift 897258
  have htrace : WordTrace (prefixWord ++ tailWord_897258) baseStart_897258 baseEnd_897258 := by
    simpa [prefixWord, tailWord_897258, baseEnd_897258] using wordTrace_append hprefix tailTrace_897258
  have hstable : (prefixWord ++ tailWord_897258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897258).length < 2 ^ (prefixWord ++ tailWord_897258).sum := by decide
  have hdescent : baseEnd_897258 < baseStart_897258 := by decide
  rcases family_descends (prefixWord ++ tailWord_897258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897288 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_897288 : Nat := 118140960795 + 897288 * 2 ^ 59
def prefixEnd_897288 : Nat := 4983230072969 + 3 ^ 40 * 897288 * 2
def baseEnd_897288 : Nat := 307160019674393726848969

theorem tailTrace_897288 : CollatzResearch.WordTrace tailWord_897288 prefixEnd_897288 307160019674393726848969 := by
  unfold tailWord_897288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363390986643147717542259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21817854648857530290056345 16363390986643147717542259)
  ·
    refine ⟨24545086479964721576313389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16363390986643147717542259 24545086479964721576313389)
    ·
      refine ⟨9204407429986770591117521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24545086479964721576313389 9204407429986770591117521)
      ·
        refine ⟨6903305572490077943338141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9204407429986770591117521 6903305572490077943338141)
        ·
          refine ⟨2588739589683779228751803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6903305572490077943338141 2588739589683779228751803)
          ·
            refine ⟨3883109384525668843127705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588739589683779228751803 3883109384525668843127705)
            ·
              refine ⟨2912332038394251632345779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883109384525668843127705 2912332038394251632345779)
              ·
                refine ⟨4368498057591377448518669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912332038394251632345779 4368498057591377448518669)
                ·
                  refine ⟨1638186771596766543194501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4368498057591377448518669 1638186771596766543194501)
                  ·
                    refine ⟨307160019674393726848969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638186771596766543194501 307160019674393726848969)
                    ·
                      rfl

theorem cell22_897288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_897288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897288 prefixEnd_897288 := by exact prefixLift 897288
  have htrace : WordTrace (prefixWord ++ tailWord_897288) baseStart_897288 baseEnd_897288 := by
    simpa [prefixWord, tailWord_897288, baseEnd_897288] using wordTrace_append hprefix tailTrace_897288
  have hstable : (prefixWord ++ tailWord_897288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897288).length < 2 ^ (prefixWord ++ tailWord_897288).sum := by decide
  have hdescent : baseEnd_897288 < baseStart_897288 := by decide
  rcases family_descends (prefixWord ++ tailWord_897288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897320 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_897320 : Nat := 118140960795 + 897320 * 2 ^ 59
def prefixEnd_897320 : Nat := 4983230072969 + 3 ^ 40 * 897320 * 2
def baseEnd_897320 : Nat := 102390324642785436682957

theorem tailTrace_897320 : CollatzResearch.WordTrace tailWord_897320 prefixEnd_897320 102390324642785436682957 := by
  unfold tailWord_897320
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363974554585182450124707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21818632739446909933499609 16363974554585182450124707)
  ·
    refine ⟨24545961831877773675187061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16363974554585182450124707 24545961831877773675187061)
    ·
      refine ⟨2301183921738541282048787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24545961831877773675187061 2301183921738541282048787)
      ·
        refine ⟨3451775882607811923073181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301183921738541282048787 3451775882607811923073181)
        ·
          refine ⟨1294415955977929471152443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3451775882607811923073181 1294415955977929471152443)
          ·
            refine ⟨1941623933966894206728665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294415955977929471152443 1941623933966894206728665)
            ·
              refine ⟨1456217950475170655046499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941623933966894206728665 1456217950475170655046499)
              ·
                refine ⟨2184326925712755982569749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456217950475170655046499 2184326925712755982569749)
                ·
                  refine ⟨102390324642785436682957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2184326925712755982569749 102390324642785436682957)
                  ·
                    rfl

theorem cell22_897320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_897320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897320 prefixEnd_897320 := by exact prefixLift 897320
  have htrace : WordTrace (prefixWord ++ tailWord_897320) baseStart_897320 baseEnd_897320 := by
    simpa [prefixWord, tailWord_897320, baseEnd_897320] using wordTrace_append hprefix tailTrace_897320
  have hstable : (prefixWord ++ tailWord_897320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897320).length < 2 ^ (prefixWord ++ tailWord_897320).sum := by decide
  have hdescent : baseEnd_897320 < baseStart_897320 := by decide
  rcases family_descends (prefixWord ++ tailWord_897320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897331 : List Nat := [1, 1, 1, 2, 5, 1, 2, 9]
def baseStart_897331 : Nat := 118140960795 + 897331 * 2 ^ 59
def prefixEnd_897331 : Nat := 4983230072969 + 3 ^ 40 * 897331 * 2
def baseEnd_897331 : Nat := 34130526605906216447093

theorem tailTrace_897331 : CollatzResearch.WordTrace tailWord_897331 prefixEnd_897331 34130526605906216447093 := by
  unfold tailWord_897331
  simp only [CollatzResearch.WordTrace]
  refine ⟨32728350312130513778899847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21818900208087009185933231 32728350312130513778899847)
  ·
    refine ⟨49092525468195770668349771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32728350312130513778899847 49092525468195770668349771)
    ·
      refine ⟨73638788202293656002524657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49092525468195770668349771 73638788202293656002524657)
      ·
        refine ⟨55229091151720242001893493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73638788202293656002524657 55229091151720242001893493)
        ·
          refine ⟨5177727295473772687677515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55229091151720242001893493 5177727295473772687677515)
          ·
            refine ⟨7766590943210659031516273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177727295473772687677515 7766590943210659031516273)
            ·
              refine ⟨5824943207407994273637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7766590943210659031516273 5824943207407994273637205)
              ·
                refine ⟨34130526605906216447093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5824943207407994273637205 34130526605906216447093)
                ·
                  rfl

theorem cell22_897331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 9].length) (baseStart_897331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897331 prefixEnd_897331 := by exact prefixLift 897331
  have htrace : WordTrace (prefixWord ++ tailWord_897331) baseStart_897331 baseEnd_897331 := by
    simpa [prefixWord, tailWord_897331, baseEnd_897331] using wordTrace_append hprefix tailTrace_897331
  have hstable : (prefixWord ++ tailWord_897331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897331).length < 2 ^ (prefixWord ++ tailWord_897331).sum := by decide
  have hdescent : baseEnd_897331 < baseStart_897331 := by decide
  rcases family_descends (prefixWord ++ tailWord_897331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897365 : List Nat := [1, 3, 2, 2, 5, 1, 8]
def baseStart_897365 : Nat := 118140960795 + 897365 * 2 ^ 59
def prefixEnd_897365 : Nat := 4983230072969 + 3 ^ 40 * 897365 * 2
def baseEnd_897365 : Nat := 11377273272147821950879

theorem tailTrace_897365 : CollatzResearch.WordTrace tailWord_897365 prefixEnd_897365 11377273272147821950879 := by
  unfold tailWord_897365
  simp only [CollatzResearch.WordTrace]
  refine ⟨32729590394007337585637549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21819726929338225057091699 32729590394007337585637549)
  ·
    refine ⟨12273596397752751594614081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32729590394007337585637549 12273596397752751594614081)
    ·
      refine ⟨9205197298314563695960561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12273596397752751594614081 9205197298314563695960561)
      ·
        refine ⟨6903897973735922771970421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9205197298314563695960561 6903897973735922771970421)
        ·
          refine ⟨647240435037742759872227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6903897973735922771970421 647240435037742759872227)
          ·
            refine ⟨970860652556614139808341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647240435037742759872227 970860652556614139808341)
            ·
              refine ⟨11377273272147821950879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 970860652556614139808341 11377273272147821950879)
              ·
                rfl

theorem cell22_897365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 8].length) (baseStart_897365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897365 prefixEnd_897365 := by exact prefixLift 897365
  have htrace : WordTrace (prefixWord ++ tailWord_897365) baseStart_897365 baseEnd_897365 := by
    simpa [prefixWord, tailWord_897365, baseEnd_897365] using wordTrace_append hprefix tailTrace_897365
  have hstable : (prefixWord ++ tailWord_897365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897365).length < 2 ^ (prefixWord ++ tailWord_897365).sum := by decide
  have hdescent : baseEnd_897365 < baseStart_897365 := by decide
  rcases family_descends (prefixWord ++ tailWord_897365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897470 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_897470 : Nat := 118140960795 + 897470 * 2 ^ 59
def prefixEnd_897470 : Nat := 4983230072969 + 3 ^ 40 * 897470 * 2
def baseEnd_897470 : Nat := 307222321993805918798411

theorem tailTrace_897470 : CollatzResearch.WordTrace tailWord_897470 prefixEnd_897470 307222321993805918798411 := by
  unfold tailWord_897470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091677507328367564776233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21822280039084627012139909 4091677507328367564776233)
  ·
    refine ⟨3068758130496275673582175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4091677507328367564776233 3068758130496275673582175)
    ·
      refine ⟨4603137195744413510373263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068758130496275673582175 4603137195744413510373263)
      ·
        refine ⟨6904705793616620265559895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4603137195744413510373263 6904705793616620265559895)
        ·
          refine ⟨10357058690424930398339843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904705793616620265559895 10357058690424930398339843)
          ·
            refine ⟨15535588035637395597509765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10357058690424930398339843 15535588035637395597509765)
            ·
              refine ⟨2912922756682011674533081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15535588035637395597509765 2912922756682011674533081)
              ·
                refine ⟨2184692067511508755899811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912922756682011674533081 2184692067511508755899811)
                ·
                  refine ⟨3277038101267263133849717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184692067511508755899811 3277038101267263133849717)
                  ·
                    refine ⟨307222321993805918798411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3277038101267263133849717 307222321993805918798411)
                    ·
                      rfl

theorem cell22_897470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_897470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897470 prefixEnd_897470 := by exact prefixLift 897470
  have htrace : WordTrace (prefixWord ++ tailWord_897470) baseStart_897470 baseEnd_897470 := by
    simpa [prefixWord, tailWord_897470, baseEnd_897470] using wordTrace_append hprefix tailTrace_897470
  have hstable : (prefixWord ++ tailWord_897470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897470).length < 2 ^ (prefixWord ++ tailWord_897470).sum := by decide
  have hdescent : baseEnd_897470 < baseStart_897470 := by decide
  rcases family_descends (prefixWord ++ tailWord_897470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897515 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 3, 3]
def baseStart_897515 : Nat := 118140960795 + 897515 * 2 ^ 59
def prefixEnd_897515 : Nat := 4983230072969 + 3 ^ 40 * 897515 * 2
def baseEnd_897515 : Nat := 307237726413440801423273

theorem tailTrace_897515 : CollatzResearch.WordTrace tailWord_897515 prefixEnd_897515 307237726413440801423273 := by
  unfold tailWord_897515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735061343463913203597999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21823374228975942135731999 32735061343463913203597999)
  ·
    refine ⟨49102592015195869805396999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32735061343463913203597999 49102592015195869805396999)
    ·
      refine ⟨73653888022793804708095499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49102592015195869805396999 73653888022793804708095499)
      ·
        refine ⟨110480832034190707062143249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73653888022793804708095499 110480832034190707062143249)
        ·
          refine ⟨82860624025643030296607437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110480832034190707062143249 82860624025643030296607437)
          ·
            refine ⟨31072734009616136361227789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82860624025643030296607437 31072734009616136361227789)
            ·
              refine ⟨11652275253606051135460421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31072734009616136361227789 11652275253606051135460421)
              ·
                refine ⟨2184801610051134587898829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11652275253606051135460421 2184801610051134587898829)
                ·
                  refine ⟨819300603769175470462061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2184801610051134587898829 819300603769175470462061)
                  ·
                    refine ⟨307237726413440801423273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819300603769175470462061 307237726413440801423273)
                    ·
                      rfl

theorem cell22_897515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3].length) (baseStart_897515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897515 prefixEnd_897515 := by exact prefixLift 897515
  have htrace : WordTrace (prefixWord ++ tailWord_897515) baseStart_897515 baseEnd_897515 := by
    simpa [prefixWord, tailWord_897515, baseEnd_897515] using wordTrace_append hprefix tailTrace_897515
  have hstable : (prefixWord ++ tailWord_897515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897515).length < 2 ^ (prefixWord ++ tailWord_897515).sum := by decide
  have hdescent : baseEnd_897515 < baseStart_897515 := by decide
  rcases family_descends (prefixWord ++ tailWord_897515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897517 : List Nat := [1, 5, 1, 3, 1, 1, 4, 6]
def baseStart_897517 : Nat := 118140960795 + 897517 * 2 ^ 59
def prefixEnd_897517 : Nat := 4983230072969 + 3 ^ 40 * 897517 * 2
def baseEnd_897517 : Nat := 34137601228257051430363

theorem tailTrace_897517 : CollatzResearch.WordTrace tailWord_897517 prefixEnd_897517 34137601228257051430363 := by
  unfold tailWord_897517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735134289456667545170805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21823422859637778363447203 32735134289456667545170805)
  ·
    refine ⟨3068918839636562582359763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32735134289456667545170805 3068918839636562582359763)
    ·
      refine ⟨4603378259454843873539645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068918839636562582359763 4603378259454843873539645)
      ·
        refine ⟨1726266847295566452577367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4603378259454843873539645 1726266847295566452577367)
        ·
          refine ⟨2589400270943349678866051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726266847295566452577367 2589400270943349678866051)
          ·
            refine ⟨3884100406415024518299077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589400270943349678866051 3884100406415024518299077)
            ·
              refine ⟨728268826202817097181077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3884100406415024518299077 728268826202817097181077)
              ·
                refine ⟨34137601228257051430363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 728268826202817097181077 34137601228257051430363)
                ·
                  rfl

theorem cell22_897517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 6].length) (baseStart_897517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897517 prefixEnd_897517 := by exact prefixLift 897517
  have htrace : WordTrace (prefixWord ++ tailWord_897517) baseStart_897517 baseEnd_897517 := by
    simpa [prefixWord, tailWord_897517, baseEnd_897517] using wordTrace_append hprefix tailTrace_897517
  have hstable : (prefixWord ++ tailWord_897517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897517).length < 2 ^ (prefixWord ++ tailWord_897517).sum := by decide
  have hdescent : baseEnd_897517 < baseStart_897517 := by decide
  rcases family_descends (prefixWord ++ tailWord_897517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897528 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_897528 : Nat := 118140960795 + 897528 * 2 ^ 59
def prefixEnd_897528 : Nat := 4983230072969 + 3 ^ 40 * 897528 * 2
def baseEnd_897528 : Nat := 102414058859704366949411

theorem tailTrace_897528 : CollatzResearch.WordTrace tailWord_897528 prefixEnd_897528 102414058859704366949411 := by
  unfold tailWord_897528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367767746208408211910619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21823690328277877615880825 16367767746208408211910619)
  ·
    refine ⟨24551651619312612317865929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16367767746208408211910619 24551651619312612317865929)
    ·
      refine ⟨18413738714484459238399447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24551651619312612317865929 18413738714484459238399447)
      ·
        refine ⟨27620608071726688857599171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18413738714484459238399447 27620608071726688857599171)
        ·
          refine ⟨41430912107590033286398757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27620608071726688857599171 41430912107590033286398757)
          ·
            refine ⟨7768296020173131241199767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41430912107590033286398757 7768296020173131241199767)
            ·
              refine ⟨11652444030259696861799651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768296020173131241199767 11652444030259696861799651)
              ·
                refine ⟨17478666045389545292699477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652444030259696861799651 17478666045389545292699477)
                ·
                  refine ⟨102414058859704366949411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17478666045389545292699477 102414058859704366949411)
                  ·
                    rfl

theorem cell22_897528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_897528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897528 prefixEnd_897528 := by exact prefixLift 897528
  have htrace : WordTrace (prefixWord ++ tailWord_897528) baseStart_897528 baseEnd_897528 := by
    simpa [prefixWord, tailWord_897528, baseEnd_897528] using wordTrace_append hprefix tailTrace_897528
  have hstable : (prefixWord ++ tailWord_897528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897528).length < 2 ^ (prefixWord ++ tailWord_897528).sum := by decide
  have hdescent : baseEnd_897528 < baseStart_897528 := by decide
  rcases family_descends (prefixWord ++ tailWord_897528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897562 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_897562 : Nat := 118140960795 + 897562 * 2 ^ 59
def prefixEnd_897562 : Nat := 4983230072969 + 3 ^ 40 * 897562 * 2
def baseEnd_897562 : Nat := 102417938491316115166043

theorem tailTrace_897562 : CollatzResearch.WordTrace tailWord_897562 prefixEnd_897562 102417938491316115166043 := by
  unfold tailWord_897562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184193893573410057639735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21824517049529093487039293 8184193893573410057639735)
  ·
    refine ⟨12276290840360115086459603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184193893573410057639735 12276290840360115086459603)
    ·
      refine ⟨18414436260540172629689405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276290840360115086459603 18414436260540172629689405)
      ·
        refine ⟨6905413597702564736133527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18414436260540172629689405 6905413597702564736133527)
        ·
          refine ⟨10358120396553847104200291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905413597702564736133527 10358120396553847104200291)
          ·
            refine ⟨15537180594830770656300437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358120396553847104200291 15537180594830770656300437)
            ·
              refine ⟨728305340382692374514083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15537180594830770656300437 728305340382692374514083)
              ·
                refine ⟨1092458010574038561771125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728305340382692374514083 1092458010574038561771125)
                ·
                  refine ⟨102417938491316115166043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092458010574038561771125 102417938491316115166043)
                  ·
                    rfl

theorem cell22_897562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_897562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897562 prefixEnd_897562 := by exact prefixLift 897562
  have htrace : WordTrace (prefixWord ++ tailWord_897562) baseStart_897562 baseEnd_897562 := by
    simpa [prefixWord, tailWord_897562, baseEnd_897562] using wordTrace_append hprefix tailTrace_897562
  have hstable : (prefixWord ++ tailWord_897562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897562).length < 2 ^ (prefixWord ++ tailWord_897562).sum := by decide
  have hdescent : baseEnd_897562 < baseStart_897562 := by decide
  rcases family_descends (prefixWord ++ tailWord_897562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897637 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_897637 : Nat := 118140960795 + 897637 * 2 ^ 59
def prefixEnd_897637 : Nat := 4983230072969 + 3 ^ 40 * 897637 * 2
def baseEnd_897637 : Nat := 307279489506673149872899

theorem tailTrace_897637 : CollatzResearch.WordTrace tailWord_897637 prefixEnd_897637 307279489506673149872899 := by
  unfold tailWord_897637
  simp only [CollatzResearch.WordTrace]
  refine ⟨32739511049021928039539165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21826340699347952026359443 32739511049021928039539165)
  ·
    refine ⟨12277316643383223014827187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32739511049021928039539165 12277316643383223014827187)
    ·
      refine ⟨18415974965074834522240781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277316643383223014827187 18415974965074834522240781)
      ·
        refine ⟨6905990611903062945840293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18415974965074834522240781 6905990611903062945840293)
        ·
          refine ⟨1294873239731824302345055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6905990611903062945840293 1294873239731824302345055)
          ·
            refine ⟨1942309859597736453517583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294873239731824302345055 1942309859597736453517583)
            ·
              refine ⟨2913464789396604680276375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942309859597736453517583 2913464789396604680276375)
              ·
                refine ⟨4370197184094907020414563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913464789396604680276375 4370197184094907020414563)
                ·
                  refine ⟨6555295776142360530621845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370197184094907020414563 6555295776142360530621845)
                  ·
                    refine ⟨307279489506673149872899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6555295776142360530621845 307279489506673149872899)
                    ·
                      rfl

theorem cell22_897637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_897637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897637 prefixEnd_897637 := by exact prefixLift 897637
  have htrace : WordTrace (prefixWord ++ tailWord_897637) baseStart_897637 baseEnd_897637 := by
    simpa [prefixWord, tailWord_897637, baseEnd_897637] using wordTrace_append hprefix tailTrace_897637
  have hstable : (prefixWord ++ tailWord_897637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897637).length < 2 ^ (prefixWord ++ tailWord_897637).sum := by decide
  have hdescent : baseEnd_897637 < baseStart_897637 := by decide
  rcases family_descends (prefixWord ++ tailWord_897637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897667 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 3, 3]
def baseStart_897667 : Nat := 118140960795 + 897667 * 2 ^ 59
def prefixEnd_897667 : Nat := 4983230072969 + 3 ^ 40 * 897667 * 2
def baseEnd_897667 : Nat := 307289759119763071622807

theorem tailTrace_897667 : CollatzResearch.WordTrace tailWord_897667 prefixEnd_897667 307289759119763071622807 := by
  unfold tailWord_897667
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740605238913243163131255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21827070159275495442087503 32740605238913243163131255)
  ·
    refine ⟨49110907858369864744696883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32740605238913243163131255 49110907858369864744696883)
    ·
      refine ⟨73666361787554797117045325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49110907858369864744696883 73666361787554797117045325)
      ·
        refine ⟨27624885670333048918891997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73666361787554797117045325 27624885670333048918891997)
        ·
          refine ⟨10359332126374893344584499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27624885670333048918891997 10359332126374893344584499)
          ·
            refine ⟨15538998189562340016876749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359332126374893344584499 15538998189562340016876749)
            ·
              refine ⟨5827124321085877506328781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15538998189562340016876749 5827124321085877506328781)
              ·
                refine ⟨2185171620407204064873293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5827124321085877506328781 2185171620407204064873293)
                ·
                  refine ⟨819439357652701524327485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2185171620407204064873293 819439357652701524327485)
                  ·
                    refine ⟨307289759119763071622807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819439357652701524327485 307289759119763071622807)
                    ·
                      rfl

theorem cell22_897667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3].length) (baseStart_897667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897667 prefixEnd_897667 := by exact prefixLift 897667
  have htrace : WordTrace (prefixWord ++ tailWord_897667) baseStart_897667 baseEnd_897667 := by
    simpa [prefixWord, tailWord_897667, baseEnd_897667] using wordTrace_append hprefix tailTrace_897667
  have hstable : (prefixWord ++ tailWord_897667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897667).length < 2 ^ (prefixWord ++ tailWord_897667).sum := by decide
  have hdescent : baseEnd_897667 < baseStart_897667 := by decide
  rcases family_descends (prefixWord ++ tailWord_897667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897761 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_897761 : Nat := 118140960795 + 897761 * 2 ^ 59
def prefixEnd_897761 : Nat := 4983230072969 + 3 ^ 40 * 897761 * 2
def baseEnd_897761 : Nat := 307321937240778159772519

theorem tailTrace_897761 : CollatzResearch.WordTrace tailWord_897761 prefixEnd_897761 307321937240778159772519 := by
  unfold tailWord_897761
  simp only [CollatzResearch.WordTrace]
  refine ⟨32744033700572697217053137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21829355800381798144702091 32744033700572697217053137)
  ·
    refine ⟨24558025275429522912789853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32744033700572697217053137 24558025275429522912789853)
    ·
      refine ⟨9209259478286071092296195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24558025275429522912789853 9209259478286071092296195)
      ·
        refine ⟨13813889217429106638444293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209259478286071092296195 13813889217429106638444293)
        ·
          refine ⟨2590104228267957494708305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13813889217429106638444293 2590104228267957494708305)
          ·
            refine ⟨1942578171200968121031229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2590104228267957494708305 1942578171200968121031229)
            ·
              refine ⟨728466814200363045386711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942578171200968121031229 728466814200363045386711)
              ·
                refine ⟨1092700221300544568080067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728466814200363045386711 1092700221300544568080067)
                ·
                  refine ⟨1639050331950816852120101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092700221300544568080067 1639050331950816852120101)
                  ·
                    refine ⟨307321937240778159772519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639050331950816852120101 307321937240778159772519)
                    ·
                      rfl

theorem cell22_897761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_897761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897761 prefixEnd_897761 := by exact prefixLift 897761
  have htrace : WordTrace (prefixWord ++ tailWord_897761) baseStart_897761 baseEnd_897761 := by
    simpa [prefixWord, tailWord_897761, baseEnd_897761] using wordTrace_append hprefix tailTrace_897761
  have hstable : (prefixWord ++ tailWord_897761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897761).length < 2 ^ (prefixWord ++ tailWord_897761).sum := by decide
  have hdescent : baseEnd_897761 < baseStart_897761 := by decide
  rcases family_descends (prefixWord ++ tailWord_897761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897836 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_897836 : Nat := 118140960795 + 897836 * 2 ^ 59
def prefixEnd_897836 : Nat := 4983230072969 + 3 ^ 40 * 897836 * 2
def baseEnd_897836 : Nat := 307347611273502964147289

theorem tailTrace_897836 : CollatzResearch.WordTrace tailWord_897836 prefixEnd_897836 307347611273502964147289 := by
  unfold tailWord_897836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373384587650492513016681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21831179450200656684022241 16373384587650492513016681)
  ·
    refine ⟨12280038440737869384762511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16373384587650492513016681 12280038440737869384762511)
    ·
      refine ⟨18420057661106804077143767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12280038440737869384762511 18420057661106804077143767)
      ·
        refine ⟨27630086491660206115715651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18420057661106804077143767 27630086491660206115715651)
        ·
          refine ⟨41445129737490309173573477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27630086491660206115715651 41445129737490309173573477)
          ·
            refine ⟨7770961825779432970045027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41445129737490309173573477 7770961825779432970045027)
            ·
              refine ⟨11656442738669149455067541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770961825779432970045027 11656442738669149455067541)
              ·
                refine ⟨546395753375116380706291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11656442738669149455067541 546395753375116380706291)
                ·
                  refine ⟨819593630062674571059437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546395753375116380706291 819593630062674571059437)
                  ·
                    refine ⟨307347611273502964147289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819593630062674571059437 307347611273502964147289)
                    ·
                      rfl

theorem cell22_897836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_897836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897836 prefixEnd_897836 := by exact prefixLift 897836
  have htrace : WordTrace (prefixWord ++ tailWord_897836) baseStart_897836 baseEnd_897836 := by
    simpa [prefixWord, tailWord_897836, baseEnd_897836] using wordTrace_append hprefix tailTrace_897836
  have hstable : (prefixWord ++ tailWord_897836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897836).length < 2 ^ (prefixWord ++ tailWord_897836).sum := by decide
  have hdescent : baseEnd_897836 < baseStart_897836 := by decide
  rcases family_descends (prefixWord ++ tailWord_897836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897847 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_897847 : Nat := 118140960795 + 897847 * 2 ^ 59
def prefixEnd_897847 : Nat := 4983230072969 + 3 ^ 40 * 897847 * 2
def baseEnd_897847 : Nat := 307351376798302602122255

theorem tailTrace_897847 : CollatzResearch.WordTrace tailWord_897847 prefixEnd_897847 307351376798302602122255 := by
  unfold tailWord_897847
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747170378261133904683795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21831446918840755936455863 32747170378261133904683795)
  ·
    refine ⟨49120755567391700857025693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32747170378261133904683795 49120755567391700857025693)
    ·
      refine ⟨18420283337771887821384635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49120755567391700857025693 18420283337771887821384635)
      ·
        refine ⟨27630425006657831732076953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18420283337771887821384635 27630425006657831732076953)
        ·
          refine ⟨20722818754993373799057715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27630425006657831732076953 20722818754993373799057715)
          ·
            refine ⟨31084228132490060698586573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20722818754993373799057715 31084228132490060698586573)
            ·
              refine ⟨11656585549683772761969965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31084228132490060698586573 11656585549683772761969965)
              ·
                refine ⟨4371219581131414785738737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11656585549683772761969965 4371219581131414785738737)
                ·
                  refine ⟨3278414685848561089304053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371219581131414785738737 3278414685848561089304053)
                  ·
                    refine ⟨307351376798302602122255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3278414685848561089304053 307351376798302602122255)
                    ·
                      rfl

theorem cell22_897847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_897847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897847 prefixEnd_897847 := by exact prefixLift 897847
  have htrace : WordTrace (prefixWord ++ tailWord_897847) baseStart_897847 baseEnd_897847 := by
    simpa [prefixWord, tailWord_897847, baseEnd_897847] using wordTrace_append hprefix tailTrace_897847
  have hstable : (prefixWord ++ tailWord_897847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897847).length < 2 ^ (prefixWord ++ tailWord_897847).sum := by decide
  have hdescent : baseEnd_897847 < baseStart_897847 := by decide
  rcases family_descends (prefixWord ++ tailWord_897847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897907 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_897907 : Nat := 118140960795 + 897907 * 2 ^ 59
def prefixEnd_897907 : Nat := 4983230072969 + 3 ^ 40 * 897907 * 2
def baseEnd_897907 : Nat := 307371916024482445622071

theorem tailTrace_897907 : CollatzResearch.WordTrace tailWord_897907 prefixEnd_897907 307371916024482445622071 := by
  unfold tailWord_897907
  simp only [CollatzResearch.WordTrace]
  refine ⟨32749358758043764151867975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21832905838695842767911983 32749358758043764151867975)
  ·
    refine ⟨49124038137065646227801963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32749358758043764151867975 49124038137065646227801963)
    ·
      refine ⟨73686057205598469341702945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49124038137065646227801963 73686057205598469341702945)
      ·
        refine ⟨55264542904198852006277209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73686057205598469341702945 55264542904198852006277209)
        ·
          refine ⟨41448407178149139004707907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55264542904198852006277209 41448407178149139004707907)
          ·
            refine ⟨62172610767223708507061861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41448407178149139004707907 62172610767223708507061861)
            ·
              refine ⟨11657364518854445345074099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62172610767223708507061861 11657364518854445345074099)
              ·
                refine ⟨17486046778281668017611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11657364518854445345074099 17486046778281668017611149)
                ·
                  refine ⟨6557267541855625506604181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17486046778281668017611149 6557267541855625506604181)
                  ·
                    refine ⟨307371916024482445622071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6557267541855625506604181 307371916024482445622071)
                    ·
                      rfl

theorem cell22_897907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_897907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897907 prefixEnd_897907 := by exact prefixLift 897907
  have htrace : WordTrace (prefixWord ++ tailWord_897907) baseStart_897907 baseEnd_897907 := by
    simpa [prefixWord, tailWord_897907, baseEnd_897907] using wordTrace_append hprefix tailTrace_897907
  have hstable : (prefixWord ++ tailWord_897907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897907).length < 2 ^ (prefixWord ++ tailWord_897907).sum := by decide
  have hdescent : baseEnd_897907 < baseStart_897907 := by decide
  rcases family_descends (prefixWord ++ tailWord_897907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897999 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_897999 : Nat := 118140960795 + 897999 * 2 ^ 59
def prefixEnd_897999 : Nat := 4983230072969 + 3 ^ 40 * 897999 * 2
def baseEnd_897999 : Nat := 307403409504624872321789

theorem tailTrace_897999 : CollatzResearch.WordTrace tailWord_897999 prefixEnd_897999 307403409504624872321789 := by
  unfold tailWord_897999
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752714273710463864217051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21835142849140309242811367 32752714273710463864217051)
  ·
    refine ⟨49129071410565695796325577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32752714273710463864217051 49129071410565695796325577)
    ·
      refine ⟨36846803557924271847244183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49129071410565695796325577 36846803557924271847244183)
      ·
        refine ⟨55270205336886407770866275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36846803557924271847244183 55270205336886407770866275)
        ·
          refine ⟨82905308005329611656299413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55270205336886407770866275 82905308005329611656299413)
          ·
            refine ⟨3886186312749825546389035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82905308005329611656299413 3886186312749825546389035)
            ·
              refine ⟨5829279469124738319583553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886186312749825546389035 5829279469124738319583553)
              ·
                refine ⟨4371959601843553739687665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829279469124738319583553 4371959601843553739687665)
                ·
                  refine ⟨3278969701382665304765749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371959601843553739687665 3278969701382665304765749)
                  ·
                    refine ⟨307403409504624872321789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3278969701382665304765749 307403409504624872321789)
                    ·
                      rfl

theorem cell22_897999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_897999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897999 prefixEnd_897999 := by exact prefixLift 897999
  have htrace : WordTrace (prefixWord ++ tailWord_897999) baseStart_897999 baseEnd_897999 := by
    simpa [prefixWord, tailWord_897999, baseEnd_897999] using wordTrace_append hprefix tailTrace_897999
  have hstable : (prefixWord ++ tailWord_897999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897999).length < 2 ^ (prefixWord ++ tailWord_897999).sum := by decide
  have hdescent : baseEnd_897999 < baseStart_897999 := by decide
  rcases family_descends (prefixWord ++ tailWord_897999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898031 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 1, 4]
def baseStart_898031 : Nat := 118140960795 + 898031 * 2 ^ 59
def prefixEnd_898031 : Nat := 4983230072969 + 3 ^ 40 * 898031 * 2
def baseEnd_898031 : Nat := 307414363758587455521691

theorem tailTrace_898031 : CollatzResearch.WordTrace tailWord_898031 prefixEnd_898031 307414363758587455521691 := by
  unfold tailWord_898031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32753881409594533329381947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21835920939729688886254631 32753881409594533329381947)
  ·
    refine ⟨49130822114391799994072921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32753881409594533329381947 49130822114391799994072921)
    ·
      refine ⟨36848116585793849995554691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49130822114391799994072921 36848116585793849995554691)
      ·
        refine ⟨55272174878690774993332037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36848116585793849995554691 55272174878690774993332037)
        ·
          refine ⟨10363532789754520311249757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55272174878690774993332037 10363532789754520311249757)
          ·
            refine ⟨3886324796157945116718659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10363532789754520311249757 3886324796157945116718659)
            ·
              refine ⟨5829487194236917675077989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886324796157945116718659 5829487194236917675077989)
              ·
                refine ⟨1093028848919422064077123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5829487194236917675077989 1093028848919422064077123)
                ·
                  refine ⟨1639543273379133096115685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093028848919422064077123 1639543273379133096115685)
                  ·
                    refine ⟨307414363758587455521691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639543273379133096115685 307414363758587455521691)
                    ·
                      rfl

theorem cell22_898031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_898031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898031 prefixEnd_898031 := by exact prefixLift 898031
  have htrace : WordTrace (prefixWord ++ tailWord_898031) baseStart_898031 baseEnd_898031 := by
    simpa [prefixWord, tailWord_898031, baseEnd_898031] using wordTrace_append hprefix tailTrace_898031
  have hstable : (prefixWord ++ tailWord_898031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898031).length < 2 ^ (prefixWord ++ tailWord_898031).sum := by decide
  have hdescent : baseEnd_898031 < baseStart_898031 := by decide
  rcases family_descends (prefixWord ++ tailWord_898031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898136 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_898136 : Nat := 118140960795 + 898136 * 2 ^ 59
def prefixEnd_898136 : Nat := 4983230072969 + 3 ^ 40 * 898136 * 2
def baseEnd_898136 : Nat := 102483435801467393882123

theorem tailTrace_898136 : CollatzResearch.WordTrace tailWord_898136 prefixEnd_898136 102483435801467393882123 := by
  unfold tailWord_898136
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378855537107068130977131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21838474049476090841302841 16378855537107068130977131)
  ·
    refine ⟨24568283305660602196465697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16378855537107068130977131 24568283305660602196465697)
    ·
      refine ⟨18426212479245451647349273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24568283305660602196465697 18426212479245451647349273)
      ·
        refine ⟨13819659359434088735511955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18426212479245451647349273 13819659359434088735511955)
        ·
          refine ⟨20729489039151133103267933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13819659359434088735511955 20729489039151133103267933)
          ·
            refine ⟨7773558389681674913725475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20729489039151133103267933 7773558389681674913725475)
            ·
              refine ⟨11660337584522512370588213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773558389681674913725475 11660337584522512370588213)
              ·
                refine ⟨1093156648548985534742645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11660337584522512370588213 1093156648548985534742645)
                ·
                  refine ⟨102483435801467393882123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1093156648548985534742645 102483435801467393882123)
                  ·
                    rfl

theorem cell22_898136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_898136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898136 prefixEnd_898136 := by exact prefixLift 898136
  have htrace : WordTrace (prefixWord ++ tailWord_898136) baseStart_898136 baseEnd_898136 := by
    simpa [prefixWord, tailWord_898136, baseEnd_898136] using wordTrace_append hprefix tailTrace_898136
  have hstable : (prefixWord ++ tailWord_898136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898136).length < 2 ^ (prefixWord ++ tailWord_898136).sum := by decide
  have hdescent : baseEnd_898136 < baseStart_898136 := by decide
  rcases family_descends (prefixWord ++ tailWord_898136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898142 : List Nat := [4, 4, 1, 1, 1, 2, 3, 6]
def baseStart_898142 : Nat := 118140960795 + 898142 * 2 ^ 59
def prefixEnd_898142 : Nat := 4983230072969 + 3 ^ 40 * 898142 * 2
def baseEnd_898142 : Nat := 34161373480780018444039

theorem tailTrace_898142 : CollatzResearch.WordTrace tailWord_898142 prefixEnd_898142 34161373480780018444039 := by
  unfold tailWord_898142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094741239024049910834085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21838619941461599524448453 4094741239024049910834085)
  ·
    refine ⟨767763982317009358281391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4094741239024049910834085 767763982317009358281391)
    ·
      refine ⟨1151645973475514037422087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767763982317009358281391 1151645973475514037422087)
      ·
        refine ⟨1727468960213271056133131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151645973475514037422087 1727468960213271056133131)
        ·
          refine ⟨2591203440319906584199697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727468960213271056133131 2591203440319906584199697)
          ·
            refine ⟨1943402580239929938149773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591203440319906584199697 1943402580239929938149773)
            ·
              refine ⟨728775967589973726806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1943402580239929938149773 728775967589973726806165)
              ·
                refine ⟨34161373480780018444039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 728775967589973726806165 34161373480780018444039)
                ·
                  rfl

theorem cell22_898142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_898142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898142 prefixEnd_898142 := by exact prefixLift 898142
  have htrace : WordTrace (prefixWord ++ tailWord_898142) baseStart_898142 baseEnd_898142 := by
    simpa [prefixWord, tailWord_898142, baseEnd_898142] using wordTrace_append hprefix tailTrace_898142
  have hstable : (prefixWord ++ tailWord_898142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898142).length < 2 ^ (prefixWord ++ tailWord_898142).sum := by decide
  have hdescent : baseEnd_898142 < baseStart_898142 := by decide
  rcases family_descends (prefixWord ++ tailWord_898142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898157 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_898157 : Nat := 118140960795 + 898157 * 2 ^ 59
def prefixEnd_898157 : Nat := 4983230072969 + 3 ^ 40 * 898157 * 2
def baseEnd_898157 : Nat := 307457496133565126871305

theorem tailTrace_898157 : CollatzResearch.WordTrace tailWord_898157 prefixEnd_898157 307457496133565126871305 := by
  unfold tailWord_898157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32758477007138056848468725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21838984671425371232312483 32758477007138056848468725)
  ·
    refine ⟨3071107219419192829543943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32758477007138056848468725 3071107219419192829543943)
    ·
      refine ⟨4606660829128789244315915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071107219419192829543943 4606660829128789244315915)
      ·
        refine ⟨6909991243693183866473873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606660829128789244315915 6909991243693183866473873)
        ·
          refine ⟨5182493432769887899855405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909991243693183866473873 5182493432769887899855405)
          ·
            refine ⟨1943435037288707962445777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5182493432769887899855405 1943435037288707962445777)
            ·
              refine ⟨1457576277966530971834333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943435037288707962445777 1457576277966530971834333)
              ·
                refine ⟨546591104237449114437875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1457576277966530971834333 546591104237449114437875)
                ·
                  refine ⟨819886656356173671656813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546591104237449114437875 819886656356173671656813)
                  ·
                    refine ⟨307457496133565126871305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819886656356173671656813 307457496133565126871305)
                    ·
                      rfl

theorem cell22_898157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_898157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898157 prefixEnd_898157 := by exact prefixLift 898157
  have htrace : WordTrace (prefixWord ++ tailWord_898157) baseStart_898157 baseEnd_898157 := by
    simpa [prefixWord, tailWord_898157, baseEnd_898157] using wordTrace_append hprefix tailTrace_898157
  have hstable : (prefixWord ++ tailWord_898157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898157).length < 2 ^ (prefixWord ++ tailWord_898157).sum := by decide
  have hdescent : baseEnd_898157 < baseStart_898157 := by decide
  rcases family_descends (prefixWord ++ tailWord_898157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898200 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_898200 : Nat := 118140960795 + 898200 * 2 ^ 59
def prefixEnd_898200 : Nat := 4983230072969 + 3 ^ 40 * 898200 * 2
def baseEnd_898200 : Nat := 307472215912327348046173

theorem tailTrace_898200 : CollatzResearch.WordTrace tailWord_898200 prefixEnd_898200 307472215912327348046173 := by
  unfold tailWord_898200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380022672991137596142027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21840030230654850128189369 16380022672991137596142027)
  ·
    refine ⟨24570034009486706394213041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16380022672991137596142027 24570034009486706394213041)
    ·
      refine ⟨18427525507115029795659781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24570034009486706394213041 18427525507115029795659781)
      ·
        refine ⟨3455161032584068086686209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18427525507115029795659781 3455161032584068086686209)
        ·
          refine ⟨2591370774438051065014657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3455161032584068086686209 2591370774438051065014657)
          ·
            refine ⟨1943528080828538298760993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591370774438051065014657 1943528080828538298760993)
            ·
              refine ⟨1457646060621403724070745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943528080828538298760993 1457646060621403724070745)
              ·
                refine ⟨1093234545466052793053059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457646060621403724070745 1093234545466052793053059)
                ·
                  refine ⟨1639851818199079189579589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093234545466052793053059 1639851818199079189579589)
                  ·
                    refine ⟨307472215912327348046173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639851818199079189579589 307472215912327348046173)
                    ·
                      rfl

theorem cell22_898200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_898200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898200 prefixEnd_898200 := by exact prefixLift 898200
  have htrace : WordTrace (prefixWord ++ tailWord_898200) baseStart_898200 baseEnd_898200 := by
    simpa [prefixWord, tailWord_898200, baseEnd_898200] using wordTrace_append hprefix tailTrace_898200
  have hstable : (prefixWord ++ tailWord_898200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898200).length < 2 ^ (prefixWord ++ tailWord_898200).sum := by decide
  have hdescent : baseEnd_898200 < baseStart_898200 := by decide
  rcases family_descends (prefixWord ++ tailWord_898200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898211 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_898211 : Nat := 118140960795 + 898211 * 2 ^ 59
def prefixEnd_898211 : Nat := 4983230072969 + 3 ^ 40 * 898211 * 2
def baseEnd_898211 : Nat := 307475981437126986021139

theorem tailTrace_898211 : CollatzResearch.WordTrace tailWord_898211 prefixEnd_898211 307475981437126986021139 := by
  unfold tailWord_898211
  simp only [CollatzResearch.WordTrace]
  refine ⟨32760446548942424070934487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21840297699294949380622991 32760446548942424070934487)
  ·
    refine ⟨49140669823413636106401731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32760446548942424070934487 49140669823413636106401731)
    ·
      refine ⟨73711004735120454159602597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49140669823413636106401731 73711004735120454159602597)
      ·
        refine ⟨13820813387835085154925487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73711004735120454159602597 13820813387835085154925487)
        ·
          refine ⟨20731220081752627732388231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13820813387835085154925487 20731220081752627732388231)
          ·
            refine ⟨31096830122628941598582347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20731220081752627732388231 31096830122628941598582347)
            ·
              refine ⟨46645245183943412397873521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31096830122628941598582347 46645245183943412397873521)
              ·
                refine ⟨34983933887957559298405141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46645245183943412397873521 34983933887957559298405141)
                ·
                  refine ⟨1639871900998010592112741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34983933887957559298405141 1639871900998010592112741)
                  ·
                    refine ⟨307475981437126986021139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639871900998010592112741 307475981437126986021139)
                    ·
                      rfl

theorem cell22_898211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_898211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898211 prefixEnd_898211 := by exact prefixLift 898211
  have htrace : WordTrace (prefixWord ++ tailWord_898211) baseStart_898211 baseEnd_898211 := by
    simpa [prefixWord, tailWord_898211, baseEnd_898211] using wordTrace_append hprefix tailTrace_898211
  have hstable : (prefixWord ++ tailWord_898211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898211).length < 2 ^ (prefixWord ++ tailWord_898211).sum := by decide
  have hdescent : baseEnd_898211 < baseStart_898211 := by decide
  rcases family_descends (prefixWord ++ tailWord_898211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898213 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_898213 : Nat := 118140960795 + 898213 * 2 ^ 59
def prefixEnd_898213 : Nat := 4983230072969 + 3 ^ 40 * 898213 * 2
def baseEnd_898213 : Nat := 307476666077999647471133

theorem tailTrace_898213 : CollatzResearch.WordTrace tailWord_898213 prefixEnd_898213 307476666077999647471133 := by
  unfold tailWord_898213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32760519494935178412507293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21840346329956785608338195 32760519494935178412507293)
  ·
    refine ⟨12285194810600691904690235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32760519494935178412507293 12285194810600691904690235)
    ·
      refine ⟨18427792215901037857035353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12285194810600691904690235 18427792215901037857035353)
      ·
        refine ⟨13820844161925778392776515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18427792215901037857035353 13820844161925778392776515)
        ·
          refine ⟨20731266242888667589164773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13820844161925778392776515 20731266242888667589164773)
          ·
            refine ⟨3887112420541625172968395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20731266242888667589164773 3887112420541625172968395)
            ·
              refine ⟨5830668630812437759452593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887112420541625172968395 5830668630812437759452593)
              ·
                refine ⟨4373001473109328319589445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5830668630812437759452593 4373001473109328319589445)
                ·
                  refine ⟨819937776207999059923021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4373001473109328319589445 819937776207999059923021)
                  ·
                    refine ⟨307476666077999647471133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 819937776207999059923021 307476666077999647471133)
                    ·
                      rfl

theorem cell22_898213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_898213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898213 prefixEnd_898213 := by exact prefixLift 898213
  have htrace : WordTrace (prefixWord ++ tailWord_898213) baseStart_898213 baseEnd_898213 := by
    simpa [prefixWord, tailWord_898213, baseEnd_898213] using wordTrace_append hprefix tailTrace_898213
  have hstable : (prefixWord ++ tailWord_898213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898213).length < 2 ^ (prefixWord ++ tailWord_898213).sum := by decide
  have hdescent : baseEnd_898213 < baseStart_898213 := by decide
  rcases family_descends (prefixWord ++ tailWord_898213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898226 : List Nat := [3, 2, 1, 1, 1, 4, 10]
def baseStart_898226 : Nat := 118140960795 + 898226 * 2 ^ 59
def prefixEnd_898226 : Nat := 4983230072969 + 3 ^ 40 * 898226 * 2
def baseEnd_898226 : Nat := 11388189490506368403559

theorem tailTrace_898226 : CollatzResearch.WordTrace tailWord_898226 prefixEnd_898226 11388189490506368403559 := by
  unfold tailWord_898226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8190248410972020408182633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21840662429258721088487021 8190248410972020408182633)
  ·
    refine ⟨6142686308229015306136975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8190248410972020408182633 6142686308229015306136975)
    ·
      refine ⟨9214029462343522959205463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142686308229015306136975 9214029462343522959205463)
      ·
        refine ⟨13821044193515284438808195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9214029462343522959205463 13821044193515284438808195)
        ·
          refine ⟨20731566290272926658212293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13821044193515284438808195 20731566290272926658212293)
          ·
            refine ⟨3887168679426173748414805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20731566290272926658212293 3887168679426173748414805)
            ·
              refine ⟨11388189490506368403559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3887168679426173748414805 11388189490506368403559)
              ·
                rfl

theorem cell22_898226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 10].length) (baseStart_898226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898226 prefixEnd_898226 := by exact prefixLift 898226
  have htrace : WordTrace (prefixWord ++ tailWord_898226) baseStart_898226 baseEnd_898226 := by
    simpa [prefixWord, tailWord_898226, baseEnd_898226] using wordTrace_append hprefix tailTrace_898226
  have hstable : (prefixWord ++ tailWord_898226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898226).length < 2 ^ (prefixWord ++ tailWord_898226).sum := by decide
  have hdescent : baseEnd_898226 < baseStart_898226 := by decide
  rcases family_descends (prefixWord ++ tailWord_898226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898271 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 9]
def baseStart_898271 : Nat := 118140960795 + 898271 * 2 ^ 59
def prefixEnd_898271 : Nat := 4983230072969 + 3 ^ 40 * 898271 * 2
def baseEnd_898271 : Nat := 102498840221102276506985

theorem tailTrace_898271 : CollatzResearch.WordTrace tailWord_898271 prefixEnd_898271 102498840221102276506985 := by
  unfold tailWord_898271
  simp only [CollatzResearch.WordTrace]
  refine ⟨32762634928725054318118667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21841756619150036212079111 32762634928725054318118667)
  ·
    refine ⟨49143952393087581477178001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32762634928725054318118667 49143952393087581477178001)
    ·
      refine ⟨36857964294815686107883501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49143952393087581477178001 36857964294815686107883501)
      ·
        refine ⟨13821736610555882290456313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36857964294815686107883501 13821736610555882290456313)
        ·
          refine ⟨10366302457916911717842235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13821736610555882290456313 10366302457916911717842235)
          ·
            refine ⟨15549453686875367576763353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366302457916911717842235 15549453686875367576763353)
            ·
              refine ⟨11662090265156525682572515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15549453686875367576763353 11662090265156525682572515)
              ·
                refine ⟨17493135397734788523858773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11662090265156525682572515 17493135397734788523858773)
                ·
                  refine ⟨102498840221102276506985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17493135397734788523858773 102498840221102276506985)
                  ·
                    rfl

theorem cell22_898271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_898271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898271 prefixEnd_898271 := by exact prefixLift 898271
  have htrace : WordTrace (prefixWord ++ tailWord_898271) baseStart_898271 baseEnd_898271 := by
    simpa [prefixWord, tailWord_898271, baseEnd_898271] using wordTrace_append hprefix tailTrace_898271
  have hstable : (prefixWord ++ tailWord_898271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898271).length < 2 ^ (prefixWord ++ tailWord_898271).sum := by decide
  have hdescent : baseEnd_898271 < baseStart_898271 := by decide
  rcases family_descends (prefixWord ++ tailWord_898271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898303 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_898303 : Nat := 118140960795 + 898303 * 2 ^ 59
def prefixEnd_898303 : Nat := 4983230072969 + 3 ^ 40 * 898303 * 2
def baseEnd_898303 : Nat := 307507474917269412720857

theorem tailTrace_898303 : CollatzResearch.WordTrace tailWord_898303 prefixEnd_898303 307507474917269412720857 := by
  unfold tailWord_898303
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763802064609123783283563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21842534709739415855522375 32763802064609123783283563)
  ·
    refine ⟨49145703096913685674925345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32763802064609123783283563 49145703096913685674925345)
    ·
      refine ⟨36859277322685264256194009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49145703096913685674925345 36859277322685264256194009)
      ·
        refine ⟨27644457992013948192145507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36859277322685264256194009 27644457992013948192145507)
        ·
          refine ⟨41466686988020922288218261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27644457992013948192145507 41466686988020922288218261)
          ·
            refine ⟨1943750952563480732260231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41466686988020922288218261 1943750952563480732260231)
            ·
              refine ⟨2915626428845221098390347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943750952563480732260231 2915626428845221098390347)
              ·
                refine ⟨4373439643267831647585521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915626428845221098390347 4373439643267831647585521)
                ·
                  refine ⟨3280079732450873735689141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373439643267831647585521 3280079732450873735689141)
                  ·
                    refine ⟨307507474917269412720857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3280079732450873735689141 307507474917269412720857)
                    ·
                      rfl

theorem cell22_898303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_898303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898303 prefixEnd_898303 := by exact prefixLift 898303
  have htrace : WordTrace (prefixWord ++ tailWord_898303) baseStart_898303 baseEnd_898303 := by
    simpa [prefixWord, tailWord_898303, baseEnd_898303] using wordTrace_append hprefix tailTrace_898303
  have hstable : (prefixWord ++ tailWord_898303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898303).length < 2 ^ (prefixWord ++ tailWord_898303).sum := by decide
  have hdescent : baseEnd_898303 < baseStart_898303 := by decide
  rcases family_descends (prefixWord ++ tailWord_898303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898461 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_898461 : Nat := 118140960795 + 898461 * 2 ^ 59
def prefixEnd_898461 : Nat := 4983230072969 + 3 ^ 40 * 898461 * 2
def baseEnd_898461 : Nat := 307561561546209667270373

theorem tailTrace_898461 : CollatzResearch.WordTrace tailWord_898461 prefixEnd_898461 307561561546209667270373 := by
  unfold tailWord_898461
  simp only [CollatzResearch.WordTrace]
  refine ⟨32769564798036716767535237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21846376532024477845023491 32769564798036716767535237)
  ·
    refine ⟨6144293399631884393912857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32769564798036716767535237 6144293399631884393912857)
    ·
      refine ⟨4608220049723913295434643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6144293399631884393912857 4608220049723913295434643)
      ·
        refine ⟨6912330074585869943151965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608220049723913295434643 6912330074585869943151965)
        ·
          refine ⟨2592123777969701228681987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6912330074585869943151965 2592123777969701228681987)
          ·
            refine ⟨3888185666954551843022981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592123777969701228681987 3888185666954551843022981)
            ·
              refine ⟨729034812553978470566809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3888185666954551843022981 729034812553978470566809)
              ·
                refine ⟨546776109415483852925107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729034812553978470566809 546776109415483852925107)
                ·
                  refine ⟨820164164123225779387661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546776109415483852925107 820164164123225779387661)
                  ·
                    refine ⟨307561561546209667270373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820164164123225779387661 307561561546209667270373)
                    ·
                      rfl

theorem cell22_898461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_898461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898461 prefixEnd_898461 := by exact prefixLift 898461
  have htrace : WordTrace (prefixWord ++ tailWord_898461) baseStart_898461 baseEnd_898461 := by
    simpa [prefixWord, tailWord_898461, baseEnd_898461] using wordTrace_append hprefix tailTrace_898461
  have hstable : (prefixWord ++ tailWord_898461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898461).length < 2 ^ (prefixWord ++ tailWord_898461).sum := by decide
  have hdescent : baseEnd_898461 < baseStart_898461 := by decide
  rcases family_descends (prefixWord ++ tailWord_898461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898485 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 8]
def baseStart_898485 : Nat := 118140960795 + 898485 * 2 ^ 59
def prefixEnd_898485 : Nat := 4983230072969 + 3 ^ 40 * 898485 * 2
def baseEnd_898485 : Nat := 102523259078893868223433

theorem tailTrace_898485 : CollatzResearch.WordTrace tailWord_898485 prefixEnd_898485 102523259078893868223433 := by
  unfold tailWord_898485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32770440149949768866408909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21846960099966512577605939 32770440149949768866408909)
  ·
    refine ⟨12288915056231163324903341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32770440149949768866408909 12288915056231163324903341)
    ·
      refine ⟨4608343146086686246838753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12288915056231163324903341 4608343146086686246838753)
      ·
        refine ⟨3456257359565014685129065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608343146086686246838753 3456257359565014685129065)
        ·
          refine ⟨2592193019673761013846799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456257359565014685129065 2592193019673761013846799)
          ·
            refine ⟨3888289529510641520770199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592193019673761013846799 3888289529510641520770199)
            ·
              refine ⟨5832434294265962281155299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888289529510641520770199 5832434294265962281155299)
              ·
                refine ⟨8748651441398943421732949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832434294265962281155299 8748651441398943421732949)
                ·
                  refine ⟨102523259078893868223433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8748651441398943421732949 102523259078893868223433)
                  ·
                    rfl

theorem cell22_898485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_898485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898485 prefixEnd_898485 := by exact prefixLift 898485
  have htrace : WordTrace (prefixWord ++ tailWord_898485) baseStart_898485 baseEnd_898485 := by
    simpa [prefixWord, tailWord_898485, baseEnd_898485] using wordTrace_append hprefix tailTrace_898485
  have hstable : (prefixWord ++ tailWord_898485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898485).length < 2 ^ (prefixWord ++ tailWord_898485).sum := by decide
  have hdescent : baseEnd_898485 < baseStart_898485 := by decide
  rcases family_descends (prefixWord ++ tailWord_898485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898517 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_898517 : Nat := 118140960795 + 898517 * 2 ^ 59
def prefixEnd_898517 : Nat := 4983230072969 + 3 ^ 40 * 898517 * 2
def baseEnd_898517 : Nat := 307580731490644187870201

theorem tailTrace_898517 : CollatzResearch.WordTrace tailWord_898517 prefixEnd_898517 307580731490644187870201 := by
  unfold tailWord_898517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32771607285833838331573805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21847738190555892221049203 32771607285833838331573805)
  ·
    refine ⟨12289352732187689374340177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32771607285833838331573805 12289352732187689374340177)
    ·
      refine ⟨9217014549140767030755133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12289352732187689374340177 9217014549140767030755133)
      ·
        refine ⟨3456380455927787636533175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9217014549140767030755133 3456380455927787636533175)
        ·
          refine ⟨5184570683891681454799763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456380455927787636533175 5184570683891681454799763)
          ·
            refine ⟨7776856025837522182199645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184570683891681454799763 7776856025837522182199645)
            ·
              refine ⟨2916321009689070818324867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7776856025837522182199645 2916321009689070818324867)
              ·
                refine ⟨4374481514533606227487301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916321009689070818324867 4374481514533606227487301)
                ·
                  refine ⟨820215283975051167653869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4374481514533606227487301 820215283975051167653869)
                  ·
                    refine ⟨307580731490644187870201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820215283975051167653869 307580731490644187870201)
                    ·
                      rfl

theorem cell22_898517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_898517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898517 prefixEnd_898517 := by exact prefixLift 898517
  have htrace : WordTrace (prefixWord ++ tailWord_898517) baseStart_898517 baseEnd_898517 := by
    simpa [prefixWord, tailWord_898517, baseEnd_898517] using wordTrace_append hprefix tailTrace_898517
  have hstable : (prefixWord ++ tailWord_898517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898517).length < 2 ^ (prefixWord ++ tailWord_898517).sum := by decide
  have hdescent : baseEnd_898517 < baseStart_898517 := by decide
  rcases family_descends (prefixWord ++ tailWord_898517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898564 : List Nat := [2, 3, 2, 3, 3, 1, 8]
def baseStart_898564 : Nat := 118140960795 + 898564 * 2 ^ 59
def prefixEnd_898564 : Nat := 4983230072969 + 3 ^ 40 * 898564 * 2
def baseEnd_898564 : Nat := 11392474835227841923891

theorem tailTrace_898564 : CollatzResearch.WordTrace tailWord_898564 prefixEnd_898564 11392474835227841923891 := by
  unfold tailWord_898564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16386660758331782679267373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21848881011109043572356497 16386660758331782679267373)
  ·
    refine ⟨6144997784374418504725265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16386660758331782679267373 6144997784374418504725265)
    ·
      refine ⟨4608748338280813878543949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6144997784374418504725265 4608748338280813878543949)
      ·
        refine ⟨1728280626855305204453981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4608748338280813878543949 1728280626855305204453981)
        ·
          refine ⟨648105235070739451670243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1728280626855305204453981 648105235070739451670243)
          ·
            refine ⟨972157852606109177505365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648105235070739451670243 972157852606109177505365)
            ·
              refine ⟨11392474835227841923891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 972157852606109177505365 11392474835227841923891)
              ·
                rfl

theorem cell22_898564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 8].length) (baseStart_898564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898564 prefixEnd_898564 := by exact prefixLift 898564
  have htrace : WordTrace (prefixWord ++ tailWord_898564) baseStart_898564 baseEnd_898564 := by
    simpa [prefixWord, tailWord_898564, baseEnd_898564] using wordTrace_append hprefix tailTrace_898564
  have hstable : (prefixWord ++ tailWord_898564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898564).length < 2 ^ (prefixWord ++ tailWord_898564).sum := by decide
  have hdescent : baseEnd_898564 < baseStart_898564 := by decide
  rcases family_descends (prefixWord ++ tailWord_898564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898579 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 3, 3]
def baseStart_898579 : Nat := 118140960795 + 898579 * 2 ^ 59
def prefixEnd_898579 : Nat := 4983230072969 + 3 ^ 40 * 898579 * 2
def baseEnd_898579 : Nat := 307601955357696692820011

theorem tailTrace_898579 : CollatzResearch.WordTrace tailWord_898579 prefixEnd_898579 307601955357696692820011 := by
  unfold tailWord_898579
  simp only [CollatzResearch.WordTrace]
  refine ⟨32773868611609222920330791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21849245741072815280220527 32773868611609222920330791)
  ·
    refine ⟨49160802917413834380496187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32773868611609222920330791 49160802917413834380496187)
    ·
      refine ⟨73741204376120751570744281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49160802917413834380496187 73741204376120751570744281)
      ·
        refine ⟨55305903282090563678058211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73741204376120751570744281 55305903282090563678058211)
        ·
          refine ⟨82958854923135845517087317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55305903282090563678058211 82958854923135845517087317)
          ·
            refine ⟨972174081130498189653367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 82958854923135845517087317 972174081130498189653367)
            ·
              refine ⟨1458261121695747284480051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972174081130498189653367 1458261121695747284480051)
              ·
                refine ⟨2187391682543620926720077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458261121695747284480051 2187391682543620926720077)
                ·
                  refine ⟨820271880953857847520029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2187391682543620926720077 820271880953857847520029)
                  ·
                    refine ⟨307601955357696692820011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820271880953857847520029 307601955357696692820011)
                    ·
                      rfl

theorem cell22_898579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3].length) (baseStart_898579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898579 prefixEnd_898579 := by exact prefixLift 898579
  have htrace : WordTrace (prefixWord ++ tailWord_898579) baseStart_898579 baseEnd_898579 := by
    simpa [prefixWord, tailWord_898579, baseEnd_898579] using wordTrace_append hprefix tailTrace_898579
  have hstable : (prefixWord ++ tailWord_898579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898579).length < 2 ^ (prefixWord ++ tailWord_898579).sum := by decide
  have hdescent : baseEnd_898579 < baseStart_898579 := by decide
  rcases family_descends (prefixWord ++ tailWord_898579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898630 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_898630 : Nat := 118140960795 + 898630 * 2 ^ 59
def prefixEnd_898630 : Nat := 4983230072969 + 3 ^ 40 * 898630 * 2
def baseEnd_898630 : Nat := 307619413699949559794855

theorem tailTrace_898630 : CollatzResearch.WordTrace tailWord_898630 prefixEnd_898630 307619413699949559794855 := by
  unfold tailWord_898630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024241522950764332201167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21850485822949639086958229 1024241522950764332201167)
  ·
    refine ⟨1536362284426146498301751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1024241522950764332201167 1536362284426146498301751)
    ·
      refine ⟨2304543426639219747452627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1536362284426146498301751 2304543426639219747452627)
      ·
        refine ⟨3456815139958829621178941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304543426639219747452627 3456815139958829621178941)
        ·
          refine ⟨1296305677484561107942103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3456815139958829621178941 1296305677484561107942103)
          ·
            refine ⟨1944458516226841661913155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296305677484561107942103 1944458516226841661913155)
            ·
              refine ⟨2916687774340262492869733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944458516226841661913155 2916687774340262492869733)
              ·
                refine ⟨546878957688799217413075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2916687774340262492869733 546878957688799217413075)
                ·
                  refine ⟨820318436533198826119613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546878957688799217413075 820318436533198826119613)
                  ·
                    refine ⟨307619413699949559794855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820318436533198826119613 307619413699949559794855)
                    ·
                      rfl

theorem cell22_898630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_898630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898630 prefixEnd_898630 := by exact prefixLift 898630
  have htrace : WordTrace (prefixWord ++ tailWord_898630) baseStart_898630 baseEnd_898630 := by
    simpa [prefixWord, tailWord_898630, baseEnd_898630] using wordTrace_append hprefix tailTrace_898630
  have hstable : (prefixWord ++ tailWord_898630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898630).length < 2 ^ (prefixWord ++ tailWord_898630).sum := by decide
  have hdescent : baseEnd_898630 < baseStart_898630 := by decide
  rcases family_descends (prefixWord ++ tailWord_898630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898635 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_898635 : Nat := 118140960795 + 898635 * 2 ^ 59
def prefixEnd_898635 : Nat := 4983230072969 + 3 ^ 40 * 898635 * 2
def baseEnd_898635 : Nat := 307621125302131213419839

theorem tailTrace_898635 : CollatzResearch.WordTrace tailWord_898635 prefixEnd_898635 307621125302131213419839 := by
  unfold tailWord_898635
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775911099406344484369359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21850607399604229656246239 32775911099406344484369359)
  ·
    refine ⟨49163866649109516726554039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32775911099406344484369359 49163866649109516726554039)
    ·
      refine ⟨73745799973664275089831059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49163866649109516726554039 73745799973664275089831059)
      ·
        refine ⟨110618699960496412634746589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73745799973664275089831059 110618699960496412634746589)
        ·
          refine ⟨41482012485186154738029971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110618699960496412634746589 41482012485186154738029971)
          ·
            refine ⟨62223018727779232107044957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41482012485186154738029971 62223018727779232107044957)
            ·
              refine ⟨23333632022917212040141859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62223018727779232107044957 23333632022917212040141859)
              ·
                refine ⟨35000448034375818060212789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23333632022917212040141859 35000448034375818060212789)
                ·
                  refine ⟨3281292003222732943144949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35000448034375818060212789 3281292003222732943144949)
                  ·
                    refine ⟨307621125302131213419839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3281292003222732943144949 307621125302131213419839)
                    ·
                      rfl

theorem cell22_898635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_898635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898635 prefixEnd_898635 := by exact prefixLift 898635
  have htrace : WordTrace (prefixWord ++ tailWord_898635) baseStart_898635 baseEnd_898635 := by
    simpa [prefixWord, tailWord_898635, baseEnd_898635] using wordTrace_append hprefix tailTrace_898635
  have hstable : (prefixWord ++ tailWord_898635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898635).length < 2 ^ (prefixWord ++ tailWord_898635).sum := by decide
  have hdescent : baseEnd_898635 < baseStart_898635 := by decide
  rcases family_descends (prefixWord ++ tailWord_898635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898665 : List Nat := [1, 2, 1, 1, 1, 4, 2, 10]
def baseStart_898665 : Nat := 118140960795 + 898665 * 2 ^ 59
def prefixEnd_898665 : Nat := 4983230072969 + 3 ^ 40 * 898665 * 2
def baseEnd_898665 : Nat := 34181266101691237241083

theorem tailTrace_898665 : CollatzResearch.WordTrace tailWord_898665 prefixEnd_898665 34181266101691237241083 := by
  unfold tailWord_898665
  simp only [CollatzResearch.WordTrace]
  refine ⟨32777005289297659607961449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21851336859531773071974299 32777005289297659607961449)
  ·
    refine ⟨24582753966973244705971087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32777005289297659607961449 24582753966973244705971087)
    ·
      refine ⟨36874130950459867058956631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24582753966973244705971087 36874130950459867058956631)
      ·
        refine ⟨55311196425689800588434947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36874130950459867058956631 55311196425689800588434947)
        ·
          refine ⟨82966794638534700882652421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55311196425689800588434947 82966794638534700882652421)
          ·
            refine ⟨15556273994725256415497329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82966794638534700882652421 15556273994725256415497329)
            ·
              refine ⟨11667205496043942311622997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15556273994725256415497329 11667205496043942311622997)
              ·
                refine ⟨34181266101691237241083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11667205496043942311622997 34181266101691237241083)
                ·
                  rfl

theorem cell22_898665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 10].length) (baseStart_898665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898665 prefixEnd_898665 := by exact prefixLift 898665
  have htrace : WordTrace (prefixWord ++ tailWord_898665) baseStart_898665 baseEnd_898665 := by
    simpa [prefixWord, tailWord_898665, baseEnd_898665] using wordTrace_append hprefix tailTrace_898665
  have hstable : (prefixWord ++ tailWord_898665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898665).length < 2 ^ (prefixWord ++ tailWord_898665).sum := by decide
  have hdescent : baseEnd_898665 < baseStart_898665 := by decide
  rcases family_descends (prefixWord ++ tailWord_898665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898716 : List Nat := [2, 2, 3, 2, 3, 2, 2, 6]
def baseStart_898716 : Nat := 118140960795 + 898716 * 2 ^ 59
def prefixEnd_898716 : Nat := 4983230072969 + 3 ^ 40 * 898716 * 2
def baseEnd_898716 : Nat := 34183205917497111349399

theorem tailTrace_898716 : CollatzResearch.WordTrace tailWord_898716 prefixEnd_898716 34183205917497111349399 := by
  unfold tailWord_898716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389432706056447659034001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21852576941408596878712001 16389432706056447659034001)
  ·
    refine ⟨12292074529542335744275501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16389432706056447659034001 12292074529542335744275501)
    ·
      refine ⟨4609527948578375904103313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12292074529542335744275501 4609527948578375904103313)
      ·
        refine ⟨3457145961433781928077485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4609527948578375904103313 3457145961433781928077485)
        ·
          refine ⟨1296429735537668223029057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3457145961433781928077485 1296429735537668223029057)
          ·
            refine ⟨972322301653251167271793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1296429735537668223029057 972322301653251167271793)
            ·
              refine ⟨729241726239938375453845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972322301653251167271793 729241726239938375453845)
              ·
                refine ⟨34183205917497111349399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 729241726239938375453845 34183205917497111349399)
                ·
                  rfl

theorem cell22_898716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_898716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898716 prefixEnd_898716 := by exact prefixLift 898716
  have htrace : WordTrace (prefixWord ++ tailWord_898716) baseStart_898716 baseEnd_898716 := by
    simpa [prefixWord, tailWord_898716, baseEnd_898716] using wordTrace_append hprefix tailTrace_898716
  have hstable : (prefixWord ++ tailWord_898716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898716).length < 2 ^ (prefixWord ++ tailWord_898716).sum := by decide
  have hdescent : baseEnd_898716 < baseStart_898716 := by decide
  rcases family_descends (prefixWord ++ tailWord_898716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898754 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_898754 : Nat := 118140960795 + 898754 * 2 ^ 59
def prefixEnd_898754 : Nat := 4983230072969 + 3 ^ 40 * 898754 * 2
def baseEnd_898754 : Nat := 307661861434054569694475

theorem tailTrace_898754 : CollatzResearch.WordTrace tailWord_898754 prefixEnd_898754 307661861434054569694475 := by
  unfold tailWord_898754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195062846493806951987829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21853500923983485205300877 8195062846493806951987829)
  ·
    refine ⟨768287141858794401748859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8195062846493806951987829 768287141858794401748859)
    ·
      refine ⟨1152430712788191602623289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768287141858794401748859 1152430712788191602623289)
      ·
        refine ⟨864323034591143701967467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152430712788191602623289 864323034591143701967467)
        ·
          refine ⟨1296484551886715552951201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864323034591143701967467 1296484551886715552951201)
          ·
            refine ⟨972363413915036664713401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1296484551886715552951201 972363413915036664713401)
            ·
              refine ⟨729272560436277498535051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972363413915036664713401 729272560436277498535051)
              ·
                refine ⟨1093908840654416247802577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729272560436277498535051 1093908840654416247802577)
                ·
                  refine ⟨820431630490812185851933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1093908840654416247802577 820431630490812185851933)
                  ·
                    refine ⟨307661861434054569694475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820431630490812185851933 307661861434054569694475)
                    ·
                      rfl

theorem cell22_898754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_898754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898754 prefixEnd_898754 := by exact prefixLift 898754
  have htrace : WordTrace (prefixWord ++ tailWord_898754) baseStart_898754 baseEnd_898754 := by
    simpa [prefixWord, tailWord_898754, baseEnd_898754] using wordTrace_append hprefix tailTrace_898754
  have hstable : (prefixWord ++ tailWord_898754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898754).length < 2 ^ (prefixWord ++ tailWord_898754).sum := by decide
  have hdescent : baseEnd_898754 < baseStart_898754 := by decide
  rcases family_descends (prefixWord ++ tailWord_898754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898757 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_898757 : Nat := 118140960795 + 898757 * 2 ^ 59
def prefixEnd_898757 : Nat := 4983230072969 + 3 ^ 40 * 898757 * 2
def baseEnd_898757 : Nat := 307662888395363561869465

theorem tailTrace_898757 : CollatzResearch.WordTrace tailWord_898757 prefixEnd_898757 307662888395363561869465 := by
  unfold tailWord_898757
  simp only [CollatzResearch.WordTrace]
  refine ⟨32780360804964359320310525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21853573869976239546873683 32780360804964359320310525)
  ·
    refine ⟨12292635301861634745116447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32780360804964359320310525 12292635301861634745116447)
    ·
      refine ⟨18438952952792452117674671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12292635301861634745116447 18438952952792452117674671)
      ·
        refine ⟨27658429429188678176512007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18438952952792452117674671 27658429429188678176512007)
        ·
          refine ⟨41487644143783017264768011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27658429429188678176512007 41487644143783017264768011)
          ·
            refine ⟨62231466215674525897152017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41487644143783017264768011 62231466215674525897152017)
            ·
              refine ⟨46673599661755894422864013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62231466215674525897152017 46673599661755894422864013)
              ·
                refine ⟨17502599873158460408574005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46673599661755894422864013 17502599873158460408574005)
                ·
                  refine ⟨1640868738108605663303813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17502599873158460408574005 1640868738108605663303813)
                  ·
                    refine ⟨307662888395363561869465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1640868738108605663303813 307662888395363561869465)
                    ·
                      rfl

theorem cell22_898757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_898757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898757 prefixEnd_898757 := by exact prefixLift 898757
  have htrace : WordTrace (prefixWord ++ tailWord_898757) baseStart_898757 baseEnd_898757 := by
    simpa [prefixWord, tailWord_898757, baseEnd_898757] using wordTrace_append hprefix tailTrace_898757
  have hstable : (prefixWord ++ tailWord_898757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898757).length < 2 ^ (prefixWord ++ tailWord_898757).sum := by decide
  have hdescent : baseEnd_898757 < baseStart_898757 := by decide
  rcases family_descends (prefixWord ++ tailWord_898757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898866 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_898866 : Nat := 118140960795 + 898866 * 2 ^ 59
def prefixEnd_898866 : Nat := 4983230072969 + 3 ^ 40 * 898866 * 2
def baseEnd_898866 : Nat := 307700201322923610894131

theorem tailTrace_898866 : CollatzResearch.WordTrace tailWord_898866 prefixEnd_898866 307700201322923610894131 := by
  unfold tailWord_898866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196084090392367734007113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21856224241046313957352301 8196084090392367734007113)
  ·
    refine ⟨6147063067794275800505335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8196084090392367734007113 6147063067794275800505335)
    ·
      refine ⟨9220594601691413700758003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6147063067794275800505335 9220594601691413700758003)
      ·
        refine ⟨13830891902537120551137005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9220594601691413700758003 13830891902537120551137005)
        ·
          refine ⟨5186584463451420206676377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13830891902537120551137005 5186584463451420206676377)
          ·
            refine ⟨3889938347588565155007283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186584463451420206676377 3889938347588565155007283)
            ·
              refine ⟨5834907521382847732510925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889938347588565155007283 5834907521382847732510925)
              ·
                refine ⟨2188090320518567899691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834907521382847732510925 2188090320518567899691597)
                ·
                  refine ⟨820533870194462962384349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2188090320518567899691597 820533870194462962384349)
                  ·
                    refine ⟨307700201322923610894131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820533870194462962384349 307700201322923610894131)
                    ·
                      rfl

theorem cell22_898866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_898866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898866 prefixEnd_898866 := by exact prefixLift 898866
  have htrace : WordTrace (prefixWord ++ tailWord_898866) baseStart_898866 baseEnd_898866 := by
    simpa [prefixWord, tailWord_898866, baseEnd_898866] using wordTrace_append hprefix tailTrace_898866
  have hstable : (prefixWord ++ tailWord_898866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898866).length < 2 ^ (prefixWord ++ tailWord_898866).sum := by decide
  have hdescent : baseEnd_898866 < baseStart_898866 := by decide
  rcases family_descends (prefixWord ++ tailWord_898866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898900 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_898900 : Nat := 118140960795 + 898900 * 2 ^ 59
def prefixEnd_898900 : Nat := 4983230072969 + 3 ^ 40 * 898900 * 2
def baseEnd_898900 : Nat := 307711840217758855544027

theorem tailTrace_898900 : CollatzResearch.WordTrace tailWord_898900 prefixEnd_898900 307711840217758855544027 := by
  unfold tailWord_898900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392788221723147371383077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21857050962297529828510769 16392788221723147371383077)
  ·
    refine ⟨3073647791573090132134327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16392788221723147371383077 3073647791573090132134327)
    ·
      refine ⟨4610471687359635198201491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073647791573090132134327 4610471687359635198201491)
      ·
        refine ⟨6915707531039452797302237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610471687359635198201491 6915707531039452797302237)
        ·
          refine ⟨2593390324139794798988339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6915707531039452797302237 2593390324139794798988339)
          ·
            refine ⟨3890085486209692198482509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593390324139794798988339 3890085486209692198482509)
            ·
              refine ⟨1458782057328634574430941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3890085486209692198482509 1458782057328634574430941)
              ·
                refine ⟨547043271498237965411603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458782057328634574430941 547043271498237965411603)
                ·
                  refine ⟨820564907247356948117405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547043271498237965411603 820564907247356948117405)
                  ·
                    refine ⟨307711840217758855544027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820564907247356948117405 307711840217758855544027)
                    ·
                      rfl

theorem cell22_898900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_898900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898900 prefixEnd_898900 := by exact prefixLift 898900
  have htrace : WordTrace (prefixWord ++ tailWord_898900) baseStart_898900 baseEnd_898900 := by
    simpa [prefixWord, tailWord_898900, baseEnd_898900] using wordTrace_append hprefix tailTrace_898900
  have hstable : (prefixWord ++ tailWord_898900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898900).length < 2 ^ (prefixWord ++ tailWord_898900).sum := by decide
  have hdescent : baseEnd_898900 < baseStart_898900 := by decide
  rcases family_descends (prefixWord ++ tailWord_898900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898939 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_898939 : Nat := 118140960795 + 898939 * 2 ^ 59
def prefixEnd_898939 : Nat := 4983230072969 + 3 ^ 40 * 898939 * 2
def baseEnd_898939 : Nat := 307725190714775753818907

theorem tailTrace_898939 : CollatzResearch.WordTrace tailWord_898939 prefixEnd_898939 307725190714775753818907 := by
  unfold tailWord_898939
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786998890305004403435871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21857999260203336268957247 32786998890305004403435871)
  ·
    refine ⟨49180498335457506605153807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32786998890305004403435871 49180498335457506605153807)
    ·
      refine ⟨73770747503186259907730711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49180498335457506605153807 73770747503186259907730711)
      ·
        refine ⟨110656121254779389861596067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73770747503186259907730711 110656121254779389861596067)
        ·
          refine ⟨165984181882169084792394101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110656121254779389861596067 165984181882169084792394101)
          ·
            refine ⟨15561017051453351699286947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165984181882169084792394101 15561017051453351699286947)
            ·
              refine ⟨23341525577180027548930421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15561017051453351699286947 23341525577180027548930421)
              ·
                refine ⟨2188268022860627582712227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23341525577180027548930421 2188268022860627582712227)
                ·
                  refine ⟨3282402034290941374068341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188268022860627582712227 3282402034290941374068341)
                  ·
                    refine ⟨307725190714775753818907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3282402034290941374068341 307725190714775753818907)
                    ·
                      rfl

theorem cell22_898939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_898939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898939 prefixEnd_898939 := by exact prefixLift 898939
  have htrace : WordTrace (prefixWord ++ tailWord_898939) baseStart_898939 baseEnd_898939 := by
    simpa [prefixWord, tailWord_898939, baseEnd_898939] using wordTrace_append hprefix tailTrace_898939
  have hstable : (prefixWord ++ tailWord_898939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898939).length < 2 ^ (prefixWord ++ tailWord_898939).sum := by decide
  have hdescent : baseEnd_898939 < baseStart_898939 := by decide
  rcases family_descends (prefixWord ++ tailWord_898939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898973 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_898973 : Nat := 118140960795 + 898973 * 2 ^ 59
def prefixEnd_898973 : Nat := 4983230072969 + 3 ^ 40 * 898973 * 2
def baseEnd_898973 : Nat := 307736829609610998468803

theorem tailTrace_898973 : CollatzResearch.WordTrace tailWord_898973 prefixEnd_898973 307736829609610998468803 := by
  unfold tailWord_898973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32788238972181828210173573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21858825981454552140115715 32788238972181828210173573)
  ·
    refine ⟨6147794807284092789407545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32788238972181828210173573 6147794807284092789407545)
    ·
      refine ⟨4610846105463069592055659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6147794807284092789407545 4610846105463069592055659)
      ·
        refine ⟨6916269158194604388083489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610846105463069592055659 6916269158194604388083489)
        ·
          refine ⟨5187201868645953291062617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6916269158194604388083489 5187201868645953291062617)
          ·
            refine ⟨3890401401484464968296963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5187201868645953291062617 3890401401484464968296963)
            ·
              refine ⟨5835602102226697452445445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890401401484464968296963 5835602102226697452445445)
              ·
                refine ⟨1094175394167505772333521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5835602102226697452445445 1094175394167505772333521)
                ·
                  refine ⟨820631545625629329250141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1094175394167505772333521 820631545625629329250141)
                  ·
                    refine ⟨307736829609610998468803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820631545625629329250141 307736829609610998468803)
                    ·
                      rfl

theorem cell22_898973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_898973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898973 prefixEnd_898973 := by exact prefixLift 898973
  have htrace : WordTrace (prefixWord ++ tailWord_898973) baseStart_898973 baseEnd_898973 := by
    simpa [prefixWord, tailWord_898973, baseEnd_898973] using wordTrace_append hprefix tailTrace_898973
  have hstable : (prefixWord ++ tailWord_898973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898973).length < 2 ^ (prefixWord ++ tailWord_898973).sum := by decide
  have hdescent : baseEnd_898973 < baseStart_898973 := by decide
  rcases family_descends (prefixWord ++ tailWord_898973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898999 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_898999 : Nat := 118140960795 + 898999 * 2 ^ 59
def prefixEnd_898999 : Nat := 4983230072969 + 3 ^ 40 * 898999 * 2
def baseEnd_898999 : Nat := 307745729940955597318723

theorem tailTrace_898999 : CollatzResearch.WordTrace tailWord_898999 prefixEnd_898999 307745729940955597318723 := by
  unfold tailWord_898999
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789187270087634650620051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21859458180058423100413367 32789187270087634650620051)
  ·
    refine ⟨49183780905131451975930077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789187270087634650620051 49183780905131451975930077)
    ·
      refine ⟨18443917839424294490973779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49183780905131451975930077 18443917839424294490973779)
      ·
        refine ⟨27665876759136441736460669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18443917839424294490973779 27665876759136441736460669)
        ·
          refine ⟨10374703784676165651172751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27665876759136441736460669 10374703784676165651172751)
          ·
            refine ⟨15562055677014248476759127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10374703784676165651172751 15562055677014248476759127)
            ·
              refine ⟨23343083515521372715138691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15562055677014248476759127 23343083515521372715138691)
              ·
                refine ⟨35014625273282059072708037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23343083515521372715138691 35014625273282059072708037)
                ·
                  refine ⟨6565242238740386076132757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35014625273282059072708037 6565242238740386076132757)
                  ·
                    refine ⟨307745729940955597318723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6565242238740386076132757 307745729940955597318723)
                    ·
                      rfl

theorem cell22_898999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_898999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_898999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_898999 prefixEnd_898999 := by exact prefixLift 898999
  have htrace : WordTrace (prefixWord ++ tailWord_898999) baseStart_898999 baseEnd_898999 := by
    simpa [prefixWord, tailWord_898999, baseEnd_898999] using wordTrace_append hprefix tailTrace_898999
  have hstable : (prefixWord ++ tailWord_898999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898999).length < 2 ^ (prefixWord ++ tailWord_898999).sum := by decide
  have hdescent : baseEnd_898999 < baseStart_898999 := by decide
  rcases family_descends (prefixWord ++ tailWord_898999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899121 : List Nat := [1, 2, 2, 3, 1, 3, 2, 8]
def baseStart_899121 : Nat := 118140960795 + 899121 * 2 ^ 59
def prefixEnd_899121 : Nat := 4983230072969 + 3 ^ 40 * 899121 * 2
def baseEnd_899121 : Nat := 34198610337131993974261

theorem tailTrace_899121 : CollatzResearch.WordTrace tailWord_899121 prefixEnd_899121 34198610337131993974261 := by
  unfold tailWord_899121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32793636975645649486561217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21862424650430432991040811 32793636975645649486561217)
  ·
    refine ⟨24595227731734237114920913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32793636975645649486561217 24595227731734237114920913)
    ·
      refine ⟨18446420798800677836190685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24595227731734237114920913 18446420798800677836190685)
      ·
        refine ⟨6917407799550254188571507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18446420798800677836190685 6917407799550254188571507)
        ·
          refine ⟨10376111699325381282857261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917407799550254188571507 10376111699325381282857261)
          ·
            refine ⟨3891041887247017981071473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10376111699325381282857261 3891041887247017981071473)
            ·
              refine ⟨2918281415435263485803605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891041887247017981071473 2918281415435263485803605)
              ·
                refine ⟨34198610337131993974261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2918281415435263485803605 34198610337131993974261)
                ·
                  rfl

theorem cell22_899121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 8].length) (baseStart_899121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899121 prefixEnd_899121 := by exact prefixLift 899121
  have htrace : WordTrace (prefixWord ++ tailWord_899121) baseStart_899121 baseEnd_899121 := by
    simpa [prefixWord, tailWord_899121, baseEnd_899121] using wordTrace_append hprefix tailTrace_899121
  have hstable : (prefixWord ++ tailWord_899121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899121).length < 2 ^ (prefixWord ++ tailWord_899121).sum := by decide
  have hdescent : baseEnd_899121 < baseStart_899121 := by decide
  rcases family_descends (prefixWord ++ tailWord_899121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899153 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_899153 : Nat := 118140960795 + 899153 * 2 ^ 59
def prefixEnd_899153 : Nat := 4983230072969 + 3 ^ 40 * 899153 * 2
def baseEnd_899153 : Nat := 307798447288150528968251

theorem tailTrace_899153 : CollatzResearch.WordTrace tailWord_899153 prefixEnd_899153 307798447288150528968251 := by
  unfold tailWord_899153
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794804111529718951726113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21863202741019812634484075 32794804111529718951726113)
  ·
    refine ⟨24596103083647289213794585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32794804111529718951726113 24596103083647289213794585)
    ·
      refine ⟨18447077312735466910345939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24596103083647289213794585 18447077312735466910345939)
      ·
        refine ⟨27670615969103200365518909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18447077312735466910345939 27670615969103200365518909)
        ·
          refine ⟨10376480988413700137069591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27670615969103200365518909 10376480988413700137069591)
          ·
            refine ⟨15564721482620550205604387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376480988413700137069591 15564721482620550205604387)
            ·
              refine ⟨23347082223930825308406581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15564721482620550205604387 23347082223930825308406581)
              ·
                refine ⟨2188788958493514872663117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23347082223930825308406581 2188788958493514872663117)
                ·
                  refine ⟨820795859435068077248669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2188788958493514872663117 820795859435068077248669)
                  ·
                    refine ⟨307798447288150528968251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 820795859435068077248669 307798447288150528968251)
                    ·
                      rfl

theorem cell22_899153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_899153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899153 prefixEnd_899153 := by exact prefixLift 899153
  have htrace : WordTrace (prefixWord ++ tailWord_899153) baseStart_899153 baseEnd_899153 := by
    simpa [prefixWord, tailWord_899153, baseEnd_899153] using wordTrace_append hprefix tailTrace_899153
  have hstable : (prefixWord ++ tailWord_899153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899153).length < 2 ^ (prefixWord ++ tailWord_899153).sum := by decide
  have hdescent : baseEnd_899153 < baseStart_899153 := by decide
  rcases family_descends (prefixWord ++ tailWord_899153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899228 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_899228 : Nat := 118140960795 + 899228 * 2 ^ 59
def prefixEnd_899228 : Nat := 4983230072969 + 3 ^ 40 * 899228 * 2
def baseEnd_899228 : Nat := 102608040440291777781007

theorem tailTrace_899228 : CollatzResearch.WordTrace tailWord_899228 prefixEnd_899228 102608040440291777781007 := by
  unfold tailWord_899228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16398769793129003380353169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21865026390838671173804225 16398769793129003380353169)
  ·
    refine ⟨12299077344846752535264877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16398769793129003380353169 12299077344846752535264877)
    ·
      refine ⟨4612154004317532200724329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12299077344846752535264877 4612154004317532200724329)
      ·
        refine ⟨3459115503238149150543247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4612154004317532200724329 3459115503238149150543247)
        ·
          refine ⟨5188673254857223725814871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459115503238149150543247 5188673254857223725814871)
          ·
            refine ⟨7783009882285835588722307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188673254857223725814871 7783009882285835588722307)
            ·
              refine ⟨11674514823428753383083461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7783009882285835588722307 11674514823428753383083461)
              ·
                refine ⟨2188971529392891259328149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11674514823428753383083461 2188971529392891259328149)
                ·
                  refine ⟨102608040440291777781007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2188971529392891259328149 102608040440291777781007)
                  ·
                    rfl

theorem cell22_899228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_899228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899228 prefixEnd_899228 := by exact prefixLift 899228
  have htrace : WordTrace (prefixWord ++ tailWord_899228) baseStart_899228 baseEnd_899228 := by
    simpa [prefixWord, tailWord_899228, baseEnd_899228] using wordTrace_append hprefix tailTrace_899228
  have hstable : (prefixWord ++ tailWord_899228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899228).length < 2 ^ (prefixWord ++ tailWord_899228).sum := by decide
  have hdescent : baseEnd_899228 < baseStart_899228 := by decide
  rcases family_descends (prefixWord ++ tailWord_899228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899258 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_899258 : Nat := 118140960795 + 899258 * 2 ^ 59
def prefixEnd_899258 : Nat := 4983230072969 + 3 ^ 40 * 899258 * 2
def baseEnd_899258 : Nat := 307834390933965255092929

theorem tailTrace_899258 : CollatzResearch.WordTrace tailWord_899258 prefixEnd_899258 307834390933965255092929 := by
  unfold tailWord_899258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8199658444037330471074607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21865755850766214589532285 8199658444037330471074607)
  ·
    refine ⟨12299487666055995706611911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8199658444037330471074607 12299487666055995706611911)
    ·
      refine ⟨18449231499083993559917867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12299487666055995706611911 18449231499083993559917867)
      ·
        refine ⟨27673847248625990339876801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18449231499083993559917867 27673847248625990339876801)
        ·
          refine ⟨20755385436469492754907601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27673847248625990339876801 20755385436469492754907601)
          ·
            refine ⟨15566539077352119566180701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20755385436469492754907601 15566539077352119566180701)
            ·
              refine ⟨5837452154007044837317763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15566539077352119566180701 5837452154007044837317763)
              ·
                refine ⟨8756178231010567255976645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837452154007044837317763 8756178231010567255976645)
                ·
                  refine ⟨1641783418314481360495621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8756178231010567255976645 1641783418314481360495621)
                  ·
                    refine ⟨307834390933965255092929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641783418314481360495621 307834390933965255092929)
                    ·
                      rfl

theorem cell22_899258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_899258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899258 prefixEnd_899258 := by exact prefixLift 899258
  have htrace : WordTrace (prefixWord ++ tailWord_899258) baseStart_899258 baseEnd_899258 := by
    simpa [prefixWord, tailWord_899258, baseEnd_899258] using wordTrace_append hprefix tailTrace_899258
  have hstable : (prefixWord ++ tailWord_899258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899258).length < 2 ^ (prefixWord ++ tailWord_899258).sum := by decide
  have hdescent : baseEnd_899258 < baseStart_899258 := by decide
  rcases family_descends (prefixWord ++ tailWord_899258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899262 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_899262 : Nat := 118140960795 + 899262 * 2 ^ 59
def prefixEnd_899262 : Nat := 4983230072969 + 3 ^ 40 * 899262 * 2
def baseEnd_899262 : Nat := 102611920071903525997639

theorem tailTrace_899262 : CollatzResearch.WordTrace tailWord_899262 prefixEnd_899262 102611920071903525997639 := by
  unfold tailWord_899262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099847458516853820930505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21865853112089887044962693 4099847458516853820930505)
  ·
    refine ⟨3074885593887640365697879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4099847458516853820930505 3074885593887640365697879)
    ·
      refine ⟨4612328390831460548546819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3074885593887640365697879 4612328390831460548546819)
      ·
        refine ⟨6918492586247190822820229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612328390831460548546819 6918492586247190822820229)
        ·
          refine ⟨1297217359921348279278793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6918492586247190822820229 1297217359921348279278793)
          ·
            refine ⟨972913019941011209459095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297217359921348279278793 972913019941011209459095)
            ·
              refine ⟨1459369529911516814188643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972913019941011209459095 1459369529911516814188643)
              ·
                refine ⟨2189054294867275221282965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459369529911516814188643 2189054294867275221282965)
                ·
                  refine ⟨102611920071903525997639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2189054294867275221282965 102611920071903525997639)
                  ·
                    rfl

theorem cell22_899262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_899262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899262 prefixEnd_899262 := by exact prefixLift 899262
  have htrace : WordTrace (prefixWord ++ tailWord_899262) baseStart_899262 baseEnd_899262 := by
    simpa [prefixWord, tailWord_899262, baseEnd_899262] using wordTrace_append hprefix tailTrace_899262
  have hstable : (prefixWord ++ tailWord_899262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899262).length < 2 ^ (prefixWord ++ tailWord_899262).sum := by decide
  have hdescent : baseEnd_899262 < baseStart_899262 := by decide
  rcases family_descends (prefixWord ++ tailWord_899262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899298 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_899298 : Nat := 118140960795 + 899298 * 2 ^ 59
def prefixEnd_899298 : Nat := 4983230072969 + 3 ^ 40 * 899298 * 2
def baseEnd_899298 : Nat := 307848083751418484092807

theorem tailTrace_899298 : CollatzResearch.WordTrace tailWord_899298 prefixEnd_899298 307848083751418484092807 := by
  unfold tailWord_899298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200023174001102178938637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21866728464002939143836365 8200023174001102178938637)
  ·
    refine ⟨3075008690250413317101989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8200023174001102178938637 3075008690250413317101989)
    ·
      refine ⟨576564129421952496956623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3075008690250413317101989 576564129421952496956623)
      ·
        refine ⟨864846194132928745434935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576564129421952496956623 864846194132928745434935)
        ·
          refine ⟨1297269291199393118152403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864846194132928745434935 1297269291199393118152403)
          ·
            refine ⟨1945903936799089677228605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297269291199393118152403 1945903936799089677228605)
            ·
              refine ⟨729713976299658628960727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1945903936799089677228605 729713976299658628960727)
              ·
                refine ⟨1094570964449487943441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729713976299658628960727 1094570964449487943441091)
                ·
                  refine ⟨1641856446674231915161637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094570964449487943441091 1641856446674231915161637)
                  ·
                    refine ⟨307848083751418484092807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641856446674231915161637 307848083751418484092807)
                    ·
                      rfl

theorem cell22_899298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_899298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899298 prefixEnd_899298 := by exact prefixLift 899298
  have htrace : WordTrace (prefixWord ++ tailWord_899298) baseStart_899298 baseEnd_899298 := by
    simpa [prefixWord, tailWord_899298, baseEnd_899298] using wordTrace_append hprefix tailTrace_899298
  have hstable : (prefixWord ++ tailWord_899298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899298).length < 2 ^ (prefixWord ++ tailWord_899298).sum := by decide
  have hdescent : baseEnd_899298 < baseStart_899298 := by decide
  rcases family_descends (prefixWord ++ tailWord_899298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899363 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 8]
def baseStart_899363 : Nat := 118140960795 + 899363 * 2 ^ 59
def prefixEnd_899363 : Nat := 4983230072969 + 3 ^ 40 * 899363 * 2
def baseEnd_899363 : Nat := 102623444859926660405869

theorem tailTrace_899363 : CollatzResearch.WordTrace tailWord_899363 prefixEnd_899363 102623444859926660405869 := by
  unfold tailWord_899363
  simp only [CollatzResearch.WordTrace]
  refine ⟨32802463440768924816870743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21868308960512616544580495 32802463440768924816870743)
  ·
    refine ⟨49203695161153387225306115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32802463440768924816870743 49203695161153387225306115)
    ·
      refine ⟨73805542741730080837959173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49203695161153387225306115 73805542741730080837959173)
      ·
        refine ⟨13838539264074390157117345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73805542741730080837959173 13838539264074390157117345)
        ·
          refine ⟨10378904448055792617838009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13838539264074390157117345 10378904448055792617838009)
          ·
            refine ⟨7784178336041844463378507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10378904448055792617838009 7784178336041844463378507)
            ·
              refine ⟨11676267504062766695067761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7784178336041844463378507 11676267504062766695067761)
              ·
                refine ⟨8757200628047075021300821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11676267504062766695067761 8757200628047075021300821)
                ·
                  refine ⟨102623444859926660405869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8757200628047075021300821 102623444859926660405869)
                  ·
                    rfl

theorem cell22_899363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_899363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899363 prefixEnd_899363 := by exact prefixLift 899363
  have htrace : WordTrace (prefixWord ++ tailWord_899363) baseStart_899363 baseEnd_899363 := by
    simpa [prefixWord, tailWord_899363, baseEnd_899363] using wordTrace_append hprefix tailTrace_899363
  have hstable : (prefixWord ++ tailWord_899363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899363).length < 2 ^ (prefixWord ++ tailWord_899363).sum := by decide
  have hdescent : baseEnd_899363 < baseStart_899363 := by decide
  rcases family_descends (prefixWord ++ tailWord_899363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899395 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 1, 5]
def baseStart_899395 : Nat := 118140960795 + 899395 * 2 ^ 59
def prefixEnd_899395 : Nat := 4983230072969 + 3 ^ 40 * 899395 * 2
def baseEnd_899395 : Nat := 307881288833742564417509

theorem tailTrace_899395 : CollatzResearch.WordTrace tailWord_899395 prefixEnd_899395 307881288833742564417509 := by
  unfold tailWord_899395
  simp only [CollatzResearch.WordTrace]
  refine ⟨32803630576652994282035639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21869087051101996188023759 32803630576652994282035639)
  ·
    refine ⟨49205445864979491423053459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32803630576652994282035639 49205445864979491423053459)
    ·
      refine ⟨73808168797469237134580189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49205445864979491423053459 73808168797469237134580189)
      ·
        refine ⟨27678063299050963925467571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73808168797469237134580189 27678063299050963925467571)
        ·
          refine ⟨41517094948576445888201357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27678063299050963925467571 41517094948576445888201357)
          ·
            refine ⟨15568910605716167208075509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41517094948576445888201357 15568910605716167208075509)
            ·
              refine ⟨1459585369285890675757079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15568910605716167208075509 1459585369285890675757079)
              ·
                refine ⟨2189378053928836013635619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459585369285890675757079 2189378053928836013635619)
                ·
                  refine ⟨3284067080893254020453429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189378053928836013635619 3284067080893254020453429)
                  ·
                    refine ⟨307881288833742564417509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3284067080893254020453429 307881288833742564417509)
                    ·
                      rfl

theorem cell22_899395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_899395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899395 prefixEnd_899395 := by exact prefixLift 899395
  have htrace : WordTrace (prefixWord ++ tailWord_899395) baseStart_899395 baseEnd_899395 := by
    simpa [prefixWord, tailWord_899395, baseEnd_899395] using wordTrace_append hprefix tailTrace_899395
  have hstable : (prefixWord ++ tailWord_899395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899395).length < 2 ^ (prefixWord ++ tailWord_899395).sum := by decide
  have hdescent : baseEnd_899395 < baseStart_899395 := by decide
  rcases family_descends (prefixWord ++ tailWord_899395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899410 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_899410 : Nat := 118140960795 + 899410 * 2 ^ 59
def prefixEnd_899410 : Nat := 4983230072969 + 3 ^ 40 * 899410 * 2
def baseEnd_899410 : Nat := 307886423640287525292463

theorem tailTrace_899410 : CollatzResearch.WordTrace tailWord_899410 prefixEnd_899410 307886423640287525292463 := by
  unfold tailWord_899410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201044417899662960957921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21869451781065767895887789 8201044417899662960957921)
  ·
    refine ⟨6150783313424747220718441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8201044417899662960957921 6150783313424747220718441)
    ·
      refine ⟨4613087485068560415538831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6150783313424747220718441 4613087485068560415538831)
      ·
        refine ⟨6919631227602840623308247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613087485068560415538831 6919631227602840623308247)
        ·
          refine ⟨10379446841404260934962371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919631227602840623308247 10379446841404260934962371)
          ·
            refine ⟨15569170262106391402443557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10379446841404260934962371 15569170262106391402443557)
            ·
              refine ⟨2919219424144948387958167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15569170262106391402443557 2919219424144948387958167)
              ·
                refine ⟨4378829136217422581937251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919219424144948387958167 4378829136217422581937251)
                ·
                  refine ⟨6568243704326133872905877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4378829136217422581937251 6568243704326133872905877)
                  ·
                    refine ⟨307886423640287525292463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6568243704326133872905877 307886423640287525292463)
                    ·
                      rfl

theorem cell22_899410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_899410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899410 prefixEnd_899410 := by exact prefixLift 899410
  have htrace : WordTrace (prefixWord ++ tailWord_899410) baseStart_899410 baseEnd_899410 := by
    simpa [prefixWord, tailWord_899410, baseEnd_899410] using wordTrace_append hprefix tailTrace_899410
  have hstable : (prefixWord ++ tailWord_899410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899410).length < 2 ^ (prefixWord ++ tailWord_899410).sum := by decide
  have hdescent : baseEnd_899410 < baseStart_899410 := by decide
  rcases family_descends (prefixWord ++ tailWord_899410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899412 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_899412 : Nat := 118140960795 + 899412 * 2 ^ 59
def prefixEnd_899412 : Nat := 4983230072969 + 3 ^ 40 * 899412 * 2
def baseEnd_899412 : Nat := 307887108281160186742457

theorem tailTrace_899412 : CollatzResearch.WordTrace tailWord_899412 prefixEnd_899412 307887108281160186742457 := by
  unfold tailWord_899412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16402125308795703092702245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21869500411727604123602993 16402125308795703092702245)
  ·
    refine ⟨3075398495399194329881671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16402125308795703092702245 3075398495399194329881671)
    ·
      refine ⟨4613097743098791494822507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075398495399194329881671 4613097743098791494822507)
      ·
        refine ⟨6919646614648187242233761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613097743098791494822507 6919646614648187242233761)
        ·
          refine ⟨5189734960986140431675321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6919646614648187242233761 5189734960986140431675321)
          ·
            refine ⟨3892301220739605323756491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189734960986140431675321 3892301220739605323756491)
            ·
              refine ⟨5838451831109407985634737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892301220739605323756491 5838451831109407985634737)
              ·
                refine ⟨4378838873332055989226053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5838451831109407985634737 4378838873332055989226053)
                ·
                  refine ⟨821032288749760497979885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4378838873332055989226053 821032288749760497979885)
                  ·
                    refine ⟨307887108281160186742457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821032288749760497979885 307887108281160186742457)
                    ·
                      rfl

theorem cell22_899412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_899412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899412 prefixEnd_899412 := by exact prefixLift 899412
  have htrace : WordTrace (prefixWord ++ tailWord_899412) baseStart_899412 baseEnd_899412 := by
    simpa [prefixWord, tailWord_899412, baseEnd_899412] using wordTrace_append hprefix tailTrace_899412
  have hstable : (prefixWord ++ tailWord_899412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899412).length < 2 ^ (prefixWord ++ tailWord_899412).sum := by decide
  have hdescent : baseEnd_899412 < baseStart_899412 := by decide
  rcases family_descends (prefixWord ++ tailWord_899412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899487 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 5]
def baseStart_899487 : Nat := 118140960795 + 899487 * 2 ^ 59
def prefixEnd_899487 : Nat := 4983230072969 + 3 ^ 40 * 899487 * 2
def baseEnd_899487 : Nat := 102637594104628330372409

theorem tailTrace_899487 : CollatzResearch.WordTrace tailWord_899487 prefixEnd_899487 102637594104628330372409 := by
  unfold tailWord_899487
  simp only [CollatzResearch.WordTrace]
  refine ⟨32806986092319693994384715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21871324061546462662923143 32806986092319693994384715)
  ·
    refine ⟨49210479138479540991577073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32806986092319693994384715 49210479138479540991577073)
    ·
      refine ⟨36907859353859655743682805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49210479138479540991577073 36907859353859655743682805)
      ·
        refine ⟨3460111814424342725970263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36907859353859655743682805 3460111814424342725970263)
        ·
          refine ⟨5190167721636514088955395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460111814424342725970263 5190167721636514088955395)
          ·
            refine ⟨7785251582454771133433093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190167721636514088955395 7785251582454771133433093)
            ·
              refine ⟨1459734671710269587518705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7785251582454771133433093 1459734671710269587518705)
              ·
                refine ⟨1094801003782702190639029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459734671710269587518705 1094801003782702190639029)
                ·
                  refine ⟨102637594104628330372409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094801003782702190639029 102637594104628330372409)
                  ·
                    rfl

theorem cell22_899487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 5].length) (baseStart_899487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899487 prefixEnd_899487 := by exact prefixLift 899487
  have htrace : WordTrace (prefixWord ++ tailWord_899487) baseStart_899487 baseEnd_899487 := by
    simpa [prefixWord, tailWord_899487, baseEnd_899487] using wordTrace_append hprefix tailTrace_899487
  have hstable : (prefixWord ++ tailWord_899487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899487).length < 2 ^ (prefixWord ++ tailWord_899487).sum := by decide
  have hdescent : baseEnd_899487 < baseStart_899487 := by decide
  rcases family_descends (prefixWord ++ tailWord_899487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899491 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 1, 3]
def baseStart_899491 : Nat := 118140960795 + 899491 * 2 ^ 59
def prefixEnd_899491 : Nat := 4983230072969 + 3 ^ 40 * 899491 * 2
def baseEnd_899491 : Nat := 307914151595630314017215

theorem tailTrace_899491 : CollatzResearch.WordTrace tailWord_899491 prefixEnd_899491 307914151595630314017215 := by
  unfold tailWord_899491
  simp only [CollatzResearch.WordTrace]
  refine ⟨32807131984305202677530327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21871421322870135118353551 32807131984305202677530327)
  ·
    refine ⟨49210697976457804016295491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32807131984305202677530327 49210697976457804016295491)
    ·
      refine ⟨73816046964686706024443237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49210697976457804016295491 73816046964686706024443237)
      ·
        refine ⟨13840508805878757379583107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73816046964686706024443237 13840508805878757379583107)
        ·
          refine ⟨20760763208818136069374661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13840508805878757379583107 20760763208818136069374661)
          ·
            refine ⟨3892643101653400513007749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20760763208818136069374661 3892643101653400513007749)
            ·
              refine ⟨729870581560012596188953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3892643101653400513007749 729870581560012596188953)
              ·
                refine ⟨547402936170009447141715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729870581560012596188953 547402936170009447141715)
                ·
                  refine ⟨821104404255014170712573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547402936170009447141715 821104404255014170712573)
                  ·
                    refine ⟨307914151595630314017215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821104404255014170712573 307914151595630314017215)
                    ·
                      rfl

theorem cell22_899491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 3].length) (baseStart_899491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899491 prefixEnd_899491 := by exact prefixLift 899491
  have htrace : WordTrace (prefixWord ++ tailWord_899491) baseStart_899491 baseEnd_899491 := by
    simpa [prefixWord, tailWord_899491, baseEnd_899491] using wordTrace_append hprefix tailTrace_899491
  have hstable : (prefixWord ++ tailWord_899491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899491).length < 2 ^ (prefixWord ++ tailWord_899491).sum := by decide
  have hdescent : baseEnd_899491 < baseStart_899491 := by decide
  rcases family_descends (prefixWord ++ tailWord_899491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899508 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_899508 : Nat := 118140960795 + 899508 * 2 ^ 59
def prefixEnd_899508 : Nat := 4983230072969 + 3 ^ 40 * 899508 * 2
def baseEnd_899508 : Nat := 307919971043047936342163

theorem tailTrace_899508 : CollatzResearch.WordTrace tailWord_899508 prefixEnd_899508 307919971043047936342163 := by
  unfold tailWord_899508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16403876012621807290449589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21871834683495743053932785 16403876012621807290449589)
  ·
    refine ⟨1537863376183294433479649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16403876012621807290449589 1537863376183294433479649)
    ·
      refine ⟨1153397532137470825109737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1537863376183294433479649 1153397532137470825109737)
      ·
        refine ⟨865048149103103118832303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1153397532137470825109737 865048149103103118832303)
        ·
          refine ⟨1297572223654654678248455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865048149103103118832303 1297572223654654678248455)
          ·
            refine ⟨1946358335481982017372683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297572223654654678248455 1946358335481982017372683)
            ·
              refine ⟨2919537503222973026059025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946358335481982017372683 2919537503222973026059025)
              ·
                refine ⟨2189653127417229769544269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2919537503222973026059025 2189653127417229769544269)
                ·
                  refine ⟨821119922781461163579101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2189653127417229769544269 821119922781461163579101)
                  ·
                    refine ⟨307919971043047936342163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821119922781461163579101 307919971043047936342163)
                    ·
                      rfl

theorem cell22_899508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_899508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899508 prefixEnd_899508 := by exact prefixLift 899508
  have htrace : WordTrace (prefixWord ++ tailWord_899508) baseStart_899508 baseEnd_899508 := by
    simpa [prefixWord, tailWord_899508, baseEnd_899508] using wordTrace_append hprefix tailTrace_899508
  have hstable : (prefixWord ++ tailWord_899508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899508).length < 2 ^ (prefixWord ++ tailWord_899508).sum := by decide
  have hdescent : baseEnd_899508 < baseStart_899508 := by decide
  rcases family_descends (prefixWord ++ tailWord_899508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899517 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_899517 : Nat := 118140960795 + 899517 * 2 ^ 59
def prefixEnd_899517 : Nat := 4983230072969 + 3 ^ 40 * 899517 * 2
def baseEnd_899517 : Nat := 307923051926974912867135

theorem tailTrace_899517 : CollatzResearch.WordTrace tailWord_899517 prefixEnd_899517 307923051926974912867135 := by
  unfold tailWord_899517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32808080282211009117976805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21872053521474006078651203 32808080282211009117976805)
  ·
    refine ⟨6151515052914564209620651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32808080282211009117976805 6151515052914564209620651)
    ·
      refine ⟨9227272579371846314430977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151515052914564209620651 9227272579371846314430977)
      ·
        refine ⟨6920454434528884735823233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227272579371846314430977 6920454434528884735823233)
        ·
          refine ⟨5190340825896663551867425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920454434528884735823233 5190340825896663551867425)
          ·
            refine ⟨3892755619422497663900569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5190340825896663551867425 3892755619422497663900569)
            ·
              refine ⟨2919566714566873247925427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3892755619422497663900569 2919566714566873247925427)
              ·
                refine ⟨4379350071850309871888141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919566714566873247925427 4379350071850309871888141)
                ·
                  refine ⟨1642256276943866201958053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4379350071850309871888141 1642256276943866201958053)
                  ·
                    refine ⟨307923051926974912867135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1642256276943866201958053 307923051926974912867135)
                    ·
                      rfl

theorem cell22_899517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_899517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899517 prefixEnd_899517 := by exact prefixLift 899517
  have htrace : WordTrace (prefixWord ++ tailWord_899517) baseStart_899517 baseEnd_899517 := by
    simpa [prefixWord, tailWord_899517, baseEnd_899517] using wordTrace_append hprefix tailTrace_899517
  have hstable : (prefixWord ++ tailWord_899517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899517).length < 2 ^ (prefixWord ++ tailWord_899517).sum := by decide
  have hdescent : baseEnd_899517 < baseStart_899517 := by decide
  rcases family_descends (prefixWord ++ tailWord_899517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899538 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_899538 : Nat := 118140960795 + 899538 * 2 ^ 59
def prefixEnd_899538 : Nat := 4983230072969 + 3 ^ 40 * 899538 * 2
def baseEnd_899538 : Nat := 102643413552045952697357

theorem tailTrace_899538 : CollatzResearch.WordTrace tailWord_899538 prefixEnd_899538 102643413552045952697357 := by
  unfold tailWord_899538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202211553783732426122817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21872564143423286469660845 8202211553783732426122817)
  ·
    refine ⟨6151658665337799319592113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8202211553783732426122817 6151658665337799319592113)
    ·
      refine ⟨4613743999003349489694085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6151658665337799319592113 4613743999003349489694085)
      ·
        refine ⟨865076999813128029317641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4613743999003349489694085 865076999813128029317641)
        ·
          refine ⟨648807749859846021988231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865076999813128029317641 648807749859846021988231)
          ·
            refine ⟨973211624789769032982347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648807749859846021988231 973211624789769032982347)
            ·
              refine ⟨1459817437184653549473521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973211624789769032982347 1459817437184653549473521)
              ·
                refine ⟨1094863077888490162105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459817437184653549473521 1094863077888490162105141)
                ·
                  refine ⟨102643413552045952697357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094863077888490162105141 102643413552045952697357)
                  ·
                    rfl

theorem cell22_899538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_899538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899538 prefixEnd_899538 := by exact prefixLift 899538
  have htrace : WordTrace (prefixWord ++ tailWord_899538) baseStart_899538 baseEnd_899538 := by
    simpa [prefixWord, tailWord_899538, baseEnd_899538] using wordTrace_append hprefix tailTrace_899538
  have hstable : (prefixWord ++ tailWord_899538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899538).length < 2 ^ (prefixWord ++ tailWord_899538).sum := by decide
  have hdescent : baseEnd_899538 < baseStart_899538 := by decide
  rcases family_descends (prefixWord ++ tailWord_899538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899549 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 4]
def baseStart_899549 : Nat := 118140960795 + 899549 * 2 ^ 59
def prefixEnd_899549 : Nat := 4983230072969 + 3 ^ 40 * 899549 * 2
def baseEnd_899549 : Nat := 102644668726979165355679

theorem tailTrace_899549 : CollatzResearch.WordTrace tailWord_899549 prefixEnd_899549 102644668726979165355679 := by
  unfold tailWord_899549
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809247418095078583141701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21872831612063385722094467 32809247418095078583141701)
  ·
    refine ⟨6151733890892827234339069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32809247418095078583141701 6151733890892827234339069)
    ·
      refine ⟨2306900209084810212877151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6151733890892827234339069 2306900209084810212877151)
      ·
        refine ⟨3460350313627215319315727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306900209084810212877151 3460350313627215319315727)
        ·
          refine ⟨5190525470440822978973591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460350313627215319315727 5190525470440822978973591)
          ·
            refine ⟨7785788205661234468460387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190525470440822978973591 7785788205661234468460387)
            ·
              refine ⟨11678682308491851702690581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785788205661234468460387 11678682308491851702690581)
              ·
                refine ⟨547438233210555548563621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11678682308491851702690581 547438233210555548563621)
                ·
                  refine ⟨102644668726979165355679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547438233210555548563621 102644668726979165355679)
                  ·
                    rfl

theorem cell22_899549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_899549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899549 prefixEnd_899549 := by exact prefixLift 899549
  have htrace : WordTrace (prefixWord ++ tailWord_899549) baseStart_899549 baseEnd_899549 := by
    simpa [prefixWord, tailWord_899549, baseEnd_899549] using wordTrace_append hprefix tailTrace_899549
  have hstable : (prefixWord ++ tailWord_899549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899549).length < 2 ^ (prefixWord ++ tailWord_899549).sum := by decide
  have hdescent : baseEnd_899549 < baseStart_899549 := by decide
  rcases family_descends (prefixWord ++ tailWord_899549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899562 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_899562 : Nat := 118140960795 + 899562 * 2 ^ 59
def prefixEnd_899562 : Nat := 4983230072969 + 3 ^ 40 * 899562 * 2
def baseEnd_899562 : Nat := 307938456346609795491997

theorem tailTrace_899562 : CollatzResearch.WordTrace tailWord_899562 prefixEnd_899562 307938456346609795491997 := by
  unfold tailWord_899562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202430391761995450841235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21873147711365321202243293 8202430391761995450841235)
  ·
    refine ⟨12303645587642993176261853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202430391761995450841235 12303645587642993176261853)
    ·
      refine ⟨4613867095366122441098195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12303645587642993176261853 4613867095366122441098195)
      ·
        refine ⟨6920800643049183661647293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613867095366122441098195 6920800643049183661647293)
        ·
          refine ⟨2595300241143443873117735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6920800643049183661647293 2595300241143443873117735)
          ·
            refine ⟨3892950361715165809676603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595300241143443873117735 3892950361715165809676603)
            ·
              refine ⟨5839425542572748714514905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892950361715165809676603 5839425542572748714514905)
              ·
                refine ⟨4379569156929561535886179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839425542572748714514905 4379569156929561535886179)
                ·
                  refine ⟨6569353735394342303829269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379569156929561535886179 6569353735394342303829269)
                  ·
                    refine ⟨307938456346609795491997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6569353735394342303829269 307938456346609795491997)
                    ·
                      rfl

theorem cell22_899562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_899562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899562 prefixEnd_899562 := by exact prefixLift 899562
  have htrace : WordTrace (prefixWord ++ tailWord_899562) baseStart_899562 baseEnd_899562 := by
    simpa [prefixWord, tailWord_899562, baseEnd_899562] using wordTrace_append hprefix tailTrace_899562
  have hstable : (prefixWord ++ tailWord_899562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899562).length < 2 ^ (prefixWord ++ tailWord_899562).sum := by decide
  have hdescent : baseEnd_899562 < baseStart_899562 := by decide
  rcases family_descends (prefixWord ++ tailWord_899562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899577 : List Nat := [1, 2, 1, 3, 1, 2, 6, 6]
def baseStart_899577 : Nat := 118140960795 + 899577 * 2 ^ 59
def prefixEnd_899577 : Nat := 4983230072969 + 3 ^ 40 * 899577 * 2
def baseEnd_899577 : Nat := 34215954572572750707439

theorem tailTrace_899577 : CollatzResearch.WordTrace tailWord_899577 prefixEnd_899577 34215954572572750707439 := by
  unfold tailWord_899577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810268661993639365160985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21873512441329092910107323 32810268661993639365160985)
  ·
    refine ⟨24607701496495229523870739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32810268661993639365160985 24607701496495229523870739)
    ·
      refine ⟨36911552244742844285806109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24607701496495229523870739 36911552244742844285806109)
      ·
        refine ⟨13841832091778566607177291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36911552244742844285806109 13841832091778566607177291)
        ·
          refine ⟨20762748137667849910765937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13841832091778566607177291 20762748137667849910765937)
          ·
            refine ⟨15572061103250887433074453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20762748137667849910765937 15572061103250887433074453)
            ·
              refine ⟨729940364214885348425365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15572061103250887433074453 729940364214885348425365)
              ·
                refine ⟨34215954572572750707439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 729940364214885348425365 34215954572572750707439)
                ·
                  rfl

theorem cell22_899577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 6].length) (baseStart_899577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899577 prefixEnd_899577 := by exact prefixLift 899577
  have htrace : WordTrace (prefixWord ++ tailWord_899577) baseStart_899577 baseEnd_899577 := by
    simpa [prefixWord, tailWord_899577, baseEnd_899577] using wordTrace_append hprefix tailTrace_899577
  have hstable : (prefixWord ++ tailWord_899577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899577).length < 2 ^ (prefixWord ++ tailWord_899577).sum := by decide
  have hdescent : baseEnd_899577 < baseStart_899577 := by decide
  rcases family_descends (prefixWord ++ tailWord_899577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899712 : List Nat := [2, 1, 1, 2, 1, 6, 9]
def baseStart_899712 : Nat := 118140960795 + 899712 * 2 ^ 59
def prefixEnd_899712 : Nat := 4983230072969 + 3 ^ 40 * 899712 * 2
def baseEnd_899712 : Nat := 11407029793039237194131

theorem tailTrace_899712 : CollatzResearch.WordTrace tailWord_899712 prefixEnd_899712 11407029793039237194131 := by
  unfold tailWord_899712
  simp only [CollatzResearch.WordTrace]
  refine ⟨16407596258252278710662695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21876795011003038280883593 16407596258252278710662695)
  ·
    refine ⟨24611394387378418065994043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16407596258252278710662695 24611394387378418065994043)
    ·
      refine ⟨36917091581067627098991065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24611394387378418065994043 36917091581067627098991065)
      ·
        refine ⟨27687818685800720324243299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36917091581067627098991065 27687818685800720324243299)
        ·
          refine ⟨41531728028701080486364949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27687818685800720324243299 41531728028701080486364949)
          ·
            refine ⟨1946799751345363147798357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41531728028701080486364949 1946799751345363147798357)
            ·
              refine ⟨11407029793039237194131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1946799751345363147798357 11407029793039237194131)
              ·
                rfl

theorem cell22_899712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 9].length) (baseStart_899712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899712 prefixEnd_899712 := by exact prefixLift 899712
  have htrace : WordTrace (prefixWord ++ tailWord_899712) baseStart_899712 baseEnd_899712 := by
    simpa [prefixWord, tailWord_899712, baseEnd_899712] using wordTrace_append hprefix tailTrace_899712
  have hstable : (prefixWord ++ tailWord_899712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899712).length < 2 ^ (prefixWord ++ tailWord_899712).sum := by decide
  have hdescent : baseEnd_899712 < baseStart_899712 := by decide
  rcases family_descends (prefixWord ++ tailWord_899712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899716 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_899716 : Nat := 118140960795 + 899716 * 2 ^ 59
def prefixEnd_899716 : Nat := 4983230072969 + 3 ^ 40 * 899716 * 2
def baseEnd_899716 : Nat := 307991173693804727141525

theorem tailTrace_899716 : CollatzResearch.WordTrace tailWord_899716 prefixEnd_899716 307991173693804727141525 := by
  unfold tailWord_899716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16407669204245033052235501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21876892272326710736314001 16407669204245033052235501)
  ·
    refine ⟨6152875951591887394588313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16407669204245033052235501 6152875951591887394588313)
    ·
      refine ⟨4614656963693915545941235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6152875951591887394588313 4614656963693915545941235)
      ·
        refine ⟨6921985445540873318911853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614656963693915545941235 6921985445540873318911853)
        ·
          refine ⟨2595744542077827494591945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6921985445540873318911853 2595744542077827494591945)
          ·
            refine ⟨1946808406558370620943959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2595744542077827494591945 1946808406558370620943959)
            ·
              refine ⟨2920212609837555931415939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946808406558370620943959 2920212609837555931415939)
              ·
                refine ⟨4380318914756333897123909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920212609837555931415939 4380318914756333897123909)
                ·
                  refine ⟨821309796516812605710733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4380318914756333897123909 821309796516812605710733)
                  ·
                    refine ⟨307991173693804727141525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821309796516812605710733 307991173693804727141525)
                    ·
                      rfl

theorem cell22_899716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_899716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899716 prefixEnd_899716 := by exact prefixLift 899716
  have htrace : WordTrace (prefixWord ++ tailWord_899716) baseStart_899716 baseEnd_899716 := by
    simpa [prefixWord, tailWord_899716, baseEnd_899716] using wordTrace_append hprefix tailTrace_899716
  have hstable : (prefixWord ++ tailWord_899716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899716).length < 2 ^ (prefixWord ++ tailWord_899716).sum := by decide
  have hdescent : baseEnd_899716 < baseStart_899716 := by decide
  rcases family_descends (prefixWord ++ tailWord_899716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899774 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_899774 : Nat := 118140960795 + 899774 * 2 ^ 59
def prefixEnd_899774 : Nat := 4983230072969 + 3 ^ 40 * 899774 * 2
def baseEnd_899774 : Nat := 102670342759703969730449

theorem tailTrace_899774 : CollatzResearch.WordTrace tailWord_899774 prefixEnd_899774 102670342759703969730449 := by
  unfold tailWord_899774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102181730284992751260297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21878302561519961340054917 4102181730284992751260297)
  ·
    refine ⟨3076636297713744563445223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4102181730284992751260297 3076636297713744563445223)
    ·
      refine ⟨4614954446570616845167835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076636297713744563445223 4614954446570616845167835)
      ·
        refine ⟨6922431669855925267751753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4614954446570616845167835 6922431669855925267751753)
        ·
          refine ⟨5191823752391943950813815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6922431669855925267751753 5191823752391943950813815)
          ·
            refine ⟨7787735628587915926220723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191823752391943950813815 7787735628587915926220723)
            ·
              refine ⟨11681603442881873889331085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787735628587915926220723 11681603442881873889331085)
              ·
                refine ⟨4380601291080702708499157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11681603442881873889331085 4380601291080702708499157)
                ·
                  refine ⟨102670342759703969730449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4380601291080702708499157 102670342759703969730449)
                  ·
                    rfl

theorem cell22_899774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_899774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899774 prefixEnd_899774 := by exact prefixLift 899774
  have htrace : WordTrace (prefixWord ++ tailWord_899774) baseStart_899774 baseEnd_899774 := by
    simpa [prefixWord, tailWord_899774, baseEnd_899774] using wordTrace_append hprefix tailTrace_899774
  have hstable : (prefixWord ++ tailWord_899774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899774).length < 2 ^ (prefixWord ++ tailWord_899774).sum := by decide
  have hdescent : baseEnd_899774 < baseStart_899774 := by decide
  rcases family_descends (prefixWord ++ tailWord_899774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899787 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_899787 : Nat := 118140960795 + 899787 * 2 ^ 59
def prefixEnd_899787 : Nat := 4983230072969 + 3 ^ 40 * 899787 * 2
def baseEnd_899787 : Nat := 308015478444784208616307

theorem tailTrace_899787 : CollatzResearch.WordTrace tailWord_899787 prefixEnd_899787 308015478444784208616307 := by
  unfold tailWord_899787
  simp only [CollatzResearch.WordTrace]
  refine ⟨32817927991232845230305615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21878618660821896820203743 32817927991232845230305615)
  ·
    refine ⟨49226891986849267845458423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32817927991232845230305615 49226891986849267845458423)
    ·
      refine ⟨73840337980273901768187635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49226891986849267845458423 73840337980273901768187635)
      ·
        refine ⟨110760506970410852652281453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73840337980273901768187635 110760506970410852652281453)
        ·
          refine ⟨41535190113904069744605545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110760506970410852652281453 41535190113904069744605545)
          ·
            refine ⟨31151392585428052308454159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41535190113904069744605545 31151392585428052308454159)
            ·
              refine ⟨46727088878142078462681239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31151392585428052308454159 46727088878142078462681239)
              ·
                refine ⟨70090633317213117694021859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46727088878142078462681239 70090633317213117694021859)
                ·
                  refine ⟨105135949975819676541032789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70090633317213117694021859 105135949975819676541032789)
                  ·
                    refine ⟨308015478444784208616307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 105135949975819676541032789 308015478444784208616307)
                    ·
                      rfl

theorem cell22_899787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_899787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899787 prefixEnd_899787 := by exact prefixLift 899787
  have htrace : WordTrace (prefixWord ++ tailWord_899787) baseStart_899787 baseEnd_899787 := by
    simpa [prefixWord, tailWord_899787, baseEnd_899787] using wordTrace_append hprefix tailTrace_899787
  have hstable : (prefixWord ++ tailWord_899787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899787).length < 2 ^ (prefixWord ++ tailWord_899787).sum := by decide
  have hdescent : baseEnd_899787 < baseStart_899787 := by decide
  rcases family_descends (prefixWord ++ tailWord_899787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899829 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_899829 : Nat := 118140960795 + 899829 * 2 ^ 59
def prefixEnd_899829 : Nat := 4983230072969 + 3 ^ 40 * 899829 * 2
def baseEnd_899829 : Nat := 308029855903110099066179

theorem tailTrace_899829 : CollatzResearch.WordTrace tailWord_899829 prefixEnd_899829 308029855903110099066179 := by
  unfold tailWord_899829
  simp only [CollatzResearch.WordTrace]
  refine ⟨32819459857080686403334541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21879639904720457602223027 32819459857080686403334541)
  ·
    refine ⟨12307297446405257401250453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32819459857080686403334541 12307297446405257401250453)
    ·
      refine ⟨576904567800246440683615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12307297446405257401250453 576904567800246440683615)
      ·
        refine ⟨865356851700369661025423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576904567800246440683615 865356851700369661025423)
        ·
          refine ⟨1298035277550554491538135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865356851700369661025423 1298035277550554491538135)
          ·
            refine ⟨1947052916325831737307203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298035277550554491538135 1947052916325831737307203)
            ·
              refine ⟨2920579374488747605960805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947052916325831737307203 2920579374488747605960805)
              ·
                refine ⟨547608632716640176117651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2920579374488747605960805 547608632716640176117651)
                ·
                  refine ⟨821412949074960264176477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547608632716640176117651 821412949074960264176477)
                  ·
                    refine ⟨308029855903110099066179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821412949074960264176477 308029855903110099066179)
                    ·
                      rfl

theorem cell22_899829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_899829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899829 prefixEnd_899829 := by exact prefixLift 899829
  have htrace : WordTrace (prefixWord ++ tailWord_899829) baseStart_899829 baseEnd_899829 := by
    simpa [prefixWord, tailWord_899829, baseEnd_899829] using wordTrace_append hprefix tailTrace_899829
  have hstable : (prefixWord ++ tailWord_899829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899829).length < 2 ^ (prefixWord ++ tailWord_899829).sum := by decide
  have hdescent : baseEnd_899829 < baseStart_899829 := by decide
  rcases family_descends (prefixWord ++ tailWord_899829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899849 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_899849 : Nat := 118140960795 + 899849 * 2 ^ 59
def prefixEnd_899849 : Nat := 4983230072969 + 3 ^ 40 * 899849 * 2
def baseEnd_899849 : Nat := 308036702311836713566117

theorem tailTrace_899849 : CollatzResearch.WordTrace tailWord_899849 prefixEnd_899849 308036702311836713566117 := by
  unfold tailWord_899849
  simp only [CollatzResearch.WordTrace]
  refine ⟨32820189317008229819062601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21880126211338819879375067 32820189317008229819062601)
  ·
    refine ⟨24615141987756172364296951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32820189317008229819062601 24615141987756172364296951)
    ·
      refine ⟨36922712981634258546445427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24615141987756172364296951 36922712981634258546445427)
      ·
        refine ⟨55384069472451387819668141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36922712981634258546445427 55384069472451387819668141)
        ·
          refine ⟨20769026052169270432375553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55384069472451387819668141 20769026052169270432375553)
          ·
            refine ⟨15576769539126952824281665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20769026052169270432375553 15576769539126952824281665)
            ·
              refine ⟨11682577154345214618211249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15576769539126952824281665 11682577154345214618211249)
              ·
                refine ⟨8761932865758910963658437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11682577154345214618211249 8761932865758910963658437)
                ·
                  refine ⟨1642862412329795805685957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8761932865758910963658437 1642862412329795805685957)
                  ·
                    refine ⟨308036702311836713566117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1642862412329795805685957 308036702311836713566117)
                    ·
                      rfl

theorem cell22_899849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_899849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899849 prefixEnd_899849 := by exact prefixLift 899849
  have htrace : WordTrace (prefixWord ++ tailWord_899849) baseStart_899849 baseEnd_899849 := by
    simpa [prefixWord, tailWord_899849, baseEnd_899849] using wordTrace_append hprefix tailTrace_899849
  have hstable : (prefixWord ++ tailWord_899849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899849).length < 2 ^ (prefixWord ++ tailWord_899849).sum := by decide
  have hdescent : baseEnd_899849 < baseStart_899849 := by decide
  rcases family_descends (prefixWord ++ tailWord_899849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899902 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_899902 : Nat := 118140960795 + 899902 * 2 ^ 59
def prefixEnd_899902 : Nat := 4983230072969 + 3 ^ 40 * 899902 * 2
def baseEnd_899902 : Nat := 308054845294962241990955

theorem tailTrace_899902 : CollatzResearch.WordTrace tailWord_899902 prefixEnd_899902 308054845294962241990955 := by
  unfold tailWord_899902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102765298227027483842745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21881414923877479913827973 4102765298227027483842745)
  ·
    refine ⟨3077073973670270612882059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4102765298227027483842745 3077073973670270612882059)
    ·
      refine ⟨4615610960505405919323089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077073973670270612882059 4615610960505405919323089)
      ·
        refine ⟨3461708220379054439492317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4615610960505405919323089 3461708220379054439492317)
        ·
          refine ⟨1298140582642145414809619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3461708220379054439492317 1298140582642145414809619)
          ·
            refine ⟨1947210873963218122214429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298140582642145414809619 1947210873963218122214429)
            ·
              refine ⟨730204077736206795830411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1947210873963218122214429 730204077736206795830411)
              ·
                refine ⟨1095306116604310193745617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730204077736206795830411 1095306116604310193745617)
                ·
                  refine ⟨821479587453232645309213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095306116604310193745617 821479587453232645309213)
                  ·
                    refine ⟨308054845294962241990955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821479587453232645309213 308054845294962241990955)
                    ·
                      rfl

theorem cell22_899902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_899902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899902 prefixEnd_899902 := by exact prefixLift 899902
  have htrace : WordTrace (prefixWord ++ tailWord_899902) baseStart_899902 baseEnd_899902 := by
    simpa [prefixWord, tailWord_899902, baseEnd_899902] using wordTrace_append hprefix tailTrace_899902
  have hstable : (prefixWord ++ tailWord_899902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899902).length < 2 ^ (prefixWord ++ tailWord_899902).sum := by decide
  have hdescent : baseEnd_899902 < baseStart_899902 := by decide
  rcases family_descends (prefixWord ++ tailWord_899902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899930 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_899930 : Nat := 118140960795 + 899930 * 2 ^ 59
def prefixEnd_899930 : Nat := 4983230072969 + 3 ^ 40 * 899930 * 2
def baseEnd_899930 : Nat := 308064430267179502290869

theorem tailTrace_899930 : CollatzResearch.WordTrace tailWord_899930 prefixEnd_899930 308064430267179502290869 := by
  unfold tailWord_899930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205785907428695163190311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21882095753143187101840829 8205785907428695163190311)
  ·
    refine ⟨12308678861143042744785467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205785907428695163190311 12308678861143042744785467)
    ·
      refine ⟨18463018291714564117178201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12308678861143042744785467 18463018291714564117178201)
      ·
        refine ⟨13847263718785923087883651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18463018291714564117178201 13847263718785923087883651)
        ·
          refine ⟨20770895578178884631825477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13847263718785923087883651 20770895578178884631825477)
          ·
            refine ⟨3894542920908540868467277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20770895578178884631825477 3894542920908540868467277)
            ·
              refine ⟨1460453595340702825675229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3894542920908540868467277 1460453595340702825675229)
              ·
                refine ⟨547670098252763559628211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1460453595340702825675229 547670098252763559628211)
                ·
                  refine ⟨821505147379145339442317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547670098252763559628211 821505147379145339442317)
                  ·
                    refine ⟨308064430267179502290869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821505147379145339442317 308064430267179502290869)
                    ·
                      rfl

theorem cell22_899930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_899930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899930 prefixEnd_899930 := by exact prefixLift 899930
  have htrace : WordTrace (prefixWord ++ tailWord_899930) baseStart_899930 baseEnd_899930 := by
    simpa [prefixWord, tailWord_899930, baseEnd_899930] using wordTrace_append hprefix tailTrace_899930
  have hstable : (prefixWord ++ tailWord_899930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899930).length < 2 ^ (prefixWord ++ tailWord_899930).sum := by decide
  have hdescent : baseEnd_899930 < baseStart_899930 := by decide
  rcases family_descends (prefixWord ++ tailWord_899930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899973 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_899973 : Nat := 118140960795 + 899973 * 2 ^ 59
def prefixEnd_899973 : Nat := 4983230072969 + 3 ^ 40 * 899973 * 2
def baseEnd_899973 : Nat := 308079150045941723465737

theorem tailTrace_899973 : CollatzResearch.WordTrace tailWord_899973 prefixEnd_899973 308079150045941723465737 := by
  unfold tailWord_899973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824711968558998996576573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21883141312372665997717715 32824711968558998996576573)
  ·
    refine ⟨12309266988209624623716215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32824711968558998996576573 12309266988209624623716215)
    ·
      refine ⟨18463900482314436935574323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309266988209624623716215 18463900482314436935574323)
      ·
        refine ⟨27695850723471655403361485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18463900482314436935574323 27695850723471655403361485)
        ·
          refine ⟨10385944021301870776260557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27695850723471655403361485 10385944021301870776260557)
          ·
            refine ⟨3894729007988201541097709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10385944021301870776260557 3894729007988201541097709)
            ·
              refine ⟨1460523377995575577911641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3894729007988201541097709 1460523377995575577911641)
              ·
                refine ⟨1095392533496681683433731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460523377995575577911641 1095392533496681683433731)
                ·
                  refine ⟨1643088800245022525150597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095392533496681683433731 1643088800245022525150597)
                  ·
                    refine ⟨308079150045941723465737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643088800245022525150597 308079150045941723465737)
                    ·
                      rfl

theorem cell22_899973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_899973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_899973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_899973 prefixEnd_899973 := by exact prefixLift 899973
  have htrace : WordTrace (prefixWord ++ tailWord_899973) baseStart_899973 baseEnd_899973 := by
    simpa [prefixWord, tailWord_899973, baseEnd_899973] using wordTrace_append hprefix tailTrace_899973
  have hstable : (prefixWord ++ tailWord_899973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899973).length < 2 ^ (prefixWord ++ tailWord_899973).sum := by decide
  have hdescent : baseEnd_899973 < baseStart_899973 := by decide
  rcases family_descends (prefixWord ++ tailWord_899973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900003 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 2, 3]
def baseStart_900003 : Nat := 118140960795 + 900003 * 2 ^ 59
def prefixEnd_900003 : Nat := 4983230072969 + 3 ^ 40 * 900003 * 2
def baseEnd_900003 : Nat := 308089419659031645215645

theorem tailTrace_900003 : CollatzResearch.WordTrace tailWord_900003 prefixEnd_900003 308089419659031645215645 := by
  unfold tailWord_900003
  simp only [CollatzResearch.WordTrace]
  refine ⟨32825806158450314120168663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21883870772300209413445775 32825806158450314120168663)
  ·
    refine ⟨49238709237675471180252995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32825806158450314120168663 49238709237675471180252995)
    ·
      refine ⟨73858063856513206770379493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49238709237675471180252995 73858063856513206770379493)
      ·
        refine ⟨13848386973096226269446155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73858063856513206770379493 13848386973096226269446155)
        ·
          refine ⟨20772580459644339404169233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13848386973096226269446155 20772580459644339404169233)
          ·
            refine ⟨15579435344733254553126925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20772580459644339404169233 15579435344733254553126925)
            ·
              refine ⟨5842288254274970457422597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15579435344733254553126925 5842288254274970457422597)
              ·
                refine ⟨1095429047676556960766737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5842288254274970457422597 1095429047676556960766737)
                ·
                  refine ⟨821571785757417720575053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095429047676556960766737 821571785757417720575053)
                  ·
                    refine ⟨308089419659031645215645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821571785757417720575053 308089419659031645215645)
                    ·
                      rfl

theorem cell22_900003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3].length) (baseStart_900003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900003 prefixEnd_900003 := by exact prefixLift 900003
  have htrace : WordTrace (prefixWord ++ tailWord_900003) baseStart_900003 baseEnd_900003 := by
    simpa [prefixWord, tailWord_900003, baseEnd_900003] using wordTrace_append hprefix tailTrace_900003
  have hstable : (prefixWord ++ tailWord_900003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900003).length < 2 ^ (prefixWord ++ tailWord_900003).sum := by decide
  have hdescent : baseEnd_900003 < baseStart_900003 := by decide
  rcases family_descends (prefixWord ++ tailWord_900003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900020 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_900020 : Nat := 118140960795 + 900020 * 2 ^ 59
def prefixEnd_900020 : Nat := 4983230072969 + 3 ^ 40 * 900020 * 2
def baseEnd_900020 : Nat := 308095239106449267540593

theorem tailTrace_900020 : CollatzResearch.WordTrace tailWord_900020 prefixEnd_900020 308095239106449267540593 := by
  unfold tailWord_900020
  simp only [CollatzResearch.WordTrace]
  refine ⟨16413213099694363011768757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21884284132925817349025009 16413213099694363011768757)
  ·
    refine ⟨1538738728096346532353321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16413213099694363011768757 1538738728096346532353321)
    ·
      refine ⟨1154054046072259899264991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1538738728096346532353321 1154054046072259899264991)
      ·
        refine ⟨1731081069108389848897487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154054046072259899264991 1731081069108389848897487)
        ·
          refine ⟨2596621603662584773346231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731081069108389848897487 2596621603662584773346231)
          ·
            refine ⟨3894932405493877160019347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596621603662584773346231 3894932405493877160019347)
            ·
              refine ⟨5842398608240815740029021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894932405493877160019347 5842398608240815740029021)
              ·
                refine ⟨2190899478090305902510883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842398608240815740029021 2190899478090305902510883)
                ·
                  refine ⟨3286349217135458853766325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190899478090305902510883 3286349217135458853766325)
                  ·
                    refine ⟨308095239106449267540593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3286349217135458853766325 308095239106449267540593)
                    ·
                      rfl

theorem cell22_900020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_900020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900020 prefixEnd_900020 := by exact prefixLift 900020
  have htrace : WordTrace (prefixWord ++ tailWord_900020) baseStart_900020 baseEnd_900020 := by
    simpa [prefixWord, tailWord_900020, baseEnd_900020] using wordTrace_append hprefix tailTrace_900020
  have hstable : (prefixWord ++ tailWord_900020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900020).length < 2 ^ (prefixWord ++ tailWord_900020).sum := by decide
  have hdescent : baseEnd_900020 < baseStart_900020 := by decide
  rcases family_descends (prefixWord ++ tailWord_900020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900054 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_900054 : Nat := 118140960795 + 900054 * 2 ^ 59
def prefixEnd_900054 : Nat := 4983230072969 + 3 ^ 40 * 900054 * 2
def baseEnd_900054 : Nat := 308106878001284512190489

theorem tailTrace_900054 : CollatzResearch.WordTrace tailWord_900054 prefixEnd_900054 308106878001284512190489 := by
  unfold tailWord_900054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051729142579096864392201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21885110854177033220183477 2051729142579096864392201)
  ·
    refine ⟨1538796856934322648294151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2051729142579096864392201 1538796856934322648294151)
    ·
      refine ⟨2308195285401483972441227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538796856934322648294151 2308195285401483972441227)
      ·
        refine ⟨3462292928102225958661841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308195285401483972441227 3462292928102225958661841)
        ·
          refine ⟨2596719696076669468996381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462292928102225958661841 2596719696076669468996381)
          ·
            refine ⟨973769886028751050873643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596719696076669468996381 973769886028751050873643)
            ·
              refine ⟨1460654829043126576310465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973769886028751050873643 1460654829043126576310465)
              ·
                refine ⟨1095491121782344932232849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460654829043126576310465 1095491121782344932232849)
                ·
                  refine ⟨821618341336758699174637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095491121782344932232849 821618341336758699174637)
                  ·
                    refine ⟨308106878001284512190489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821618341336758699174637 308106878001284512190489)
                    ·
                      rfl

theorem cell22_900054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_900054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900054 prefixEnd_900054 := by exact prefixLift 900054
  have htrace : WordTrace (prefixWord ++ tailWord_900054) baseStart_900054 baseEnd_900054 := by
    simpa [prefixWord, tailWord_900054, baseEnd_900054] using wordTrace_append hprefix tailTrace_900054
  have hstable : (prefixWord ++ tailWord_900054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900054).length < 2 ^ (prefixWord ++ tailWord_900054).sum := by decide
  have hdescent : baseEnd_900054 < baseStart_900054 := by decide
  rcases family_descends (prefixWord ++ tailWord_900054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900084 : List Nat := [2, 6, 2, 1, 1, 1, 1, 8]
def baseStart_900084 : Nat := 118140960795 + 900084 * 2 ^ 59
def prefixEnd_900084 : Nat := 4983230072969 + 3 ^ 40 * 900084 * 2
def baseEnd_900084 : Nat := 34235238623819381548933

theorem tailTrace_900084 : CollatzResearch.WordTrace tailWord_900084 prefixEnd_900084 34235238623819381548933 := by
  unfold tailWord_900084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16414380235578432476933653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21885840314104576635911537 16414380235578432476933653)
  ·
    refine ⟨769424073542739022356265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16414380235578432476933653 769424073542739022356265)
    ·
      refine ⟨577068055157054266767199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769424073542739022356265 577068055157054266767199)
      ·
        refine ⟨865602082735581400150799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577068055157054266767199 865602082735581400150799)
        ·
          refine ⟨1298403124103372100226199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865602082735581400150799 1298403124103372100226199)
          ·
            refine ⟨1947604686155058150339299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298403124103372100226199 1947604686155058150339299)
            ·
              refine ⟨2921407029232587225508949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947604686155058150339299 2921407029232587225508949)
              ·
                refine ⟨34235238623819381548933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2921407029232587225508949 34235238623819381548933)
                ·
                  rfl

theorem cell22_900084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_900084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900084 prefixEnd_900084 := by exact prefixLift 900084
  have htrace : WordTrace (prefixWord ++ tailWord_900084) baseStart_900084 baseEnd_900084 := by
    simpa [prefixWord, tailWord_900084, baseEnd_900084] using wordTrace_append hprefix tailTrace_900084
  have hstable : (prefixWord ++ tailWord_900084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900084).length < 2 ^ (prefixWord ++ tailWord_900084).sum := by decide
  have hdescent : baseEnd_900084 < baseStart_900084 := by decide
  rcases family_descends (prefixWord ++ tailWord_900084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900243 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_900243 : Nat := 118140960795 + 900243 * 2 ^ 59
def prefixEnd_900243 : Nat := 4983230072969 + 3 ^ 40 * 900243 * 2
def baseEnd_900243 : Nat := 308171576563751019214909

theorem tailTrace_900243 : CollatzResearch.WordTrace tailWord_900243 prefixEnd_900243 308171576563751019214909 := by
  unfold tailWord_900243
  simp only [CollatzResearch.WordTrace]
  refine ⟨32834559677580835108905383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21889706451720556739270255 32834559677580835108905383)
  ·
    refine ⟨49251839516371252663358075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32834559677580835108905383 49251839516371252663358075)
    ·
      refine ⟨73877759274556878995037113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49251839516371252663358075 73877759274556878995037113)
      ·
        refine ⟨55408319455917659246277835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73877759274556878995037113 55408319455917659246277835)
        ·
          refine ⟨83112479183876488869416753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55408319455917659246277835 83112479183876488869416753)
          ·
            refine ⟨62334359387907366652062565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83112479183876488869416753 62334359387907366652062565)
            ·
              refine ⟨11687692385232631247261731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62334359387907366652062565 11687692385232631247261731)
              ·
                refine ⟨17531538577848946870892597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11687692385232631247261731 17531538577848946870892597)
                ·
                  refine ⟨1643581741673338769146181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17531538577848946870892597 1643581741673338769146181)
                  ·
                    refine ⟨308171576563751019214909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643581741673338769146181 308171576563751019214909)
                    ·
                      rfl

theorem cell22_900243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_900243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900243 prefixEnd_900243 := by exact prefixLift 900243
  have htrace : WordTrace (prefixWord ++ tailWord_900243) baseStart_900243 baseEnd_900243 := by
    simpa [prefixWord, tailWord_900243, baseEnd_900243] using wordTrace_append hprefix tailTrace_900243
  have hstable : (prefixWord ++ tailWord_900243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900243).length < 2 ^ (prefixWord ++ tailWord_900243).sum := by decide
  have hdescent : baseEnd_900243 < baseStart_900243 := by decide
  rcases family_descends (prefixWord ++ tailWord_900243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900247 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 5]
def baseStart_900247 : Nat := 118140960795 + 900247 * 2 ^ 59
def prefixEnd_900247 : Nat := 4983230072969 + 3 ^ 40 * 900247 * 2
def baseEnd_900247 : Nat := 102724315281832114038299

theorem tailTrace_900247 : CollatzResearch.WordTrace tailWord_900247 prefixEnd_900247 102724315281832114038299 := by
  unfold tailWord_900247
  simp only [CollatzResearch.WordTrace]
  refine ⟨32834705569566343792050995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21889803713044229194700663 32834705569566343792050995)
  ·
    refine ⟨49252058354349515688076493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32834705569566343792050995 49252058354349515688076493)
    ·
      refine ⟨18469521882881068383028685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49252058354349515688076493 18469521882881068383028685)
      ·
        refine ⟨6926070706080400643635757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18469521882881068383028685 6926070706080400643635757)
        ·
          refine ⟨2597276514780150241363409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6926070706080400643635757 2597276514780150241363409)
          ·
            refine ⟨1947957386085112681022557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2597276514780150241363409 1947957386085112681022557)
            ·
              refine ⟨730484019781917255383459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1947957386085112681022557 730484019781917255383459)
              ·
                refine ⟨1095726029672875883075189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730484019781917255383459 1095726029672875883075189)
                ·
                  refine ⟨102724315281832114038299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1095726029672875883075189 102724315281832114038299)
                  ·
                    rfl

theorem cell22_900247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 5].length) (baseStart_900247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900247 prefixEnd_900247 := by exact prefixLift 900247
  have htrace : WordTrace (prefixWord ++ tailWord_900247) baseStart_900247 baseEnd_900247 := by
    simpa [prefixWord, tailWord_900247, baseEnd_900247] using wordTrace_append hprefix tailTrace_900247
  have hstable : (prefixWord ++ tailWord_900247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900247).length < 2 ^ (prefixWord ++ tailWord_900247).sum := by decide
  have hdescent : baseEnd_900247 < baseStart_900247 := by decide
  rcases family_descends (prefixWord ++ tailWord_900247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900354 : List Nat := [3, 4, 1, 1, 3, 2, 1, 7]
def baseStart_900354 : Nat := 118140960795 + 900354 * 2 ^ 59
def prefixEnd_900354 : Nat := 4983230072969 + 3 ^ 40 * 900354 * 2
def baseEnd_900354 : Nat := 34245508236909303298841

theorem tailTrace_900354 : CollatzResearch.WordTrace tailWord_900354 prefixEnd_900354 34245508236909303298841 := by
  unfold tailWord_900354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8209652045044675266549029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21892405453452467377464077 8209652045044675266549029)
  ·
    refine ⟨1539309758445876612477943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8209652045044675266549029 1539309758445876612477943)
    ·
      refine ⟨2308964637668814918716915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539309758445876612477943 2308964637668814918716915)
      ·
        refine ⟨3463446956503222378075373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308964637668814918716915 3463446956503222378075373)
        ·
          refine ⟨1298792608688708391778265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3463446956503222378075373 1298792608688708391778265)
          ·
            refine ⟨974094456516531293833699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298792608688708391778265 974094456516531293833699)
            ·
              refine ⟨1461141684774796940750549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974094456516531293833699 1461141684774796940750549)
              ·
                refine ⟨34245508236909303298841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1461141684774796940750549 34245508236909303298841)
                ·
                  rfl

theorem cell22_900354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_900354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900354 prefixEnd_900354 := by exact prefixLift 900354
  have htrace : WordTrace (prefixWord ++ tailWord_900354) baseStart_900354 baseEnd_900354 := by
    simpa [prefixWord, tailWord_900354, baseEnd_900354] using wordTrace_append hprefix tailTrace_900354
  have hstable : (prefixWord ++ tailWord_900354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900354).length < 2 ^ (prefixWord ++ tailWord_900354).sum := by decide
  have hdescent : baseEnd_900354 < baseStart_900354 := by decide
  rcases family_descends (prefixWord ++ tailWord_900354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900440 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_900440 : Nat := 118140960795 + 900440 * 2 ^ 59
def prefixEnd_900440 : Nat := 4983230072969 + 3 ^ 40 * 900440 * 2
def baseEnd_900440 : Nat := 308239013689708172039305

theorem tailTrace_900440 : CollatzResearch.WordTrace tailWord_900440 prefixEnd_900440 308239013689708172039305 := by
  unfold tailWord_900440
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420872428933568876913387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21894496571911425169217849 16420872428933568876913387)
  ·
    refine ⟨24631308643400353315370081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16420872428933568876913387 24631308643400353315370081)
    ·
      refine ⟨18473481482550264986527561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24631308643400353315370081 18473481482550264986527561)
      ·
        refine ⟨13855111111912698739895671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18473481482550264986527561 13855111111912698739895671)
        ·
          refine ⟨20782666667869048109843507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855111111912698739895671 20782666667869048109843507)
          ·
            refine ⟨31174000001803572164765261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20782666667869048109843507 31174000001803572164765261)
            ·
              refine ⟨11690250000676339561786973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31174000001803572164765261 11690250000676339561786973)
              ·
                refine ⟨4383843750253627335670115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11690250000676339561786973 4383843750253627335670115)
                ·
                  refine ⟨6575765625380441003505173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383843750253627335670115 6575765625380441003505173)
                  ·
                    refine ⟨308239013689708172039305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6575765625380441003505173 308239013689708172039305)
                    ·
                      rfl

theorem cell22_900440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_900440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900440 prefixEnd_900440 := by exact prefixLift 900440
  have htrace : WordTrace (prefixWord ++ tailWord_900440) baseStart_900440 baseEnd_900440 := by
    simpa [prefixWord, tailWord_900440, baseEnd_900440] using wordTrace_append hprefix tailTrace_900440
  have hstable : (prefixWord ++ tailWord_900440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900440).length < 2 ^ (prefixWord ++ tailWord_900440).sum := by decide
  have hdescent : baseEnd_900440 < baseStart_900440 := by decide
  rcases family_descends (prefixWord ++ tailWord_900440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900442 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_900442 : Nat := 118140960795 + 900442 * 2 ^ 59
def prefixEnd_900442 : Nat := 4983230072969 + 3 ^ 40 * 900442 * 2
def baseEnd_900442 : Nat := 308239698330580833489299

theorem tailTrace_900442 : CollatzResearch.WordTrace tailWord_900442 prefixEnd_900442 308239698330580833489299 := by
  unfold tailWord_900442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8210454450964973023849895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21894545202573261396933053 8210454450964973023849895)
  ·
    refine ⟨12315681676447459535774843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8210454450964973023849895 12315681676447459535774843)
    ·
      refine ⟨18473522514671189303662265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315681676447459535774843 18473522514671189303662265)
      ·
        refine ⟨13855141886003391977746699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18473522514671189303662265 13855141886003391977746699)
        ·
          refine ⟨20782712829005087966620049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855141886003391977746699 20782712829005087966620049)
          ·
            refine ⟨15587034621753815974965037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20782712829005087966620049 15587034621753815974965037)
            ·
              refine ⟨5845137983157680990611889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15587034621753815974965037 5845137983157680990611889)
              ·
                refine ⟨4383853487368260742958917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845137983157680990611889 4383853487368260742958917)
                ·
                  refine ⟨821972528881548889304797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4383853487368260742958917 821972528881548889304797)
                  ·
                    refine ⟨308239698330580833489299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821972528881548889304797 308239698330580833489299)
                    ·
                      rfl

theorem cell22_900442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_900442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900442 prefixEnd_900442 := by exact prefixLift 900442
  have htrace : WordTrace (prefixWord ++ tailWord_900442) baseStart_900442 baseEnd_900442 := by
    simpa [prefixWord, tailWord_900442, baseEnd_900442] using wordTrace_append hprefix tailTrace_900442
  have hstable : (prefixWord ++ tailWord_900442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900442).length < 2 ^ (prefixWord ++ tailWord_900442).sum := by decide
  have hdescent : baseEnd_900442 < baseStart_900442 := by decide
  rcases family_descends (prefixWord ++ tailWord_900442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900461 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 4]
def baseStart_900461 : Nat := 118140960795 + 900461 * 2 ^ 59
def prefixEnd_900461 : Nat := 4983230072969 + 3 ^ 40 * 900461 * 2
def baseEnd_900461 : Nat := 102748734139623705754747

theorem tailTrace_900461 : CollatzResearch.WordTrace tailWord_900461 prefixEnd_900461 102748734139623705754747 := by
  unfold tailWord_900461
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842510790791058340341237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21895007193860705560227491 32842510790791058340341237)
  ·
    refine ⟨3078985386636661719406991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32842510790791058340341237 3078985386636661719406991)
    ·
      refine ⟨4618478079954992579110487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3078985386636661719406991 4618478079954992579110487)
      ·
        refine ⟨6927717119932488868665731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618478079954992579110487 6927717119932488868665731)
        ·
          refine ⟨10391575679898733302998597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927717119932488868665731 10391575679898733302998597)
          ·
            refine ⟨1948420439981012494312237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10391575679898733302998597 1948420439981012494312237)
            ·
              refine ⟨730657664992879685367089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1948420439981012494312237 730657664992879685367089)
              ·
                refine ⟨547993248744659764025317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730657664992879685367089 547993248744659764025317)
                ·
                  refine ⟨102748734139623705754747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547993248744659764025317 102748734139623705754747)
                  ·
                    rfl

theorem cell22_900461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_900461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900461 prefixEnd_900461 := by exact prefixLift 900461
  have htrace : WordTrace (prefixWord ++ tailWord_900461) baseStart_900461 baseEnd_900461 := by
    simpa [prefixWord, tailWord_900461, baseEnd_900461] using wordTrace_append hprefix tailTrace_900461
  have hstable : (prefixWord ++ tailWord_900461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900461).length < 2 ^ (prefixWord ++ tailWord_900461).sum := by decide
  have hdescent : baseEnd_900461 < baseStart_900461 := by decide
  rcases family_descends (prefixWord ++ tailWord_900461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900547 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_900547 : Nat := 118140960795 + 900547 * 2 ^ 59
def prefixEnd_900547 : Nat := 4983230072969 + 3 ^ 40 * 900547 * 2
def baseEnd_900547 : Nat := 308275641976395559613977

theorem tailTrace_900547 : CollatzResearch.WordTrace tailWord_900547 prefixEnd_900547 308275641976395559613977 := by
  unfold tailWord_900547
  simp only [CollatzResearch.WordTrace]
  refine ⟨32845647468479495027971895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21897098312319663351981263 32845647468479495027971895)
  ·
    refine ⟨49268471202719242541957843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32845647468479495027971895 49268471202719242541957843)
    ·
      refine ⟨73902706804078863812936765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49268471202719242541957843 73902706804078863812936765)
      ·
        refine ⟨27713515051529573929851287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73902706804078863812936765 27713515051529573929851287)
        ·
          refine ⟨41570272577294360894776931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27713515051529573929851287 41570272577294360894776931)
          ·
            refine ⟨62355408865941541342165397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41570272577294360894776931 62355408865941541342165397)
            ·
              refine ⟨2922909790591009750414003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62355408865941541342165397 2922909790591009750414003)
              ·
                refine ⟨4384364685886514625621005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922909790591009750414003 4384364685886514625621005)
                ·
                  refine ⟨1644136757207442984607877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384364685886514625621005 1644136757207442984607877)
                  ·
                    refine ⟨308275641976395559613977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1644136757207442984607877 308275641976395559613977)
                    ·
                      rfl

theorem cell22_900547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_900547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900547 prefixEnd_900547 := by exact prefixLift 900547
  have htrace : WordTrace (prefixWord ++ tailWord_900547) baseStart_900547 baseEnd_900547 := by
    simpa [prefixWord, tailWord_900547, baseEnd_900547] using wordTrace_append hprefix tailTrace_900547
  have hstable : (prefixWord ++ tailWord_900547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900547).length < 2 ^ (prefixWord ++ tailWord_900547).sum := by decide
  have hdescent : baseEnd_900547 < baseStart_900547 := by decide
  rcases family_descends (prefixWord ++ tailWord_900547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900579 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 6]
def baseStart_900579 : Nat := 118140960795 + 900579 * 2 ^ 59
def prefixEnd_900579 : Nat := 4983230072969 + 3 ^ 40 * 900579 * 2
def baseEnd_900579 : Nat := 102762198743452714271293

theorem tailTrace_900579 : CollatzResearch.WordTrace tailWord_900579 prefixEnd_900579 102762198743452714271293 := by
  unfold tailWord_900579
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846814604363564493136791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21897876402909042995424527 32846814604363564493136791)
  ·
    refine ⟨49270221906545346739705187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32846814604363564493136791 49270221906545346739705187)
    ·
      refine ⟨73905332859818020109557781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49270221906545346739705187 73905332859818020109557781)
      ·
        refine ⟨3464312477803969692635521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73905332859818020109557781 3464312477803969692635521)
        ·
          refine ⟨2598234358352977269476641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3464312477803969692635521 2598234358352977269476641)
          ·
            refine ⟨1948675768764732952107481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2598234358352977269476641 1948675768764732952107481)
            ·
              refine ⟨1461506826573549714080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1948675768764732952107481 1461506826573549714080611)
              ·
                refine ⟨2192260239860324571120917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461506826573549714080611 2192260239860324571120917)
                ·
                  refine ⟨102762198743452714271293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2192260239860324571120917 102762198743452714271293)
                  ·
                    rfl

theorem cell22_900579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 6].length) (baseStart_900579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900579 prefixEnd_900579 := by exact prefixLift 900579
  have htrace : WordTrace (prefixWord ++ tailWord_900579) baseStart_900579 baseEnd_900579 := by
    simpa [prefixWord, tailWord_900579, baseEnd_900579] using wordTrace_append hprefix tailTrace_900579
  have hstable : (prefixWord ++ tailWord_900579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900579).length < 2 ^ (prefixWord ++ tailWord_900579).sum := by decide
  have hdescent : baseEnd_900579 < baseStart_900579 := by decide
  rcases family_descends (prefixWord ++ tailWord_900579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900592 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_900592 : Nat := 118140960795 + 900592 * 2 ^ 59
def prefixEnd_900592 : Nat := 4983230072969 + 3 ^ 40 * 900592 * 2
def baseEnd_900592 : Nat := 308291046396030442238839

theorem tailTrace_900592 : CollatzResearch.WordTrace tailWord_900592 prefixEnd_900592 308291046396030442238839 := by
  unfold tailWord_900592
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423644376658233856680015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21898192502210978475573353 16423644376658233856680015)
  ·
    refine ⟨24635466564987350785020023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423644376658233856680015 24635466564987350785020023)
    ·
      refine ⟨36953199847481026177530035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24635466564987350785020023 36953199847481026177530035)
      ·
        refine ⟨55429799771221539266295053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36953199847481026177530035 55429799771221539266295053)
        ·
          refine ⟨20786174914208077224860645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55429799771221539266295053 20786174914208077224860645)
          ·
            refine ⟨3897407796414014479661371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20786174914208077224860645 3897407796414014479661371)
            ·
              refine ⟨5846111694621021719492057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897407796414014479661371 5846111694621021719492057)
              ·
                refine ⟨4384583770965766289619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5846111694621021719492057 4384583770965766289619043)
                ·
                  refine ⟨6576875656448649434428565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384583770965766289619043 6576875656448649434428565)
                  ·
                    refine ⟨308291046396030442238839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6576875656448649434428565 308291046396030442238839)
                    ·
                      rfl

theorem cell22_900592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_900592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900592 prefixEnd_900592 := by exact prefixLift 900592
  have htrace : WordTrace (prefixWord ++ tailWord_900592) baseStart_900592 baseEnd_900592 := by
    simpa [prefixWord, tailWord_900592, baseEnd_900592] using wordTrace_append hprefix tailTrace_900592
  have hstable : (prefixWord ++ tailWord_900592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900592).length < 2 ^ (prefixWord ++ tailWord_900592).sum := by decide
  have hdescent : baseEnd_900592 < baseStart_900592 := by decide
  rcases family_descends (prefixWord ++ tailWord_900592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900673 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 1, 3]
def baseStart_900673 : Nat := 118140960795 + 900673 * 2 ^ 59
def prefixEnd_900673 : Nat := 4983230072969 + 3 ^ 40 * 900673 * 2
def baseEnd_900673 : Nat := 308318774351373230963591

theorem tailTrace_900673 : CollatzResearch.WordTrace tailWord_900673 prefixEnd_900673 308318774351373230963591 := by
  unfold tailWord_900673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32850243066023018547058673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21900162044015345698039115 32850243066023018547058673)
  ·
    refine ⟨24637682299517263910294005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32850243066023018547058673 24637682299517263910294005)
    ·
      refine ⟨2309782715579743491590063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24637682299517263910294005 2309782715579743491590063)
      ·
        refine ⟨3464674073369615237385095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2309782715579743491590063 3464674073369615237385095)
        ·
          refine ⟨5197011110054422856077643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464674073369615237385095 5197011110054422856077643)
          ·
            refine ⟨7795516665081634284116465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197011110054422856077643 7795516665081634284116465)
            ·
              refine ⟨5846637498811225713087349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7795516665081634284116465 5846637498811225713087349)
              ·
                refine ⟨548122265513552410601939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5846637498811225713087349 548122265513552410601939)
                ·
                  refine ⟨822183398270328615902909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548122265513552410601939 822183398270328615902909)
                  ·
                    refine ⟨308318774351373230963591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822183398270328615902909 308318774351373230963591)
                    ·
                      rfl

theorem cell22_900673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_900673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900673 prefixEnd_900673 := by exact prefixLift 900673
  have htrace : WordTrace (prefixWord ++ tailWord_900673) baseStart_900673 baseEnd_900673 := by
    simpa [prefixWord, tailWord_900673, baseEnd_900673] using wordTrace_append hprefix tailTrace_900673
  have hstable : (prefixWord ++ tailWord_900673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900673).length < 2 ^ (prefixWord ++ tailWord_900673).sum := by decide
  have hdescent : baseEnd_900673 < baseStart_900673 := by decide
  rcases family_descends (prefixWord ++ tailWord_900673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900690 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_900690 : Nat := 118140960795 + 900690 * 2 ^ 59
def prefixEnd_900690 : Nat := 4983230072969 + 3 ^ 40 * 900690 * 2
def baseEnd_900690 : Nat := 308324593798790853288539

theorem tailTrace_900690 : CollatzResearch.WordTrace tailWord_900690 prefixEnd_900690 308324593798790853288539 := by
  unfold tailWord_900690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212715776740357612606881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21900575404640953633618349 8212715776740357612606881)
  ·
    refine ⟨6159536832555268209455161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8212715776740357612606881 6159536832555268209455161)
    ·
      refine ⟨4619652624416451157091371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6159536832555268209455161 4619652624416451157091371)
      ·
        refine ⟨6929478936624676735637057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619652624416451157091371 6929478936624676735637057)
        ·
          refine ⟨5197109202468507551727793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929478936624676735637057 5197109202468507551727793)
          ·
            refine ⟨3897831901851380663795845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197109202468507551727793 3897831901851380663795845)
            ·
              refine ⟨730843481597133874461721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3897831901851380663795845 730843481597133874461721)
              ·
                refine ⟨548132611197850405846291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730843481597133874461721 548132611197850405846291)
                ·
                  refine ⟨822198916796775608769437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548132611197850405846291 822198916796775608769437)
                  ·
                    refine ⟨308324593798790853288539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822198916796775608769437 308324593798790853288539)
                    ·
                      rfl

theorem cell22_900690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_900690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900690 prefixEnd_900690 := by exact prefixLift 900690
  have htrace : WordTrace (prefixWord ++ tailWord_900690) baseStart_900690 baseEnd_900690 := by
    simpa [prefixWord, tailWord_900690, baseEnd_900690] using wordTrace_append hprefix tailTrace_900690
  have hstable : (prefixWord ++ tailWord_900690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900690).length < 2 ^ (prefixWord ++ tailWord_900690).sum := by decide
  have hdescent : baseEnd_900690 < baseStart_900690 := by decide
  rcases family_descends (prefixWord ++ tailWord_900690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900697 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 10]
def baseStart_900697 : Nat := 118140960795 + 900697 * 2 ^ 59
def prefixEnd_900697 : Nat := 4983230072969 + 3 ^ 40 * 900697 * 2
def baseEnd_900697 : Nat := 102775663347281722787839

theorem tailTrace_900697 : CollatzResearch.WordTrace tailWord_900697 prefixEnd_900697 102775663347281722787839 := by
  unfold tailWord_900697
  simp only [CollatzResearch.WordTrace]
  refine ⟨32851118417936070645932345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21900745611957380430621563 32851118417936070645932345)
  ·
    refine ⟨24638338813452052984449259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32851118417936070645932345 24638338813452052984449259)
    ·
      refine ⟨36957508220178079476673889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638338813452052984449259 36957508220178079476673889)
      ·
        refine ⟨27718131165133559607505417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36957508220178079476673889 27718131165133559607505417)
        ·
          refine ⟨20788598373850169705629063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27718131165133559607505417 20788598373850169705629063)
          ·
            refine ⟨31182897560775254558443595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20788598373850169705629063 31182897560775254558443595)
            ·
              refine ⟨46774346341162881837665393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31182897560775254558443595 46774346341162881837665393)
              ·
                refine ⟨35080759755872161378249045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46774346341162881837665393 35080759755872161378249045)
                ·
                  refine ⟨102775663347281722787839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35080759755872161378249045 102775663347281722787839)
                  ·
                    rfl

theorem cell22_900697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_900697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900697 prefixEnd_900697 := by exact prefixLift 900697
  have htrace : WordTrace (prefixWord ++ tailWord_900697) baseStart_900697 baseEnd_900697 := by
    simpa [prefixWord, tailWord_900697, baseEnd_900697] using wordTrace_append hprefix tailTrace_900697
  have hstable : (prefixWord ++ tailWord_900697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900697).length < 2 ^ (prefixWord ++ tailWord_900697).sum := by decide
  have hdescent : baseEnd_900697 < baseStart_900697 := by decide
  rcases family_descends (prefixWord ++ tailWord_900697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900714 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_900714 : Nat := 118140960795 + 900714 * 2 ^ 59
def prefixEnd_900714 : Nat := 4983230072969 + 3 ^ 40 * 900714 * 2
def baseEnd_900714 : Nat := 102777603163087596896155

theorem tailTrace_900714 : CollatzResearch.WordTrace tailWord_900714 prefixEnd_900714 102777603163087596896155 := by
  unfold tailWord_900714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212934614718620637325299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21901158972582988366200797 8212934614718620637325299)
  ·
    refine ⟨12319401922077930955987949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212934614718620637325299 12319401922077930955987949)
    ·
      refine ⟨4619775720779224108495481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12319401922077930955987949 4619775720779224108495481)
      ·
        refine ⟨3464831790584418081371611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4619775720779224108495481 3464831790584418081371611)
        ·
          refine ⟨5197247685876627122057417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3464831790584418081371611 5197247685876627122057417)
          ·
            refine ⟨3897935764407470341543063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5197247685876627122057417 3897935764407470341543063)
            ·
              refine ⟨5846903646611205512314595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897935764407470341543063 5846903646611205512314595)
              ·
                refine ⟨8770355469916808268471893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846903646611205512314595 8770355469916808268471893)
                ·
                  refine ⟨102777603163087596896155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8770355469916808268471893 102777603163087596896155)
                  ·
                    rfl

theorem cell22_900714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_900714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900714 prefixEnd_900714 := by exact prefixLift 900714
  have htrace : WordTrace (prefixWord ++ tailWord_900714) baseStart_900714 baseEnd_900714 := by
    simpa [prefixWord, tailWord_900714, baseEnd_900714] using wordTrace_append hprefix tailTrace_900714
  have hstable : (prefixWord ++ tailWord_900714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900714).length < 2 ^ (prefixWord ++ tailWord_900714).sum := by decide
  have hdescent : baseEnd_900714 < baseStart_900714 := by decide
  rcases family_descends (prefixWord ++ tailWord_900714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900729 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_900729 : Nat := 118140960795 + 900729 * 2 ^ 59
def prefixEnd_900729 : Nat := 4983230072969 + 3 ^ 40 * 900729 * 2
def baseEnd_900729 : Nat := 308337944295807751563419

theorem tailTrace_900729 : CollatzResearch.WordTrace tailWord_900729 prefixEnd_900729 308337944295807751563419 := by
  unfold tailWord_900729
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852285553820140111097241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21901523702546760074064827 32852285553820140111097241)
  ·
    refine ⟨24639214165365105083322931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32852285553820140111097241 24639214165365105083322931)
    ·
      refine ⟨36958821248047657624984397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24639214165365105083322931 36958821248047657624984397)
      ·
        refine ⟨13859557968017871609369149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36958821248047657624984397 13859557968017871609369149)
        ·
          refine ⟨5197334238006701853513431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13859557968017871609369149 5197334238006701853513431)
          ·
            refine ⟨7796001357010052780270147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197334238006701853513431 7796001357010052780270147)
            ·
              refine ⟨11694002035515079170405221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796001357010052780270147 11694002035515079170405221)
              ·
                refine ⟨2192625381659077344450979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11694002035515079170405221 2192625381659077344450979)
                ·
                  refine ⟨3288938072488616016676469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192625381659077344450979 3288938072488616016676469)
                  ·
                    refine ⟨308337944295807751563419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3288938072488616016676469 308337944295807751563419)
                    ·
                      rfl

theorem cell22_900729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_900729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900729 prefixEnd_900729 := by exact prefixLift 900729
  have htrace : WordTrace (prefixWord ++ tailWord_900729) baseStart_900729 baseEnd_900729 := by
    simpa [prefixWord, tailWord_900729, baseEnd_900729] using wordTrace_append hprefix tailTrace_900729
  have hstable : (prefixWord ++ tailWord_900729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900729).length < 2 ^ (prefixWord ++ tailWord_900729).sum := by decide
  have hdescent : baseEnd_900729 < baseStart_900729 := by decide
  rcases family_descends (prefixWord ++ tailWord_900729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900731 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 4]
def baseStart_900731 : Nat := 118140960795 + 900731 * 2 ^ 59
def prefixEnd_900731 : Nat := 4983230072969 + 3 ^ 40 * 900731 * 2
def baseEnd_900731 : Nat := 102779542978893471004471

theorem tailTrace_900731 : CollatzResearch.WordTrace tailWord_900731 prefixEnd_900731 102779542978893471004471 := by
  unfold tailWord_900731
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852358499812894452670047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21901572333208596301780031 32852358499812894452670047)
  ·
    refine ⟨49278537749719341679005071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32852358499812894452670047 49278537749719341679005071)
    ·
      refine ⟨73917806624579012518507607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49278537749719341679005071 73917806624579012518507607)
      ·
        refine ⟨110876709936868518777761411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73917806624579012518507607 110876709936868518777761411)
        ·
          refine ⟨166315064905302778166642117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110876709936868518777761411 166315064905302778166642117)
          ·
            refine ⟨31184074669744270906245397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166315064905302778166642117 31184074669744270906245397)
            ·
              refine ⟨1461753500144262698730253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31184074669744270906245397 1461753500144262698730253)
              ·
                refine ⟨548157562554098512023845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1461753500144262698730253 548157562554098512023845)
                ·
                  refine ⟨102779542978893471004471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548157562554098512023845 102779542978893471004471)
                  ·
                    rfl

theorem cell22_900731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 4].length) (baseStart_900731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900731 prefixEnd_900731 := by exact prefixLift 900731
  have htrace : WordTrace (prefixWord ++ tailWord_900731) baseStart_900731 baseEnd_900731 := by
    simpa [prefixWord, tailWord_900731, baseEnd_900731] using wordTrace_append hprefix tailTrace_900731
  have hstable : (prefixWord ++ tailWord_900731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900731).length < 2 ^ (prefixWord ++ tailWord_900731).sum := by decide
  have hdescent : baseEnd_900731 < baseStart_900731 := by decide
  rcases family_descends (prefixWord ++ tailWord_900731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900733 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_900733 : Nat := 118140960795 + 900733 * 2 ^ 59
def prefixEnd_900733 : Nat := 4983230072969 + 3 ^ 40 * 900733 * 2
def baseEnd_900733 : Nat := 308339313577553074463407

theorem tailTrace_900733 : CollatzResearch.WordTrace tailWord_900733 prefixEnd_900733 308339313577553074463407 := by
  unfold tailWord_900733
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852431445805648794242853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21901620963870432529495235 32852431445805648794242853)
  ·
    refine ⟨6159830896088559148920535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32852431445805648794242853 6159830896088559148920535)
    ·
      refine ⟨9239746344132838723380803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159830896088559148920535 9239746344132838723380803)
      ·
        refine ⟨13859619516199258085071205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239746344132838723380803 13859619516199258085071205)
        ·
          refine ⟨2598678659287360890950851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13859619516199258085071205 2598678659287360890950851)
          ·
            refine ⟨3898017988931041336426277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598678659287360890950851 3898017988931041336426277)
            ·
              refine ⟨730878372924570250579927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3898017988931041336426277 730878372924570250579927)
              ·
                refine ⟨1096317559386855375869891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730878372924570250579927 1096317559386855375869891)
                ·
                  refine ⟨1644476339080283063804837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096317559386855375869891 1644476339080283063804837)
                  ·
                    refine ⟨308339313577553074463407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1644476339080283063804837 308339313577553074463407)
                    ·
                      rfl

theorem cell22_900733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_900733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900733 prefixEnd_900733 := by exact prefixLift 900733
  have htrace : WordTrace (prefixWord ++ tailWord_900733) baseStart_900733 baseEnd_900733 := by
    simpa [prefixWord, tailWord_900733, baseEnd_900733] using wordTrace_append hprefix tailTrace_900733
  have hstable : (prefixWord ++ tailWord_900733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900733).length < 2 ^ (prefixWord ++ tailWord_900733).sum := by decide
  have hdescent : baseEnd_900733 < baseStart_900733 := by decide
  rcases family_descends (prefixWord ++ tailWord_900733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900782 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_900782 : Nat := 118140960795 + 900782 * 2 ^ 59
def prefixEnd_900782 : Nat := 4983230072969 + 3 ^ 40 * 900782 * 2
def baseEnd_900782 : Nat := 102785362426311093329419

theorem tailTrace_900782 : CollatzResearch.WordTrace tailWord_900782 prefixEnd_900782 102785362426311093329419 := by
  unfold tailWord_900782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106777327828516270347075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21902812415085420108517733 4106777327828516270347075)
  ·
    refine ⟨6160165991742774405520613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106777327828516270347075 6160165991742774405520613)
    ·
      refine ⟨1155031123451770201035115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6160165991742774405520613 1155031123451770201035115)
      ·
        refine ⟨1732546685177655301552673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155031123451770201035115 1732546685177655301552673)
        ·
          refine ⟨1299410013883241476164505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732546685177655301552673 1299410013883241476164505)
          ·
            refine ⟨974557510412431107123379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299410013883241476164505 974557510412431107123379)
            ·
              refine ⟨1461836265618646660685069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974557510412431107123379 1461836265618646660685069)
              ·
                refine ⟨548188599606992497756901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1461836265618646660685069 548188599606992497756901)
                ·
                  refine ⟨102785362426311093329419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548188599606992497756901 102785362426311093329419)
                  ·
                    rfl

theorem cell22_900782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_900782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900782 prefixEnd_900782 := by exact prefixLift 900782
  have htrace : WordTrace (prefixWord ++ tailWord_900782) baseStart_900782 baseEnd_900782 := by
    simpa [prefixWord, tailWord_900782, baseEnd_900782] using wordTrace_append hprefix tailTrace_900782
  have hstable : (prefixWord ++ tailWord_900782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900782).length < 2 ^ (prefixWord ++ tailWord_900782).sum := by decide
  have hdescent : baseEnd_900782 < baseStart_900782 := by decide
  rcases family_descends (prefixWord ++ tailWord_900782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900851 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 1, 4]
def baseStart_900851 : Nat := 118140960795 + 900851 * 2 ^ 59
def prefixEnd_900851 : Nat := 4983230072969 + 3 ^ 40 * 900851 * 2
def baseEnd_900851 : Nat := 308379707389040100013045

theorem tailTrace_900851 : CollatzResearch.WordTrace tailWord_900851 prefixEnd_900851 308379707389040100013045 := by
  unfold tailWord_900851
  simp only [CollatzResearch.WordTrace]
  refine ⟨32856735259378154947038407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21904490172918769964692271 32856735259378154947038407)
  ·
    refine ⟨49285102889067232420557611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32856735259378154947038407 49285102889067232420557611)
    ·
      refine ⟨73927654333600848630836417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49285102889067232420557611 73927654333600848630836417)
      ·
        refine ⟨55445740750200636473127313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73927654333600848630836417 55445740750200636473127313)
        ·
          refine ⟨41584305562650477354845485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55445740750200636473127313 41584305562650477354845485)
          ·
            refine ⟨15594114585993929008067057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41584305562650477354845485 15594114585993929008067057)
            ·
              refine ⟨11695585939495446756050293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15594114585993929008067057 11695585939495446756050293)
              ·
                refine ⟨1096461181827698133379715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11695585939495446756050293 1096461181827698133379715)
                ·
                  refine ⟨1644691772741547200069573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096461181827698133379715 1644691772741547200069573)
                  ·
                    refine ⟨308379707389040100013045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1644691772741547200069573 308379707389040100013045)
                    ·
                      rfl

theorem cell22_900851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4].length) (baseStart_900851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900851 prefixEnd_900851 := by exact prefixLift 900851
  have htrace : WordTrace (prefixWord ++ tailWord_900851) baseStart_900851 baseEnd_900851 := by
    simpa [prefixWord, tailWord_900851, baseEnd_900851] using wordTrace_append hprefix tailTrace_900851
  have hstable : (prefixWord ++ tailWord_900851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900851).length < 2 ^ (prefixWord ++ tailWord_900851).sum := by decide
  have hdescent : baseEnd_900851 < baseStart_900851 := by decide
  rcases family_descends (prefixWord ++ tailWord_900851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900881 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_900881 : Nat := 118140960795 + 900881 * 2 ^ 59
def prefixEnd_900881 : Nat := 4983230072969 + 3 ^ 40 * 900881 * 2
def baseEnd_900881 : Nat := 308389977002130021762953

theorem tailTrace_900881 : CollatzResearch.WordTrace tailWord_900881 prefixEnd_900881 308389977002130021762953 := by
  unfold tailWord_900881
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857829449269470070630497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21905219632846313380420331 32857829449269470070630497)
  ·
    refine ⟨24643372086952102552972873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32857829449269470070630497 24643372086952102552972873)
    ·
      refine ⟨18482529065214076914729655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24643372086952102552972873 18482529065214076914729655)
      ·
        refine ⟨27723793597821115372094483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18482529065214076914729655 27723793597821115372094483)
        ·
          refine ⟨41585690396731673058141725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27723793597821115372094483 41585690396731673058141725)
          ·
            refine ⟨15594633898774377396803147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41585690396731673058141725 15594633898774377396803147)
            ·
              refine ⟨23391950848161566095204721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15594633898774377396803147 23391950848161566095204721)
              ·
                refine ⟨17543963136121174571403541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23391950848161566095204721 17543963136121174571403541)
                ·
                  refine ⟨822373272005680058034541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17543963136121174571403541 822373272005680058034541)
                  ·
                    refine ⟨308389977002130021762953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822373272005680058034541 308389977002130021762953)
                    ·
                      rfl

theorem cell22_900881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_900881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900881 prefixEnd_900881 := by exact prefixLift 900881
  have htrace : WordTrace (prefixWord ++ tailWord_900881) baseStart_900881 baseEnd_900881 := by
    simpa [prefixWord, tailWord_900881, baseEnd_900881] using wordTrace_append hprefix tailTrace_900881
  have hstable : (prefixWord ++ tailWord_900881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900881).length < 2 ^ (prefixWord ++ tailWord_900881).sum := by decide
  have hdescent : baseEnd_900881 < baseStart_900881 := by decide
  rcases family_descends (prefixWord ++ tailWord_900881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900896 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_900896 : Nat := 118140960795 + 900896 * 2 ^ 59
def prefixEnd_900896 : Nat := 4983230072969 + 3 ^ 40 * 900896 * 2
def baseEnd_900896 : Nat := 308395111808674982637907

theorem tailTrace_900896 : CollatzResearch.WordTrace tailWord_900896 prefixEnd_900896 308395111808674982637907 := by
  unfold tailWord_900896
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429188272107563816213271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21905584362810085088284361 16429188272107563816213271)
  ·
    refine ⟨24643782408161345724319907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16429188272107563816213271 24643782408161345724319907)
    ·
      refine ⟨36965673612242018586479861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24643782408161345724319907 36965673612242018586479861)
      ·
        refine ⟨3465531901147689242482487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36965673612242018586479861 3465531901147689242482487)
        ·
          refine ⟨5198297851721533863723731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3465531901147689242482487 5198297851721533863723731)
          ·
            refine ⟨7797446777582300795585597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198297851721533863723731 7797446777582300795585597)
            ·
              refine ⟨2924042541593362798344599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7797446777582300795585597 2924042541593362798344599)
              ·
                refine ⟨4386063812390044197516899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924042541593362798344599 4386063812390044197516899)
                ·
                  refine ⟨6579095718585066296275349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386063812390044197516899 6579095718585066296275349)
                  ·
                    refine ⟨308395111808674982637907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6579095718585066296275349 308395111808674982637907)
                    ·
                      rfl

theorem cell22_900896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_900896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900896 prefixEnd_900896 := by exact prefixLift 900896
  have htrace : WordTrace (prefixWord ++ tailWord_900896) baseStart_900896 baseEnd_900896 := by
    simpa [prefixWord, tailWord_900896, baseEnd_900896] using wordTrace_append hprefix tailTrace_900896
  have hstable : (prefixWord ++ tailWord_900896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900896).length < 2 ^ (prefixWord ++ tailWord_900896).sum := by decide
  have hdescent : baseEnd_900896 < baseStart_900896 := by decide
  rcases family_descends (prefixWord ++ tailWord_900896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900898 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_900898 : Nat := 118140960795 + 900898 * 2 ^ 59
def prefixEnd_900898 : Nat := 4983230072969 + 3 ^ 40 * 900898 * 2
def baseEnd_900898 : Nat := 308395796449547644087901

theorem tailTrace_900898 : CollatzResearch.WordTrace tailWord_900898 prefixEnd_900898 308395796449547644087901 := by
  unfold tailWord_900898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214612372551970493499837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21905632993471921315999565 8214612372551970493499837)
  ·
    refine ⟨3080479639706988935062439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8214612372551970493499837 3080479639706988935062439)
    ·
      refine ⟨4620719459560483402593659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080479639706988935062439 4620719459560483402593659)
      ·
        refine ⟨6931079189340725103890489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620719459560483402593659 6931079189340725103890489)
        ·
          refine ⟨5198309392005543827917867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6931079189340725103890489 5198309392005543827917867)
          ·
            refine ⟨7797464088008315741876801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198309392005543827917867 7797464088008315741876801)
            ·
              refine ⟨5848098066006236806407601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7797464088008315741876801 5848098066006236806407601)
              ·
                refine ⟨4386073549504677604805701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5848098066006236806407601 4386073549504677604805701)
                ·
                  refine ⟨822388790532127050901069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4386073549504677604805701 822388790532127050901069)
                  ·
                    refine ⟨308395796449547644087901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822388790532127050901069 308395796449547644087901)
                    ·
                      rfl

theorem cell22_900898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_900898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900898 prefixEnd_900898 := by exact prefixLift 900898
  have htrace : WordTrace (prefixWord ++ tailWord_900898) baseStart_900898 baseEnd_900898 := by
    simpa [prefixWord, tailWord_900898, baseEnd_900898] using wordTrace_append hprefix tailTrace_900898
  have hstable : (prefixWord ++ tailWord_900898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900898).length < 2 ^ (prefixWord ++ tailWord_900898).sum := by decide
  have hdescent : baseEnd_900898 < baseStart_900898 := by decide
  rcases family_descends (prefixWord ++ tailWord_900898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900900 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_900900 : Nat := 118140960795 + 900900 * 2 ^ 59
def prefixEnd_900900 : Nat := 4983230072969 + 3 ^ 40 * 900900 * 2
def baseEnd_900900 : Nat := 102798827030140101845965

theorem tailTrace_900900 : CollatzResearch.WordTrace tailWord_900900 prefixEnd_900900 102798827030140101845965 := by
  unfold tailWord_900900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429261218100318157786077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21905681624133757543714769 16429261218100318157786077)
  ·
    refine ⟨6160972956787619309169779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16429261218100318157786077 6160972956787619309169779)
    ·
      refine ⟨9241459435181428963754669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6160972956787619309169779 9241459435181428963754669)
      ·
        refine ⟨3465547288193035861408001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9241459435181428963754669 3465547288193035861408001)
        ·
          refine ⟨2599160466144776896056001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3465547288193035861408001 2599160466144776896056001)
          ·
            refine ⟨1949370349608582672042001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2599160466144776896056001 1949370349608582672042001)
            ·
              refine ⟨1462027762206437004031501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949370349608582672042001 1462027762206437004031501)
              ·
                refine ⟨548260410827413876511813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462027762206437004031501 548260410827413876511813)
                ·
                  refine ⟨102798827030140101845965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548260410827413876511813 102798827030140101845965)
                  ·
                    rfl

theorem cell22_900900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_900900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900900 prefixEnd_900900 := by exact prefixLift 900900
  have htrace : WordTrace (prefixWord ++ tailWord_900900) baseStart_900900 baseEnd_900900 := by
    simpa [prefixWord, tailWord_900900, baseEnd_900900] using wordTrace_append hprefix tailTrace_900900
  have hstable : (prefixWord ++ tailWord_900900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900900).length < 2 ^ (prefixWord ++ tailWord_900900).sum := by decide
  have hdescent : baseEnd_900900 < baseStart_900900 := by decide
  rcases family_descends (prefixWord ++ tailWord_900900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900977 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 1, 3]
def baseStart_900977 : Nat := 118140960795 + 900977 * 2 ^ 59
def prefixEnd_900977 : Nat := 4983230072969 + 3 ^ 40 * 900977 * 2
def baseEnd_900977 : Nat := 308422839764017771362659

theorem tailTrace_900977 : CollatzResearch.WordTrace tailWord_900977 prefixEnd_900977 308422839764017771362659 := by
  unfold tailWord_900977
  simp only [CollatzResearch.WordTrace]
  refine ⟨32861330856921678466125185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21907553904614452310750123 32861330856921678466125185)
  ·
    refine ⟨24645998142691258849593889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32861330856921678466125185 24645998142691258849593889)
    ·
      refine ⟨18484498607018444137195417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24645998142691258849593889 18484498607018444137195417)
      ·
        refine ⟨13863373955263833102896563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18484498607018444137195417 13863373955263833102896563)
        ·
          refine ⟨20795060932895749654344845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13863373955263833102896563 20795060932895749654344845)
          ·
            refine ⟨7798147849835906120379317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20795060932895749654344845 7798147849835906120379317)
            ·
              refine ⟨731076360922116198785561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7798147849835906120379317 731076360922116198785561)
              ·
                refine ⟨548307270691587149089171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731076360922116198785561 548307270691587149089171)
                ·
                  refine ⟨822460906037380723633757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548307270691587149089171 822460906037380723633757)
                  ·
                    refine ⟨308422839764017771362659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822460906037380723633757 308422839764017771362659)
                    ·
                      rfl

theorem cell22_900977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_900977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_900977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_900977 prefixEnd_900977 := by exact prefixLift 900977
  have htrace : WordTrace (prefixWord ++ tailWord_900977) baseStart_900977 baseEnd_900977 := by
    simpa [prefixWord, tailWord_900977, baseEnd_900977] using wordTrace_append hprefix tailTrace_900977
  have hstable : (prefixWord ++ tailWord_900977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900977).length < 2 ^ (prefixWord ++ tailWord_900977).sum := by decide
  have hdescent : baseEnd_900977 < baseStart_900977 := by decide
  rcases family_descends (prefixWord ++ tailWord_900977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901001 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 8]
def baseStart_901001 : Nat := 118140960795 + 901001 * 2 ^ 59
def prefixEnd_901001 : Nat := 4983230072969 + 3 ^ 40 * 901001 * 2
def baseEnd_901001 : Nat := 102810351818163236254195

theorem tailTrace_901001 : CollatzResearch.WordTrace tailWord_901001 prefixEnd_901001 102810351818163236254195 := by
  unfold tailWord_901001
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862206208834730564998857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21908137472556487043332571 32862206208834730564998857)
  ·
    refine ⟨24646654656626047923749143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32862206208834730564998857 24646654656626047923749143)
    ·
      refine ⟨36969981984939071885623715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24646654656626047923749143 36969981984939071885623715)
      ·
        refine ⟨55454972977408607828435573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36969981984939071885623715 55454972977408607828435573)
        ·
          refine ⟨5198903716632056983915835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55454972977408607828435573 5198903716632056983915835)
          ·
            refine ⟨7798355574948085475873753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198903716632056983915835 7798355574948085475873753)
            ·
              refine ⟨5848766681211064106905315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7798355574948085475873753 5848766681211064106905315)
              ·
                refine ⟨8773150021816596160357973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848766681211064106905315 8773150021816596160357973)
                ·
                  refine ⟨102810351818163236254195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8773150021816596160357973 102810351818163236254195)
                  ·
                    rfl

theorem cell22_901001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_901001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901001 prefixEnd_901001 := by exact prefixLift 901001
  have htrace : WordTrace (prefixWord ++ tailWord_901001) baseStart_901001 baseEnd_901001 := by
    simpa [prefixWord, tailWord_901001, baseEnd_901001] using wordTrace_append hprefix tailTrace_901001
  have hstable : (prefixWord ++ tailWord_901001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901001).length < 2 ^ (prefixWord ++ tailWord_901001).sum := by decide
  have hdescent : baseEnd_901001 < baseStart_901001 := by decide
  rcases family_descends (prefixWord ++ tailWord_901001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901061 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_901061 : Nat := 118140960795 + 901061 * 2 ^ 59
def prefixEnd_901061 : Nat := 4983230072969 + 3 ^ 40 * 901061 * 2
def baseEnd_901061 : Nat := 308451594680669552262401

theorem tailTrace_901061 : CollatzResearch.WordTrace tailWord_901061 prefixEnd_901061 308451594680669552262401 := by
  unfold tailWord_901061
  simp only [CollatzResearch.WordTrace]
  refine ⟨32864394588617360812183037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21909596392411573874788691 32864394588617360812183037)
  ·
    refine ⟨12324147970731510304568639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32864394588617360812183037 12324147970731510304568639)
    ·
      refine ⟨18486221956097265456852959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12324147970731510304568639 18486221956097265456852959)
      ·
        refine ⟨27729332934145898185279439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18486221956097265456852959 27729332934145898185279439)
        ·
          refine ⟨41593999401218847277919159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27729332934145898185279439 41593999401218847277919159)
          ·
            refine ⟨62390999101828270916878739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41593999401218847277919159 62390999101828270916878739)
            ·
              refine ⟨93586498652742406375318109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62390999101828270916878739 93586498652742406375318109)
              ·
                refine ⟨35094936994778402390744291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93586498652742406375318109 35094936994778402390744291)
                ·
                  refine ⟨52642405492167603586116437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35094936994778402390744291 52642405492167603586116437)
                  ·
                    refine ⟨308451594680669552262401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 52642405492167603586116437 308451594680669552262401)
                    ·
                      rfl

theorem cell22_901061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_901061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901061 prefixEnd_901061 := by exact prefixLift 901061
  have htrace : WordTrace (prefixWord ++ tailWord_901061) baseStart_901061 baseEnd_901061 := by
    simpa [prefixWord, tailWord_901061, baseEnd_901061] using wordTrace_append hprefix tailTrace_901061
  have hstable : (prefixWord ++ tailWord_901061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901061).length < 2 ^ (prefixWord ++ tailWord_901061).sum := by decide
  have hdescent : baseEnd_901061 < baseStart_901061 := by decide
  rcases family_descends (prefixWord ++ tailWord_901061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901101 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_901101 : Nat := 118140960795 + 901101 * 2 ^ 59
def prefixEnd_901101 : Nat := 4983230072969 + 3 ^ 40 * 901101 * 2
def baseEnd_901101 : Nat := 308465287498122781262279

theorem tailTrace_901101 : CollatzResearch.WordTrace tailWord_901101 prefixEnd_901101 308465287498122781262279 := by
  unfold tailWord_901101
  simp only [CollatzResearch.WordTrace]
  refine ⟨32865853508472447643639157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21910569005648298429092771 32865853508472447643639157)
  ·
    refine ⟨3081173766419291966591171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32865853508472447643639157 3081173766419291966591171)
    ·
      refine ⟨4621760649628937949886757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081173766419291966591171 4621760649628937949886757)
      ·
        refine ⟨866580121805425865603767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4621760649628937949886757 866580121805425865603767)
        ·
          refine ⟨1299870182708138798405651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866580121805425865603767 1299870182708138798405651)
          ·
            refine ⟨1949805274062208197608477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299870182708138798405651 1949805274062208197608477)
            ·
              refine ⟨731176977773328074103179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1949805274062208197608477 731176977773328074103179)
              ·
                refine ⟨1096765466659992111154769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731176977773328074103179 1096765466659992111154769)
                ·
                  refine ⟨822574099994994083366077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1096765466659992111154769 822574099994994083366077)
                  ·
                    refine ⟨308465287498122781262279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822574099994994083366077 308465287498122781262279)
                    ·
                      rfl

theorem cell22_901101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_901101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901101 prefixEnd_901101 := by exact prefixLift 901101
  have htrace : WordTrace (prefixWord ++ tailWord_901101) baseStart_901101 baseEnd_901101 := by
    simpa [prefixWord, tailWord_901101, baseEnd_901101] using wordTrace_append hprefix tailTrace_901101
  have hstable : (prefixWord ++ tailWord_901101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901101).length < 2 ^ (prefixWord ++ tailWord_901101).sum := by decide
  have hdescent : baseEnd_901101 < baseStart_901101 := by decide
  rcases family_descends (prefixWord ++ tailWord_901101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901183 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_901183 : Nat := 118140960795 + 901183 * 2 ^ 59
def prefixEnd_901183 : Nat := 4983230072969 + 3 ^ 40 * 901183 * 2
def baseEnd_901183 : Nat := 308493357773901900712027

theorem tailTrace_901183 : CollatzResearch.WordTrace tailWord_901183 prefixEnd_901183 308493357773901900712027 := by
  unfold tailWord_901183
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868844294175375648124203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21912562862783583765416135 32868844294175375648124203)
  ·
    refine ⟨49303266441263063472186305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32868844294175375648124203 49303266441263063472186305)
    ·
      refine ⟨36977449830947297604139729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49303266441263063472186305 36977449830947297604139729)
      ·
        refine ⟨27733087373210473203104797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36977449830947297604139729 27733087373210473203104797)
        ·
          refine ⟨10399907764953927451164299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27733087373210473203104797 10399907764953927451164299)
          ·
            refine ⟨15599861647430891176746449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399907764953927451164299 15599861647430891176746449)
            ·
              refine ⟨11699896235573168382559837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15599861647430891176746449 11699896235573168382559837)
              ·
                refine ⟨4387461088339938143459939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11699896235573168382559837 4387461088339938143459939)
                ·
                  refine ⟨6581191632509907215189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387461088339938143459939 6581191632509907215189909)
                  ·
                    refine ⟨308493357773901900712027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6581191632509907215189909 308493357773901900712027)
                    ·
                      rfl

theorem cell22_901183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_901183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901183 prefixEnd_901183 := by exact prefixLift 901183
  have htrace : WordTrace (prefixWord ++ tailWord_901183) baseStart_901183 baseEnd_901183 := by
    simpa [prefixWord, tailWord_901183, baseEnd_901183] using wordTrace_append hprefix tailTrace_901183
  have hstable : (prefixWord ++ tailWord_901183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901183).length < 2 ^ (prefixWord ++ tailWord_901183).sum := by decide
  have hdescent : baseEnd_901183 < baseStart_901183 := by decide
  rcases family_descends (prefixWord ++ tailWord_901183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901185 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_901185 : Nat := 118140960795 + 901185 * 2 ^ 59
def prefixEnd_901185 : Nat := 4983230072969 + 3 ^ 40 * 901185 * 2
def baseEnd_901185 : Nat := 308494042414774562162021

theorem tailTrace_901185 : CollatzResearch.WordTrace tailWord_901185 prefixEnd_901185 308494042414774562162021 := by
  unfold tailWord_901185
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868917240168129989697009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21912611493445419993131339 32868917240168129989697009)
  ·
    refine ⟨24651687930126097492272757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32868917240168129989697009 24651687930126097492272757)
    ·
      refine ⟨2311095743449321639900571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24651687930126097492272757 2311095743449321639900571)
      ·
        refine ⟨3466643615173982459850857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311095743449321639900571 3466643615173982459850857)
        ·
          refine ⟨2599982711380486844888143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3466643615173982459850857 2599982711380486844888143)
          ·
            refine ⟨3899974067070730267332215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599982711380486844888143 3899974067070730267332215)
            ·
              refine ⟨5849961100606095400998323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899974067070730267332215 5849961100606095400998323)
              ·
                refine ⟨8774941650909143101497485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849961100606095400998323 8774941650909143101497485)
                ·
                  refine ⟨3290603119090928663061557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8774941650909143101497485 3290603119090928663061557)
                  ·
                    refine ⟨308494042414774562162021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3290603119090928663061557 308494042414774562162021)
                    ·
                      rfl

theorem cell22_901185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_901185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901185 prefixEnd_901185 := by exact prefixLift 901185
  have htrace : WordTrace (prefixWord ++ tailWord_901185) baseStart_901185 baseEnd_901185 := by
    simpa [prefixWord, tailWord_901185, baseEnd_901185] using wordTrace_append hprefix tailTrace_901185
  have hstable : (prefixWord ++ tailWord_901185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901185).length < 2 ^ (prefixWord ++ tailWord_901185).sum := by decide
  have hdescent : baseEnd_901185 < baseStart_901185 := by decide
  rcases family_descends (prefixWord ++ tailWord_901185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901198 : List Nat := [4, 1, 1, 1, 1, 14]
def baseStart_901198 : Nat := 118140960795 + 901198 * 2 ^ 59
def prefixEnd_901198 : Nat := 4983230072969 + 3 ^ 40 * 901198 * 2
def baseEnd_901198 : Nat := 3808623365190701994901

theorem tailTrace_901198 : CollatzResearch.WordTrace tailWord_901198 prefixEnd_901198 3808623365190701994901 := by
  unfold tailWord_901198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108673923640129151240031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21912927592747355473280165 4108673923640129151240031)
  ·
    refine ⟨6163010885460193726860047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4108673923640129151240031 6163010885460193726860047)
    ·
      refine ⟨9244516328190290590290071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163010885460193726860047 9244516328190290590290071)
      ·
        refine ⟨13866774492285435885435107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244516328190290590290071 13866774492285435885435107)
        ·
          refine ⟨20800161738428153828152661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13866774492285435885435107 20800161738428153828152661)
          ·
            refine ⟨3808623365190701994901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 20800161738428153828152661 3808623365190701994901)
            ·
              rfl

theorem cell22_901198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 14].length) (baseStart_901198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901198 prefixEnd_901198 := by exact prefixLift 901198
  have htrace : WordTrace (prefixWord ++ tailWord_901198) baseStart_901198 baseEnd_901198 := by
    simpa [prefixWord, tailWord_901198, baseEnd_901198] using wordTrace_append hprefix tailTrace_901198
  have hstable : (prefixWord ++ tailWord_901198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901198).length < 2 ^ (prefixWord ++ tailWord_901198).sum := by decide
  have hdescent : baseEnd_901198 < baseStart_901198 := by decide
  rcases family_descends (prefixWord ++ tailWord_901198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901270 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_901270 : Nat := 118140960795 + 901270 * 2 ^ 59
def prefixEnd_901270 : Nat := 4983230072969 + 3 ^ 40 * 901270 * 2
def baseEnd_901270 : Nat := 308523139651862673786761

theorem tailTrace_901270 : CollatzResearch.WordTrace tailWord_901270 prefixEnd_901270 308523139651862673786761 := by
  unfold tailWord_901270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054501090303761844158829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21914678296573459671027509 2054501090303761844158829)
  ·
    refine ⟨770437908863910691559561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2054501090303761844158829 770437908863910691559561)
    ·
      refine ⟨577828431647933018669671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770437908863910691559561 577828431647933018669671)
      ·
        refine ⟨866742647471899528004507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577828431647933018669671 866742647471899528004507)
        ·
          refine ⟨1300113971207849292006761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866742647471899528004507 1300113971207849292006761)
          ·
            refine ⟨975085478405886969005071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300113971207849292006761 975085478405886969005071)
            ·
              refine ⟨1462628217608830453507607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975085478405886969005071 1462628217608830453507607)
              ·
                refine ⟨2193942326413245680261411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462628217608830453507607 2193942326413245680261411)
                ·
                  refine ⟨3290913489619868520392117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193942326413245680261411 3290913489619868520392117)
                  ·
                    refine ⟨308523139651862673786761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3290913489619868520392117 308523139651862673786761)
                    ·
                      rfl

theorem cell22_901270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_901270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901270 prefixEnd_901270 := by exact prefixLift 901270
  have htrace : WordTrace (prefixWord ++ tailWord_901270) baseStart_901270 baseEnd_901270 := by
    simpa [prefixWord, tailWord_901270, baseEnd_901270] using wordTrace_append hprefix tailTrace_901270
  have hstable : (prefixWord ++ tailWord_901270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901270).length < 2 ^ (prefixWord ++ tailWord_901270).sum := by decide
  have hdescent : baseEnd_901270 < baseStart_901270 := by decide
  rcases family_descends (prefixWord ++ tailWord_901270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901335 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_901335 : Nat := 118140960795 + 901335 * 2 ^ 59
def prefixEnd_901335 : Nat := 4983230072969 + 3 ^ 40 * 901335 * 2
def baseEnd_901335 : Nat := 308545390480224170911561

theorem tailTrace_901335 : CollatzResearch.WordTrace tailWord_901335 prefixEnd_901335 308545390480224170911561 := by
  unfold tailWord_901335
  simp only [CollatzResearch.WordTrace]
  refine ⟨32874388189624705607657459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21916258793083137071771639 32874388189624705607657459)
  ·
    refine ⟨49311582284437058411486189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32874388189624705607657459 49311582284437058411486189)
    ·
      refine ⟨18491843356663896904307321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49311582284437058411486189 18491843356663896904307321)
      ·
        refine ⟨13868882517497922678230491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18491843356663896904307321 13868882517497922678230491)
        ·
          refine ⟨20803323776246884017345737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13868882517497922678230491 20803323776246884017345737)
          ·
            refine ⟨15602492832185163013009303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20803323776246884017345737 15602492832185163013009303)
            ·
              refine ⟨23403739248277744519513955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15602492832185163013009303 23403739248277744519513955)
              ·
                refine ⟨35105608872416616779270933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23403739248277744519513955 35105608872416616779270933)
                ·
                  refine ⟨1645575415894528911528325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35105608872416616779270933 1645575415894528911528325)
                  ·
                    refine ⟨308545390480224170911561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645575415894528911528325 308545390480224170911561)
                    ·
                      rfl

theorem cell22_901335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_901335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901335 prefixEnd_901335 := by exact prefixLift 901335
  have htrace : WordTrace (prefixWord ++ tailWord_901335) baseStart_901335 baseEnd_901335 := by
    simpa [prefixWord, tailWord_901335, baseEnd_901335] using wordTrace_append hprefix tailTrace_901335
  have hstable : (prefixWord ++ tailWord_901335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901335).length < 2 ^ (prefixWord ++ tailWord_901335).sum := by decide
  have hdescent : baseEnd_901335 < baseStart_901335 := by decide
  rcases family_descends (prefixWord ++ tailWord_901335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901341 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_901341 : Nat := 118140960795 + 901341 * 2 ^ 59
def prefixEnd_901341 : Nat := 4983230072969 + 3 ^ 40 * 901341 * 2
def baseEnd_901341 : Nat := 308547444402842155261543

theorem tailTrace_901341 : CollatzResearch.WordTrace tailWord_901341 prefixEnd_901341 308547444402842155261543 := by
  unfold tailWord_901341
  simp only [CollatzResearch.WordTrace]
  refine ⟨32874607027602968632375877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21916404685068645754917251 32874607027602968632375877)
  ·
    refine ⟨6163988817675556618570477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32874607027602968632375877 6163988817675556618570477)
    ·
      refine ⟨2311495806628333731963929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6163988817675556618570477 2311495806628333731963929)
      ·
        refine ⟨1733621854971250298972947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2311495806628333731963929 1733621854971250298972947)
        ·
          refine ⟨2600432782456875448459421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733621854971250298972947 2600432782456875448459421)
          ·
            refine ⟨975162293421328293172283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2600432782456875448459421 975162293421328293172283)
            ·
              refine ⟨1462743440131992439758425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975162293421328293172283 1462743440131992439758425)
              ·
                refine ⟨1097057580098994329818819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462743440131992439758425 1097057580098994329818819)
                ·
                  refine ⟨1645586370148491494728229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097057580098994329818819 1645586370148491494728229)
                  ·
                    refine ⟨308547444402842155261543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645586370148491494728229 308547444402842155261543)
                    ·
                      rfl

theorem cell22_901341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_901341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901341 prefixEnd_901341 := by exact prefixLift 901341
  have htrace : WordTrace (prefixWord ++ tailWord_901341) baseStart_901341 baseEnd_901341 := by
    simpa [prefixWord, tailWord_901341, baseEnd_901341] using wordTrace_append hprefix tailTrace_901341
  have hstable : (prefixWord ++ tailWord_901341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901341).length < 2 ^ (prefixWord ++ tailWord_901341).sum := by decide
  have hdescent : baseEnd_901341 < baseStart_901341 := by decide
  rcases family_descends (prefixWord ++ tailWord_901341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901352 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_901352 : Nat := 118140960795 + 901352 * 2 ^ 59
def prefixEnd_901352 : Nat := 4983230072969 + 3 ^ 40 * 901352 * 2
def baseEnd_901352 : Nat := 308551209927641793236509

theorem tailTrace_901352 : CollatzResearch.WordTrace tailWord_901352 prefixEnd_901352 308551209927641793236509 := by
  unfold tailWord_901352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437504115281558755513155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21916672153708745007350873 16437504115281558755513155)
  ·
    refine ⟨24656256172922338133269733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16437504115281558755513155 24656256172922338133269733)
    ·
      refine ⟨4623048032422938399988075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24656256172922338133269733 4623048032422938399988075)
      ·
        refine ⟨6934572048634407599982113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623048032422938399988075 6934572048634407599982113)
        ·
          refine ⟨5200929036475805699986585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934572048634407599982113 5200929036475805699986585)
          ·
            refine ⟨3900696777356854274989939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200929036475805699986585 3900696777356854274989939)
            ·
              refine ⟨5851045166035281412484909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900696777356854274989939 5851045166035281412484909)
              ·
                refine ⟨2194141937263230529681841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851045166035281412484909 2194141937263230529681841)
                ·
                  refine ⟨1645606452947422897261381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194141937263230529681841 1645606452947422897261381)
                  ·
                    refine ⟨308551209927641793236509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645606452947422897261381 308551209927641793236509)
                    ·
                      rfl

theorem cell22_901352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_901352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901352 prefixEnd_901352 := by exact prefixLift 901352
  have htrace : WordTrace (prefixWord ++ tailWord_901352) baseStart_901352 baseEnd_901352 := by
    simpa [prefixWord, tailWord_901352, baseEnd_901352] using wordTrace_append hprefix tailTrace_901352
  have hstable : (prefixWord ++ tailWord_901352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901352).length < 2 ^ (prefixWord ++ tailWord_901352).sum := by decide
  have hdescent : baseEnd_901352 < baseStart_901352 := by decide
  rcases family_descends (prefixWord ++ tailWord_901352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901399 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 3, 3]
def baseStart_901399 : Nat := 118140960795 + 901399 * 2 ^ 59
def prefixEnd_901399 : Nat := 4983230072969 + 3 ^ 40 * 901399 * 2
def baseEnd_901399 : Nat := 308567298988149337311365

theorem tailTrace_901399 : CollatzResearch.WordTrace tailWord_901399 prefixEnd_901399 308567298988149337311365 := by
  unfold tailWord_901399
  simp only [CollatzResearch.WordTrace]
  refine ⟨32876722461392844537987251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21917814974261896358658167 32876722461392844537987251)
  ·
    refine ⟨49315083692089266806980877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32876722461392844537987251 49315083692089266806980877)
    ·
      refine ⟨18493156384533475052617829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49315083692089266806980877 18493156384533475052617829)
      ·
        refine ⟨3467466822100026572365843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18493156384533475052617829 3467466822100026572365843)
        ·
          refine ⟨5201200233150039858548765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467466822100026572365843 5201200233150039858548765)
          ·
            refine ⟨1950450087431264946955787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5201200233150039858548765 1950450087431264946955787)
            ·
              refine ⟨2925675131146897420433681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950450087431264946955787 2925675131146897420433681)
              ·
                refine ⟨2194256348360173065325261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925675131146897420433681 2194256348360173065325261)
                ·
                  refine ⟨822846130635064899496973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2194256348360173065325261 822846130635064899496973)
                  ·
                    refine ⟨308567298988149337311365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822846130635064899496973 308567298988149337311365)
                    ·
                      rfl

theorem cell22_901399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_901399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901399 prefixEnd_901399 := by exact prefixLift 901399
  have htrace : WordTrace (prefixWord ++ tailWord_901399) baseStart_901399 baseEnd_901399 := by
    simpa [prefixWord, tailWord_901399, baseEnd_901399] using wordTrace_append hprefix tailTrace_901399
  have hstable : (prefixWord ++ tailWord_901399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901399).length < 2 ^ (prefixWord ++ tailWord_901399).sum := by decide
  have hdescent : baseEnd_901399 < baseStart_901399 := by decide
  rcases family_descends (prefixWord ++ tailWord_901399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901457 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 6]
def baseStart_901457 : Nat := 118140960795 + 901457 * 2 ^ 59
def prefixEnd_901457 : Nat := 4983230072969 + 3 ^ 40 * 901457 * 2
def baseEnd_901457 : Nat := 102862384524485506453729

theorem tailTrace_901457 : CollatzResearch.WordTrace tailWord_901457 prefixEnd_901457 102862384524485506453729 := by
  unfold tailWord_901457
  simp only [CollatzResearch.WordTrace]
  refine ⟨32878837895182720443598625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21919225263455146962399083 32878837895182720443598625)
  ·
    refine ⟨24659128421387040332698969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32878837895182720443598625 24659128421387040332698969)
    ·
      refine ⟨18494346316040280249524227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24659128421387040332698969 18494346316040280249524227)
      ·
        refine ⟨27741519474060420374286341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18494346316040280249524227 27741519474060420374286341)
        ·
          refine ⟨5201534901386328820178689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27741519474060420374286341 5201534901386328820178689)
          ·
            refine ⟨3901151176039746615134017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201534901386328820178689 3901151176039746615134017)
            ·
              refine ⟨2925863382029809961350513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901151176039746615134017 2925863382029809961350513)
              ·
                refine ⟨2194397536522357471012885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925863382029809961350513 2194397536522357471012885)
                ·
                  refine ⟨102862384524485506453729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2194397536522357471012885 102862384524485506453729)
                  ·
                    rfl

theorem cell22_901457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_901457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901457 prefixEnd_901457 := by exact prefixLift 901457
  have htrace : WordTrace (prefixWord ++ tailWord_901457) baseStart_901457 baseEnd_901457 := by
    simpa [prefixWord, tailWord_901457, baseEnd_901457] using wordTrace_append hprefix tailTrace_901457
  have hstable : (prefixWord ++ tailWord_901457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901457).length < 2 ^ (prefixWord ++ tailWord_901457).sum := by decide
  have hdescent : baseEnd_901457 < baseStart_901457 := by decide
  rcases family_descends (prefixWord ++ tailWord_901457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901489 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_901489 : Nat := 118140960795 + 901489 * 2 ^ 59
def prefixEnd_901489 : Nat := 4983230072969 + 3 ^ 40 * 901489 * 2
def baseEnd_901489 : Nat := 308598107827419102561089

theorem tailTrace_901489 : CollatzResearch.WordTrace tailWord_901489 prefixEnd_901489 308598107827419102561089 := by
  unfold tailWord_901489
  simp only [CollatzResearch.WordTrace]
  refine ⟨32880005031066789908763521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21920003354044526605842347 32880005031066789908763521)
  ·
    refine ⟨24660003773300092431572641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32880005031066789908763521 24660003773300092431572641)
    ·
      refine ⟨18495002829975069323679481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24660003773300092431572641 18495002829975069323679481)
      ·
        refine ⟨13871252122481301992759611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18495002829975069323679481 13871252122481301992759611)
        ·
          refine ⟨20806878183721952989139417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13871252122481301992759611 20806878183721952989139417)
          ·
            refine ⟨15605158637791464741854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20806878183721952989139417 15605158637791464741854563)
            ·
              refine ⟨23407737956687197112781845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15605158637791464741854563 23407737956687197112781845)
              ·
                refine ⟨1097237716719712364661649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23407737956687197112781845 1097237716719712364661649)
                ·
                  refine ⟨822928287539784273496237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097237716719712364661649 822928287539784273496237)
                  ·
                    refine ⟨308598107827419102561089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 822928287539784273496237 308598107827419102561089)
                    ·
                      rfl

theorem cell22_901489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_901489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901489 prefixEnd_901489 := by exact prefixLift 901489
  have htrace : WordTrace (prefixWord ++ tailWord_901489) baseStart_901489 baseEnd_901489 := by
    simpa [prefixWord, tailWord_901489, baseEnd_901489] using wordTrace_append hprefix tailTrace_901489
  have hstable : (prefixWord ++ tailWord_901489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901489).length < 2 ^ (prefixWord ++ tailWord_901489).sum := by decide
  have hdescent : baseEnd_901489 < baseStart_901489 := by decide
  rcases family_descends (prefixWord ++ tailWord_901489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901592 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_901592 : Nat := 118140960795 + 901592 * 2 ^ 59
def prefixEnd_901592 : Nat := 4983230072969 + 3 ^ 40 * 901592 * 2
def baseEnd_901592 : Nat := 102877788944120389078591

theorem tailTrace_901592 : CollatzResearch.WordTrace tailWord_901592 prefixEnd_901592 102877788944120389078591 := by
  unfold tailWord_901592
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441880874846819249881515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21922507833129092333175353 16441880874846819249881515)
  ·
    refine ⟨24662821312270228874822273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16441880874846819249881515 24662821312270228874822273)
    ·
      refine ⟨18497115984202671656116705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24662821312270228874822273 18497115984202671656116705)
      ·
        refine ⟨13872836988152003742087529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18497115984202671656116705 13872836988152003742087529)
        ·
          refine ⟨10404627741114002806565647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13872836988152003742087529 10404627741114002806565647)
          ·
            refine ⟨15606941611671004209848471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404627741114002806565647 15606941611671004209848471)
            ·
              refine ⟨23410412417506506314772707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15606941611671004209848471 23410412417506506314772707)
              ·
                refine ⟨35115618626259759472159061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23410412417506506314772707 35115618626259759472159061)
                ·
                  refine ⟨102877788944120389078591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35115618626259759472159061 102877788944120389078591)
                  ·
                    rfl

theorem cell22_901592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_901592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901592 prefixEnd_901592 := by exact prefixLift 901592
  have htrace : WordTrace (prefixWord ++ tailWord_901592) baseStart_901592 baseEnd_901592 := by
    simpa [prefixWord, tailWord_901592, baseEnd_901592] using wordTrace_append hprefix tailTrace_901592
  have hstable : (prefixWord ++ tailWord_901592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901592).length < 2 ^ (prefixWord ++ tailWord_901592).sum := by decide
  have hdescent : baseEnd_901592 < baseStart_901592 := by decide
  rcases family_descends (prefixWord ++ tailWord_901592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901643 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 4]
def baseStart_901643 : Nat := 118140960795 + 901643 * 2 ^ 59
def prefixEnd_901643 : Nat := 4983230072969 + 3 ^ 40 * 901643 * 2
def baseEnd_901643 : Nat := 102883608391538011403539

theorem tailTrace_901643 : CollatzResearch.WordTrace tailWord_901643 prefixEnd_901643 102883608391538011403539 := by
  unfold tailWord_901643
  simp only [CollatzResearch.WordTrace]
  refine ⟨32885621872508874209869583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21923747915005916139913055 32885621872508874209869583)
  ·
    refine ⟨49328432808763311314804375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32885621872508874209869583 49328432808763311314804375)
    ·
      refine ⟨73992649213144966972206563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49328432808763311314804375 73992649213144966972206563)
      ·
        refine ⟨110988973819717450458309845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73992649213144966972206563 110988973819717450458309845)
        ·
          refine ⟨2601304073899627745116637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110988973819717450458309845 2601304073899627745116637)
          ·
            refine ⟨975489027712360404418739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2601304073899627745116637 975489027712360404418739)
            ·
              refine ⟨1463233541568540606628109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975489027712360404418739 1463233541568540606628109)
              ·
                refine ⟨548712578088202727485541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1463233541568540606628109 548712578088202727485541)
                ·
                  refine ⟨102883608391538011403539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548712578088202727485541 102883608391538011403539)
                  ·
                    rfl

theorem cell22_901643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 4].length) (baseStart_901643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901643 prefixEnd_901643 := by exact prefixLift 901643
  have htrace : WordTrace (prefixWord ++ tailWord_901643) baseStart_901643 baseEnd_901643 := by
    simpa [prefixWord, tailWord_901643, baseEnd_901643] using wordTrace_append hprefix tailTrace_901643
  have hstable : (prefixWord ++ tailWord_901643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901643).length < 2 ^ (prefixWord ++ tailWord_901643).sum := by decide
  have hdescent : baseEnd_901643 < baseStart_901643 := by decide
  rcases family_descends (prefixWord ++ tailWord_901643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901645 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_901645 : Nat := 118140960795 + 901645 * 2 ^ 59
def prefixEnd_901645 : Nat := 4983230072969 + 3 ^ 40 * 901645 * 2
def baseEnd_901645 : Nat := 308651509815486695660611

theorem tailTrace_901645 : CollatzResearch.WordTrace tailWord_901645 prefixEnd_901645 308651509815486695660611 := by
  unfold tailWord_901645
  simp only [CollatzResearch.WordTrace]
  refine ⟨32885694818501628551442389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21923796545667752367628259 32885694818501628551442389)
  ·
    refine ⟨770758472308631919174431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32885694818501628551442389 770758472308631919174431)
    ·
      refine ⟨1156137708462947878761647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770758472308631919174431 1156137708462947878761647)
      ·
        refine ⟨1734206562694421818142471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156137708462947878761647 1734206562694421818142471)
        ·
          refine ⟨2601309844041632727213707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734206562694421818142471 2601309844041632727213707)
          ·
            refine ⟨3901964766062449090820561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601309844041632727213707 3901964766062449090820561)
            ·
              refine ⟨2926473574546836818115421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901964766062449090820561 2926473574546836818115421)
              ·
                refine ⟨1097427590455063806793283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2926473574546836818115421 1097427590455063806793283)
                ·
                  refine ⟨1646141385682595710189925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097427590455063806793283 1646141385682595710189925)
                  ·
                    refine ⟨308651509815486695660611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646141385682595710189925 308651509815486695660611)
                    ·
                      rfl

theorem cell22_901645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_901645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901645 prefixEnd_901645 := by exact prefixLift 901645
  have htrace : WordTrace (prefixWord ++ tailWord_901645) baseStart_901645 baseEnd_901645 := by
    simpa [prefixWord, tailWord_901645, baseEnd_901645] using wordTrace_append hprefix tailTrace_901645
  have hstable : (prefixWord ++ tailWord_901645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901645).length < 2 ^ (prefixWord ++ tailWord_901645).sum := by decide
  have hdescent : baseEnd_901645 < baseStart_901645 := by decide
  rcases family_descends (prefixWord ++ tailWord_901645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901656 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_901656 : Nat := 118140960795 + 901656 * 2 ^ 59
def prefixEnd_901656 : Nat := 4983230072969 + 3 ^ 40 * 901656 * 2
def baseEnd_901656 : Nat := 308655275340286333635577

theorem tailTrace_901656 : CollatzResearch.WordTrace tailWord_901656 prefixEnd_901656 308655275340286333635577 := by
  unfold tailWord_901656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443048010730888715046411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21924064014307851620061881 16443048010730888715046411)
  ·
    refine ⟨24664572016096333072569617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16443048010730888715046411 24664572016096333072569617)
    ·
      refine ⟨18498429012072249804427213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24664572016096333072569617 18498429012072249804427213)
      ·
        refine ⟨6936910879527093676660205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18498429012072249804427213 6936910879527093676660205)
        ·
          refine ⟨2601341579822660128747577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6936910879527093676660205 2601341579822660128747577)
          ·
            refine ⟨1951006184866995096560683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601341579822660128747577 1951006184866995096560683)
            ·
              refine ⟨2926509277300492644841025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951006184866995096560683 2926509277300492644841025)
              ·
                refine ⟨2194881957975369483630769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926509277300492644841025 2194881957975369483630769)
                ·
                  refine ⟨1646161468481527112723077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194881957975369483630769 1646161468481527112723077)
                  ·
                    refine ⟨308655275340286333635577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646161468481527112723077 308655275340286333635577)
                    ·
                      rfl

theorem cell22_901656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_901656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901656 prefixEnd_901656 := by exact prefixLift 901656
  have htrace : WordTrace (prefixWord ++ tailWord_901656) baseStart_901656 baseEnd_901656 := by
    simpa [prefixWord, tailWord_901656, baseEnd_901656] using wordTrace_append hprefix tailTrace_901656
  have hstable : (prefixWord ++ tailWord_901656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901656).length < 2 ^ (prefixWord ++ tailWord_901656).sum := by decide
  have hdescent : baseEnd_901656 < baseStart_901656 := by decide
  rcases family_descends (prefixWord ++ tailWord_901656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901716 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_901716 : Nat := 118140960795 + 901716 * 2 ^ 59
def prefixEnd_901716 : Nat := 4983230072969 + 3 ^ 40 * 901716 * 2
def baseEnd_901716 : Nat := 102891938188822059045131

theorem tailTrace_901716 : CollatzResearch.WordTrace tailWord_901716 prefixEnd_901716 102891938188822059045131 := by
  unfold tailWord_901716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444142200622203838638501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21925522934162938451518001 16444142200622203838638501)
  ·
    refine ⟨3083276662616663219744719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16444142200622203838638501 3083276662616663219744719)
    ·
      refine ⟨4624914993924994829617079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083276662616663219744719 4624914993924994829617079)
      ·
        refine ⟨6937372490887492244425619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624914993924994829617079 6937372490887492244425619)
        ·
          refine ⟨10406058736331238366638429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937372490887492244425619 10406058736331238366638429)
          ·
            refine ⟨3902272026124214387489411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10406058736331238366638429 3902272026124214387489411)
            ·
              refine ⟨5853408039186321581234117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902272026124214387489411 5853408039186321581234117)
              ·
                refine ⟨1097514007347435296481397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5853408039186321581234117 1097514007347435296481397)
                ·
                  refine ⟨102891938188822059045131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1097514007347435296481397 102891938188822059045131)
                  ·
                    rfl

theorem cell22_901716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_901716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901716 prefixEnd_901716 := by exact prefixLift 901716
  have htrace : WordTrace (prefixWord ++ tailWord_901716) baseStart_901716 baseEnd_901716 := by
    simpa [prefixWord, tailWord_901716, baseEnd_901716] using wordTrace_append hprefix tailTrace_901716
  have hstable : (prefixWord ++ tailWord_901716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901716).length < 2 ^ (prefixWord ++ tailWord_901716).sum := by decide
  have hdescent : baseEnd_901716 < baseStart_901716 := by decide
  rcases family_descends (prefixWord ++ tailWord_901716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901720 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 1, 3]
def baseStart_901720 : Nat := 118140960795 + 901720 * 2 ^ 59
def prefixEnd_901720 : Nat := 4983230072969 + 3 ^ 40 * 901720 * 2
def baseEnd_901720 : Nat := 308677183848211500035381

theorem tailTrace_901720 : CollatzResearch.WordTrace tailWord_901720 prefixEnd_901720 308677183848211500035381 := by
  unfold tailWord_901720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444215146614958180211307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21925620195486610906948409 16444215146614958180211307)
  ·
    refine ⟨24666322719922437270316961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444215146614958180211307 24666322719922437270316961)
    ·
      refine ⟨18499742039941827952737721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24666322719922437270316961 18499742039941827952737721)
      ·
        refine ⟨13874806529956370964553291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18499742039941827952737721 13874806529956370964553291)
        ·
          refine ⟨20812209794934556446829937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13874806529956370964553291 20812209794934556446829937)
          ·
            refine ⟨15609157346200917335122453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20812209794934556446829937 15609157346200917335122453)
            ·
              refine ⟨731679250603168000083865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15609157346200917335122453 731679250603168000083865)
              ·
                refine ⟨548759437952376000062899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731679250603168000083865 548759437952376000062899)
                ·
                  refine ⟨823139156928564000094349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548759437952376000062899 823139156928564000094349)
                  ·
                    refine ⟨308677183848211500035381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823139156928564000094349 308677183848211500035381)
                    ·
                      rfl

theorem cell22_901720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_901720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901720 prefixEnd_901720 := by exact prefixLift 901720
  have htrace : WordTrace (prefixWord ++ tailWord_901720) baseStart_901720 baseEnd_901720 := by
    simpa [prefixWord, tailWord_901720, baseEnd_901720] using wordTrace_append hprefix tailTrace_901720
  have hstable : (prefixWord ++ tailWord_901720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901720).length < 2 ^ (prefixWord ++ tailWord_901720).sum := by decide
  have hdescent : baseEnd_901720 < baseStart_901720 := by decide
  rcases family_descends (prefixWord ++ tailWord_901720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901759 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_901759 : Nat := 118140960795 + 901759 * 2 ^ 59
def prefixEnd_901759 : Nat := 4983230072969 + 3 ^ 40 * 901759 * 2
def baseEnd_901759 : Nat := 308690534345228398310261

theorem tailTrace_901759 : CollatzResearch.WordTrace tailWord_901759 prefixEnd_901759 308690534345228398310261 := by
  unfold tailWord_901759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889852740088626021092331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21926568493392417347394887 32889852740088626021092331)
  ·
    refine ⟨49334779110132939031638497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889852740088626021092331 49334779110132939031638497)
    ·
      refine ⟨37001084332599704273728873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49334779110132939031638497 37001084332599704273728873)
      ·
        refine ⟨27750813249449778205296655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37001084332599704273728873 27750813249449778205296655)
        ·
          refine ⟨41626219874174667307944983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750813249449778205296655 41626219874174667307944983)
          ·
            refine ⟨62439329811262000961917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41626219874174667307944983 62439329811262000961917475)
            ·
              refine ⟨93658994716893001442876213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62439329811262000961917475 93658994716893001442876213)
              ·
                refine ⟨8780530754708718885269645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93658994716893001442876213 8780530754708718885269645)
                ·
                  refine ⟨3292699033015769581976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8780530754708718885269645 3292699033015769581976117)
                  ·
                    refine ⟨308690534345228398310261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3292699033015769581976117 308690534345228398310261)
                    ·
                      rfl

theorem cell22_901759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_901759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901759 prefixEnd_901759 := by exact prefixLift 901759
  have htrace : WordTrace (prefixWord ++ tailWord_901759) baseStart_901759 baseEnd_901759 := by
    simpa [prefixWord, tailWord_901759, baseEnd_901759] using wordTrace_append hprefix tailTrace_901759
  have hstable : (prefixWord ++ tailWord_901759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901759).length < 2 ^ (prefixWord ++ tailWord_901759).sum := by decide
  have hdescent : baseEnd_901759 < baseStart_901759 := by decide
  rcases family_descends (prefixWord ++ tailWord_901759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901763 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 1, 4]
def baseStart_901763 : Nat := 118140960795 + 901763 * 2 ^ 59
def prefixEnd_901763 : Nat := 4983230072969 + 3 ^ 40 * 901763 * 2
def baseEnd_901763 : Nat := 308691903626973721210249

theorem tailTrace_901763 : CollatzResearch.WordTrace tailWord_901763 prefixEnd_901763 308691903626973721210249 := by
  unfold tailWord_901763
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889998632074134704237943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21926665754716089802825295 32889998632074134704237943)
  ·
    refine ⟨49334997948111202056356915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889998632074134704237943 49334997948111202056356915)
    ·
      refine ⟨74002496922166803084535373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49334997948111202056356915 74002496922166803084535373)
      ·
        refine ⟨27750936345812551156700765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74002496922166803084535373 27750936345812551156700765)
        ·
          refine ⟨10406601129679706683762787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27750936345812551156700765 10406601129679706683762787)
          ·
            refine ⟨15609901694519560025644181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406601129679706683762787 15609901694519560025644181)
            ·
              refine ⟨731714141930604376202071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15609901694519560025644181 731714141930604376202071)
              ·
                refine ⟨1097571212895906564303107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731714141930604376202071 1097571212895906564303107)
                ·
                  refine ⟨1646356819343859846454661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097571212895906564303107 1646356819343859846454661)
                  ·
                    refine ⟨308691903626973721210249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646356819343859846454661 308691903626973721210249)
                    ·
                      rfl

theorem cell22_901763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 4].length) (baseStart_901763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901763 prefixEnd_901763 := by exact prefixLift 901763
  have htrace : WordTrace (prefixWord ++ tailWord_901763) baseStart_901763 baseEnd_901763 := by
    simpa [prefixWord, tailWord_901763, baseEnd_901763] using wordTrace_append hprefix tailTrace_901763
  have hstable : (prefixWord ++ tailWord_901763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901763).length < 2 ^ (prefixWord ++ tailWord_901763).sum := by decide
  have hdescent : baseEnd_901763 < baseStart_901763 := by decide
  rcases family_descends (prefixWord ++ tailWord_901763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901778 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_901778 : Nat := 118140960795 + 901778 * 2 ^ 59
def prefixEnd_901778 : Nat := 4983230072969 + 3 ^ 40 * 901778 * 2
def baseEnd_901778 : Nat := 102899012811172894028401

theorem tailTrace_901778 : CollatzResearch.WordTrace tailWord_901778 prefixEnd_901778 102899012811172894028401 := by
  unfold tailWord_901778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222636431754948066508497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21927030484679861510689325 8222636431754948066508497)
  ·
    refine ⟨6166977323816211049881373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8222636431754948066508497 6166977323816211049881373)
    ·
      refine ⟨2312616496431079143705515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6166977323816211049881373 2312616496431079143705515)
      ·
        refine ⟨3468924744646618715558273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312616496431079143705515 3468924744646618715558273)
        ·
          refine ⟨2601693558484964036668705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3468924744646618715558273 2601693558484964036668705)
          ·
            refine ⟨1951270168863723027501529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601693558484964036668705 1951270168863723027501529)
            ·
              refine ⟨1463452626647792270626147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951270168863723027501529 1463452626647792270626147)
              ·
                refine ⟨2195178939971688405939221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463452626647792270626147 2195178939971688405939221)
                ·
                  refine ⟨102899012811172894028401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2195178939971688405939221 102899012811172894028401)
                  ·
                    rfl

theorem cell22_901778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_901778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901778 prefixEnd_901778 := by exact prefixLift 901778
  have htrace : WordTrace (prefixWord ++ tailWord_901778) baseStart_901778 baseEnd_901778 := by
    simpa [prefixWord, tailWord_901778, baseEnd_901778] using wordTrace_append hprefix tailTrace_901778
  have hstable : (prefixWord ++ tailWord_901778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901778).length < 2 ^ (prefixWord ++ tailWord_901778).sum := by decide
  have hdescent : baseEnd_901778 < baseStart_901778 := by decide
  rcases family_descends (prefixWord ++ tailWord_901778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901819 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_901819 : Nat := 118140960795 + 901819 * 2 ^ 59
def prefixEnd_901819 : Nat := 4983230072969 + 3 ^ 40 * 901819 * 2
def baseEnd_901819 : Nat := 308711073571408241810077

theorem tailTrace_901819 : CollatzResearch.WordTrace tailWord_901819 prefixEnd_901819 308711073571408241810077 := by
  unfold tailWord_901819
  simp only [CollatzResearch.WordTrace]
  refine ⟨32892041119871256268276511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21928027413247504178851007 32892041119871256268276511)
  ·
    refine ⟨49338061679806884402414767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32892041119871256268276511 49338061679806884402414767)
    ·
      refine ⟨74007092519710326603622151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49338061679806884402414767 74007092519710326603622151)
      ·
        refine ⟨111010638779565489905433227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74007092519710326603622151 111010638779565489905433227)
        ·
          refine ⟨166515958169348234858149841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111010638779565489905433227 166515958169348234858149841)
          ·
            refine ⟨124886968627011176143612381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166515958169348234858149841 124886968627011176143612381)
            ·
              refine ⟨46832613235129191053854643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124886968627011176143612381 46832613235129191053854643)
              ·
                refine ⟨70248919852693786580781965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46832613235129191053854643 70248919852693786580781965)
                ·
                  refine ⟨26343344944760169967793237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70248919852693786580781965 26343344944760169967793237)
                  ·
                    refine ⟨308711073571408241810077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26343344944760169967793237 308711073571408241810077)
                    ·
                      rfl

theorem cell22_901819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_901819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901819 prefixEnd_901819 := by exact prefixLift 901819
  have htrace : WordTrace (prefixWord ++ tailWord_901819) baseStart_901819 baseEnd_901819 := by
    simpa [prefixWord, tailWord_901819, baseEnd_901819] using wordTrace_append hprefix tailTrace_901819
  have hstable : (prefixWord ++ tailWord_901819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901819).length < 2 ^ (prefixWord ++ tailWord_901819).sum := by decide
  have hdescent : baseEnd_901819 < baseStart_901819 := by decide
  rcases family_descends (prefixWord ++ tailWord_901819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901844 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_901844 : Nat := 118140960795 + 901844 * 2 ^ 59
def prefixEnd_901844 : Nat := 4983230072969 + 3 ^ 40 * 901844 * 2
def baseEnd_901844 : Nat := 308719631582316509935001

theorem tailTrace_901844 : CollatzResearch.WordTrace tailWord_901844 prefixEnd_901844 308719631582316509935001 := by
  unfold tailWord_901844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446476472390342768968293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21928635296520457025291057 16446476472390342768968293)
  ·
    refine ⟨3083714338573189269181555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16446476472390342768968293 3083714338573189269181555)
    ·
      refine ⟨4625571507859783903772333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083714338573189269181555 4625571507859783903772333)
      ·
        refine ⟨1734589315447418963914625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4625571507859783903772333 1734589315447418963914625)
        ·
          refine ⟨1300941986585564222935969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734589315447418963914625 1300941986585564222935969)
          ·
            refine ⟨975706489939173167201977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300941986585564222935969 975706489939173167201977)
            ·
              refine ⟨731779867454379875401483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975706489939173167201977 731779867454379875401483)
              ·
                refine ⟨1097669801181569813102225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731779867454379875401483 1097669801181569813102225)
                ·
                  refine ⟨823252350886177359826669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097669801181569813102225 823252350886177359826669)
                  ·
                    refine ⟨308719631582316509935001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823252350886177359826669 308719631582316509935001)
                    ·
                      rfl

theorem cell22_901844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_901844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901844 prefixEnd_901844 := by exact prefixLift 901844
  have htrace : WordTrace (prefixWord ++ tailWord_901844) baseStart_901844 baseEnd_901844 := by
    simpa [prefixWord, tailWord_901844, baseEnd_901844] using wordTrace_append hprefix tailTrace_901844
  have hstable : (prefixWord ++ tailWord_901844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901844).length < 2 ^ (prefixWord ++ tailWord_901844).sum := by decide
  have hdescent : baseEnd_901844 < baseStart_901844 := by decide
  rcases family_descends (prefixWord ++ tailWord_901844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901866 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_901866 : Nat := 118140960795 + 901866 * 2 ^ 59
def prefixEnd_901866 : Nat := 4983230072969 + 3 ^ 40 * 901866 * 2
def baseEnd_901866 : Nat := 308727162631915785884933

theorem tailTrace_901866 : CollatzResearch.WordTrace tailWord_901866 prefixEnd_901866 308727162631915785884933 := by
  unfold tailWord_901866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223438837675245823809363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21929170233800655530158301 8223438837675245823809363)
  ·
    refine ⟨12335158256512868735714045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8223438837675245823809363 12335158256512868735714045)
    ·
      refine ⟨4625684346192325775892767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12335158256512868735714045 4625684346192325775892767)
      ·
        refine ⟨6938526519288488663839151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625684346192325775892767 6938526519288488663839151)
        ·
          refine ⟨10407789778932732995758727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938526519288488663839151 10407789778932732995758727)
          ·
            refine ⟨15611684668399099493638091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10407789778932732995758727 15611684668399099493638091)
            ·
              refine ⟨23417527002598649240457137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15611684668399099493638091 23417527002598649240457137)
              ·
                refine ⟨17563145251948986930342853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23417527002598649240457137 17563145251948986930342853)
                ·
                  refine ⟨3293089734740435049439285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17563145251948986930342853 3293089734740435049439285)
                  ·
                    refine ⟨308727162631915785884933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3293089734740435049439285 308727162631915785884933)
                    ·
                      rfl

theorem cell22_901866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_901866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901866 prefixEnd_901866 := by exact prefixLift 901866
  have htrace : WordTrace (prefixWord ++ tailWord_901866) baseStart_901866 baseEnd_901866 := by
    simpa [prefixWord, tailWord_901866, baseEnd_901866] using wordTrace_append hprefix tailTrace_901866
  have hstable : (prefixWord ++ tailWord_901866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901866).length < 2 ^ (prefixWord ++ tailWord_901866).sum := by decide
  have hdescent : baseEnd_901866 < baseStart_901866 := by decide
  rcases family_descends (prefixWord ++ tailWord_901866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901928 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_901928 : Nat := 118140960795 + 901928 * 2 ^ 59
def prefixEnd_901928 : Nat := 4983230072969 + 3 ^ 40 * 901928 * 2
def baseEnd_901928 : Nat := 308748386498968290834743

theorem tailTrace_901928 : CollatzResearch.WordTrace tailWord_901928 prefixEnd_901928 308748386498968290834743 := by
  unfold tailWord_901928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448008338238183941997219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21930677784317578589329625 16448008338238183941997219)
  ·
    refine ⟨24672012507357275912995829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16448008338238183941997219 24672012507357275912995829)
    ·
      refine ⟨2313001172564744616843359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24672012507357275912995829 2313001172564744616843359)
      ·
        refine ⟨3469501758847116925265039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313001172564744616843359 3469501758847116925265039)
        ·
          refine ⟨5204252638270675387897559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469501758847116925265039 5204252638270675387897559)
          ·
            refine ⟨7806378957406013081846339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204252638270675387897559 7806378957406013081846339)
            ·
              refine ⟨11709568436109019622769509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806378957406013081846339 11709568436109019622769509)
              ·
                refine ⟨2195544081770441179269283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11709568436109019622769509 2195544081770441179269283)
                ·
                  refine ⟨3293316122655661768903925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195544081770441179269283 3293316122655661768903925)
                  ·
                    refine ⟨308748386498968290834743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3293316122655661768903925 308748386498968290834743)
                    ·
                      rfl

theorem cell22_901928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_901928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901928 prefixEnd_901928 := by exact prefixLift 901928
  have htrace : WordTrace (prefixWord ++ tailWord_901928) baseStart_901928 baseEnd_901928 := by
    simpa [prefixWord, tailWord_901928, baseEnd_901928] using wordTrace_append hprefix tailTrace_901928
  have hstable : (prefixWord ++ tailWord_901928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901928).length < 2 ^ (prefixWord ++ tailWord_901928).sum := by decide
  have hdescent : baseEnd_901928 < baseStart_901928 := by decide
  rcases family_descends (prefixWord ++ tailWord_901928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901971 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_901971 : Nat := 118140960795 + 901971 * 2 ^ 59
def prefixEnd_901971 : Nat := 4983230072969 + 3 ^ 40 * 901971 * 2
def baseEnd_901971 : Nat := 308763106277730512009611

theorem tailTrace_901971 : CollatzResearch.WordTrace tailWord_901971 prefixEnd_901971 308763106277730512009611 := by
  unfold tailWord_901971
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897585015320586227809767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21931723343547057485206511 32897585015320586227809767)
  ·
    refine ⟨49346377522980879341714651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32897585015320586227809767 49346377522980879341714651)
    ·
      refine ⟨74019566284471319012571977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49346377522980879341714651 74019566284471319012571977)
      ·
        refine ⟨55514674713353489259428983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74019566284471319012571977 55514674713353489259428983)
        ·
          refine ⟨83272012070030233889143475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55514674713353489259428983 83272012070030233889143475)
          ·
            refine ⟨124908018105045350833715213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83272012070030233889143475 124908018105045350833715213)
            ·
              refine ⟨46840506789392006562643205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124908018105045350833715213 46840506789392006562643205)
              ·
                refine ⟨8782595023011001230495601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46840506789392006562643205 8782595023011001230495601)
                ·
                  refine ⟨6586946267258250922871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8782595023011001230495601 6586946267258250922871701)
                  ·
                    refine ⟨308763106277730512009611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6586946267258250922871701 308763106277730512009611)
                    ·
                      rfl

theorem cell22_901971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_901971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901971 prefixEnd_901971 := by exact prefixLift 901971
  have htrace : WordTrace (prefixWord ++ tailWord_901971) baseStart_901971 baseEnd_901971 := by
    simpa [prefixWord, tailWord_901971, baseEnd_901971] using wordTrace_append hprefix tailTrace_901971
  have hstable : (prefixWord ++ tailWord_901971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901971).length < 2 ^ (prefixWord ++ tailWord_901971).sum := by decide
  have hdescent : baseEnd_901971 < baseStart_901971 := by decide
  rcases family_descends (prefixWord ++ tailWord_901971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901975 : List Nat := [1, 1, 3, 2, 4, 3, 2, 6]
def baseStart_901975 : Nat := 118140960795 + 901975 * 2 ^ 59
def prefixEnd_901975 : Nat := 4983230072969 + 3 ^ 40 * 901975 * 2
def baseEnd_901975 : Nat := 34307163951052870545511

theorem tailTrace_901975 : CollatzResearch.WordTrace tailWord_901975 prefixEnd_901975 34307163951052870545511 := by
  unfold tailWord_901975
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897730907306094910955379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21931820604870729940636919 32897730907306094910955379)
  ·
    refine ⟨49346596360959142366433069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32897730907306094910955379 49346596360959142366433069)
    ·
      refine ⟨18504973635359678387412401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49346596360959142366433069 18504973635359678387412401)
      ·
        refine ⟨13878730226519758790559301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18504973635359678387412401 13878730226519758790559301)
        ·
          refine ⟨2602261917472454773229869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13878730226519758790559301 2602261917472454773229869)
          ·
            refine ⟨975848219052170539961201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2602261917472454773229869 975848219052170539961201)
            ·
              refine ⟨731886164289127904970901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975848219052170539961201 731886164289127904970901)
              ·
                refine ⟨34307163951052870545511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 731886164289127904970901 34307163951052870545511)
                ·
                  rfl

theorem cell22_901975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 6].length) (baseStart_901975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_901975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_901975 prefixEnd_901975 := by exact prefixLift 901975
  have htrace : WordTrace (prefixWord ++ tailWord_901975) baseStart_901975 baseEnd_901975 := by
    simpa [prefixWord, tailWord_901975, baseEnd_901975] using wordTrace_append hprefix tailTrace_901975
  have hstable : (prefixWord ++ tailWord_901975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901975).length < 2 ^ (prefixWord ++ tailWord_901975).sum := by decide
  have hdescent : baseEnd_901975 < baseStart_901975 := by decide
  rcases family_descends (prefixWord ++ tailWord_901975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902080 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_902080 : Nat := 118140960795 + 902080 * 2 ^ 59
def prefixEnd_902080 : Nat := 4983230072969 + 3 ^ 40 * 902080 * 2
def baseEnd_902080 : Nat := 308800419205290561034277

theorem tailTrace_902080 : CollatzResearch.WordTrace tailWord_902080 prefixEnd_902080 308800419205290561034277 := by
  unfold tailWord_902080
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450780285962848921763847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21934373714617131895685129 16450780285962848921763847)
  ·
    refine ⟨24676170428944273382645771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16450780285962848921763847 24676170428944273382645771)
    ·
      refine ⟨37014255643416410073968657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676170428944273382645771 37014255643416410073968657)
      ·
        refine ⟨27760691732562307555476493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37014255643416410073968657 27760691732562307555476493)
        ·
          refine ⟨10410259399710865333303685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27760691732562307555476493 10410259399710865333303685)
          ·
            refine ⟨1951923637445787249994441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10410259399710865333303685 1951923637445787249994441)
            ·
              refine ⟨1463942728084340437495831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951923637445787249994441 1463942728084340437495831)
              ·
                refine ⟨2195914092126510656243747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463942728084340437495831 2195914092126510656243747)
                ·
                  refine ⟨3293871138189765984365621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195914092126510656243747 3293871138189765984365621)
                  ·
                    refine ⟨308800419205290561034277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3293871138189765984365621 308800419205290561034277)
                    ·
                      rfl

theorem cell22_902080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_902080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902080 prefixEnd_902080 := by exact prefixLift 902080
  have htrace : WordTrace (prefixWord ++ tailWord_902080) baseStart_902080 baseEnd_902080 := by
    simpa [prefixWord, tailWord_902080, baseEnd_902080] using wordTrace_append hprefix tailTrace_902080
  have hstable : (prefixWord ++ tailWord_902080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902080).length < 2 ^ (prefixWord ++ tailWord_902080).sum := by decide
  have hdescent : baseEnd_902080 < baseStart_902080 := by decide
  rcases family_descends (prefixWord ++ tailWord_902080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902095 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 2, 4]
def baseStart_902095 : Nat := 118140960795 + 902095 * 2 ^ 59
def prefixEnd_902095 : Nat := 4983230072969 + 3 ^ 40 * 902095 * 2
def baseEnd_902095 : Nat := 308805554011835521909231

theorem tailTrace_902095 : CollatzResearch.WordTrace tailWord_902095 prefixEnd_902095 308805554011835521909231 := by
  unfold tailWord_902095
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902107666871355405323739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21934738444580903603549159 32902107666871355405323739)
  ·
    refine ⟨49353161500307033107985609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32902107666871355405323739 49353161500307033107985609)
    ·
      refine ⟨37014871125230274830989207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49353161500307033107985609 37014871125230274830989207)
      ·
        refine ⟨55522306687845412246483811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37014871125230274830989207 55522306687845412246483811)
        ·
          refine ⟨83283460031768118369725717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55522306687845412246483811 83283460031768118369725717)
          ·
            refine ⟨3903912188989130548580893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83283460031768118369725717 3903912188989130548580893)
            ·
              refine ⟨1463967070870923955717835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3903912188989130548580893 1463967070870923955717835)
              ·
                refine ⟨2195950606306385933576753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463967070870923955717835 2195950606306385933576753)
                ·
                  refine ⟨1646962954729789450182565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2195950606306385933576753 1646962954729789450182565)
                  ·
                    refine ⟨308805554011835521909231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646962954729789450182565 308805554011835521909231)
                    ·
                      rfl

theorem cell22_902095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_902095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902095 prefixEnd_902095 := by exact prefixLift 902095
  have htrace : WordTrace (prefixWord ++ tailWord_902095) baseStart_902095 baseEnd_902095 := by
    simpa [prefixWord, tailWord_902095, baseEnd_902095] using wordTrace_append hprefix tailTrace_902095
  have hstable : (prefixWord ++ tailWord_902095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902095).length < 2 ^ (prefixWord ++ tailWord_902095).sum := by decide
  have hdescent : baseEnd_902095 < baseStart_902095 := by decide
  rcases family_descends (prefixWord ++ tailWord_902095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902101 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_902101 : Nat := 118140960795 + 902101 * 2 ^ 59
def prefixEnd_902101 : Nat := 4983230072969 + 3 ^ 40 * 902101 * 2
def baseEnd_902101 : Nat := 308807607934453506259213

theorem tailTrace_902101 : CollatzResearch.WordTrace tailWord_902101 prefixEnd_902101 308807607934453506259213 := by
  unfold tailWord_902101
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902326504849618430042157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21934884336566412286694771 32902326504849618430042157)
  ·
    refine ⟨12338372439318606911265809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32902326504849618430042157 12338372439318606911265809)
    ·
      refine ⟨9253779329488955183449357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12338372439318606911265809 9253779329488955183449357)
      ·
        refine ⟨3470167248558358193793509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9253779329488955183449357 3470167248558358193793509)
        ·
          refine ⟨650656359104692161336283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3470167248558358193793509 650656359104692161336283)
          ·
            refine ⟨975984538657038242004425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650656359104692161336283 975984538657038242004425)
            ·
              refine ⟨731988403992778681503319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975984538657038242004425 731988403992778681503319)
              ·
                refine ⟨1097982605989168022254979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731988403992778681503319 1097982605989168022254979)
                ·
                  refine ⟨1646973908983752033382469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097982605989168022254979 1646973908983752033382469)
                  ·
                    refine ⟨308807607934453506259213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1646973908983752033382469 308807607934453506259213)
                    ·
                      rfl

theorem cell22_902101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_902101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902101 prefixEnd_902101 := by exact prefixLift 902101
  have htrace : WordTrace (prefixWord ++ tailWord_902101) baseStart_902101 baseEnd_902101 := by
    simpa [prefixWord, tailWord_902101, baseEnd_902101] using wordTrace_append hprefix tailTrace_902101
  have hstable : (prefixWord ++ tailWord_902101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902101).length < 2 ^ (prefixWord ++ tailWord_902101).sum := by decide
  have hdescent : baseEnd_902101 < baseStart_902101 := by decide
  rcases family_descends (prefixWord ++ tailWord_902101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902114 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_902114 : Nat := 118140960795 + 902114 * 2 ^ 59
def prefixEnd_902114 : Nat := 4983230072969 + 3 ^ 40 * 902114 * 2
def baseEnd_902114 : Nat := 308812058100125805684173

theorem tailTrace_902114 : CollatzResearch.WordTrace tailWord_902114 prefixEnd_902114 308812058100125805684173 := by
  unfold tailWord_902114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225700163450630412566349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21935200435868347766843597 8225700163450630412566349)
  ·
    refine ⟨3084637561293986404712381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8225700163450630412566349 3084637561293986404712381)
    ·
      refine ⟨1156739085485244901767143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3084637561293986404712381 1156739085485244901767143)
      ·
        refine ⟨1735108628227867352650715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156739085485244901767143 1735108628227867352650715)
        ·
          refine ⟨2602662942341801028976073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735108628227867352650715 2602662942341801028976073)
          ·
            refine ⟨1951997206756350771732055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2602662942341801028976073 1951997206756350771732055)
            ·
              refine ⟨2927995810134526157598083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951997206756350771732055 2927995810134526157598083)
              ·
                refine ⟨4391993715201789236397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927995810134526157598083 4391993715201789236397125)
                ·
                  refine ⟨823498821600335481824461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4391993715201789236397125 823498821600335481824461)
                  ·
                    refine ⟨308812058100125805684173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823498821600335481824461 308812058100125805684173)
                    ·
                      rfl

theorem cell22_902114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_902114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902114 prefixEnd_902114 := by exact prefixLift 902114
  have htrace : WordTrace (prefixWord ++ tailWord_902114) baseStart_902114 baseEnd_902114 := by
    simpa [prefixWord, tailWord_902114, baseEnd_902114] using wordTrace_append hprefix tailTrace_902114
  have hstable : (prefixWord ++ tailWord_902114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902114).length < 2 ^ (prefixWord ++ tailWord_902114).sum := by decide
  have hdescent : baseEnd_902114 < baseStart_902114 := by decide
  rcases family_descends (prefixWord ++ tailWord_902114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902153 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_902153 : Nat := 118140960795 + 902153 * 2 ^ 59
def prefixEnd_902153 : Nat := 4983230072969 + 3 ^ 40 * 902153 * 2
def baseEnd_902153 : Nat := 308825408597142703959053

theorem tailTrace_902153 : CollatzResearch.WordTrace tailWord_902153 prefixEnd_902153 308825408597142703959053 := by
  unfold tailWord_902153
  simp only [CollatzResearch.WordTrace]
  refine ⟨32904223100661231310935113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21936148733774154207290075 32904223100661231310935113)
  ·
    refine ⟨24678167325495923483201335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32904223100661231310935113 24678167325495923483201335)
    ·
      refine ⟨37017250988243885224802003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24678167325495923483201335 37017250988243885224802003)
      ·
        refine ⟨55525876482365827837203005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37017250988243885224802003 55525876482365827837203005)
        ·
          refine ⟨20822203680887185438951127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55525876482365827837203005 20822203680887185438951127)
          ·
            refine ⟨31233305521330778158426691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822203680887185438951127 31233305521330778158426691)
            ·
              refine ⟨46849958281996167237640037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31233305521330778158426691 46849958281996167237640037)
              ·
                refine ⟨8784367177874281357057507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46849958281996167237640037 8784367177874281357057507)
                ·
                  refine ⟨13176550766811422035586261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784367177874281357057507 13176550766811422035586261)
                  ·
                    refine ⟨308825408597142703959053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13176550766811422035586261 308825408597142703959053)
                    ·
                      rfl

theorem cell22_902153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_902153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902153 prefixEnd_902153 := by exact prefixLift 902153
  have htrace : WordTrace (prefixWord ++ tailWord_902153) baseStart_902153 baseEnd_902153 := by
    simpa [prefixWord, tailWord_902153, baseEnd_902153] using wordTrace_append hprefix tailTrace_902153
  have hstable : (prefixWord ++ tailWord_902153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902153).length < 2 ^ (prefixWord ++ tailWord_902153).sum := by decide
  have hdescent : baseEnd_902153 < baseStart_902153 := by decide
  rcases family_descends (prefixWord ++ tailWord_902153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902176 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_902176 : Nat := 118140960795 + 902176 * 2 ^ 59
def prefixEnd_902176 : Nat := 4983230072969 + 3 ^ 40 * 902176 * 2
def baseEnd_902176 : Nat := 308833281967178310633983

theorem tailTrace_902176 : CollatzResearch.WordTrace tailWord_902176 prefixEnd_902176 308833281967178310633983 := by
  unfold tailWord_902176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452530989788953119511191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21936707986385270826014921 16452530989788953119511191)
  ·
    refine ⟨24678796484683429679266787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16452530989788953119511191 24678796484683429679266787)
    ·
      refine ⟨37018194727025144518900181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24678796484683429679266787 37018194727025144518900181)
      ·
        refine ⟨867613938914651824661723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37018194727025144518900181 867613938914651824661723)
        ·
          refine ⟨1301420908371977736992585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867613938914651824661723 1301420908371977736992585)
          ·
            refine ⟨976065681278983302744439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301420908371977736992585 976065681278983302744439)
            ·
              refine ⟨1464098521918474954116659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976065681278983302744439 1464098521918474954116659)
              ·
                refine ⟨2196147782877712431174989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464098521918474954116659 2196147782877712431174989)
                ·
                  refine ⟨823555418579142161690621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2196147782877712431174989 823555418579142161690621)
                  ·
                    refine ⟨308833281967178310633983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823555418579142161690621 308833281967178310633983)
                    ·
                      rfl

theorem cell22_902176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_902176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902176 prefixEnd_902176 := by exact prefixLift 902176
  have htrace : WordTrace (prefixWord ++ tailWord_902176) baseStart_902176 baseEnd_902176 := by
    simpa [prefixWord, tailWord_902176, baseEnd_902176] using wordTrace_append hprefix tailTrace_902176
  have hstable : (prefixWord ++ tailWord_902176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902176).length < 2 ^ (prefixWord ++ tailWord_902176).sum := by decide
  have hdescent : baseEnd_902176 < baseStart_902176 := by decide
  rcases family_descends (prefixWord ++ tailWord_902176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902202 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_902202 : Nat := 118140960795 + 902202 * 2 ^ 59
def prefixEnd_902202 : Nat := 4983230072969 + 3 ^ 40 * 902202 * 2
def baseEnd_902202 : Nat := 308842182298522909483903

theorem tailTrace_902202 : CollatzResearch.WordTrace tailWord_902202 prefixEnd_902202 308842182298522909483903 := by
  unfold tailWord_902202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226502569370928169867215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21937340184989141786312573 8226502569370928169867215)
  ·
    refine ⟨12339753854056392254800823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226502569370928169867215 12339753854056392254800823)
    ·
      refine ⟨18509630781084588382201235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339753854056392254800823 18509630781084588382201235)
      ·
        refine ⟨27764446171626882573301853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18509630781084588382201235 27764446171626882573301853)
        ·
          refine ⟨10411667314360080964988195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27764446171626882573301853 10411667314360080964988195)
          ·
            refine ⟨15617500971540121447482293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411667314360080964988195 15617500971540121447482293)
            ·
              refine ⟨1464140716081886385701465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15617500971540121447482293 1464140716081886385701465)
              ·
                refine ⟨1098105537061414789276099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464140716081886385701465 1098105537061414789276099)
                ·
                  refine ⟨1647158305592122183914149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098105537061414789276099 1647158305592122183914149)
                  ·
                    refine ⟨308842182298522909483903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1647158305592122183914149 308842182298522909483903)
                    ·
                      rfl

theorem cell22_902202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_902202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902202 prefixEnd_902202 := by exact prefixLift 902202
  have htrace : WordTrace (prefixWord ++ tailWord_902202) baseStart_902202 baseEnd_902202 := by
    simpa [prefixWord, tailWord_902202, baseEnd_902202] using wordTrace_append hprefix tailTrace_902202
  have hstable : (prefixWord ++ tailWord_902202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902202).length < 2 ^ (prefixWord ++ tailWord_902202).sum := by decide
  have hdescent : baseEnd_902202 < baseStart_902202 := by decide
  rcases family_descends (prefixWord ++ tailWord_902202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902215 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_902215 : Nat := 118140960795 + 902215 * 2 ^ 59
def prefixEnd_902215 : Nat := 4983230072969 + 3 ^ 40 * 902215 * 2
def baseEnd_902215 : Nat := 308846632464195208908863

theorem tailTrace_902215 : CollatzResearch.WordTrace tailWord_902215 prefixEnd_902215 308846632464195208908863 := by
  unfold tailWord_902215
  simp only [CollatzResearch.WordTrace]
  refine ⟨32906484426436615899692099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21937656284291077266461399 32906484426436615899692099)
  ·
    refine ⟨49359726639654923849538149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32906484426436615899692099 49359726639654923849538149)
    ·
      refine ⟨9254948744935298221788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49359726639654923849538149 9254948744935298221788403)
      ·
        refine ⟨13882423117402947332682605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9254948744935298221788403 13882423117402947332682605)
        ·
          refine ⟨5205908669026105249755977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13882423117402947332682605 5205908669026105249755977)
          ·
            refine ⟨3904431501769578937316983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5205908669026105249755977 3904431501769578937316983)
            ·
              refine ⟨5856647252654368405975475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904431501769578937316983 5856647252654368405975475)
              ·
                refine ⟨8784970878981552608963213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856647252654368405975475 8784970878981552608963213)
                ·
                  refine ⟨3294364079618082228361205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8784970878981552608963213 3294364079618082228361205)
                  ·
                    refine ⟨308846632464195208908863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3294364079618082228361205 308846632464195208908863)
                    ·
                      rfl

theorem cell22_902215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_902215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902215 prefixEnd_902215 := by exact prefixLift 902215
  have htrace : WordTrace (prefixWord ++ tailWord_902215) baseStart_902215 baseEnd_902215 := by
    simpa [prefixWord, tailWord_902215, baseEnd_902215] using wordTrace_append hprefix tailTrace_902215
  have hstable : (prefixWord ++ tailWord_902215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902215).length < 2 ^ (prefixWord ++ tailWord_902215).sum := by decide
  have hdescent : baseEnd_902215 < baseStart_902215 := by decide
  rcases family_descends (prefixWord ++ tailWord_902215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902335 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 8]
def baseStart_902335 : Nat := 118140960795 + 902335 * 2 ^ 59
def prefixEnd_902335 : Nat := 4983230072969 + 3 ^ 40 * 902335 * 2
def baseEnd_902335 : Nat := 102962570305518298636165

theorem tailTrace_902335 : CollatzResearch.WordTrace tailWord_902335 prefixEnd_902335 102962570305518298636165 := by
  unfold tailWord_902335
  simp only [CollatzResearch.WordTrace]
  refine ⟨32910861186001876394060459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21940574124001250929373639 32910861186001876394060459)
  ·
    refine ⟨49366291779002814591090689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32910861186001876394060459 49366291779002814591090689)
    ·
      refine ⟨37024718834252110943318017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49366291779002814591090689 37024718834252110943318017)
      ·
        refine ⟨27768539125689083207488513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37024718834252110943318017 27768539125689083207488513)
        ·
          refine ⟨20826404344266812405616385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27768539125689083207488513 20826404344266812405616385)
          ·
            refine ⟨15619803258200109304212289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20826404344266812405616385 15619803258200109304212289)
            ·
              refine ⟨11714852443650081978159217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15619803258200109304212289 11714852443650081978159217)
              ·
                refine ⟨8786139332737561483619413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11714852443650081978159217 8786139332737561483619413)
                ·
                  refine ⟨102962570305518298636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8786139332737561483619413 102962570305518298636165)
                  ·
                    rfl

theorem cell22_902335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_902335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902335 prefixEnd_902335 := by exact prefixLift 902335
  have htrace : WordTrace (prefixWord ++ tailWord_902335) baseStart_902335 baseEnd_902335 := by
    simpa [prefixWord, tailWord_902335, baseEnd_902335] using wordTrace_append hprefix tailTrace_902335
  have hstable : (prefixWord ++ tailWord_902335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902335).length < 2 ^ (prefixWord ++ tailWord_902335).sum := by decide
  have hdescent : baseEnd_902335 < baseStart_902335 := by decide
  rcases family_descends (prefixWord ++ tailWord_902335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902382 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_902382 : Nat := 118140960795 + 902382 * 2 ^ 59
def prefixEnd_902382 : Nat := 4983230072969 + 3 ^ 40 * 902382 * 2
def baseEnd_902382 : Nat := 308903799977062439983351

theorem tailTrace_902382 : CollatzResearch.WordTrace tailWord_902382 prefixEnd_902382 308903799977062439983351 := by
  unfold tailWord_902382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114071927103950427627675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21941716944554402280680933 4114071927103950427627675)
  ·
    refine ⟨6171107890655925641441513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114071927103950427627675 6171107890655925641441513)
    ·
      refine ⟨4628330917991944231081135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6171107890655925641441513 4628330917991944231081135)
      ·
        refine ⟨6942496376987916346621703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628330917991944231081135 6942496376987916346621703)
        ·
          refine ⟨10413744565481874519932555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942496376987916346621703 10413744565481874519932555)
          ·
            refine ⟨15620616848222811779898833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413744565481874519932555 15620616848222811779898833)
            ·
              refine ⟨11715462636167108834924125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15620616848222811779898833 11715462636167108834924125)
              ·
                refine ⟨4393298488562665813096547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11715462636167108834924125 4393298488562665813096547)
                ·
                  refine ⟨6589947732843998719644821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393298488562665813096547 6589947732843998719644821)
                  ·
                    refine ⟨308903799977062439983351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6589947732843998719644821 308903799977062439983351)
                    ·
                      rfl

theorem cell22_902382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_902382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902382 prefixEnd_902382 := by exact prefixLift 902382
  have htrace : WordTrace (prefixWord ++ tailWord_902382) baseStart_902382 baseEnd_902382 := by
    simpa [prefixWord, tailWord_902382, baseEnd_902382] using wordTrace_append hprefix tailTrace_902382
  have hstable : (prefixWord ++ tailWord_902382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902382).length < 2 ^ (prefixWord ++ tailWord_902382).sum := by decide
  have hdescent : baseEnd_902382 < baseStart_902382 := by decide
  rcases family_descends (prefixWord ++ tailWord_902382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902401 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_902401 : Nat := 118140960795 + 902401 * 2 ^ 59
def prefixEnd_902401 : Nat := 4983230072969 + 3 ^ 40 * 902401 * 2
def baseEnd_902401 : Nat := 308910304065352723758293

theorem tailTrace_902401 : CollatzResearch.WordTrace tailWord_902401 prefixEnd_902401 308910304065352723758293 := by
  unfold tailWord_902401
  simp only [CollatzResearch.WordTrace]
  refine ⟨32913268403762769665963057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21942178935841846443975371 32913268403762769665963057)
  ·
    refine ⟨24684951302822077249472293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32913268403762769665963057 24684951302822077249472293)
    ·
      refine ⟨4628428369279139484276055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24684951302822077249472293 4628428369279139484276055)
      ·
        refine ⟨6942642553918709226414083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628428369279139484276055 6942642553918709226414083)
        ·
          refine ⟨10413963830878063839621125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942642553918709226414083 10413963830878063839621125)
          ·
            refine ⟨1952618218289636969928961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10413963830878063839621125 1952618218289636969928961)
            ·
              refine ⟨1464463663717227727446721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952618218289636969928961 1464463663717227727446721)
              ·
                refine ⟨1098347747787920795585041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464463663717227727446721 1098347747787920795585041)
                ·
                  refine ⟨823760810840940596688781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098347747787920795585041 823760810840940596688781)
                  ·
                    refine ⟨308910304065352723758293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823760810840940596688781 308910304065352723758293)
                    ·
                      rfl

theorem cell22_902401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_902401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902401 prefixEnd_902401 := by exact prefixLift 902401
  have htrace : WordTrace (prefixWord ++ tailWord_902401) baseStart_902401 baseEnd_902401 := by
    simpa [prefixWord, tailWord_902401, baseEnd_902401] using wordTrace_append hprefix tailTrace_902401
  have hstable : (prefixWord ++ tailWord_902401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902401).length < 2 ^ (prefixWord ++ tailWord_902401).sum := by decide
  have hdescent : baseEnd_902401 < baseStart_902401 := by decide
  rcases family_descends (prefixWord ++ tailWord_902401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902414 : List Nat := [4, 1, 1, 2, 1, 5, 1, 7]
def baseStart_902414 : Nat := 118140960795 + 902414 * 2 ^ 59
def prefixEnd_902414 : Nat := 4983230072969 + 3 ^ 40 * 902414 * 2
def baseEnd_902414 : Nat := 34323861581225002575917

theorem tailTrace_902414 : CollatzResearch.WordTrace tailWord_902414 prefixEnd_902414 34323861581225002575917 := by
  unfold tailWord_902414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114217819089459110773287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21942495035143781924124197 4114217819089459110773287)
  ·
    refine ⟨6171326728634188666159931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114217819089459110773287 6171326728634188666159931)
    ·
      refine ⟨9256990092951282999239897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6171326728634188666159931 9256990092951282999239897)
      ·
        refine ⟨6942742569713462249429923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9256990092951282999239897 6942742569713462249429923)
        ·
          refine ⟨10414113854570193374144885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942742569713462249429923 10414113854570193374144885)
          ·
            refine ⟨976323173865955628826083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10414113854570193374144885 976323173865955628826083)
            ·
              refine ⟨1464484760798933443239125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976323173865955628826083 1464484760798933443239125)
              ·
                refine ⟨34323861581225002575917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1464484760798933443239125 34323861581225002575917)
                ·
                  rfl

theorem cell22_902414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_902414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902414 prefixEnd_902414 := by exact prefixLift 902414
  have htrace : WordTrace (prefixWord ++ tailWord_902414) baseStart_902414 baseEnd_902414 := by
    simpa [prefixWord, tailWord_902414, baseEnd_902414] using wordTrace_append hprefix tailTrace_902414
  have hstable : (prefixWord ++ tailWord_902414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902414).length < 2 ^ (prefixWord ++ tailWord_902414).sum := by decide
  have hdescent : baseEnd_902414 < baseStart_902414 := by decide
  rcases family_descends (prefixWord ++ tailWord_902414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902418 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_902418 : Nat := 118140960795 + 902418 * 2 ^ 59
def prefixEnd_902418 : Nat := 4983230072969 + 3 ^ 40 * 902418 * 2
def baseEnd_902418 : Nat := 308916123512770346083241

theorem tailTrace_902418 : CollatzResearch.WordTrace tailWord_902418 prefixEnd_902418 308916123512770346083241 := by
  unfold tailWord_902418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228472111175295392332977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21942592296467454379554605 8228472111175295392332977)
  ·
    refine ⟨6171354083381471544249733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8228472111175295392332977 6171354083381471544249733)
    ·
      refine ⟨1157128890634025914546825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6171354083381471544249733 1157128890634025914546825)
      ·
        refine ⟨867846667975519435910119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157128890634025914546825 867846667975519435910119)
        ·
          refine ⟨1301770001963279153865179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867846667975519435910119 1301770001963279153865179)
          ·
            refine ⟨1952655002944918730797769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301770001963279153865179 1952655002944918730797769)
            ·
              refine ⟨1464491252208689048098327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1952655002944918730797769 1464491252208689048098327)
              ·
                refine ⟨2196736878313033572147491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464491252208689048098327 2196736878313033572147491)
                ·
                  refine ⟨3295105317469550358221237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196736878313033572147491 3295105317469550358221237)
                  ·
                    refine ⟨308916123512770346083241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3295105317469550358221237 308916123512770346083241)
                    ·
                      rfl

theorem cell22_902418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_902418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902418 prefixEnd_902418 := by exact prefixLift 902418
  have htrace : WordTrace (prefixWord ++ tailWord_902418) baseStart_902418 baseEnd_902418 := by
    simpa [prefixWord, tailWord_902418, baseEnd_902418] using wordTrace_append hprefix tailTrace_902418
  have hstable : (prefixWord ++ tailWord_902418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902418).length < 2 ^ (prefixWord ++ tailWord_902418).sum := by decide
  have hdescent : baseEnd_902418 < baseStart_902418 := by decide
  rcases family_descends (prefixWord ++ tailWord_902418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902476 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_902476 : Nat := 118140960795 + 902476 * 2 ^ 59
def prefixEnd_902476 : Nat := 4983230072969 + 3 ^ 40 * 902476 * 2
def baseEnd_902476 : Nat := 102978659366025842711021

theorem tailTrace_902476 : CollatzResearch.WordTrace tailWord_902476 prefixEnd_902476 102978659366025842711021 := by
  unfold tailWord_902476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16458001939245528737471641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21944002585660704983295521 16458001939245528737471641)
  ·
    refine ⟨12343501454434146553103731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16458001939245528737471641 12343501454434146553103731)
    ·
      refine ⟨18515252181651219829655597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12343501454434146553103731 18515252181651219829655597)
      ·
        refine ⟨6943219568119207436120849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18515252181651219829655597 6943219568119207436120849)
        ·
          refine ⟨5207414676089405577090637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943219568119207436120849 5207414676089405577090637)
          ·
            refine ⟨1952780503533527091408989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5207414676089405577090637 1952780503533527091408989)
            ·
              refine ⟨732292688825072659278371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1952780503533527091408989 732292688825072659278371)
              ·
                refine ⟨1098439033237608988917557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732292688825072659278371 1098439033237608988917557)
                ·
                  refine ⟨102978659366025842711021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098439033237608988917557 102978659366025842711021)
                  ·
                    rfl

theorem cell22_902476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_902476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902476 prefixEnd_902476 := by exact prefixLift 902476
  have htrace : WordTrace (prefixWord ++ tailWord_902476) baseStart_902476 baseEnd_902476 := by
    simpa [prefixWord, tailWord_902476, baseEnd_902476] using wordTrace_append hprefix tailTrace_902476
  have hstable : (prefixWord ++ tailWord_902476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902476).length < 2 ^ (prefixWord ++ tailWord_902476).sum := by decide
  have hdescent : baseEnd_902476 < baseStart_902476 := by decide
  rcases family_descends (prefixWord ++ tailWord_902476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902489 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_902489 : Nat := 118140960795 + 902489 * 2 ^ 59
def prefixEnd_902489 : Nat := 4983230072969 + 3 ^ 40 * 902489 * 2
def baseEnd_902489 : Nat := 308940428263749827558023

theorem tailTrace_902489 : CollatzResearch.WordTrace tailWord_902489 prefixEnd_902489 308940428263749827558023 := by
  unfold tailWord_902489
  simp only [CollatzResearch.WordTrace]
  refine ⟨32916478027443960695166521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21944318684962640463444347 32916478027443960695166521)
  ·
    refine ⟨24687358520582970521374891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32916478027443960695166521 24687358520582970521374891)
    ·
      refine ⟨37031037780874455782062337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24687358520582970521374891 37031037780874455782062337)
      ·
        refine ⟨27773278335655841836546753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37031037780874455782062337 27773278335655841836546753)
        ·
          refine ⟨20829958751741881377410065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27773278335655841836546753 20829958751741881377410065)
          ·
            refine ⟨15622469063806411033057549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20829958751741881377410065 15622469063806411033057549)
            ·
              refine ⟨5858425898927404137396581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15622469063806411033057549 5858425898927404137396581)
              ·
                refine ⟨1098454856048888275761859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5858425898927404137396581 1098454856048888275761859)
                ·
                  refine ⟨1647682284073332413642789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1098454856048888275761859 1647682284073332413642789)
                  ·
                    refine ⟨308940428263749827558023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1647682284073332413642789 308940428263749827558023)
                    ·
                      rfl

theorem cell22_902489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_902489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902489 prefixEnd_902489 := by exact prefixLift 902489
  have htrace : WordTrace (prefixWord ++ tailWord_902489) baseStart_902489 baseEnd_902489 := by
    simpa [prefixWord, tailWord_902489, baseEnd_902489] using wordTrace_append hprefix tailTrace_902489
  have hstable : (prefixWord ++ tailWord_902489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902489).length < 2 ^ (prefixWord ++ tailWord_902489).sum := by decide
  have hdescent : baseEnd_902489 < baseStart_902489 := by decide
  rcases family_descends (prefixWord ++ tailWord_902489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902519 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 4, 3]
def baseStart_902519 : Nat := 118140960795 + 902519 * 2 ^ 59
def prefixEnd_902519 : Nat := 4983230072969 + 3 ^ 40 * 902519 * 2
def baseEnd_902519 : Nat := 308950697876839749307931

theorem tailTrace_902519 : CollatzResearch.WordTrace tailWord_902519 prefixEnd_902519 308950697876839749307931 := by
  unfold tailWord_902519
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917572217335275818758611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21945048144890183879172407 32917572217335275818758611)
  ·
    refine ⟨49376358326002913728137917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32917572217335275818758611 49376358326002913728137917)
    ·
      refine ⟨18516134372251092648051719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49376358326002913728137917 18516134372251092648051719)
      ·
        refine ⟨27774201558376638972077579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18516134372251092648051719 27774201558376638972077579)
        ·
          refine ⟨41661302337564958458116369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27774201558376638972077579 41661302337564958458116369)
          ·
            refine ⟨31245976753173718843587277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41661302337564958458116369 31245976753173718843587277)
            ·
              refine ⟨11717241282440144566345229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31245976753173718843587277 11717241282440144566345229)
              ·
                refine ⟨4393965480915054212379461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11717241282440144566345229 4393965480915054212379461)
                ·
                  refine ⟨823868527671572664821149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4393965480915054212379461 823868527671572664821149)
                  ·
                    refine ⟨308950697876839749307931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 823868527671572664821149 308950697876839749307931)
                    ·
                      rfl

theorem cell22_902519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_902519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902519 prefixEnd_902519 := by exact prefixLift 902519
  have htrace : WordTrace (prefixWord ++ tailWord_902519) baseStart_902519 baseEnd_902519 := by
    simpa [prefixWord, tailWord_902519, baseEnd_902519] using wordTrace_append hprefix tailTrace_902519
  have hstable : (prefixWord ++ tailWord_902519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902519).length < 2 ^ (prefixWord ++ tailWord_902519).sum := by decide
  have hdescent : baseEnd_902519 < baseStart_902519 := by decide
  rcases family_descends (prefixWord ++ tailWord_902519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902624 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_902624 : Nat := 118140960795 + 902624 * 2 ^ 59
def prefixEnd_902624 : Nat := 4983230072969 + 3 ^ 40 * 902624 * 2
def baseEnd_902624 : Nat := 308986641522654475432609

theorem tailTrace_902624 : CollatzResearch.WordTrace tailWord_902624 prefixEnd_902624 308986641522654475432609 := by
  unfold tailWord_902624
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460700940977439375665463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21947601254636585834220617 16460700940977439375665463)
  ·
    refine ⟨24691051411466159063498195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16460700940977439375665463 24691051411466159063498195)
    ·
      refine ⟨37036577117199238595247293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24691051411466159063498195 37036577117199238595247293)
      ·
        refine ⟨13888716418949714473217735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37036577117199238595247293 13888716418949714473217735)
        ·
          refine ⟨20833074628424571709826603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13888716418949714473217735 20833074628424571709826603)
          ·
            refine ⟨31249611942636857564739905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20833074628424571709826603 31249611942636857564739905)
            ·
              refine ⟨23437208956977643173554929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31249611942636857564739905 23437208956977643173554929)
              ·
                refine ⟨17577906717733232380166197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23437208956977643173554929 17577906717733232380166197)
                ·
                  refine ⟨1647928754787490535640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17577906717733232380166197 1647928754787490535640581)
                  ·
                    refine ⟨308986641522654475432609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1647928754787490535640581 308986641522654475432609)
                    ·
                      rfl

theorem cell22_902624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_902624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902624 prefixEnd_902624 := by exact prefixLift 902624
  have htrace : WordTrace (prefixWord ++ tailWord_902624) baseStart_902624 baseEnd_902624 := by
    simpa [prefixWord, tailWord_902624, baseEnd_902624] using wordTrace_append hprefix tailTrace_902624
  have hstable : (prefixWord ++ tailWord_902624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902624).length < 2 ^ (prefixWord ++ tailWord_902624).sum := by decide
  have hdescent : baseEnd_902624 < baseStart_902624 := by decide
  rcases family_descends (prefixWord ++ tailWord_902624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902639 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 6]
def baseStart_902639 : Nat := 118140960795 + 902639 * 2 ^ 59
def prefixEnd_902639 : Nat := 4983230072969 + 3 ^ 40 * 902639 * 2
def baseEnd_902639 : Nat := 102997258776399812102521

theorem tailTrace_902639 : CollatzResearch.WordTrace tailWord_902639 prefixEnd_902639 102997258776399812102521 := by
  unfold tailWord_902639
  simp only [CollatzResearch.WordTrace]
  refine ⟨32921948976900536313126971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21947965984600357542084647 32921948976900536313126971)
  ·
    refine ⟨49382923465350804469690457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32921948976900536313126971 49382923465350804469690457)
    ·
      refine ⟨37037192599013103352267843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49382923465350804469690457 37037192599013103352267843)
      ·
        refine ⟨55555788898519655028401765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37037192599013103352267843 55555788898519655028401765)
        ·
          refine ⟨10416710418472435317825331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55555788898519655028401765 10416710418472435317825331)
          ·
            refine ⟨15625065627708652976737997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416710418472435317825331 15625065627708652976737997)
            ·
              refine ⟨5859399610390744866276749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15625065627708652976737997 5859399610390744866276749)
              ·
                refine ⟨2197274853896529324853781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5859399610390744866276749 2197274853896529324853781)
                ·
                  refine ⟨102997258776399812102521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2197274853896529324853781 102997258776399812102521)
                  ·
                    rfl

theorem cell22_902639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_902639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902639 prefixEnd_902639 := by exact prefixLift 902639
  have htrace : WordTrace (prefixWord ++ tailWord_902639) baseStart_902639 baseEnd_902639 := by
    simpa [prefixWord, tailWord_902639, baseEnd_902639] using wordTrace_append hprefix tailTrace_902639
  have hstable : (prefixWord ++ tailWord_902639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902639).length < 2 ^ (prefixWord ++ tailWord_902639).sum := by decide
  have hdescent : baseEnd_902639 < baseStart_902639 := by decide
  rcases family_descends (prefixWord ++ tailWord_902639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902645 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 5]
def baseStart_902645 : Nat := 118140960795 + 902645 * 2 ^ 59
def prefixEnd_902645 : Nat := 4983230072969 + 3 ^ 40 * 902645 * 2
def baseEnd_902645 : Nat := 102997943417272473552515

theorem tailTrace_902645 : CollatzResearch.WordTrace tailWord_902645 prefixEnd_902645 102997943417272473552515 := by
  unfold tailWord_902645
  simp only [CollatzResearch.WordTrace]
  refine ⟨32922167814878799337845389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21948111876585866225230259 32922167814878799337845389)
  ·
    refine ⟨12345812930579549751692021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32922167814878799337845389 12345812930579549751692021)
    ·
      refine ⟨1157419962241832789221127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12345812930579549751692021 1157419962241832789221127)
      ·
        refine ⟨1736129943362749183831691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157419962241832789221127 1736129943362749183831691)
        ·
          refine ⟨2604194915044123775747537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736129943362749183831691 2604194915044123775747537)
          ·
            refine ⟨1953146186283092831810653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604194915044123775747537 1953146186283092831810653)
            ·
              refine ⟨732429819856159811928995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953146186283092831810653 732429819856159811928995)
              ·
                refine ⟨1098644729784239717893493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732429819856159811928995 1098644729784239717893493)
                ·
                  refine ⟨102997943417272473552515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098644729784239717893493 102997943417272473552515)
                  ·
                    rfl

theorem cell22_902645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_902645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902645 prefixEnd_902645 := by exact prefixLift 902645
  have htrace : WordTrace (prefixWord ++ tailWord_902645) baseStart_902645 baseEnd_902645 := by
    simpa [prefixWord, tailWord_902645, baseEnd_902645] using wordTrace_append hprefix tailTrace_902645
  have hstable : (prefixWord ++ tailWord_902645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902645).length < 2 ^ (prefixWord ++ tailWord_902645).sum := by decide
  have hdescent : baseEnd_902645 < baseStart_902645 := by decide
  rcases family_descends (prefixWord ++ tailWord_902645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902688 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_902688 : Nat := 118140960795 + 902688 * 2 ^ 59
def prefixEnd_902688 : Nat := 4983230072969 + 3 ^ 40 * 902688 * 2
def baseEnd_902688 : Nat := 309008550030579641832413

theorem tailTrace_902688 : CollatzResearch.WordTrace tailWord_902688 prefixEnd_902688 309008550030579641832413 := by
  unfold tailWord_902688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16461868076861508840830359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21949157435815345121107145 16461868076861508840830359)
  ·
    refine ⟨24692802115292263261245539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16461868076861508840830359 24692802115292263261245539)
    ·
      refine ⟨37039203172938394891868309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24692802115292263261245539 37039203172938394891868309)
      ·
        refine ⟨1736212648731487260556327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37039203172938394891868309 1736212648731487260556327)
        ·
          refine ⟨2604318973097230890834491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736212648731487260556327 2604318973097230890834491)
          ·
            refine ⟨3906478459645846336251737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604318973097230890834491 3906478459645846336251737)
            ·
              refine ⟨2929858844734384752188803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906478459645846336251737 2929858844734384752188803)
              ·
                refine ⟨4394788267101577128283205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929858844734384752188803 4394788267101577128283205)
                ·
                  refine ⟨824022800081545711553101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4394788267101577128283205 824022800081545711553101)
                  ·
                    refine ⟨309008550030579641832413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 824022800081545711553101 309008550030579641832413)
                    ·
                      rfl

theorem cell22_902688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_902688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902688 prefixEnd_902688 := by exact prefixLift 902688
  have htrace : WordTrace (prefixWord ++ tailWord_902688) baseStart_902688 baseEnd_902688 := by
    simpa [prefixWord, tailWord_902688, baseEnd_902688] using wordTrace_append hprefix tailTrace_902688
  have hstable : (prefixWord ++ tailWord_902688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902688).length < 2 ^ (prefixWord ++ tailWord_902688).sum := by decide
  have hdescent : baseEnd_902688 < baseStart_902688 := by decide
  rcases family_descends (prefixWord ++ tailWord_902688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902729 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 9]
def baseStart_902729 : Nat := 118140960795 + 902729 * 2 ^ 59
def prefixEnd_902729 : Nat := 4983230072969 + 3 ^ 40 * 902729 * 2
def baseEnd_902729 : Nat := 103007528389489733852429

theorem tailTrace_902729 : CollatzResearch.WordTrace tailWord_902729 prefixEnd_902729 103007528389489733852429 := by
  unfold tailWord_902729
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925231546574481683903241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21950154364382987789268827 32925231546574481683903241)
  ·
    refine ⟨24693923659930861262927431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32925231546574481683903241 24693923659930861262927431)
    ·
      refine ⟨37040885489896291894391147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24693923659930861262927431 37040885489896291894391147)
      ·
        refine ⟨55561328234844437841586721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37040885489896291894391147 55561328234844437841586721)
        ·
          refine ⟨41670996176133328381190041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55561328234844437841586721 41670996176133328381190041)
          ·
            refine ⟨31253247132099996285892531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41670996176133328381190041 31253247132099996285892531)
            ·
              refine ⟨46879870698149994428838797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31253247132099996285892531 46879870698149994428838797)
              ·
                refine ⟨17579951511806247910814549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46879870698149994428838797 17579951511806247910814549)
                ·
                  refine ⟨103007528389489733852429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17579951511806247910814549 103007528389489733852429)
                  ·
                    rfl

theorem cell22_902729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_902729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902729 prefixEnd_902729 := by exact prefixLift 902729
  have htrace : WordTrace (prefixWord ++ tailWord_902729) baseStart_902729 baseEnd_902729 := by
    simpa [prefixWord, tailWord_902729, baseEnd_902729] using wordTrace_append hprefix tailTrace_902729
  have hstable : (prefixWord ++ tailWord_902729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902729).length < 2 ^ (prefixWord ++ tailWord_902729).sum := by decide
  have hdescent : baseEnd_902729 < baseStart_902729 := by decide
  rcases family_descends (prefixWord ++ tailWord_902729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902808 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_902808 : Nat := 118140960795 + 902808 * 2 ^ 59
def prefixEnd_902808 : Nat := 4983230072969 + 3 ^ 40 * 902808 * 2
def baseEnd_902808 : Nat := 103016542827646442944015

theorem tailTrace_902808 : CollatzResearch.WordTrace tailWord_902808 prefixEnd_902808 103016542827646442944015 := by
  unfold tailWord_902808
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464056456644139088014539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21952075275525518784019385 16464056456644139088014539)
  ·
    refine ⟨24696084684966208632021809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464056456644139088014539 24696084684966208632021809)
    ·
      refine ⟨18522063513724656474016357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24696084684966208632021809 18522063513724656474016357)
      ·
        refine ⟨3472886908823373088878067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18522063513724656474016357 3472886908823373088878067)
        ·
          refine ⟨5209330363235059633317101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472886908823373088878067 5209330363235059633317101)
          ·
            refine ⟨1953498886213147362493913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5209330363235059633317101 1953498886213147362493913)
            ·
              refine ⟨1465124164659860521870435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953498886213147362493913 1465124164659860521870435)
              ·
                refine ⟨2197686246989790782805653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465124164659860521870435 2197686246989790782805653)
                ·
                  refine ⟨103016542827646442944015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2197686246989790782805653 103016542827646442944015)
                  ·
                    rfl

theorem cell22_902808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_902808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902808 prefixEnd_902808 := by exact prefixLift 902808
  have htrace : WordTrace (prefixWord ++ tailWord_902808) baseStart_902808 baseEnd_902808 := by
    simpa [prefixWord, tailWord_902808, baseEnd_902808] using wordTrace_append hprefix tailTrace_902808
  have hstable : (prefixWord ++ tailWord_902808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902808).length < 2 ^ (prefixWord ++ tailWord_902808).sum := by decide
  have hdescent : baseEnd_902808 < baseStart_902808 := by decide
  rcases family_descends (prefixWord ++ tailWord_902808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902821 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_902821 : Nat := 118140960795 + 902821 * 2 ^ 59
def prefixEnd_902821 : Nat := 4983230072969 + 3 ^ 40 * 902821 * 2
def baseEnd_902821 : Nat := 309054078648611628257005

theorem tailTrace_902821 : CollatzResearch.WordTrace tailWord_902821 prefixEnd_902821 309054078648611628257005 := by
  unfold tailWord_902821
  simp only [CollatzResearch.WordTrace]
  refine ⟨32928587062241181396252317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21952391374827454264168211 32928587062241181396252317)
  ·
    refine ⟨12348220148340443023594619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32928587062241181396252317 12348220148340443023594619)
    ·
      refine ⟨18522330222510664535391929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348220148340443023594619 18522330222510664535391929)
      ·
        refine ⟨13891747666882998401543947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18522330222510664535391929 13891747666882998401543947)
        ·
          refine ⟨20837621500324497602315921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891747666882998401543947 20837621500324497602315921)
          ·
            refine ⟨15628216125243373201736941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20837621500324497602315921 15628216125243373201736941)
            ·
              refine ⟨5860581046966264950651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15628216125243373201736941 5860581046966264950651353)
              ·
                refine ⟨4395435785224698712988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860581046966264950651353 4395435785224698712988515)
                ·
                  refine ⟨6593153677837048069482773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395435785224698712988515 6593153677837048069482773)
                  ·
                    refine ⟨309054078648611628257005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6593153677837048069482773 309054078648611628257005)
                    ·
                      rfl

theorem cell22_902821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_902821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902821 prefixEnd_902821 := by exact prefixLift 902821
  have htrace : WordTrace (prefixWord ++ tailWord_902821) baseStart_902821 baseEnd_902821 := by
    simpa [prefixWord, tailWord_902821, baseEnd_902821] using wordTrace_append hprefix tailTrace_902821
  have hstable : (prefixWord ++ tailWord_902821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902821).length < 2 ^ (prefixWord ++ tailWord_902821).sum := by decide
  have hdescent : baseEnd_902821 < baseStart_902821 := by decide
  rcases family_descends (prefixWord ++ tailWord_902821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902896 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_902896 : Nat := 118140960795 + 902896 * 2 ^ 59
def prefixEnd_902896 : Nat := 4983230072969 + 3 ^ 40 * 902896 * 2
def baseEnd_902896 : Nat := 309079752681336432631775

theorem tailTrace_902896 : CollatzResearch.WordTrace tailWord_902896 prefixEnd_902896 309079752681336432631775 := by
  unfold tailWord_902896
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465661268484734602616271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21954215024646312803488361 16465661268484734602616271)
  ·
    refine ⟨24698491902727101903924407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16465661268484734602616271 24698491902727101903924407)
    ·
      refine ⟨37047737854090652855886611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24698491902727101903924407 37047737854090652855886611)
      ·
        refine ⟨55571606781135979283829917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37047737854090652855886611 55571606781135979283829917)
        ·
          refine ⟨20839352542925992231436219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55571606781135979283829917 20839352542925992231436219)
          ·
            refine ⟨31259028814388988347154329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20839352542925992231436219 31259028814388988347154329)
            ·
              refine ⟨23444271610791741260365747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31259028814388988347154329 23444271610791741260365747)
              ·
                refine ⟨35166407416187611890548621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23444271610791741260365747 35166407416187611890548621)
                ·
                  refine ⟨13187402781070354458955733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35166407416187611890548621 13187402781070354458955733)
                  ·
                    refine ⟨309079752681336432631775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13187402781070354458955733 309079752681336432631775)
                    ·
                      rfl

theorem cell22_902896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_902896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902896 prefixEnd_902896 := by exact prefixLift 902896
  have htrace : WordTrace (prefixWord ++ tailWord_902896) baseStart_902896 baseEnd_902896 := by
    simpa [prefixWord, tailWord_902896, baseEnd_902896] using wordTrace_append hprefix tailTrace_902896
  have hstable : (prefixWord ++ tailWord_902896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902896).length < 2 ^ (prefixWord ++ tailWord_902896).sum := by decide
  have hdescent : baseEnd_902896 < baseStart_902896 := by decide
  rcases family_descends (prefixWord ++ tailWord_902896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902919 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 1, 3]
def baseStart_902919 : Nat := 118140960795 + 902919 * 2 ^ 59
def prefixEnd_902919 : Nat := 4983230072969 + 3 ^ 40 * 902919 * 2
def baseEnd_902919 : Nat := 309087626051372039306705

theorem tailTrace_902919 : CollatzResearch.WordTrace tailWord_902919 prefixEnd_902919 309087626051372039306705 := by
  unfold tailWord_902919
  simp only [CollatzResearch.WordTrace]
  refine ⟨32932161415886144133319811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21954774277257429422213207 32932161415886144133319811)
  ·
    refine ⟨49398242123829216199979717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32932161415886144133319811 49398242123829216199979717)
    ·
      refine ⟨9262170398217978037496197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49398242123829216199979717 9262170398217978037496197)
      ·
        refine ⟨1736656949665870882030537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9262170398217978037496197 1736656949665870882030537)
        ·
          refine ⟨1302492712249403161522903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1736656949665870882030537 1302492712249403161522903)
          ·
            refine ⟨1953739068374104742284355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302492712249403161522903 1953739068374104742284355)
            ·
              refine ⟨2930608602561157113426533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953739068374104742284355 2930608602561157113426533)
              ·
                refine ⟨549489112980216958767475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2930608602561157113426533 549489112980216958767475)
                ·
                  refine ⟨824233669470325438151213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549489112980216958767475 824233669470325438151213)
                  ·
                    refine ⟨309087626051372039306705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 824233669470325438151213 309087626051372039306705)
                    ·
                      rfl

theorem cell22_902919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_902919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902919 prefixEnd_902919 := by exact prefixLift 902919
  have htrace : WordTrace (prefixWord ++ tailWord_902919) baseStart_902919 baseEnd_902919 := by
    simpa [prefixWord, tailWord_902919, baseEnd_902919] using wordTrace_append hprefix tailTrace_902919
  have hstable : (prefixWord ++ tailWord_902919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902919).length < 2 ^ (prefixWord ++ tailWord_902919).sum := by decide
  have hdescent : baseEnd_902919 < baseStart_902919 := by decide
  rcases family_descends (prefixWord ++ tailWord_902919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902930 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_902930 : Nat := 118140960795 + 902930 * 2 ^ 59
def prefixEnd_902930 : Nat := 4983230072969 + 3 ^ 40 * 902930 * 2
def baseEnd_902930 : Nat := 309091391576171677281671

theorem tailTrace_902930 : CollatzResearch.WordTrace tailWord_902930 prefixEnd_902930 309091391576171677281671 := by
  unfold tailWord_902930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8233140654711573252992561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21955041745897528674646829 8233140654711573252992561)
  ·
    refine ⟨6174855491033679939744421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8233140654711573252992561 6174855491033679939744421)
    ·
      refine ⟨1157785404568814988702079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6174855491033679939744421 1157785404568814988702079)
      ·
        refine ⟨1736678106853222483053119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157785404568814988702079 1736678106853222483053119)
        ·
          refine ⟨2605017160279833724579679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736678106853222483053119 2605017160279833724579679)
          ·
            refine ⟨3907525740419750586869519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605017160279833724579679 3907525740419750586869519)
            ·
              refine ⟨5861288610629625880304279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907525740419750586869519 5861288610629625880304279)
              ·
                refine ⟨8791932915944438820456419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861288610629625880304279 8791932915944438820456419)
                ·
                  refine ⟨13187899373916658230684629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791932915944438820456419 13187899373916658230684629)
                  ·
                    refine ⟨309091391576171677281671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13187899373916658230684629 309091391576171677281671)
                    ·
                      rfl

theorem cell22_902930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_902930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902930 prefixEnd_902930 := by exact prefixLift 902930
  have htrace : WordTrace (prefixWord ++ tailWord_902930) baseStart_902930 baseEnd_902930 := by
    simpa [prefixWord, tailWord_902930, baseEnd_902930] using wordTrace_append hprefix tailTrace_902930
  have hstable : (prefixWord ++ tailWord_902930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902930).length < 2 ^ (prefixWord ++ tailWord_902930).sum := by decide
  have hdescent : baseEnd_902930 < baseStart_902930 := by decide
  rcases family_descends (prefixWord ++ tailWord_902930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902943 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 6]
def baseStart_902943 : Nat := 118140960795 + 902943 * 2 ^ 59
def prefixEnd_902943 : Nat := 4983230072969 + 3 ^ 40 * 902943 * 2
def baseEnd_902943 : Nat := 103031947247281325568877

theorem tailTrace_902943 : CollatzResearch.WordTrace tailWord_902943 prefixEnd_902943 103031947247281325568877 := by
  unfold tailWord_902943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32933036767799196232193483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21955357845199464154795655 32933036767799196232193483)
  ·
    refine ⟨49399555151698794348290225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32933036767799196232193483 49399555151698794348290225)
    ·
      refine ⟨37049666363774095761217669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49399555151698794348290225 37049666363774095761217669)
      ·
        refine ⟨6946812443207642955228313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37049666363774095761217669 6946812443207642955228313)
        ·
          refine ⟨5210109332405732216421235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6946812443207642955228313 5210109332405732216421235)
          ·
            refine ⟨7815163998608598324631853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210109332405732216421235 7815163998608598324631853)
            ·
              refine ⟨2930686499478224371736945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7815163998608598324631853 2930686499478224371736945)
              ·
                refine ⟨2198014874608668278802709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930686499478224371736945 2198014874608668278802709)
                ·
                  refine ⟨103031947247281325568877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2198014874608668278802709 103031947247281325568877)
                  ·
                    rfl

theorem cell22_902943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_902943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902943 prefixEnd_902943 := by exact prefixLift 902943
  have htrace : WordTrace (prefixWord ++ tailWord_902943) baseStart_902943 baseEnd_902943 := by
    simpa [prefixWord, tailWord_902943, baseEnd_902943] using wordTrace_append hprefix tailTrace_902943
  have hstable : (prefixWord ++ tailWord_902943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902943).length < 2 ^ (prefixWord ++ tailWord_902943).sum := by decide
  have hdescent : baseEnd_902943 < baseStart_902943 := by decide
  rcases family_descends (prefixWord ++ tailWord_902943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902962 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_902962 : Nat := 118140960795 + 902962 * 2 ^ 59
def prefixEnd_902962 : Nat := 4983230072969 + 3 ^ 40 * 902962 * 2
def baseEnd_902962 : Nat := 309102345830134260481573

theorem tailTrace_902962 : CollatzResearch.WordTrace tailWord_902962 prefixEnd_902962 309102345830134260481573 := by
  unfold tailWord_902962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8233432438682590619283785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21955819836486908318090093 8233432438682590619283785)
  ·
    refine ⟨6175074329011942964462839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8233432438682590619283785 6175074329011942964462839)
    ·
      refine ⟨9262611493517914446694259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175074329011942964462839 9262611493517914446694259)
      ·
        refine ⟨13893917240276871670041389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262611493517914446694259 13893917240276871670041389)
        ·
          refine ⟨5210218965103826876265521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13893917240276871670041389 5210218965103826876265521)
          ·
            refine ⟨3907664223827870157199141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5210218965103826876265521 3907664223827870157199141)
            ·
              refine ⟨732687041967725654474839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3907664223827870157199141 732687041967725654474839)
              ·
                refine ⟨1099030562951588481712259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732687041967725654474839 1099030562951588481712259)
                ·
                  refine ⟨1648545844427382722568389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099030562951588481712259 1648545844427382722568389)
                  ·
                    refine ⟨309102345830134260481573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1648545844427382722568389 309102345830134260481573)
                    ·
                      rfl

theorem cell22_902962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_902962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_902962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_902962 prefixEnd_902962 := by exact prefixLift 902962
  have htrace : WordTrace (prefixWord ++ tailWord_902962) baseStart_902962 baseEnd_902962 := by
    simpa [prefixWord, tailWord_902962, baseEnd_902962] using wordTrace_append hprefix tailTrace_902962
  have hstable : (prefixWord ++ tailWord_902962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902962).length < 2 ^ (prefixWord ++ tailWord_902962).sum := by decide
  have hdescent : baseEnd_902962 < baseStart_902962 := by decide
  rcases family_descends (prefixWord ++ tailWord_902962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903033 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 7]
def baseStart_903033 : Nat := 118140960795 + 903033 * 2 ^ 59
def prefixEnd_903033 : Nat := 4983230072969 + 3 ^ 40 * 903033 * 2
def baseEnd_903033 : Nat := 103042216860371247318785

theorem tailTrace_903033 : CollatzResearch.WordTrace tailWord_903033 prefixEnd_903033 103042216860371247318785 := by
  unfold tailWord_903033
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936319337473141602969753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21957546224982094401979835 32936319337473141602969753)
  ·
    refine ⟨24702239503104856202227315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32936319337473141602969753 24702239503104856202227315)
    ·
      refine ⟨37053359254657284303340973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24702239503104856202227315 37053359254657284303340973)
      ·
        refine ⟨13895009720496481613752865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37053359254657284303340973 13895009720496481613752865)
        ·
          refine ⟨10421257290372361210314649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13895009720496481613752865 10421257290372361210314649)
          ·
            refine ⟨7815942967779270907735987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10421257290372361210314649 7815942967779270907735987)
            ·
              refine ⟨11723914451668906361603981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815942967779270907735987 11723914451668906361603981)
              ·
                refine ⟨4396467919375839885601493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11723914451668906361603981 4396467919375839885601493)
                ·
                  refine ⟨103042216860371247318785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4396467919375839885601493 103042216860371247318785)
                  ·
                    rfl

theorem cell22_903033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_903033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903033 prefixEnd_903033 := by exact prefixLift 903033
  have htrace : WordTrace (prefixWord ++ tailWord_903033) baseStart_903033 baseEnd_903033 := by
    simpa [prefixWord, tailWord_903033, baseEnd_903033] using wordTrace_append hprefix tailTrace_903033
  have hstable : (prefixWord ++ tailWord_903033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903033).length < 2 ^ (prefixWord ++ tailWord_903033).sum := by decide
  have hdescent : baseEnd_903033 < baseStart_903033 := by decide
  rcases family_descends (prefixWord ++ tailWord_903033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903129 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 4]
def baseStart_903129 : Nat := 118140960795 + 903129 * 2 ^ 59
def prefixEnd_903129 : Nat := 4983230072969 + 3 ^ 40 * 903129 * 2
def baseEnd_903129 : Nat := 103053171114333830518687

theorem tailTrace_903129 : CollatzResearch.WordTrace tailWord_903129 prefixEnd_903129 103053171114333830518687 := by
  unfold tailWord_903129
  simp only [CollatzResearch.WordTrace]
  refine ⟨32939820745125349998464441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21959880496750233332309627 32939820745125349998464441)
  ·
    refine ⟨24704865558844012498848331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32939820745125349998464441 24704865558844012498848331)
    ·
      refine ⟨37057298338266018748272497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24704865558844012498848331 37057298338266018748272497)
      ·
        refine ⟨27792973753699514061204373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37057298338266018748272497 27792973753699514061204373)
        ·
          refine ⟨1302795644704664721618955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27792973753699514061204373 1302795644704664721618955)
          ·
            refine ⟨1954193467056997082428433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302795644704664721618955 1954193467056997082428433)
            ·
              refine ⟨1465645100292747811821325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954193467056997082428433 1465645100292747811821325)
              ·
                refine ⟨549616912609780429432997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1465645100292747811821325 549616912609780429432997)
                ·
                  refine ⟨103053171114333830518687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549616912609780429432997 103053171114333830518687)
                  ·
                    rfl

theorem cell22_903129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_903129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903129 prefixEnd_903129 := by exact prefixLift 903129
  have htrace : WordTrace (prefixWord ++ tailWord_903129) baseStart_903129 baseEnd_903129 := by
    simpa [prefixWord, tailWord_903129, baseEnd_903129] using wordTrace_append hprefix tailTrace_903129
  have hstable : (prefixWord ++ tailWord_903129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903129).length < 2 ^ (prefixWord ++ tailWord_903129).sum := by decide
  have hdescent : baseEnd_903129 < baseStart_903129 := by decide
  rcases family_descends (prefixWord ++ tailWord_903129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903202 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_903202 : Nat := 118140960795 + 903202 * 2 ^ 59
def prefixEnd_903202 : Nat := 4983230072969 + 3 ^ 40 * 903202 * 2
def baseEnd_903202 : Nat := 103061500911617878160279

theorem tailTrace_903202 : CollatzResearch.WordTrace tailWord_903202 prefixEnd_903202 103061500911617878160279 := by
  unfold tailWord_903202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8235620818465220866467965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21961655515907255643914573 8235620818465220866467965)
  ·
    refine ⟨3088357806924457824925487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8235620818465220866467965 3088357806924457824925487)
    ·
      refine ⟨4632536710386686737388231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088357806924457824925487 4632536710386686737388231)
      ·
        refine ⟨6948805065580030106082347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632536710386686737388231 6948805065580030106082347)
        ·
          refine ⟨10423207598370045159123521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6948805065580030106082347 10423207598370045159123521)
          ·
            refine ⟨7817405698777533869342641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10423207598370045159123521 7817405698777533869342641)
            ·
              refine ⟨5863054274083150402006981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817405698777533869342641 5863054274083150402006981)
              ·
                refine ⟨1099322676390590700376309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5863054274083150402006981 1099322676390590700376309)
                ·
                  refine ⟨103061500911617878160279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099322676390590700376309 103061500911617878160279)
                  ·
                    rfl

theorem cell22_903202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_903202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903202 prefixEnd_903202 := by exact prefixLift 903202
  have htrace : WordTrace (prefixWord ++ tailWord_903202) baseStart_903202 baseEnd_903202 := by
    simpa [prefixWord, tailWord_903202, baseEnd_903202] using wordTrace_append hprefix tailTrace_903202
  have hstable : (prefixWord ++ tailWord_903202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903202).length < 2 ^ (prefixWord ++ tailWord_903202).sum := by decide
  have hdescent : baseEnd_903202 < baseStart_903202 := by decide
  rcases family_descends (prefixWord ++ tailWord_903202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903232 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_903232 : Nat := 118140960795 + 903232 * 2 ^ 59
def prefixEnd_903232 : Nat := 4983230072969 + 3 ^ 40 * 903232 * 2
def baseEnd_903232 : Nat := 309194772347943556230745

theorem tailTrace_903232 : CollatzResearch.WordTrace tailWord_903232 prefixEnd_903232 309194772347943556230745 := by
  unfold tailWord_903232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471788731876099294731975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21962384975834799059642633 16471788731876099294731975)
  ·
    refine ⟨24707683097814148942097963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16471788731876099294731975 24707683097814148942097963)
    ·
      refine ⟨37061524646721223413146945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24707683097814148942097963 37061524646721223413146945)
      ·
        refine ⟨27796143485040917559860209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37061524646721223413146945 27796143485040917559860209)
        ·
          refine ⟨20847107613780688169895157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27796143485040917559860209 20847107613780688169895157)
          ·
            refine ⟨1954416338791939515927671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20847107613780688169895157 1954416338791939515927671)
            ·
              refine ⟨2931624508187909273891507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954416338791939515927671 2931624508187909273891507)
              ·
                refine ⟨4397436762281863910837261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931624508187909273891507 4397436762281863910837261)
                ·
                  refine ⟨1649038785855698966563973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4397436762281863910837261 1649038785855698966563973)
                  ·
                    refine ⟨309194772347943556230745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1649038785855698966563973 309194772347943556230745)
                    ·
                      rfl

theorem cell22_903232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_903232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903232 prefixEnd_903232 := by exact prefixLift 903232
  have htrace : WordTrace (prefixWord ++ tailWord_903232) baseStart_903232 baseEnd_903232 := by
    simpa [prefixWord, tailWord_903232, baseEnd_903232] using wordTrace_append hprefix tailTrace_903232
  have hstable : (prefixWord ++ tailWord_903232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903232).length < 2 ^ (prefixWord ++ tailWord_903232).sum := by decide
  have hdescent : baseEnd_903232 < baseStart_903232 := by decide
  rcases family_descends (prefixWord ++ tailWord_903232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903264 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_903264 : Nat := 118140960795 + 903264 * 2 ^ 59
def prefixEnd_903264 : Nat := 4983230072969 + 3 ^ 40 * 903264 * 2
def baseEnd_903264 : Nat := 103068575533968713143549

theorem tailTrace_903264 : CollatzResearch.WordTrace tailWord_903264 prefixEnd_903264 103068575533968713143549 := by
  unfold tailWord_903264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472372299818134027314423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21963163066424178703085897 16472372299818134027314423)
  ·
    refine ⟨24708558449727201040971635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16472372299818134027314423 24708558449727201040971635)
    ·
      refine ⟨37062837674590801561457453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24708558449727201040971635 37062837674590801561457453)
      ·
        refine ⟨13898564127971550585546545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37062837674590801561457453 13898564127971550585546545)
        ·
          refine ⟨10423923095978662939159909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13898564127971550585546545 10423923095978662939159909)
          ·
            refine ⟨1954485580495999301092483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10423923095978662939159909 1954485580495999301092483)
            ·
              refine ⟨2931728370743998951638725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954485580495999301092483 2931728370743998951638725)
              ·
                refine ⟨549699069514499803432261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2931728370743998951638725 549699069514499803432261)
                ·
                  refine ⟨103068575533968713143549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549699069514499803432261 103068575533968713143549)
                  ·
                    rfl

theorem cell22_903264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_903264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903264 prefixEnd_903264 := by exact prefixLift 903264
  have htrace : WordTrace (prefixWord ++ tailWord_903264) baseStart_903264 baseEnd_903264 := by
    simpa [prefixWord, tailWord_903264, baseEnd_903264] using wordTrace_append hprefix tailTrace_903264
  have hstable : (prefixWord ++ tailWord_903264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903264).length < 2 ^ (prefixWord ++ tailWord_903264).sum := by decide
  have hdescent : baseEnd_903264 < baseStart_903264 := by decide
  rcases family_descends (prefixWord ++ tailWord_903264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903277 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_903277 : Nat := 118140960795 + 903277 * 2 ^ 59
def prefixEnd_903277 : Nat := 4983230072969 + 3 ^ 40 * 903277 * 2
def baseEnd_903277 : Nat := 309210176767578438855607

theorem tailTrace_903277 : CollatzResearch.WordTrace tailWord_903277 prefixEnd_903277 309210176767578438855607 := by
  unfold tailWord_903277
  simp only [CollatzResearch.WordTrace]
  refine ⟨32945218748589171274852085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21963479165726114183234723 32945218748589171274852085)
  ·
    refine ⟨3088614257680234807017383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32945218748589171274852085 3088614257680234807017383)
    ·
      refine ⟨4632921386520352210526075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088614257680234807017383 4632921386520352210526075)
      ·
        refine ⟨6949382079780528315789113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632921386520352210526075 6949382079780528315789113)
        ·
          refine ⟨5212036559835396236841835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6949382079780528315789113 5212036559835396236841835)
          ·
            refine ⟨7818054839753094355262753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212036559835396236841835 7818054839753094355262753)
            ·
              refine ⟨5863541129814820766447065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7818054839753094355262753 5863541129814820766447065)
              ·
                refine ⟨4397655847361115574835299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863541129814820766447065 4397655847361115574835299)
                ·
                  refine ⟨6596483771041673362252949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397655847361115574835299 6596483771041673362252949)
                  ·
                    refine ⟨309210176767578438855607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6596483771041673362252949 309210176767578438855607)
                    ·
                      rfl

theorem cell22_903277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_903277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903277 prefixEnd_903277 := by exact prefixLift 903277
  have htrace : WordTrace (prefixWord ++ tailWord_903277) baseStart_903277 baseEnd_903277 := by
    simpa [prefixWord, tailWord_903277, baseEnd_903277] using wordTrace_append hprefix tailTrace_903277
  have hstable : (prefixWord ++ tailWord_903277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903277).length < 2 ^ (prefixWord ++ tailWord_903277).sum := by decide
  have hdescent : baseEnd_903277 < baseStart_903277 := by decide
  rcases family_descends (prefixWord ++ tailWord_903277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903279 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 2, 3]
def baseStart_903279 : Nat := 118140960795 + 903279 * 2 ^ 59
def prefixEnd_903279 : Nat := 4983230072969 + 3 ^ 40 * 903279 * 2
def baseEnd_903279 : Nat := 309210861408451100305601

theorem tailTrace_903279 : CollatzResearch.WordTrace tailWord_903279 prefixEnd_903279 309210861408451100305601 := by
  unfold tailWord_903279
  simp only [CollatzResearch.WordTrace]
  refine ⟨32945291694581925616424891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21963527796387950410949927 32945291694581925616424891)
  ·
    refine ⟨49417937541872888424637337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32945291694581925616424891 49417937541872888424637337)
    ·
      refine ⟨37063453156404666318478003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49417937541872888424637337 37063453156404666318478003)
      ·
        refine ⟨55595179734606999477717005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37063453156404666318478003 55595179734606999477717005)
        ·
          refine ⟨20848192400477624804143877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55595179734606999477717005 20848192400477624804143877)
          ·
            refine ⟨3909036075089554650776977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20848192400477624804143877 3909036075089554650776977)
            ·
              refine ⟨2931777056317165988082733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909036075089554650776977 2931777056317165988082733)
              ·
                refine ⟨1099416396118937245531025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2931777056317165988082733 1099416396118937245531025)
                ·
                  refine ⟨824562297089202934148269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099416396118937245531025 824562297089202934148269)
                  ·
                    refine ⟨309210861408451100305601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 824562297089202934148269 309210861408451100305601)
                    ·
                      rfl

theorem cell22_903279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_903279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903279 prefixEnd_903279 := by exact prefixLift 903279
  have htrace : WordTrace (prefixWord ++ tailWord_903279) baseStart_903279 baseEnd_903279 := by
    simpa [prefixWord, tailWord_903279, baseEnd_903279] using wordTrace_append hprefix tailTrace_903279
  have hstable : (prefixWord ++ tailWord_903279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903279).length < 2 ^ (prefixWord ++ tailWord_903279).sum := by decide
  have hdescent : baseEnd_903279 < baseStart_903279 := by decide
  rcases family_descends (prefixWord ++ tailWord_903279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903341 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_903341 : Nat := 118140960795 + 903341 * 2 ^ 59
def prefixEnd_903341 : Nat := 4983230072969 + 3 ^ 40 * 903341 * 2
def baseEnd_903341 : Nat := 309232085275503605255411

theorem tailTrace_903341 : CollatzResearch.WordTrace tailWord_903341 prefixEnd_903341 309232085275503605255411 := by
  unfold tailWord_903341
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947553020357310205181877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21965035346904873470121251 32947553020357310205181877)
  ·
    refine ⟨3088833095658497831735801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32947553020357310205181877 3088833095658497831735801)
    ·
      refine ⟨2316624821743873373801851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3088833095658497831735801 2316624821743873373801851)
      ·
        refine ⟨3474937232615810060702777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316624821743873373801851 3474937232615810060702777)
        ·
          refine ⟨2606202924461857545527083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474937232615810060702777 2606202924461857545527083)
          ·
            refine ⟨3909304386692786318290625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606202924461857545527083 3909304386692786318290625)
            ·
              refine ⟨2931978290019589738717969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909304386692786318290625 2931978290019589738717969)
              ·
                refine ⟨2198983717514692304038477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2931978290019589738717969 2198983717514692304038477)
                ·
                  refine ⟨824618894068009614014429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2198983717514692304038477 824618894068009614014429)
                  ·
                    refine ⟨309232085275503605255411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 824618894068009614014429 309232085275503605255411)
                    ·
                      rfl

theorem cell22_903341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_903341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903341 prefixEnd_903341 := by exact prefixLift 903341
  have htrace : WordTrace (prefixWord ++ tailWord_903341) baseStart_903341 baseEnd_903341 := by
    simpa [prefixWord, tailWord_903341, baseEnd_903341] using wordTrace_append hprefix tailTrace_903341
  have hstable : (prefixWord ++ tailWord_903341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903341).length < 2 ^ (prefixWord ++ tailWord_903341).sum := by decide
  have hdescent : baseEnd_903341 < baseStart_903341 := by decide
  rcases family_descends (prefixWord ++ tailWord_903341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903367 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_903367 : Nat := 118140960795 + 903367 * 2 ^ 59
def prefixEnd_903367 : Nat := 4983230072969 + 3 ^ 40 * 903367 * 2
def baseEnd_903367 : Nat := 309240985606848204105331

theorem tailTrace_903367 : CollatzResearch.WordTrace tailWord_903367 prefixEnd_903367 309240985606848204105331 := by
  unfold tailWord_903367
  simp only [CollatzResearch.WordTrace]
  refine ⟨32948501318263116645628355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21965667545508744430418903 32948501318263116645628355)
  ·
    refine ⟨49422751977394674968442533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32948501318263116645628355 49422751977394674968442533)
    ·
      refine ⟨9266765995761501556582975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49422751977394674968442533 9266765995761501556582975)
      ·
        refine ⟨13900148993642252334874463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9266765995761501556582975 13900148993642252334874463)
        ·
          refine ⟨20850223490463378502311695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13900148993642252334874463 20850223490463378502311695)
          ·
            refine ⟨31275335235695067753467543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20850223490463378502311695 31275335235695067753467543)
            ·
              refine ⟨46913002853542601630201315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31275335235695067753467543 46913002853542601630201315)
              ·
                refine ⟨70369504280313902445301973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46913002853542601630201315 70369504280313902445301973)
                ·
                  refine ⟨1649285256569857088561765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 70369504280313902445301973 1649285256569857088561765)
                  ·
                    refine ⟨309240985606848204105331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1649285256569857088561765 309240985606848204105331)
                    ·
                      rfl

theorem cell22_903367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_903367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903367 prefixEnd_903367 := by exact prefixLift 903367
  have htrace : WordTrace (prefixWord ++ tailWord_903367) baseStart_903367 baseEnd_903367 := by
    simpa [prefixWord, tailWord_903367, baseEnd_903367] using wordTrace_append hprefix tailTrace_903367
  have hstable : (prefixWord ++ tailWord_903367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903367).length < 2 ^ (prefixWord ++ tailWord_903367).sum := by decide
  have hdescent : baseEnd_903367 < baseStart_903367 := by decide
  rcases family_descends (prefixWord ++ tailWord_903367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903388 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_903388 : Nat := 118140960795 + 903388 * 2 ^ 59
def prefixEnd_903388 : Nat := 4983230072969 + 3 ^ 40 * 903388 * 2
def baseEnd_903388 : Nat := 103082724778670383110089

theorem tailTrace_903388 : CollatzResearch.WordTrace tailWord_903388 prefixEnd_903388 103082724778670383110089 := by
  unfold tailWord_903388
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474633625593518616071409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21966178167458024821428545 16474633625593518616071409)
  ·
    refine ⟨12355975219195138962053557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16474633625593518616071409 12355975219195138962053557)
    ·
      refine ⟨1158372676799544277692521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12355975219195138962053557 1158372676799544277692521)
      ·
        refine ⟨868779507599658208269391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1158372676799544277692521 868779507599658208269391)
        ·
          refine ⟨1303169261399487312404087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868779507599658208269391 1303169261399487312404087)
          ·
            refine ⟨1954753892099230968606131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303169261399487312404087 1954753892099230968606131)
            ·
              refine ⟨2932130838148846452909197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954753892099230968606131 2932130838148846452909197)
              ·
                refine ⟨1099549064305817419840949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932130838148846452909197 1099549064305817419840949)
                ·
                  refine ⟨103082724778670383110089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099549064305817419840949 103082724778670383110089)
                  ·
                    rfl

theorem cell22_903388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_903388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903388 prefixEnd_903388 := by exact prefixLift 903388
  have htrace : WordTrace (prefixWord ++ tailWord_903388) baseStart_903388 baseEnd_903388 := by
    simpa [prefixWord, tailWord_903388, baseEnd_903388] using wordTrace_append hprefix tailTrace_903388
  have hstable : (prefixWord ++ tailWord_903388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903388).length < 2 ^ (prefixWord ++ tailWord_903388).sum := by decide
  have hdescent : baseEnd_903388 < baseStart_903388 := by decide
  rcases family_descends (prefixWord ++ tailWord_903388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903414 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_903414 : Nat := 118140960795 + 903414 * 2 ^ 59
def prefixEnd_903414 : Nat := 4983230072969 + 3 ^ 40 * 903414 * 2
def baseEnd_903414 : Nat := 309257074667355748180187

theorem tailTrace_903414 : CollatzResearch.WordTrace tailWord_903414 prefixEnd_903414 309257074667355748180187 := by
  unfold tailWord_903414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059388471818302729536831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21966810366061895781726197 2059388471818302729536831)
  ·
    refine ⟨3089082707727454094305247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2059388471818302729536831 3089082707727454094305247)
    ·
      refine ⟨4633624061591181141457871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089082707727454094305247 4633624061591181141457871)
      ·
        refine ⟨6950436092386771712186807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633624061591181141457871 6950436092386771712186807)
        ·
          refine ⟨10425654138580157568280211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950436092386771712186807 10425654138580157568280211)
          ·
            refine ⟨15638481207870236352420317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425654138580157568280211 15638481207870236352420317)
            ·
              refine ⟨5864430452951338632157619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15638481207870236352420317 5864430452951338632157619)
              ·
                refine ⟨8796645679427007948236429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864430452951338632157619 8796645679427007948236429)
                ·
                  refine ⟨3298742129785127980588661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8796645679427007948236429 3298742129785127980588661)
                  ·
                    refine ⟨309257074667355748180187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3298742129785127980588661 309257074667355748180187)
                    ·
                      rfl

theorem cell22_903414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_903414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903414 prefixEnd_903414 := by exact prefixLift 903414
  have htrace : WordTrace (prefixWord ++ tailWord_903414) baseStart_903414 baseEnd_903414 := by
    simpa [prefixWord, tailWord_903414, baseEnd_903414] using wordTrace_append hprefix tailTrace_903414
  have hstable : (prefixWord ++ tailWord_903414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903414).length < 2 ^ (prefixWord ++ tailWord_903414).sum := by decide
  have hdescent : baseEnd_903414 < baseStart_903414 := by decide
  rcases family_descends (prefixWord ++ tailWord_903414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903433 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 4]
def baseStart_903433 : Nat := 118140960795 + 903433 * 2 ^ 59
def prefixEnd_903433 : Nat := 4983230072969 + 3 ^ 40 * 903433 * 2
def baseEnd_903433 : Nat := 103087859585215343985043

theorem tailTrace_903433 : CollatzResearch.WordTrace tailWord_903433 prefixEnd_903433 103087859585215343985043 := by
  unfold tailWord_903433
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950908536024009917530953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21967272357349339945020635 32950908536024009917530953)
  ·
    refine ⟨24713181402018007438148215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32950908536024009917530953 24713181402018007438148215)
    ·
      refine ⟨37069772103027011157222323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24713181402018007438148215 37069772103027011157222323)
      ·
        refine ⟨55604658154540516735833485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37069772103027011157222323 55604658154540516735833485)
        ·
          refine ⟨20851746807952693775937557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55604658154540516735833485 20851746807952693775937557)
          ·
            refine ⟨977425631622782520747073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20851746807952693775937557 977425631622782520747073)
            ·
              refine ⟨733069223717086890560305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977425631622782520747073 733069223717086890560305)
              ·
                refine ⟨549801917787815167920229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733069223717086890560305 549801917787815167920229)
                ·
                  refine ⟨103087859585215343985043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549801917787815167920229 103087859585215343985043)
                  ·
                    rfl

theorem cell22_903433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_903433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903433 prefixEnd_903433 := by exact prefixLift 903433
  have htrace : WordTrace (prefixWord ++ tailWord_903433) baseStart_903433 baseEnd_903433 := by
    simpa [prefixWord, tailWord_903433, baseEnd_903433] using wordTrace_append hprefix tailTrace_903433
  have hstable : (prefixWord ++ tailWord_903433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903433).length < 2 ^ (prefixWord ++ tailWord_903433).sum := by decide
  have hdescent : baseEnd_903433 < baseStart_903433 := by decide
  rcases family_descends (prefixWord ++ tailWord_903433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903461 : List Nat := [1, 3, 1, 2, 5, 1, 3, 6]
def baseStart_903461 : Nat := 118140960795 + 903461 * 2 ^ 59
def prefixEnd_903461 : Nat := 4983230072969 + 3 ^ 40 * 903461 * 2
def baseEnd_903461 : Nat := 34363684858651476917227

theorem tailTrace_903461 : CollatzResearch.WordTrace tailWord_903461 prefixEnd_903461 34363684858651476917227 := by
  unfold tailWord_903461
  simp only [CollatzResearch.WordTrace]
  refine ⟨32951929779922570699550237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21967953186615047133033491 32951929779922570699550237)
  ·
    refine ⟨12356973667470964012331339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32951929779922570699550237 12356973667470964012331339)
    ·
      refine ⟨18535460501206446018497009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356973667470964012331339 18535460501206446018497009)
      ·
        refine ⟨13901595375904834513872757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18535460501206446018497009 13901595375904834513872757)
        ·
          refine ⟨1303274566491078235675571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13901595375904834513872757 1303274566491078235675571)
          ·
            refine ⟨1954911849736617353513357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303274566491078235675571 1954911849736617353513357)
            ·
              refine ⟨733091943651231507567509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1954911849736617353513357 733091943651231507567509)
              ·
                refine ⟨34363684858651476917227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 733091943651231507567509 34363684858651476917227)
                ·
                  rfl

theorem cell22_903461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 6].length) (baseStart_903461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903461 prefixEnd_903461 := by exact prefixLift 903461
  have htrace : WordTrace (prefixWord ++ tailWord_903461) baseStart_903461 baseEnd_903461 := by
    simpa [prefixWord, tailWord_903461, baseEnd_903461] using wordTrace_append hprefix tailTrace_903461
  have hstable : (prefixWord ++ tailWord_903461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903461).length < 2 ^ (prefixWord ++ tailWord_903461).sum := by decide
  have hdescent : baseEnd_903461 < baseStart_903461 := by decide
  rcases family_descends (prefixWord ++ tailWord_903461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903504 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_903504 : Nat := 118140960795 + 903504 * 2 ^ 59
def prefixEnd_903504 : Nat := 4983230072969 + 3 ^ 40 * 903504 * 2
def baseEnd_903504 : Nat := 309287883506625513429911

theorem tailTrace_903504 : CollatzResearch.WordTrace tailWord_903504 prefixEnd_903504 309287883506625513429911 := by
  unfold tailWord_903504
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476749059383394521682783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21968998745844526028910377 16476749059383394521682783)
  ·
    refine ⟨24715123589075091782524175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16476749059383394521682783 24715123589075091782524175)
    ·
      refine ⟨37072685383612637673786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715123589075091782524175 37072685383612637673786263)
      ·
        refine ⟨55609028075418956510679395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37072685383612637673786263 55609028075418956510679395)
        ·
          refine ⟨83413542113128434766019093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55609028075418956510679395 83413542113128434766019093)
          ·
            refine ⟨3910009786552895379657145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83413542113128434766019093 3910009786552895379657145)
            ·
              refine ⟨2932507339914671534742859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910009786552895379657145 2932507339914671534742859)
              ·
                refine ⟨4398761009872007302114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932507339914671534742859 4398761009872007302114289)
                ·
                  refine ⟨3299070757404005476585717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4398761009872007302114289 3299070757404005476585717)
                  ·
                    refine ⟨309287883506625513429911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3299070757404005476585717 309287883506625513429911)
                    ·
                      rfl

theorem cell22_903504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_903504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903504 prefixEnd_903504 := by exact prefixLift 903504
  have htrace : WordTrace (prefixWord ++ tailWord_903504) baseStart_903504 baseEnd_903504 := by
    simpa [prefixWord, tailWord_903504, baseEnd_903504] using wordTrace_append hprefix tailTrace_903504
  have hstable : (prefixWord ++ tailWord_903504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903504).length < 2 ^ (prefixWord ++ tailWord_903504).sum := by decide
  have hdescent : baseEnd_903504 < baseStart_903504 := by decide
  rcases family_descends (prefixWord ++ tailWord_903504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903519 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_903519 : Nat := 118140960795 + 903519 * 2 ^ 59
def prefixEnd_903519 : Nat := 4983230072969 + 3 ^ 40 * 903519 * 2
def baseEnd_903519 : Nat := 309293018313170474304865

theorem tailTrace_903519 : CollatzResearch.WordTrace tailWord_903519 prefixEnd_903519 309293018313170474304865 := by
  unfold tailWord_903519
  simp only [CollatzResearch.WordTrace]
  refine ⟨32954045213712446605161611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21969363475808297736774407 32954045213712446605161611)
  ·
    refine ⟨49431067820568669907742417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32954045213712446605161611 49431067820568669907742417)
    ·
      refine ⟨37073300865426502430806813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49431067820568669907742417 37073300865426502430806813)
      ·
        refine ⟨13902487824534938411552555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37073300865426502430806813 13902487824534938411552555)
        ·
          refine ⟨20853731736802407617328833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902487824534938411552555 20853731736802407617328833)
          ·
            refine ⟨15640298802601805712996625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20853731736802407617328833 15640298802601805712996625)
            ·
              refine ⟨11730224101951354284747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15640298802601805712996625 11730224101951354284747469)
              ·
                refine ⟨4398834038231757856780301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11730224101951354284747469 4398834038231757856780301)
                ·
                  refine ⟨1649562764336909196292613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4398834038231757856780301 1649562764336909196292613)
                  ·
                    refine ⟨309293018313170474304865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1649562764336909196292613 309293018313170474304865)
                    ·
                      rfl

theorem cell22_903519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_903519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903519 prefixEnd_903519 := by exact prefixLift 903519
  have htrace : WordTrace (prefixWord ++ tailWord_903519) baseStart_903519 baseEnd_903519 := by
    simpa [prefixWord, tailWord_903519, baseEnd_903519] using wordTrace_append hprefix tailTrace_903519
  have hstable : (prefixWord ++ tailWord_903519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903519).length < 2 ^ (prefixWord ++ tailWord_903519).sum := by decide
  have hdescent : baseEnd_903519 < baseStart_903519 := by decide
  rcases family_descends (prefixWord ++ tailWord_903519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903536 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_903536 : Nat := 118140960795 + 903536 * 2 ^ 59
def prefixEnd_903536 : Nat := 4983230072969 + 3 ^ 40 * 903536 * 2
def baseEnd_903536 : Nat := 309298837760588096629813

theorem tailTrace_903536 : CollatzResearch.WordTrace tailWord_903536 prefixEnd_903536 309298837760588096629813 := by
  unfold tailWord_903536
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477332627325429254265231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21969776836433905672353641 16477332627325429254265231)
  ·
    refine ⟨24715998940988143881397847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16477332627325429254265231 24715998940988143881397847)
    ·
      refine ⟨37073998411482215822096771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715998940988143881397847 37073998411482215822096771)
      ·
        refine ⟨55610997617223323733145157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37073998411482215822096771 55610997617223323733145157)
        ·
          refine ⟨10427062053229373199964717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55610997617223323733145157 10427062053229373199964717)
          ·
            refine ⟨3910148269961014949986769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10427062053229373199964717 3910148269961014949986769)
            ·
              refine ⟨2932611202470761212490077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910148269961014949986769 2932611202470761212490077)
              ·
                refine ⟨1099729200926535454683779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932611202470761212490077 1099729200926535454683779)
                ·
                  refine ⟨1649593801389803182025669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099729200926535454683779 1649593801389803182025669)
                  ·
                    refine ⟨309298837760588096629813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1649593801389803182025669 309298837760588096629813)
                    ·
                      rfl

theorem cell22_903536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_903536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903536 prefixEnd_903536 := by exact prefixLift 903536
  have htrace : WordTrace (prefixWord ++ tailWord_903536) baseStart_903536 baseEnd_903536 := by
    simpa [prefixWord, tailWord_903536, baseEnd_903536] using wordTrace_append hprefix tailTrace_903536
  have hstable : (prefixWord ++ tailWord_903536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903536).length < 2 ^ (prefixWord ++ tailWord_903536).sum := by decide
  have hdescent : baseEnd_903536 < baseStart_903536 := by decide
  rcases family_descends (prefixWord ++ tailWord_903536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903617 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 1, 5]
def baseStart_903617 : Nat := 118140960795 + 903617 * 2 ^ 59
def prefixEnd_903617 : Nat := 4983230072969 + 3 ^ 40 * 903617 * 2
def baseEnd_903617 : Nat := 309326565715930885354565

theorem tailTrace_903617 : CollatzResearch.WordTrace tailWord_903617 prefixEnd_903617 309326565715930885354565 := by
  unfold tailWord_903617
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957619567357409342229105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21971746378238272894819403 32957619567357409342229105)
  ·
    refine ⟨24718214675518057006671829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32957619567357409342229105 24718214675518057006671829)
    ·
      refine ⟨579333156457454461093871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24718214675518057006671829 579333156457454461093871)
      ·
        refine ⟨868999734686181691640807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579333156457454461093871 868999734686181691640807)
        ·
          refine ⟨1303499602029272537461211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868999734686181691640807 1303499602029272537461211)
          ·
            refine ⟨1955249403043908806191817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303499602029272537461211 1955249403043908806191817)
            ·
              refine ⟨1466437052282931604643863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955249403043908806191817 1466437052282931604643863)
              ·
                refine ⟨2199655578424397406965795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466437052282931604643863 2199655578424397406965795)
                ·
                  refine ⟨3299483367636596110448693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199655578424397406965795 3299483367636596110448693)
                  ·
                    refine ⟨309326565715930885354565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3299483367636596110448693 309326565715930885354565)
                    ·
                      rfl

theorem cell22_903617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_903617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903617 prefixEnd_903617 := by exact prefixLift 903617
  have htrace : WordTrace (prefixWord ++ tailWord_903617) baseStart_903617 baseEnd_903617 := by
    simpa [prefixWord, tailWord_903617, baseEnd_903617] using wordTrace_append hprefix tailTrace_903617
  have hstable : (prefixWord ++ tailWord_903617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903617).length < 2 ^ (prefixWord ++ tailWord_903617).sum := by decide
  have hdescent : baseEnd_903617 < baseStart_903617 := by decide
  rcases family_descends (prefixWord ++ tailWord_903617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903656 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_903656 : Nat := 118140960795 + 903656 * 2 ^ 59
def prefixEnd_903656 : Nat := 4983230072969 + 3 ^ 40 * 903656 * 2
def baseEnd_903656 : Nat := 309339916212947783629445

theorem tailTrace_903656 : CollatzResearch.WordTrace tailWord_903656 prefixEnd_903656 309339916212947783629445 := by
  unfold tailWord_903656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16479521007108059501449411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21972694676144079335265881 16479521007108059501449411)
  ·
    refine ⟨24719281510662089252174117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16479521007108059501449411 24719281510662089252174117)
    ·
      refine ⟨4634865283249141734782647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24719281510662089252174117 4634865283249141734782647)
      ·
        refine ⟨6952297924873712602173971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634865283249141734782647 6952297924873712602173971)
        ·
          refine ⟨10428446887310568903260957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6952297924873712602173971 10428446887310568903260957)
          ·
            refine ⟨3910667582741463338722859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10428446887310568903260957 3910667582741463338722859)
            ·
              refine ⟨5866001374112195008084289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910667582741463338722859 5866001374112195008084289)
              ·
                refine ⟨4399501030584146256063217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5866001374112195008084289 4399501030584146256063217)
                ·
                  refine ⟨3299625772938109692047413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4399501030584146256063217 3299625772938109692047413)
                  ·
                    refine ⟨309339916212947783629445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3299625772938109692047413 309339916212947783629445)
                    ·
                      rfl

theorem cell22_903656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_903656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903656 prefixEnd_903656 := by exact prefixLift 903656
  have htrace : WordTrace (prefixWord ++ tailWord_903656) baseStart_903656 baseEnd_903656 := by
    simpa [prefixWord, tailWord_903656, baseEnd_903656] using wordTrace_append hprefix tailTrace_903656
  have hstable : (prefixWord ++ tailWord_903656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903656).length < 2 ^ (prefixWord ++ tailWord_903656).sum := by decide
  have hdescent : baseEnd_903656 < baseStart_903656 := by decide
  rcases family_descends (prefixWord ++ tailWord_903656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903658 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_903658 : Nat := 118140960795 + 903658 * 2 ^ 59
def prefixEnd_903658 : Nat := 4983230072969 + 3 ^ 40 * 903658 * 2
def baseEnd_903658 : Nat := 103113533617940148359813

theorem tailTrace_903658 : CollatzResearch.WordTrace tailWord_903658 prefixEnd_903658 103113533617940148359813 := by
  unfold tailWord_903658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239778740052218336117907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21972743306805915562981085 8239778740052218336117907)
  ·
    refine ⟨12359668110078327504176861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239778740052218336117907 12359668110078327504176861)
    ·
      refine ⟨4634875541279372814066323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12359668110078327504176861 4634875541279372814066323)
      ·
        refine ⟨6952313311919059221099485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634875541279372814066323 6952313311919059221099485)
        ·
          refine ⟨2607117491969647207912307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6952313311919059221099485 2607117491969647207912307)
          ·
            refine ⟨3910676237954470811868461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607117491969647207912307 3910676237954470811868461)
            ·
              refine ⟨1466503589232926554450673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3910676237954470811868461 1466503589232926554450673)
              ·
                refine ⟨1099877691924694915838005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466503589232926554450673 1099877691924694915838005)
                ·
                  refine ⟨103113533617940148359813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099877691924694915838005 103113533617940148359813)
                  ·
                    rfl

theorem cell22_903658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_903658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903658 prefixEnd_903658 := by exact prefixLift 903658
  have htrace : WordTrace (prefixWord ++ tailWord_903658) baseStart_903658 baseEnd_903658 := by
    simpa [prefixWord, tailWord_903658, baseEnd_903658] using wordTrace_append hprefix tailTrace_903658
  have hstable : (prefixWord ++ tailWord_903658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903658).length < 2 ^ (prefixWord ++ tailWord_903658).sum := by decide
  have hdescent : baseEnd_903658 < baseStart_903658 := by decide
  rcases family_descends (prefixWord ++ tailWord_903658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903701 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_903701 : Nat := 118140960795 + 903701 * 2 ^ 59
def prefixEnd_903701 : Nat := 4983230072969 + 3 ^ 40 * 903701 * 2
def baseEnd_903701 : Nat := 309355320632582666254307

theorem tailTrace_903701 : CollatzResearch.WordTrace tailWord_903701 prefixEnd_903701 309355320632582666254307 := by
  unfold tailWord_903701
  simp only [CollatzResearch.WordTrace]
  refine ⟨32960683299053091688286957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21973788866035394458857971 32960683299053091688286957)
  ·
    refine ⟨12360256237144909383107609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32960683299053091688286957 12360256237144909383107609)
    ·
      refine ⟨9270192177858682037330707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12360256237144909383107609 9270192177858682037330707)
      ·
        refine ⟨13905288266788023055996061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9270192177858682037330707 13905288266788023055996061)
        ·
          refine ⟨5214483100045508645998523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13905288266788023055996061 5214483100045508645998523)
          ·
            refine ⟨7821724650068262968997785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214483100045508645998523 7821724650068262968997785)
            ·
              refine ⟨5866293487551197226748339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7821724650068262968997785 5866293487551197226748339)
              ·
                refine ⟨8799440231326795840122509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866293487551197226748339 8799440231326795840122509)
                ·
                  refine ⟨3299790086747548440045941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8799440231326795840122509 3299790086747548440045941)
                  ·
                    refine ⟨309355320632582666254307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3299790086747548440045941 309355320632582666254307)
                    ·
                      rfl

theorem cell22_903701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_903701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903701 prefixEnd_903701 := by exact prefixLift 903701
  have htrace : WordTrace (prefixWord ++ tailWord_903701) baseStart_903701 baseEnd_903701 := by
    simpa [prefixWord, tailWord_903701, baseEnd_903701] using wordTrace_append hprefix tailTrace_903701
  have hstable : (prefixWord ++ tailWord_903701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903701).length < 2 ^ (prefixWord ++ tailWord_903701).sum := by decide
  have hdescent : baseEnd_903701 < baseStart_903701 := by decide
  rcases family_descends (prefixWord ++ tailWord_903701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903720 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_903720 : Nat := 118140960795 + 903720 * 2 ^ 59
def prefixEnd_903720 : Nat := 4983230072969 + 3 ^ 40 * 903720 * 2
def baseEnd_903720 : Nat := 103120608240290983343083

theorem tailTrace_903720 : CollatzResearch.WordTrace tailWord_903720 prefixEnd_903720 103120608240290983343083 := by
  unfold tailWord_903720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480688142992128966614307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21974250857322838622152409 16480688142992128966614307)
  ·
    refine ⟨24721032214488193449921461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16480688142992128966614307 24721032214488193449921461)
    ·
      refine ⟨2317596770108268135930137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24721032214488193449921461 2317596770108268135930137)
      ·
        refine ⟨1738197577581201101947603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2317596770108268135930137 1738197577581201101947603)
        ·
          refine ⟨2607296366371801652921405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738197577581201101947603 2607296366371801652921405)
          ·
            refine ⟨977736137389425619845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2607296366371801652921405 977736137389425619845527)
            ·
              refine ⟨1466604206084138429768291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977736137389425619845527 1466604206084138429768291)
              ·
                refine ⟨2199906309126207644652437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466604206084138429768291 2199906309126207644652437)
                ·
                  refine ⟨103120608240290983343083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2199906309126207644652437 103120608240290983343083)
                  ·
                    rfl

theorem cell22_903720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_903720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903720 prefixEnd_903720 := by exact prefixLift 903720
  have htrace : WordTrace (prefixWord ++ tailWord_903720) baseStart_903720 baseEnd_903720 := by
    simpa [prefixWord, tailWord_903720, baseEnd_903720] using wordTrace_append hprefix tailTrace_903720
  have hstable : (prefixWord ++ tailWord_903720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903720).length < 2 ^ (prefixWord ++ tailWord_903720).sum := by decide
  have hdescent : baseEnd_903720 < baseStart_903720 := by decide
  rcases family_descends (prefixWord ++ tailWord_903720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903731 : List Nat := [1, 1, 1, 2, 4, 2, 4, 7]
def baseStart_903731 : Nat := 118140960795 + 903731 * 2 ^ 59
def prefixEnd_903731 : Nat := 4983230072969 + 3 ^ 40 * 903731 * 2
def baseEnd_903731 : Nat := 34373954471741398667135

theorem tailTrace_903731 : CollatzResearch.WordTrace tailWord_903731 prefixEnd_903731 34373954471741398667135 := by
  unfold tailWord_903731
  simp only [CollatzResearch.WordTrace]
  refine ⟨32961777488944406811879047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21974518325962937874586031 32961777488944406811879047)
  ·
    refine ⟨49442666233416610217818571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32961777488944406811879047 49442666233416610217818571)
    ·
      refine ⟨74163999350124915326727857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49442666233416610217818571 74163999350124915326727857)
      ·
        refine ⟨55622999512593686495045893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74163999350124915326727857 55622999512593686495045893)
        ·
          refine ⟨10429312408611316217821105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55622999512593686495045893 10429312408611316217821105)
          ·
            refine ⟨7821984306458487163365829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10429312408611316217821105 7821984306458487163365829)
            ·
              refine ⟨1466622057460966343131093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7821984306458487163365829 1466622057460966343131093)
              ·
                refine ⟨34373954471741398667135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1466622057460966343131093 34373954471741398667135)
                ·
                  rfl

theorem cell22_903731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 7].length) (baseStart_903731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903731 prefixEnd_903731 := by exact prefixLift 903731
  have htrace : WordTrace (prefixWord ++ tailWord_903731) baseStart_903731 baseEnd_903731 := by
    simpa [prefixWord, tailWord_903731, baseEnd_903731] using wordTrace_append hprefix tailTrace_903731
  have hstable : (prefixWord ++ tailWord_903731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903731).length < 2 ^ (prefixWord ++ tailWord_903731).sum := by decide
  have hdescent : baseEnd_903731 < baseStart_903731 := by decide
  rcases family_descends (prefixWord ++ tailWord_903731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903776 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_903776 : Nat := 118140960795 + 903776 * 2 ^ 59
def prefixEnd_903776 : Nat := 4983230072969 + 3 ^ 40 * 903776 * 2
def baseEnd_903776 : Nat := 103126998221769156876359

theorem tailTrace_903776 : CollatzResearch.WordTrace tailWord_903776 prefixEnd_903776 103126998221769156876359 := by
  unfold tailWord_903776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481709386890689748633591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21975612515854252998178121 16481709386890689748633591)
  ·
    refine ⟨24722564080336034622950387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16481709386890689748633591 24722564080336034622950387)
    ·
      refine ⟨37083846120504051934425581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24722564080336034622950387 37083846120504051934425581)
      ·
        refine ⟨13906442295189019475409593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37083846120504051934425581 13906442295189019475409593)
        ·
          refine ⟨10429831721391764606557195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13906442295189019475409593 10429831721391764606557195)
          ·
            refine ⟨15644747582087646909835793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10429831721391764606557195 15644747582087646909835793)
            ·
              refine ⟨11733560686565735182376845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15644747582087646909835793 11733560686565735182376845)
              ·
                refine ⟨4400085257462150693391317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11733560686565735182376845 4400085257462150693391317)
                ·
                  refine ⟨103126998221769156876359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4400085257462150693391317 103126998221769156876359)
                  ·
                    rfl

theorem cell22_903776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_903776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903776 prefixEnd_903776 := by exact prefixLift 903776
  have htrace : WordTrace (prefixWord ++ tailWord_903776) baseStart_903776 baseEnd_903776 := by
    simpa [prefixWord, tailWord_903776, baseEnd_903776] using wordTrace_append hprefix tailTrace_903776
  have hstable : (prefixWord ++ tailWord_903776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903776).length < 2 ^ (prefixWord ++ tailWord_903776).sum := by decide
  have hdescent : baseEnd_903776 < baseStart_903776 := by decide
  rcases family_descends (prefixWord ++ tailWord_903776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903791 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_903791 : Nat := 118140960795 + 903791 * 2 ^ 59
def prefixEnd_903791 : Nat := 4983230072969 + 3 ^ 40 * 903791 * 2
def baseEnd_903791 : Nat := 309386129471852431504031

theorem tailTrace_903791 : CollatzResearch.WordTrace tailWord_903791 prefixEnd_903791 309386129471852431504031 := by
  unfold tailWord_903791
  simp only [CollatzResearch.WordTrace]
  refine ⟨32963965868727037059063227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21975977245818024706042151 32963965868727037059063227)
  ·
    refine ⟨49445948803090555588594841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32963965868727037059063227 49445948803090555588594841)
    ·
      refine ⟨37084461602317916691446131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49445948803090555588594841 37084461602317916691446131)
      ·
        refine ⟨55626692403476875037169197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37084461602317916691446131 55626692403476875037169197)
        ·
          refine ⟨20860009651303828138938449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55626692403476875037169197 20860009651303828138938449)
          ·
            refine ⟨15645007238477871104203837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20860009651303828138938449 15645007238477871104203837)
            ·
              refine ⟨5866877714429201664076439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15645007238477871104203837 5866877714429201664076439)
              ·
                refine ⟨8800316571643802496114659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866877714429201664076439 8800316571643802496114659)
                ·
                  refine ⟨13200474857465703744171989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8800316571643802496114659 13200474857465703744171989)
                  ·
                    refine ⟨309386129471852431504031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13200474857465703744171989 309386129471852431504031)
                    ·
                      rfl

theorem cell22_903791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_903791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903791 prefixEnd_903791 := by exact prefixLift 903791
  have htrace : WordTrace (prefixWord ++ tailWord_903791) baseStart_903791 baseEnd_903791 := by
    simpa [prefixWord, tailWord_903791, baseEnd_903791] using wordTrace_append hprefix tailTrace_903791
  have hstable : (prefixWord ++ tailWord_903791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903791).length < 2 ^ (prefixWord ++ tailWord_903791).sum := by decide
  have hdescent : baseEnd_903791 < baseStart_903791 := by decide
  rcases family_descends (prefixWord ++ tailWord_903791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903797 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_903797 : Nat := 118140960795 + 903797 * 2 ^ 59
def prefixEnd_903797 : Nat := 4983230072969 + 3 ^ 40 * 903797 * 2
def baseEnd_903797 : Nat := 309388183394470415854013

theorem tailTrace_903797 : CollatzResearch.WordTrace tailWord_903797 prefixEnd_903797 309388183394470415854013 := by
  unfold tailWord_903797
  simp only [CollatzResearch.WordTrace]
  refine ⟨32964184706705300083781645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21976123137803533389187763 32964184706705300083781645)
  ·
    refine ⟨12361569265014487531418117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32964184706705300083781645 12361569265014487531418117)
    ·
      refine ⟨2317794237190216412140897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12361569265014487531418117 2317794237190216412140897)
      ·
        refine ⟨1738345677892662309105673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2317794237190216412140897 1738345677892662309105673)
        ·
          refine ⟨1303759258419496731829255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738345677892662309105673 1303759258419496731829255)
          ·
            refine ⟨1955638887629245097743883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303759258419496731829255 1955638887629245097743883)
            ·
              refine ⟨2933458331443867646615825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955638887629245097743883 2933458331443867646615825)
              ·
                refine ⟨2200093748582900734961869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933458331443867646615825 2200093748582900734961869)
                ·
                  refine ⟨825035155718587775610701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2200093748582900734961869 825035155718587775610701)
                  ·
                    refine ⟨309388183394470415854013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825035155718587775610701 309388183394470415854013)
                    ·
                      rfl

theorem cell22_903797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_903797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903797 prefixEnd_903797 := by exact prefixLift 903797
  have htrace : WordTrace (prefixWord ++ tailWord_903797) baseStart_903797 baseEnd_903797 := by
    simpa [prefixWord, tailWord_903797, baseEnd_903797] using wordTrace_append hprefix tailTrace_903797
  have hstable : (prefixWord ++ tailWord_903797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903797).length < 2 ^ (prefixWord ++ tailWord_903797).sum := by decide
  have hdescent : baseEnd_903797 < baseStart_903797 := by decide
  rcases family_descends (prefixWord ++ tailWord_903797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903823 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 1, 4]
def baseStart_903823 : Nat := 118140960795 + 903823 * 2 ^ 59
def prefixEnd_903823 : Nat := 4983230072969 + 3 ^ 40 * 903823 * 2
def baseEnd_903823 : Nat := 309397083725815014703933

theorem tailTrace_903823 : CollatzResearch.WordTrace tailWord_903823 prefixEnd_903823 309397083725815014703933 := by
  unfold tailWord_903823
  simp only [CollatzResearch.WordTrace]
  refine ⟨32965133004611106524228123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21976755336407404349485415 32965133004611106524228123)
  ·
    refine ⟨49447699506916659786342185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32965133004611106524228123 49447699506916659786342185)
    ·
      refine ⟨37085774630187494839756639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49447699506916659786342185 37085774630187494839756639)
      ·
        refine ⟨55628661945281242259634959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37085774630187494839756639 55628661945281242259634959)
        ·
          refine ⟨83442992917921863389452439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55628661945281242259634959 83442992917921863389452439)
          ·
            refine ⟨125164489376882795084178659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83442992917921863389452439 125164489376882795084178659)
            ·
              refine ⟨187746734065324192626267989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125164489376882795084178659 187746734065324192626267989)
              ·
                refine ⟨1100078519914008941169539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 187746734065324192626267989 1100078519914008941169539)
                ·
                  refine ⟨1650117779871013411754309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100078519914008941169539 1650117779871013411754309)
                  ·
                    refine ⟨309397083725815014703933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1650117779871013411754309 309397083725815014703933)
                    ·
                      rfl

theorem cell22_903823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_903823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903823 prefixEnd_903823 := by exact prefixLift 903823
  have htrace : WordTrace (prefixWord ++ tailWord_903823) baseStart_903823 baseEnd_903823 := by
    simpa [prefixWord, tailWord_903823, baseEnd_903823] using wordTrace_append hprefix tailTrace_903823
  have hstable : (prefixWord ++ tailWord_903823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903823).length < 2 ^ (prefixWord ++ tailWord_903823).sum := by decide
  have hdescent : baseEnd_903823 < baseStart_903823 := by decide
  rcases family_descends (prefixWord ++ tailWord_903823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903868 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_903868 : Nat := 118140960795 + 903868 * 2 ^ 59
def prefixEnd_903868 : Nat := 4983230072969 + 3 ^ 40 * 903868 * 2
def baseEnd_903868 : Nat := 309412488145449897328795

theorem tailTrace_903868 : CollatzResearch.WordTrace tailWord_903868 prefixEnd_903868 309412488145449897328795 := by
  unfold tailWord_903868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483387144724039604808129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21977849526298719473077505 16483387144724039604808129)
  ·
    refine ⟨12362540358543029703606097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16483387144724039604808129 12362540358543029703606097)
    ·
      refine ⟨9271905268907272277704573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12362540358543029703606097 9271905268907272277704573)
      ·
        refine ⟨3476964475840227104139215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9271905268907272277704573 3476964475840227104139215)
        ·
          refine ⟨5215446713760340656208823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3476964475840227104139215 5215446713760340656208823)
          ·
            refine ⟨7823170070640510984313235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215446713760340656208823 7823170070640510984313235)
            ·
              refine ⟨11734755105960766476469853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823170070640510984313235 11734755105960766476469853)
              ·
                refine ⟨4400533164735287428676195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11734755105960766476469853 4400533164735287428676195)
                ·
                  refine ⟨6600799747102931143014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4400533164735287428676195 6600799747102931143014293)
                  ·
                    refine ⟨309412488145449897328795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6600799747102931143014293 309412488145449897328795)
                    ·
                      rfl

theorem cell22_903868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_903868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903868 prefixEnd_903868 := by exact prefixLift 903868
  have htrace : WordTrace (prefixWord ++ tailWord_903868) baseStart_903868 baseEnd_903868 := by
    simpa [prefixWord, tailWord_903868, baseEnd_903868] using wordTrace_append hprefix tailTrace_903868
  have hstable : (prefixWord ++ tailWord_903868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903868).length < 2 ^ (prefixWord ++ tailWord_903868).sum := by decide
  have hdescent : baseEnd_903868 < baseStart_903868 := by decide
  rcases family_descends (prefixWord ++ tailWord_903868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903870 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_903870 : Nat := 118140960795 + 903870 * 2 ^ 59
def prefixEnd_903870 : Nat := 4983230072969 + 3 ^ 40 * 903870 * 2
def baseEnd_903870 : Nat := 309413172786322558778789

theorem tailTrace_903870 : CollatzResearch.WordTrace tailWord_903870 prefixEnd_903870 309413172786322558778789 := by
  unfold tailWord_903870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4120855904430104193898633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21977898156960555700792709 4120855904430104193898633)
  ·
    refine ⟨3090641928322578145423975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4120855904430104193898633 3090641928322578145423975)
    ·
      refine ⟨4635962892483867218135963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090641928322578145423975 4635962892483867218135963)
      ·
        refine ⟨6953944338725800827203945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635962892483867218135963 6953944338725800827203945)
        ·
          refine ⟨5215458254044350620402959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6953944338725800827203945 5215458254044350620402959)
          ·
            refine ⟨7823187381066525930604439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5215458254044350620402959 7823187381066525930604439)
            ·
              refine ⟨11734781071599788895906659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7823187381066525930604439 11734781071599788895906659)
              ·
                refine ⟨17602171607399683343859989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734781071599788895906659 17602171607399683343859989)
                ·
                  refine ⟨825101794096860156743437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17602171607399683343859989 825101794096860156743437)
                  ·
                    refine ⟨309413172786322558778789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825101794096860156743437 309413172786322558778789)
                    ·
                      rfl

theorem cell22_903870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_903870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903870 prefixEnd_903870 := by exact prefixLift 903870
  have htrace : WordTrace (prefixWord ++ tailWord_903870) baseStart_903870 baseEnd_903870 := by
    simpa [prefixWord, tailWord_903870, baseEnd_903870] using wordTrace_append hprefix tailTrace_903870
  have hstable : (prefixWord ++ tailWord_903870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903870).length < 2 ^ (prefixWord ++ tailWord_903870).sum := by decide
  have hdescent : baseEnd_903870 < baseStart_903870 := by decide
  rcases family_descends (prefixWord ++ tailWord_903870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903872 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_903872 : Nat := 118140960795 + 903872 * 2 ^ 59
def prefixEnd_903872 : Nat := 4983230072969 + 3 ^ 40 * 903872 * 2
def baseEnd_903872 : Nat := 103137952475731740076261

theorem tailTrace_903872 : CollatzResearch.WordTrace tailWord_903872 prefixEnd_903872 103137952475731740076261 := by
  unfold tailWord_903872
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483460090716793946380935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21977946787622391928507913 16483460090716793946380935)
  ·
    refine ⟨24725190136075190919571403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16483460090716793946380935 24725190136075190919571403)
    ·
      refine ⟨37087785204112786379357105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24725190136075190919571403 37087785204112786379357105)
      ·
        refine ⟨27815838903084589784517829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37087785204112786379357105 27815838903084589784517829)
        ·
          refine ⟨5215469794328360584597093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27815838903084589784517829 5215469794328360584597093)
          ·
            refine ⟨977900586436567609611955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5215469794328360584597093 977900586436567609611955)
            ·
              refine ⟨1466850879654851414417933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977900586436567609611955 1466850879654851414417933)
              ·
                refine ⟨550069079870569280406725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1466850879654851414417933 550069079870569280406725)
                ·
                  refine ⟨103137952475731740076261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550069079870569280406725 103137952475731740076261)
                  ·
                    rfl

theorem cell22_903872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_903872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903872 prefixEnd_903872 := by exact prefixLift 903872
  have htrace : WordTrace (prefixWord ++ tailWord_903872) baseStart_903872 baseEnd_903872 := by
    simpa [prefixWord, tailWord_903872, baseEnd_903872] using wordTrace_append hprefix tailTrace_903872
  have hstable : (prefixWord ++ tailWord_903872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903872).length < 2 ^ (prefixWord ++ tailWord_903872).sum := by decide
  have hdescent : baseEnd_903872 < baseStart_903872 := by decide
  rcases family_descends (prefixWord ++ tailWord_903872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903900 : List Nat := [2, 2, 5, 1, 1, 1, 1, 9]
def baseStart_903900 : Nat := 118140960795 + 903900 * 2 ^ 59
def prefixEnd_903900 : Nat := 4983230072969 + 3 ^ 40 * 903900 * 2
def baseEnd_903900 : Nat := 34380382488823608947633

theorem tailTrace_903900 : CollatzResearch.WordTrace tailWord_903900 prefixEnd_903900 34380382488823608947633 := by
  unfold tailWord_903900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483970712666074337390577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21978627616888099116520769 16483970712666074337390577)
  ·
    refine ⟨12362978034499555753042933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16483970712666074337390577 12362978034499555753042933)
    ·
      refine ⟨1159029190734333351847775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12362978034499555753042933 1159029190734333351847775)
      ·
        refine ⟨1738543786101500027771663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159029190734333351847775 1738543786101500027771663)
        ·
          refine ⟨2607815679152250041657495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738543786101500027771663 2607815679152250041657495)
          ·
            refine ⟨3911723518728375062486243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607815679152250041657495 3911723518728375062486243)
            ·
              refine ⟨5867585278092562593729365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911723518728375062486243 5867585278092562593729365)
              ·
                refine ⟨34380382488823608947633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5867585278092562593729365 34380382488823608947633)
                ·
                  rfl

theorem cell22_903900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_903900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_903900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_903900 prefixEnd_903900 := by exact prefixLift 903900
  have htrace : WordTrace (prefixWord ++ tailWord_903900) baseStart_903900 baseEnd_903900 := by
    simpa [prefixWord, tailWord_903900, baseEnd_903900] using wordTrace_append hprefix tailTrace_903900
  have hstable : (prefixWord ++ tailWord_903900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903900).length < 2 ^ (prefixWord ++ tailWord_903900).sum := by decide
  have hdescent : baseEnd_903900 < baseStart_903900 := by decide
  rcases family_descends (prefixWord ++ tailWord_903900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904035 : List Nat := [1, 1, 1, 5, 3, 2, 1, 8]
def baseStart_904035 : Nat := 118140960795 + 904035 * 2 ^ 59
def prefixEnd_904035 : Nat := 4983230072969 + 3 ^ 40 * 904035 * 2
def baseEnd_904035 : Nat := 34385517295368569822587

theorem tailTrace_904035 : CollatzResearch.WordTrace tailWord_904035 prefixEnd_904035 34385517295368569822587 := by
  unfold tailWord_904035
  simp only [CollatzResearch.WordTrace]
  refine ⟨32972865279843066730945559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21981910186562044487297039 32972865279843066730945559)
  ·
    refine ⟨49459297919764600096418339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32972865279843066730945559 49459297919764600096418339)
    ·
      refine ⟨74188946879646900144627509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49459297919764600096418339 74188946879646900144627509)
      ·
        refine ⟨6955213769966896888558829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74188946879646900144627509 6955213769966896888558829)
        ·
          refine ⟨2608205163737586333209561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6955213769966896888558829 2608205163737586333209561)
          ·
            refine ⟨1956153872803189749907171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608205163737586333209561 1956153872803189749907171)
            ·
              refine ⟨2934230809204784624860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956153872803189749907171 2934230809204784624860757)
              ·
                refine ⟨34385517295368569822587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2934230809204784624860757 34385517295368569822587)
                ·
                  rfl

theorem cell22_904035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 8].length) (baseStart_904035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904035 prefixEnd_904035 := by exact prefixLift 904035
  have htrace : WordTrace (prefixWord ++ tailWord_904035) baseStart_904035 baseEnd_904035 := by
    simpa [prefixWord, tailWord_904035, baseEnd_904035] using wordTrace_append hprefix tailTrace_904035
  have hstable : (prefixWord ++ tailWord_904035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904035).length < 2 ^ (prefixWord ++ tailWord_904035).sum := by decide
  have hdescent : baseEnd_904035 < baseStart_904035 := by decide
  rcases family_descends (prefixWord ++ tailWord_904035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904054 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_904054 : Nat := 118140960795 + 904054 * 2 ^ 59
def prefixEnd_904054 : Nat := 4983230072969 + 3 ^ 40 * 904054 * 2
def baseEnd_904054 : Nat := 309476159746607412178225

theorem tailTrace_904054 : CollatzResearch.WordTrace tailWord_904054 prefixEnd_904054 309476159746607412178225 := by
  unfold tailWord_904054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060847391673389560992951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21982372177849488650591477 2060847391673389560992951)
  ·
    refine ⟨3091271087510084341489427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060847391673389560992951 3091271087510084341489427)
    ·
      refine ⟨4636906631265126512234141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091271087510084341489427 4636906631265126512234141)
      ·
        refine ⟨1738839986724422442087803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4636906631265126512234141 1738839986724422442087803)
        ·
          refine ⟨2608259980086633663131705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738839986724422442087803 2608259980086633663131705)
          ·
            refine ⟨1956194985064975247348779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608259980086633663131705 1956194985064975247348779)
            ·
              refine ⟨2934292477597462871023169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956194985064975247348779 2934292477597462871023169)
              ·
                refine ⟨2200719358198097153267377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934292477597462871023169 2200719358198097153267377)
                ·
                  refine ⟨1650539518648572864950533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200719358198097153267377 1650539518648572864950533)
                  ·
                    refine ⟨309476159746607412178225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1650539518648572864950533 309476159746607412178225)
                    ·
                      rfl

theorem cell22_904054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_904054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904054 prefixEnd_904054 := by exact prefixLift 904054
  have htrace : WordTrace (prefixWord ++ tailWord_904054) baseStart_904054 baseEnd_904054 := by
    simpa [prefixWord, tailWord_904054, baseEnd_904054] using wordTrace_append hprefix tailTrace_904054
  have hstable : (prefixWord ++ tailWord_904054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904054).length < 2 ^ (prefixWord ++ tailWord_904054).sum := by decide
  have hdescent : baseEnd_904054 < baseStart_904054 := by decide
  rcases family_descends (prefixWord ++ tailWord_904054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904142 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_904142 : Nat := 118140960795 + 904142 * 2 ^ 59
def prefixEnd_904142 : Nat := 4983230072969 + 3 ^ 40 * 904142 * 2
def baseEnd_904142 : Nat := 103168761315001505325985

theorem tailTrace_904142 : CollatzResearch.WordTrace tailWord_904142 prefixEnd_904142 103168761315001505325985 := by
  unfold tailWord_904142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122095986306928000636335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21984511926970282670060453 4122095986306928000636335)
  ·
    refine ⟨6183143979460392000954503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122095986306928000636335 6183143979460392000954503)
    ·
      refine ⟨9274715969190588001431755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6183143979460392000954503 9274715969190588001431755)
      ·
        refine ⟨13912073953785882002147633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9274715969190588001431755 13912073953785882002147633)
        ·
          refine ⟨10434055465339411501610725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13912073953785882002147633 10434055465339411501610725)
          ·
            refine ⟨1956385399751139656552011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10434055465339411501610725 1956385399751139656552011)
            ·
              refine ⟨2934578099626709484828017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956385399751139656552011 2934578099626709484828017)
              ·
                refine ⟨2200933574720032113621013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934578099626709484828017 2200933574720032113621013)
                ·
                  refine ⟨103168761315001505325985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2200933574720032113621013 103168761315001505325985)
                  ·
                    rfl

theorem cell22_904142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_904142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904142 prefixEnd_904142 := by exact prefixLift 904142
  have htrace : WordTrace (prefixWord ++ tailWord_904142) baseStart_904142 baseEnd_904142 := by
    simpa [prefixWord, tailWord_904142, baseEnd_904142] using wordTrace_append hprefix tailTrace_904142
  have hstable : (prefixWord ++ tailWord_904142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904142).length < 2 ^ (prefixWord ++ tailWord_904142).sum := by decide
  have hdescent : baseEnd_904142 < baseStart_904142 := by decide
  rcases family_descends (prefixWord ++ tailWord_904142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904204 : List Nat := [2, 2, 1, 2, 3, 4, 2, 6]
def baseStart_904204 : Nat := 118140960795 + 904204 * 2 ^ 59
def prefixEnd_904204 : Nat := 4983230072969 + 3 ^ 40 * 904204 * 2
def baseEnd_904204 : Nat := 34391945312450780103085

theorem tailTrace_904204 : CollatzResearch.WordTrace tailWord_904204 prefixEnd_904204 34391945312450780103085 := by
  unfold tailWord_904204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16489514608115404296923833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21986019477487205729231777 16489514608115404296923833)
  ·
    refine ⟨12367135956086553222692875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16489514608115404296923833 12367135956086553222692875)
    ·
      refine ⟨18550703934129829834039313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367135956086553222692875 18550703934129829834039313)
      ·
        refine ⟨13913027950597372375529485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18550703934129829834039313 13913027950597372375529485)
        ·
          refine ⟨5217385481474014640823557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13913027950597372375529485 5217385481474014640823557)
          ·
            refine ⟨978259777776377745154417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5217385481474014640823557 978259777776377745154417)
            ·
              refine ⟨733694833332283308865813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978259777776377745154417 733694833332283308865813)
              ·
                refine ⟨34391945312450780103085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 733694833332283308865813 34391945312450780103085)
                ·
                  rfl

theorem cell22_904204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_904204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904204 prefixEnd_904204 := by exact prefixLift 904204
  have htrace : WordTrace (prefixWord ++ tailWord_904204) baseStart_904204 baseEnd_904204 := by
    simpa [prefixWord, tailWord_904204, baseEnd_904204] using wordTrace_append hprefix tailTrace_904204
  have hstable : (prefixWord ++ tailWord_904204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904204).length < 2 ^ (prefixWord ++ tailWord_904204).sum := by decide
  have hdescent : baseEnd_904204 < baseStart_904204 := by decide
  rcases family_descends (prefixWord ++ tailWord_904204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904249 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 5]
def baseStart_904249 : Nat := 118140960795 + 904249 * 2 ^ 59
def prefixEnd_904249 : Nat := 4983230072969 + 3 ^ 40 * 904249 * 2
def baseEnd_904249 : Nat := 103180970743897301184209

theorem tailTrace_904249 : CollatzResearch.WordTrace tailWord_904249 prefixEnd_904249 103180970743897301184209 := by
  unfold tailWord_904249
  simp only [CollatzResearch.WordTrace]
  refine ⟨32980670501067781279235801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21987113667378520852823867 32980670501067781279235801)
  ·
    refine ⟨24735502875800835959426851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32980670501067781279235801 24735502875800835959426851)
    ·
      refine ⟨37103254313701253939140277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24735502875800835959426851 37103254313701253939140277)
      ·
        refine ⟨3478430091909492556794401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37103254313701253939140277 3478430091909492556794401)
        ·
          refine ⟨2608822568932119417595801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3478430091909492556794401 2608822568932119417595801)
          ·
            refine ⟨1956616926699089563196851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608822568932119417595801 1956616926699089563196851)
            ·
              refine ⟨2934925390048634344795277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956616926699089563196851 2934925390048634344795277)
              ·
                refine ⟨1100597021268237879298229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2934925390048634344795277 1100597021268237879298229)
                ·
                  refine ⟨103180970743897301184209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1100597021268237879298229 103180970743897301184209)
                  ·
                    rfl

theorem cell22_904249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_904249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904249 prefixEnd_904249 := by exact prefixLift 904249
  have htrace : WordTrace (prefixWord ++ tailWord_904249) baseStart_904249 baseEnd_904249 := by
    simpa [prefixWord, tailWord_904249, baseEnd_904249] using wordTrace_append hprefix tailTrace_904249
  have hstable : (prefixWord ++ tailWord_904249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904249).length < 2 ^ (prefixWord ++ tailWord_904249).sum := by decide
  have hdescent : baseEnd_904249 < baseStart_904249 := by decide
  rcases family_descends (prefixWord ++ tailWord_904249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904292 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_904292 : Nat := 118140960795 + 904292 * 2 ^ 59
def prefixEnd_904292 : Nat := 4983230072969 + 3 ^ 40 * 904292 * 2
def baseEnd_904292 : Nat := 309557632010454124727495

theorem tailTrace_904292 : CollatzResearch.WordTrace tailWord_904292 prefixEnd_904292 309557632010454124727495 := by
  unfold tailWord_904292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491119419955999811525565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21988159226607999748700753 16491119419955999811525565)
  ·
    refine ⟨6184169782483499929322087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16491119419955999811525565 6184169782483499929322087)
    ·
      refine ⟨9276254673725249893983131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6184169782483499929322087 9276254673725249893983131)
      ·
        refine ⟨13914382010587874840974697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9276254673725249893983131 13914382010587874840974697)
        ·
          refine ⟨10435786507940906130731023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13914382010587874840974697 10435786507940906130731023)
          ·
            refine ⟨15653679761911359196096535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10435786507940906130731023 15653679761911359196096535)
            ·
              refine ⟨23480519642867038794144803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15653679761911359196096535 23480519642867038794144803)
              ·
                refine ⟨35220779464300558191217205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23480519642867038794144803 35220779464300558191217205)
                ·
                  refine ⟨3301948074778177330426613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35220779464300558191217205 3301948074778177330426613)
                  ·
                    refine ⟨309557632010454124727495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3301948074778177330426613 309557632010454124727495)
                    ·
                      rfl

theorem cell22_904292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_904292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904292 prefixEnd_904292 := by exact prefixLift 904292
  have htrace : WordTrace (prefixWord ++ tailWord_904292) baseStart_904292 baseEnd_904292 := by
    simpa [prefixWord, tailWord_904292, baseEnd_904292] using wordTrace_append hprefix tailTrace_904292
  have hstable : (prefixWord ++ tailWord_904292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904292).length < 2 ^ (prefixWord ++ tailWord_904292).sum := by decide
  have hdescent : baseEnd_904292 < baseStart_904292 := by decide
  rcases family_descends (prefixWord ++ tailWord_904292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904324 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_904324 : Nat := 118140960795 + 904324 * 2 ^ 59
def prefixEnd_904324 : Nat := 4983230072969 + 3 ^ 40 * 904324 * 2
def baseEnd_904324 : Nat := 309568586264416707927397

theorem tailTrace_904324 : CollatzResearch.WordTrace tailWord_904324 prefixEnd_904324 309568586264416707927397 := by
  unfold tailWord_904324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491702987898034544108013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21988937317197379392144017 16491702987898034544108013)
  ·
    refine ⟨6184388620461762954040505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16491702987898034544108013 6184388620461762954040505)
    ·
      refine ⟨4638291465346322215530379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6184388620461762954040505 4638291465346322215530379)
      ·
        refine ⟨6957437198019483323295569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638291465346322215530379 6957437198019483323295569)
        ·
          refine ⟨5218077898514612492471677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6957437198019483323295569 5218077898514612492471677)
          ·
            refine ⟨1956779211942979684676879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5218077898514612492471677 1956779211942979684676879)
            ·
              refine ⟨2935168817914469527015319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956779211942979684676879 2935168817914469527015319)
              ·
                refine ⟨4402753226871704290522979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935168817914469527015319 4402753226871704290522979)
                ·
                  refine ⟨6604129840307556435784469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4402753226871704290522979 6604129840307556435784469)
                  ·
                    refine ⟨309568586264416707927397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6604129840307556435784469 309568586264416707927397)
                    ·
                      rfl

theorem cell22_904324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_904324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904324 prefixEnd_904324 := by exact prefixLift 904324
  have htrace : WordTrace (prefixWord ++ tailWord_904324) baseStart_904324 baseEnd_904324 := by
    simpa [prefixWord, tailWord_904324, baseEnd_904324] using wordTrace_append hprefix tailTrace_904324
  have hstable : (prefixWord ++ tailWord_904324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904324).length < 2 ^ (prefixWord ++ tailWord_904324).sum := by decide
  have hdescent : baseEnd_904324 < baseStart_904324 := by decide
  rcases family_descends (prefixWord ++ tailWord_904324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904328 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_904328 : Nat := 118140960795 + 904328 * 2 ^ 59
def prefixEnd_904328 : Nat := 4983230072969 + 3 ^ 40 * 904328 * 2
def baseEnd_904328 : Nat := 103189985182054010275795

theorem tailTrace_904328 : CollatzResearch.WordTrace tailWord_904328 prefixEnd_904328 103189985182054010275795 := by
  unfold tailWord_904328
  simp only [CollatzResearch.WordTrace]
  refine ⟨16491775933890788885680819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21989034578521051847574425 16491775933890788885680819)
  ·
    refine ⟨24737663900836183328521229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16491775933890788885680819 24737663900836183328521229)
    ·
      refine ⟨9276623962813568748195461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24737663900836183328521229 9276623962813568748195461)
      ·
        refine ⟨1739366993027544140286649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9276623962813568748195461 1739366993027544140286649)
        ·
          refine ⟨1304525244770658105214987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739366993027544140286649 1304525244770658105214987)
          ·
            refine ⟨1956787867155987157822481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304525244770658105214987 1956787867155987157822481)
            ·
              refine ⟨1467590900366990368366861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956787867155987157822481 1467590900366990368366861)
              ·
                refine ⟨550346587637621388137573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467590900366990368366861 550346587637621388137573)
                ·
                  refine ⟨103189985182054010275795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 550346587637621388137573 103189985182054010275795)
                  ·
                    rfl

theorem cell22_904328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_904328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904328 prefixEnd_904328 := by exact prefixLift 904328
  have htrace : WordTrace (prefixWord ++ tailWord_904328) baseStart_904328 baseEnd_904328 := by
    simpa [prefixWord, tailWord_904328, baseEnd_904328] using wordTrace_append hprefix tailTrace_904328
  have hstable : (prefixWord ++ tailWord_904328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904328).length < 2 ^ (prefixWord ++ tailWord_904328).sum := by decide
  have hdescent : baseEnd_904328 < baseStart_904328 := by decide
  rcases family_descends (prefixWord ++ tailWord_904328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904343 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 2, 3]
def baseStart_904343 : Nat := 118140960795 + 904343 * 2 ^ 59
def prefixEnd_904343 : Nat := 4983230072969 + 3 ^ 40 * 904343 * 2
def baseEnd_904343 : Nat := 309575090352706991702339

theorem tailTrace_904343 : CollatzResearch.WordTrace tailWord_904343 prefixEnd_904343 309575090352706991702339 := by
  unfold tailWord_904343
  simp only [CollatzResearch.WordTrace]
  refine ⟨32984098962727235333157683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21989399308484823555438455 32984098962727235333157683)
  ·
    refine ⟨49476148444090852999736525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32984098962727235333157683 49476148444090852999736525)
    ·
      refine ⟨18553555666534069874901197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49476148444090852999736525 18553555666534069874901197)
      ·
        refine ⟨6957583374950276203087949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18553555666534069874901197 6957583374950276203087949)
        ·
          refine ⟨2609093765606353576157981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6957583374950276203087949 2609093765606353576157981)
          ·
            refine ⟨978410162102382591059243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2609093765606353576157981 978410162102382591059243)
            ·
              refine ⟨1467615243153573886588865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978410162102382591059243 1467615243153573886588865)
              ·
                refine ⟨1100711432365180414941649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467615243153573886588865 1100711432365180414941649)
                ·
                  refine ⟨825533574273885311206237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100711432365180414941649 825533574273885311206237)
                  ·
                    refine ⟨309575090352706991702339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825533574273885311206237 309575090352706991702339)
                    ·
                      rfl

theorem cell22_904343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_904343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904343 prefixEnd_904343 := by exact prefixLift 904343
  have htrace : WordTrace (prefixWord ++ tailWord_904343) baseStart_904343 baseEnd_904343 := by
    simpa [prefixWord, tailWord_904343, baseEnd_904343] using wordTrace_append hprefix tailTrace_904343
  have hstable : (prefixWord ++ tailWord_904343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904343).length < 2 ^ (prefixWord ++ tailWord_904343).sum := by decide
  have hdescent : baseEnd_904343 < baseStart_904343 := by decide
  rcases family_descends (prefixWord ++ tailWord_904343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904390 : List Nat := [6, 1, 2, 2, 1, 2, 8]
def baseStart_904390 : Nat := 118140960795 + 904390 * 2 ^ 59
def prefixEnd_904390 : Nat := 4983230072969 + 3 ^ 40 * 904390 * 2
def baseEnd_904390 : Nat := 11466339978267205028785

theorem tailTrace_904390 : CollatzResearch.WordTrace tailWord_904390 prefixEnd_904390 11466339978267205028785 := by
  unfold tailWord_904390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030806662298655073753707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21990542129037974906745749 1030806662298655073753707)
  ·
    refine ⟨1546209993447982610630561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1030806662298655073753707 1546209993447982610630561)
    ·
      refine ⟨1159657495085986957972921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1546209993447982610630561 1159657495085986957972921)
      ·
        refine ⟨869743121314490218479691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1159657495085986957972921 869743121314490218479691)
        ·
          refine ⟨1304614681971735327719537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869743121314490218479691 1304614681971735327719537)
          ·
            refine ⟨978461011478801495789653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304614681971735327719537 978461011478801495789653)
            ·
              refine ⟨11466339978267205028785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 978461011478801495789653 11466339978267205028785)
              ·
                rfl

theorem cell22_904390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 8].length) (baseStart_904390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904390 prefixEnd_904390 := by exact prefixLift 904390
  have htrace : WordTrace (prefixWord ++ tailWord_904390) baseStart_904390 baseEnd_904390 := by
    simpa [prefixWord, tailWord_904390, baseEnd_904390] using wordTrace_append hprefix tailTrace_904390
  have hstable : (prefixWord ++ tailWord_904390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904390).length < 2 ^ (prefixWord ++ tailWord_904390).sum := by decide
  have hdescent : baseEnd_904390 < baseStart_904390 := by decide
  rcases family_descends (prefixWord ++ tailWord_904390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904431 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 3, 4]
def baseStart_904431 : Nat := 118140960795 + 904431 * 2 ^ 59
def prefixEnd_904431 : Nat := 4983230072969 + 3 ^ 40 * 904431 * 2
def baseEnd_904431 : Nat := 309605214551104095502069

theorem tailTrace_904431 : CollatzResearch.WordTrace tailWord_904431 prefixEnd_904431 309605214551104095502069 := by
  unfold tailWord_904431
  simp only [CollatzResearch.WordTrace]
  refine ⟨32987308586408426362361147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21991539057605617574907431 32987308586408426362361147)
  ·
    refine ⟨49480962879612639543541721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32987308586408426362361147 49480962879612639543541721)
    ·
      refine ⟨37110722159709479657656291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49480962879612639543541721 37110722159709479657656291)
      ·
        refine ⟨55666083239564219486484437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37110722159709479657656291 55666083239564219486484437)
        ·
          refine ⟨1304673825927286394214479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 55666083239564219486484437 1304673825927286394214479)
          ·
            refine ⟨1957010738890929591321719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304673825927286394214479 1957010738890929591321719)
            ·
              refine ⟨2935516108336394386982579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957010738890929591321719 2935516108336394386982579)
              ·
                refine ⟨4403274162504591580473869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935516108336394386982579 4403274162504591580473869)
                ·
                  refine ⟨1651227810939221842677701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4403274162504591580473869 1651227810939221842677701)
                  ·
                    refine ⟨309605214551104095502069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1651227810939221842677701 309605214551104095502069)
                    ·
                      rfl

theorem cell22_904431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_904431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904431 prefixEnd_904431 := by exact prefixLift 904431
  have htrace : WordTrace (prefixWord ++ tailWord_904431) baseStart_904431 baseEnd_904431 := by
    simpa [prefixWord, tailWord_904431, baseEnd_904431] using wordTrace_append hprefix tailTrace_904431
  have hstable : (prefixWord ++ tailWord_904431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904431).length < 2 ^ (prefixWord ++ tailWord_904431).sum := by decide
  have hdescent : baseEnd_904431 < baseStart_904431 := by decide
  rcases family_descends (prefixWord ++ tailWord_904431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904493 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_904493 : Nat := 118140960795 + 904493 * 2 ^ 59
def prefixEnd_904493 : Nat := 4983230072969 + 3 ^ 40 * 904493 * 2
def baseEnd_904493 : Nat := 309626438418156600451879

theorem tailTrace_904493 : CollatzResearch.WordTrace tailWord_904493 prefixEnd_904493 309626438418156600451879 := by
  unfold tailWord_904493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989569912183810951118133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21993046608122540634078755 32989569912183810951118133)
  ·
    refine ⟨3092772179267232276667325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32989569912183810951118133 3092772179267232276667325)
    ·
      refine ⟨1159789567225212103750247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3092772179267232276667325 1159789567225212103750247)
      ·
        refine ⟨1739684350837818155625371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159789567225212103750247 1739684350837818155625371)
        ·
          refine ⟨2609526526256727233438057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739684350837818155625371 2609526526256727233438057)
          ·
            refine ⟨1957144894692545425078543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609526526256727233438057 1957144894692545425078543)
            ·
              refine ⟨2935717342038818137617815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957144894692545425078543 2935717342038818137617815)
              ·
                refine ⟨4403576013058227206426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935717342038818137617815 4403576013058227206426723)
                ·
                  refine ⟨6605364019587340809640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403576013058227206426723 6605364019587340809640085)
                  ·
                    refine ⟨309626438418156600451879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6605364019587340809640085 309626438418156600451879)
                    ·
                      rfl

theorem cell22_904493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_904493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904493 prefixEnd_904493 := by exact prefixLift 904493
  have htrace : WordTrace (prefixWord ++ tailWord_904493) baseStart_904493 baseEnd_904493 := by
    simpa [prefixWord, tailWord_904493, baseEnd_904493] using wordTrace_append hprefix tailTrace_904493
  have hstable : (prefixWord ++ tailWord_904493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904493).length < 2 ^ (prefixWord ++ tailWord_904493).sum := by decide
  have hdescent : baseEnd_904493 < baseStart_904493 := by decide
  rcases family_descends (prefixWord ++ tailWord_904493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904506 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_904506 : Nat := 118140960795 + 904506 * 2 ^ 59
def prefixEnd_904506 : Nat := 4983230072969 + 3 ^ 40 * 904506 * 2
def baseEnd_904506 : Nat := 309630888583828899876839

theorem tailTrace_904506 : CollatzResearch.WordTrace tailWord_904506 prefixEnd_904506 309630888583828899876839 := by
  unfold tailWord_904506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247511015284178542835343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21993362707424476114227581 8247511015284178542835343)
  ·
    refine ⟨12371266522926267814253015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8247511015284178542835343 12371266522926267814253015)
    ·
      refine ⟨18556899784389401721379523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12371266522926267814253015 18556899784389401721379523)
      ·
        refine ⟨27835349676584102582069285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556899784389401721379523 27835349676584102582069285)
        ·
          refine ⟨5219128064359519234137991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27835349676584102582069285 5219128064359519234137991)
          ·
            refine ⟨7828692096539278851206987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219128064359519234137991 7828692096539278851206987)
            ·
              refine ⟨11743038144808918276810481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828692096539278851206987 11743038144808918276810481)
              ·
                refine ⟨8807278608606688707607861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11743038144808918276810481 8807278608606688707607861)
                ·
                  refine ⟨825682369556877066338237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8807278608606688707607861 825682369556877066338237)
                  ·
                    refine ⟨309630888583828899876839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825682369556877066338237 309630888583828899876839)
                    ·
                      rfl

theorem cell22_904506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_904506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904506 prefixEnd_904506 := by exact prefixLift 904506
  have htrace : WordTrace (prefixWord ++ tailWord_904506) baseStart_904506 baseEnd_904506 := by
    simpa [prefixWord, tailWord_904506, baseEnd_904506] using wordTrace_append hprefix tailTrace_904506
  have hstable : (prefixWord ++ tailWord_904506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904506).length < 2 ^ (prefixWord ++ tailWord_904506).sum := by decide
  have hdescent : baseEnd_904506 < baseStart_904506 := by decide
  rcases family_descends (prefixWord ++ tailWord_904506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904557 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_904557 : Nat := 118140960795 + 904557 * 2 ^ 59
def prefixEnd_904557 : Nat := 4983230072969 + 3 ^ 40 * 904557 * 2
def baseEnd_904557 : Nat := 309648346926081766851683

theorem tailTrace_904557 : CollatzResearch.WordTrace tailWord_904557 prefixEnd_904557 309648346926081766851683 := by
  unfold tailWord_904557
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991904183951949881447925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21994602789301299920965283 32991904183951949881447925)
  ·
    refine ⟨3092991017245495301385743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32991904183951949881447925 3092991017245495301385743)
    ·
      refine ⟨4639486525868242952078615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092991017245495301385743 4639486525868242952078615)
      ·
        refine ⟨6959229788802364428117923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639486525868242952078615 6959229788802364428117923)
        ·
          refine ⟨10438844683203546642176885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959229788802364428117923 10438844683203546642176885)
          ·
            refine ⟨978641689050332497704083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10438844683203546642176885 978641689050332497704083)
            ·
              refine ⟨1467962533575498746556125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978641689050332497704083 1467962533575498746556125)
              ·
                refine ⟨550485950090812029958547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467962533575498746556125 550485950090812029958547)
                ·
                  refine ⟨825728925136218044937821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550485950090812029958547 825728925136218044937821)
                  ·
                    refine ⟨309648346926081766851683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825728925136218044937821 309648346926081766851683)
                    ·
                      rfl

theorem cell22_904557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_904557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904557 prefixEnd_904557 := by exact prefixLift 904557
  have htrace : WordTrace (prefixWord ++ tailWord_904557) baseStart_904557 baseEnd_904557 := by
    simpa [prefixWord, tailWord_904557, baseEnd_904557] using wordTrace_append hprefix tailTrace_904557
  have hstable : (prefixWord ++ tailWord_904557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904557).length < 2 ^ (prefixWord ++ tailWord_904557).sum := by decide
  have hdescent : baseEnd_904557 < baseStart_904557 := by decide
  rcases family_descends (prefixWord ++ tailWord_904557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904574 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_904574 : Nat := 118140960795 + 904574 * 2 ^ 59
def prefixEnd_904574 : Nat := 4983230072969 + 3 ^ 40 * 904574 * 2
def baseEnd_904574 : Nat := 309654166373499389176631

theorem tailTrace_904574 : CollatzResearch.WordTrace tailWord_904574 prefixEnd_904574 309654166373499389176631 := by
  unfold tailWord_904574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124065528111295223102097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21995016149926907856544517 4124065528111295223102097)
  ·
    refine ⟨3093049146083471417326573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4124065528111295223102097 3093049146083471417326573)
    ·
      refine ⟨1159893429781301781497465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3093049146083471417326573 1159893429781301781497465)
      ·
        refine ⟨869920072335976336123099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1159893429781301781497465 869920072335976336123099)
        ·
          refine ⟨1304880108503964504184649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869920072335976336123099 1304880108503964504184649)
          ·
            refine ⟨978660081377973378138487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304880108503964504184649 978660081377973378138487)
            ·
              refine ⟨1467990122066960067207731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978660081377973378138487 1467990122066960067207731)
              ·
                refine ⟨2201985183100440100811597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467990122066960067207731 2201985183100440100811597)
                ·
                  refine ⟨825744443662665037804349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2201985183100440100811597 825744443662665037804349)
                  ·
                    refine ⟨309654166373499389176631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 825744443662665037804349 309654166373499389176631)
                    ·
                      rfl

theorem cell22_904574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_904574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904574 prefixEnd_904574 := by exact prefixLift 904574
  have htrace : WordTrace (prefixWord ++ tailWord_904574) baseStart_904574 baseEnd_904574 := by
    simpa [prefixWord, tailWord_904574, baseEnd_904574] using wordTrace_append hprefix tailTrace_904574
  have hstable : (prefixWord ++ tailWord_904574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904574).length < 2 ^ (prefixWord ++ tailWord_904574).sum := by decide
  have hdescent : baseEnd_904574 < baseStart_904574 := by decide
  rcases family_descends (prefixWord ++ tailWord_904574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904581 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 6]
def baseStart_904581 : Nat := 118140960795 + 904581 * 2 ^ 59
def prefixEnd_904581 : Nat := 4983230072969 + 3 ^ 40 * 904581 * 2
def baseEnd_904581 : Nat := 103218854205517901417203

theorem tailTrace_904581 : CollatzResearch.WordTrace tailWord_904581 prefixEnd_904581 103218854205517901417203 := by
  unfold tailWord_904581
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992779535865001980321597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21995186357243334653547731 32992779535865001980321597)
  ·
    refine ⟨12372292325949375742620599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32992779535865001980321597 12372292325949375742620599)
    ·
      refine ⟨18558438488924063613930899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12372292325949375742620599 18558438488924063613930899)
      ·
        refine ⟨27837657733386095420896349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18558438488924063613930899 27837657733386095420896349)
        ·
          refine ⟨10439121650019785782836131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27837657733386095420896349 10439121650019785782836131)
          ·
            refine ⟨15658682475029678674254197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439121650019785782836131 15658682475029678674254197)
            ·
              refine ⟨1468001482034032375711331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15658682475029678674254197 1468001482034032375711331)
              ·
                refine ⟨2202002223051048563566997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468001482034032375711331 2202002223051048563566997)
                ·
                  refine ⟨103218854205517901417203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2202002223051048563566997 103218854205517901417203)
                  ·
                    rfl

theorem cell22_904581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_904581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904581 prefixEnd_904581 := by exact prefixLift 904581
  have htrace : WordTrace (prefixWord ++ tailWord_904581) baseStart_904581 baseEnd_904581 := by
    simpa [prefixWord, tailWord_904581, baseEnd_904581] using wordTrace_append hprefix tailTrace_904581
  have hstable : (prefixWord ++ tailWord_904581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904581).length < 2 ^ (prefixWord ++ tailWord_904581).sum := by decide
  have hdescent : baseEnd_904581 < baseStart_904581 := by decide
  rcases family_descends (prefixWord ++ tailWord_904581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904660 : List Nat := [2, 4, 1, 2, 3, 1, 3, 6]
def baseStart_904660 : Nat := 118140960795 + 904660 * 2 ^ 59
def prefixEnd_904660 : Nat := 4983230072969 + 3 ^ 40 * 904660 * 2
def baseEnd_904660 : Nat := 34409289547891536836263

theorem tailTrace_904660 : CollatzResearch.WordTrace tailWord_904660 prefixEnd_904660 34409289547891536836263 := by
  unfold tailWord_904660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16497830451289399236223717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21997107268385865648298289 16497830451289399236223717)
  ·
    refine ⟨3093343209616762356791947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16497830451289399236223717 3093343209616762356791947)
    ·
      refine ⟨4640014814425143535187921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3093343209616762356791947 4640014814425143535187921)
      ·
        refine ⟨3480011110818857651390941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4640014814425143535187921 3480011110818857651390941)
        ·
          refine ⟨1305004166557071619271603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3480011110818857651390941 1305004166557071619271603)
          ·
            refine ⟨1957506249835607428907405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305004166557071619271603 1957506249835607428907405)
            ·
              refine ⟨734064843688352785840277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957506249835607428907405 734064843688352785840277)
              ·
                refine ⟨34409289547891536836263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 734064843688352785840277 34409289547891536836263)
                ·
                  rfl

theorem cell22_904660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_904660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904660 prefixEnd_904660 := by exact prefixLift 904660
  have htrace : WordTrace (prefixWord ++ tailWord_904660) baseStart_904660 baseEnd_904660 := by
    simpa [prefixWord, tailWord_904660, baseEnd_904660] using wordTrace_append hprefix tailTrace_904660
  have hstable : (prefixWord ++ tailWord_904660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904660).length < 2 ^ (prefixWord ++ tailWord_904660).sum := by decide
  have hdescent : baseEnd_904660 < baseStart_904660 := by decide
  rcases family_descends (prefixWord ++ tailWord_904660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904662 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_904662 : Nat := 118140960795 + 904662 * 2 ^ 59
def prefixEnd_904662 : Nat := 4983230072969 + 3 ^ 40 * 904662 * 2
def baseEnd_904662 : Nat := 309684290571896492976361

theorem tailTrace_904662 : CollatzResearch.WordTrace tailWord_904662 prefixEnd_904662 309684290571896492976361 := by
  unfold tailWord_904662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062233365535722050876265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21997155899047701876013493 2062233365535722050876265)
  ·
    refine ⟨1546675024151791538157199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2062233365535722050876265 1546675024151791538157199)
    ·
      refine ⟨2320012536227687307235799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1546675024151791538157199 2320012536227687307235799)
      ·
        refine ⟨3480018804341530960853699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320012536227687307235799 3480018804341530960853699)
        ·
          refine ⟨5220028206512296441280549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480018804341530960853699 5220028206512296441280549)
          ·
            refine ⟨978755288721055582740103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5220028206512296441280549 978755288721055582740103)
            ·
              refine ⟨1468132933081583374110155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978755288721055582740103 1468132933081583374110155)
              ·
                refine ⟨2202199399622375061165233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468132933081583374110155 2202199399622375061165233)
                ·
                  refine ⟨1651649549716781295873925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202199399622375061165233 1651649549716781295873925)
                  ·
                    refine ⟨309684290571896492976361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1651649549716781295873925 309684290571896492976361)
                    ·
                      rfl

theorem cell22_904662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_904662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904662 prefixEnd_904662 := by exact prefixLift 904662
  have htrace : WordTrace (prefixWord ++ tailWord_904662) baseStart_904662 baseEnd_904662 := by
    simpa [prefixWord, tailWord_904662, baseEnd_904662] using wordTrace_append hprefix tailTrace_904662
  have hstable : (prefixWord ++ tailWord_904662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904662).length < 2 ^ (prefixWord ++ tailWord_904662).sum := by decide
  have hdescent : baseEnd_904662 < baseStart_904662 := by decide
  rcases family_descends (prefixWord ++ tailWord_904662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904671 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 7]
def baseStart_904671 : Nat := 118140960795 + 904671 * 2 ^ 59
def prefixEnd_904671 : Nat := 4983230072969 + 3 ^ 40 * 904671 * 2
def baseEnd_904671 : Nat := 103229123818607823167111

theorem tailTrace_904671 : CollatzResearch.WordTrace tailWord_904671 prefixEnd_904671 103229123818607823167111 := by
  unfold tailWord_904671
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996062105538947351097867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21997374737025964900731911 32996062105538947351097867)
  ·
    refine ⟨49494093158308421026646801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32996062105538947351097867 49494093158308421026646801)
    ·
      refine ⟨37120569868731315769985101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49494093158308421026646801 37120569868731315769985101)
      ·
        refine ⟨13920213700774243413744413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37120569868731315769985101 13920213700774243413744413)
        ·
          refine ⟨5220080137790341280154155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13920213700774243413744413 5220080137790341280154155)
          ·
            refine ⟨7830120206685511920231233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220080137790341280154155 7830120206685511920231233)
            ·
              refine ⟨5872590155014133940173425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830120206685511920231233 5872590155014133940173425)
              ·
                refine ⟨4404442616260600455130069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5872590155014133940173425 4404442616260600455130069)
                ·
                  refine ⟨103229123818607823167111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4404442616260600455130069 103229123818607823167111)
                  ·
                    rfl

theorem cell22_904671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_904671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904671 prefixEnd_904671 := by exact prefixLift 904671
  have htrace : WordTrace (prefixWord ++ tailWord_904671) baseStart_904671 baseEnd_904671 := by
    simpa [prefixWord, tailWord_904671, baseEnd_904671] using wordTrace_append hprefix tailTrace_904671
  have hstable : (prefixWord ++ tailWord_904671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904671).length < 2 ^ (prefixWord ++ tailWord_904671).sum := by decide
  have hdescent : baseEnd_904671 < baseStart_904671 := by decide
  rcases family_descends (prefixWord ++ tailWord_904671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904688 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_904688 : Nat := 118140960795 + 904688 * 2 ^ 59
def prefixEnd_904688 : Nat := 4983230072969 + 3 ^ 40 * 904688 * 2
def baseEnd_904688 : Nat := 103231063634413697275427

theorem tailTrace_904688 : CollatzResearch.WordTrace tailWord_904688 prefixEnd_904688 103231063634413697275427 := by
  unfold tailWord_904688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16498341073238679627233359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21997788097651572836311145 16498341073238679627233359)
  ·
    refine ⟨24747511609858019440850039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16498341073238679627233359 24747511609858019440850039)
    ·
      refine ⟨37121267414787029161275059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24747511609858019440850039 37121267414787029161275059)
      ·
        refine ⟨55681901122180543741912589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37121267414787029161275059 55681901122180543741912589)
        ·
          refine ⟨20880712920817703903217221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55681901122180543741912589 20880712920817703903217221)
          ·
            refine ⟨3915133672653319481853229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20880712920817703903217221 3915133672653319481853229)
            ·
              refine ⟨1468175127244994805694961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915133672653319481853229 1468175127244994805694961)
              ·
                refine ⟨1101131345433746104271221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468175127244994805694961 1101131345433746104271221)
                ·
                  refine ⟨103231063634413697275427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1101131345433746104271221 103231063634413697275427)
                  ·
                    rfl

theorem cell22_904688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_904688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904688 prefixEnd_904688 := by exact prefixLift 904688
  have htrace : WordTrace (prefixWord ++ tailWord_904688) baseStart_904688 baseEnd_904688 := by
    simpa [prefixWord, tailWord_904688, baseEnd_904688] using wordTrace_append hprefix tailTrace_904688
  have hstable : (prefixWord ++ tailWord_904688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904688).length < 2 ^ (prefixWord ++ tailWord_904688).sum := by decide
  have hdescent : baseEnd_904688 < baseStart_904688 := by decide
  rcases family_descends (prefixWord ++ tailWord_904688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904750 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_904750 : Nat := 118140960795 + 904750 * 2 ^ 59
def prefixEnd_904750 : Nat := 4983230072969 + 3 ^ 40 * 904750 * 2
def baseEnd_904750 : Nat := 103238138256764532258697

theorem tailTrace_904750 : CollatzResearch.WordTrace tailWord_904750 prefixEnd_904750 103238138256764532258697 := by
  unfold tailWord_904750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4124867934031592980402963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21999295648168495895482469 4124867934031592980402963)
  ·
    refine ⟨6187301901047389470604445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4124867934031592980402963 6187301901047389470604445)
    ·
      refine ⟨2320238212892771051476667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6187301901047389470604445 2320238212892771051476667)
      ·
        refine ⟨3480357319339156577215001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320238212892771051476667 3480357319339156577215001)
        ·
          refine ⟨2610267989504367432911251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3480357319339156577215001 2610267989504367432911251)
          ·
            refine ⟨3915401984256551149366877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610267989504367432911251 3915401984256551149366877)
            ·
              refine ⟨1468275744096206681012579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915401984256551149366877 1468275744096206681012579)
              ·
                refine ⟨2202413616144310021518869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468275744096206681012579 2202413616144310021518869)
                ·
                  refine ⟨103238138256764532258697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2202413616144310021518869 103238138256764532258697)
                  ·
                    rfl

theorem cell22_904750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_904750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904750 prefixEnd_904750 := by exact prefixLift 904750
  have htrace : WordTrace (prefixWord ++ tailWord_904750) baseStart_904750 baseEnd_904750 := by
    simpa [prefixWord, tailWord_904750, baseEnd_904750] using wordTrace_append hprefix tailTrace_904750
  have hstable : (prefixWord ++ tailWord_904750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904750).length < 2 ^ (prefixWord ++ tailWord_904750).sum := by decide
  have hdescent : baseEnd_904750 < baseStart_904750 := by decide
  rcases family_descends (prefixWord ++ tailWord_904750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904780 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_904780 : Nat := 118140960795 + 904780 * 2 ^ 59
def prefixEnd_904780 : Nat := 4983230072969 + 3 ^ 40 * 904780 * 2
def baseEnd_904780 : Nat := 309724684383383518525999

theorem tailTrace_904780 : CollatzResearch.WordTrace tailWord_904780 prefixEnd_904780 309724684383383518525999 := by
  unfold tailWord_904780
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500018831072029483407897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22000025108096039311210529 16500018831072029483407897)
  ·
    refine ⟨12375014123304022112555923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16500018831072029483407897 12375014123304022112555923)
    ·
      refine ⟨18562521184956033168833885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375014123304022112555923 18562521184956033168833885)
      ·
        refine ⟨6960945444358512438312707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18562521184956033168833885 6960945444358512438312707)
        ·
          refine ⟨10441418166537768657469061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960945444358512438312707 10441418166537768657469061)
          ·
            refine ⟨1957765906225831623275449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10441418166537768657469061 1957765906225831623275449)
            ·
              refine ⟨1468324429669373717456587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957765906225831623275449 1468324429669373717456587)
              ·
                refine ⟨2202486644504060576184881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468324429669373717456587 2202486644504060576184881)
                ·
                  refine ⟨1651864983378045432138661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2202486644504060576184881 1651864983378045432138661)
                  ·
                    refine ⟨309724684383383518525999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1651864983378045432138661 309724684383383518525999)
                    ·
                      rfl

theorem cell22_904780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_904780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904780 prefixEnd_904780 := by exact prefixLift 904780
  have htrace : WordTrace (prefixWord ++ tailWord_904780) baseStart_904780 baseEnd_904780 := by
    simpa [prefixWord, tailWord_904780, baseEnd_904780] using wordTrace_append hprefix tailTrace_904780
  have hstable : (prefixWord ++ tailWord_904780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904780).length < 2 ^ (prefixWord ++ tailWord_904780).sum := by decide
  have hdescent : baseEnd_904780 < baseStart_904780 := by decide
  rcases family_descends (prefixWord ++ tailWord_904780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904887 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 1, 4]
def baseStart_904887 : Nat := 118140960795 + 904887 * 2 ^ 59
def prefixEnd_904887 : Nat := 4983230072969 + 3 ^ 40 * 904887 * 2
def baseEnd_904887 : Nat := 309761312670070906100671

theorem tailTrace_904887 : CollatzResearch.WordTrace tailWord_904887 prefixEnd_904887 309761312670070906100671 := by
  unfold tailWord_904887
  simp only [CollatzResearch.WordTrace]
  refine ⟨33003940272756416240960915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22002626848504277493973943 33003940272756416240960915)
  ·
    refine ⟨49505910409134624361441373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33003940272756416240960915 49505910409134624361441373)
    ·
      refine ⟨18564716403425484135540515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49505910409134624361441373 18564716403425484135540515)
      ·
        refine ⟨27847074605138226203310773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18564716403425484135540515 27847074605138226203310773)
        ·
          refine ⟨2610663244231708706560385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27847074605138226203310773 2610663244231708706560385)
          ·
            refine ⟨1957997433173781529920289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2610663244231708706560385 1957997433173781529920289)
            ·
              refine ⟨1468498074880336147440217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957997433173781529920289 1468498074880336147440217)
              ·
                refine ⟨1101373556160252110580163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468498074880336147440217 1101373556160252110580163)
                ·
                  refine ⟨1652060334240378165870245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101373556160252110580163 1652060334240378165870245)
                  ·
                    refine ⟨309761312670070906100671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652060334240378165870245 309761312670070906100671)
                    ·
                      rfl

theorem cell22_904887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_904887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904887 prefixEnd_904887 := by exact prefixLift 904887
  have htrace : WordTrace (prefixWord ++ tailWord_904887) baseStart_904887 baseEnd_904887 := by
    simpa [prefixWord, tailWord_904887, baseEnd_904887] using wordTrace_append hprefix tailTrace_904887
  have hstable : (prefixWord ++ tailWord_904887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904887).length < 2 ^ (prefixWord ++ tailWord_904887).sum := by decide
  have hdescent : baseEnd_904887 < baseStart_904887 := by decide
  rcases family_descends (prefixWord ++ tailWord_904887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904900 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_904900 : Nat := 118140960795 + 904900 * 2 ^ 59
def prefixEnd_904900 : Nat := 4983230072969 + 3 ^ 40 * 904900 * 2
def baseEnd_904900 : Nat := 309765762835743205525631

theorem tailTrace_904900 : CollatzResearch.WordTrace tailWord_904900 prefixEnd_904900 309765762835743205525631 := by
  unfold tailWord_904900
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502207210854659730592077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22002942947806212974122769 16502207210854659730592077)
  ·
    refine ⟨6188327704070497398972029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16502207210854659730592077 6188327704070497398972029)
    ·
      refine ⟨2320622889026436524614511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6188327704070497398972029 2320622889026436524614511)
      ·
        refine ⟨3480934333539654786921767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320622889026436524614511 3480934333539654786921767)
        ·
          refine ⟨5221401500309482180382651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480934333539654786921767 5221401500309482180382651)
          ·
            refine ⟨7832102250464223270573977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221401500309482180382651 7832102250464223270573977)
            ·
              refine ⟨5874076687848167452930483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832102250464223270573977 5874076687848167452930483)
              ·
                refine ⟨8811115031772251179395725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874076687848167452930483 8811115031772251179395725)
                ·
                  refine ⟨3304168136914594192273397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8811115031772251179395725 3304168136914594192273397)
                  ·
                    refine ⟨309765762835743205525631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3304168136914594192273397 309765762835743205525631)
                    ·
                      rfl

theorem cell22_904900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_904900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904900 prefixEnd_904900 := by exact prefixLift 904900
  have htrace : WordTrace (prefixWord ++ tailWord_904900) baseStart_904900 baseEnd_904900 := by
    simpa [prefixWord, tailWord_904900, baseEnd_904900] using wordTrace_append hprefix tailTrace_904900
  have hstable : (prefixWord ++ tailWord_904900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904900).length < 2 ^ (prefixWord ++ tailWord_904900).sum := by decide
  have hdescent : baseEnd_904900 < baseStart_904900 := by decide
  rcases family_descends (prefixWord ++ tailWord_904900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904913 : List Nat := [1, 2, 2, 1, 2, 4, 10]
def baseStart_904913 : Nat := 118140960795 + 904913 * 2 ^ 59
def prefixEnd_904913 : Nat := 4983230072969 + 3 ^ 40 * 904913 * 2
def baseEnd_904913 : Nat := 11472970851904277961133

theorem tailTrace_904913 : CollatzResearch.WordTrace tailWord_904913 prefixEnd_904913 11472970851904277961133 := by
  unfold tailWord_904913
  simp only [CollatzResearch.WordTrace]
  refine ⟨33004888570662222681407393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22003259047108148454271595 33004888570662222681407393)
  ·
    refine ⟨24753666427996667011055545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33004888570662222681407393 24753666427996667011055545)
    ·
      refine ⟨18565249820997500258291659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24753666427996667011055545 18565249820997500258291659)
      ·
        refine ⟨27847874731496250387437489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18565249820997500258291659 27847874731496250387437489)
        ·
          refine ⟨20885906048622187790578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27847874731496250387437489 20885906048622187790578117)
          ·
            refine ⟨3916107384116660210733397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20885906048622187790578117 3916107384116660210733397)
            ·
              refine ⟨11472970851904277961133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3916107384116660210733397 11472970851904277961133)
              ·
                rfl

theorem cell22_904913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 10].length) (baseStart_904913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_904913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_904913 prefixEnd_904913 := by exact prefixLift 904913
  have htrace : WordTrace (prefixWord ++ tailWord_904913) baseStart_904913 baseEnd_904913 := by
    simpa [prefixWord, tailWord_904913, baseEnd_904913] using wordTrace_append hprefix tailTrace_904913
  have hstable : (prefixWord ++ tailWord_904913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904913).length < 2 ^ (prefixWord ++ tailWord_904913).sum := by decide
  have hdescent : baseEnd_904913 < baseStart_904913 := by decide
  rcases family_descends (prefixWord ++ tailWord_904913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905050 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_905050 : Nat := 118140960795 + 905050 * 2 ^ 59
def prefixEnd_905050 : Nat := 4983230072969 + 3 ^ 40 * 905050 * 2
def baseEnd_905050 : Nat := 309817110901192814275171

theorem tailTrace_905050 : CollatzResearch.WordTrace tailWord_905050 prefixEnd_905050 309817110901192814275171 := by
  unfold tailWord_905050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8252471342791473769786151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22006590247443930052763069 8252471342791473769786151)
  ·
    refine ⟨12378707014187210654679227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8252471342791473769786151 12378707014187210654679227)
    ·
      refine ⟨18568060521280815982018841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12378707014187210654679227 18568060521280815982018841)
      ·
        refine ⟨13926045390960611986514131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18568060521280815982018841 13926045390960611986514131)
        ·
          refine ⟨20889068086440917979771197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926045390960611986514131 20889068086440917979771197)
          ·
            refine ⟨7833400532415344242414199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889068086440917979771197 7833400532415344242414199)
            ·
              refine ⟨11750100798623016363621299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833400532415344242414199 11750100798623016363621299)
              ·
                refine ⟨17625151197934524545431949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750100798623016363621299 17625151197934524545431949)
                ·
                  refine ⟨6609431699225446704536981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17625151197934524545431949 6609431699225446704536981)
                  ·
                    refine ⟨309817110901192814275171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6609431699225446704536981 309817110901192814275171)
                    ·
                      rfl

theorem cell22_905050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_905050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905050 prefixEnd_905050 := by exact prefixLift 905050
  have htrace : WordTrace (prefixWord ++ tailWord_905050) baseStart_905050 baseEnd_905050 := by
    simpa [prefixWord, tailWord_905050, baseEnd_905050] using wordTrace_append hprefix tailTrace_905050
  have hstable : (prefixWord ++ tailWord_905050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905050).length < 2 ^ (prefixWord ++ tailWord_905050).sum := by decide
  have hdescent : baseEnd_905050 < baseStart_905050 := by decide
  rcases family_descends (prefixWord ++ tailWord_905050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905086 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_905086 : Nat := 118140960795 + 905086 * 2 ^ 59
def prefixEnd_905086 : Nat := 4983230072969 + 3 ^ 40 * 905086 * 2
def baseEnd_905086 : Nat := 309829434436900720375061

theorem tailTrace_905086 : CollatzResearch.WordTrace tailWord_905086 prefixEnd_905086 309829434436900720375061 := by
  unfold tailWord_905086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126399799879434153431889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22007465599356982151636741 4126399799879434153431889)
  ·
    refine ⟨3094799849909575615073917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4126399799879434153431889 3094799849909575615073917)
    ·
      refine ⟨1160549943716090855652719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3094799849909575615073917 1160549943716090855652719)
      ·
        refine ⟨1740824915574136283479079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160549943716090855652719 1740824915574136283479079)
        ·
          refine ⟨2611237373361204425218619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740824915574136283479079 2611237373361204425218619)
          ·
            refine ⟨3916856060041806637827929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611237373361204425218619 3916856060041806637827929)
            ·
              refine ⟨2937642045031354978370947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916856060041806637827929 2937642045031354978370947)
              ·
                refine ⟨4406463067547032467556421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937642045031354978370947 4406463067547032467556421)
                ·
                  refine ⟨826211825165068587666829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4406463067547032467556421 826211825165068587666829)
                  ·
                    refine ⟨309829434436900720375061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826211825165068587666829 309829434436900720375061)
                    ·
                      rfl

theorem cell22_905086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_905086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905086 prefixEnd_905086 := by exact prefixLift 905086
  have htrace : WordTrace (prefixWord ++ tailWord_905086) baseStart_905086 baseEnd_905086 := by
    simpa [prefixWord, tailWord_905086, baseEnd_905086] using wordTrace_append hprefix tailTrace_905086
  have hstable : (prefixWord ++ tailWord_905086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905086).length < 2 ^ (prefixWord ++ tailWord_905086).sum := by decide
  have hdescent : baseEnd_905086 < baseStart_905086 := by decide
  rcases family_descends (prefixWord ++ tailWord_905086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905118 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_905118 : Nat := 118140960795 + 905118 * 2 ^ 59
def prefixEnd_905118 : Nat := 4983230072969 + 3 ^ 40 * 905118 * 2
def baseEnd_905118 : Nat := 309840388690863303574963

theorem tailTrace_905118 : CollatzResearch.WordTrace tailWord_905118 prefixEnd_905118 309840388690863303574963 := by
  unfold tailWord_905118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126545691864942836577501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22008243689946361795080005 4126545691864942836577501)
  ·
    refine ⟨1547454634449353563716563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4126545691864942836577501 1547454634449353563716563)
    ·
      refine ⟨2321181951674030345574845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547454634449353563716563 2321181951674030345574845)
      ·
        refine ⟨870443231877761379590567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2321181951674030345574845 870443231877761379590567)
        ·
          refine ⟨1305664847816642069385851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870443231877761379590567 1305664847816642069385851)
          ·
            refine ⟨1958497271724963104078777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305664847816642069385851 1958497271724963104078777)
            ·
              refine ⟨1468872953793722328059083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958497271724963104078777 1468872953793722328059083)
              ·
                refine ⟨2203309430690583492088625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1468872953793722328059083 2203309430690583492088625)
                ·
                  refine ⟨1652482073017937619066469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2203309430690583492088625 1652482073017937619066469)
                  ·
                    refine ⟨309840388690863303574963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652482073017937619066469 309840388690863303574963)
                    ·
                      rfl

theorem cell22_905118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_905118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905118 prefixEnd_905118 := by exact prefixLift 905118
  have htrace : WordTrace (prefixWord ++ tailWord_905118) baseStart_905118 baseEnd_905118 := by
    simpa [prefixWord, tailWord_905118, baseEnd_905118] using wordTrace_append hprefix tailTrace_905118
  have hstable : (prefixWord ++ tailWord_905118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905118).length < 2 ^ (prefixWord ++ tailWord_905118).sum := by decide
  have hdescent : baseEnd_905118 < baseStart_905118 := by decide
  rcases family_descends (prefixWord ++ tailWord_905118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905191 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 1, 4]
def baseStart_905191 : Nat := 118140960795 + 905191 * 2 ^ 59
def prefixEnd_905191 : Nat := 4983230072969 + 3 ^ 40 * 905191 * 2
def baseEnd_905191 : Nat := 309865378082715446499739

theorem tailTrace_905191 : CollatzResearch.WordTrace tailWord_905191 prefixEnd_905191 309865378082715446499739 := by
  unfold tailWord_905191
  simp only [CollatzResearch.WordTrace]
  refine ⟨33015028063655076160027427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22010018709103384106684951 33015028063655076160027427)
  ·
    refine ⟨49522542095482614240041141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33015028063655076160027427 49522542095482614240041141)
    ·
      refine ⟨4642738321451495085003857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49522542095482614240041141 4642738321451495085003857)
      ·
        refine ⟨3482053741088621313752893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4642738321451495085003857 3482053741088621313752893)
        ·
          refine ⟨1305770152908232992657335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3482053741088621313752893 1305770152908232992657335)
          ·
            refine ⟨1958655229362349488986003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305770152908232992657335 1958655229362349488986003)
            ·
              refine ⟨2937982844043524233479005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958655229362349488986003 2937982844043524233479005)
              ·
                refine ⟨1101743566516321587554627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2937982844043524233479005 1101743566516321587554627)
                ·
                  refine ⟨1652615349774482381331941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1101743566516321587554627 1652615349774482381331941)
                  ·
                    refine ⟨309865378082715446499739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1652615349774482381331941 309865378082715446499739)
                    ·
                      rfl

theorem cell22_905191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_905191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905191 prefixEnd_905191 := by exact prefixLift 905191
  have htrace : WordTrace (prefixWord ++ tailWord_905191) baseStart_905191 baseEnd_905191 := by
    simpa [prefixWord, tailWord_905191, baseEnd_905191] using wordTrace_append hprefix tailTrace_905191
  have hstable : (prefixWord ++ tailWord_905191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905191).length < 2 ^ (prefixWord ++ tailWord_905191).sum := by decide
  have hdescent : baseEnd_905191 < baseStart_905191 := by decide
  rcases family_descends (prefixWord ++ tailWord_905191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905206 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_905206 : Nat := 118140960795 + 905206 * 2 ^ 59
def prefixEnd_905206 : Nat := 4983230072969 + 3 ^ 40 * 905206 * 2
def baseEnd_905206 : Nat := 103290170963086802458231

theorem tailTrace_905206 : CollatzResearch.WordTrace tailWord_905206 prefixEnd_905206 103290170963086802458231 := by
  unfold tailWord_905206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063473447412545857613967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22010383439067155814548981 2063473447412545857613967)
  ·
    refine ⟨3095210171118818786420951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063473447412545857613967 3095210171118818786420951)
    ·
      refine ⟨4642815256678228179631427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095210171118818786420951 4642815256678228179631427)
      ·
        refine ⟨6964222885017342269447141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642815256678228179631427 6964222885017342269447141)
        ·
          refine ⟨1305791790940751675521339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6964222885017342269447141 1305791790940751675521339)
          ·
            refine ⟨1958687686411127513282009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305791790940751675521339 1958687686411127513282009)
            ·
              refine ⟨1469015764808345634961507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958687686411127513282009 1469015764808345634961507)
              ·
                refine ⟨2203523647212518452442261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469015764808345634961507 2203523647212518452442261)
                ·
                  refine ⟨103290170963086802458231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2203523647212518452442261 103290170963086802458231)
                  ·
                    rfl

theorem cell22_905206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_905206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905206 prefixEnd_905206 := by exact prefixLift 905206
  have htrace : WordTrace (prefixWord ++ tailWord_905206) baseStart_905206 baseEnd_905206 := by
    simpa [prefixWord, tailWord_905206, baseEnd_905206] using wordTrace_append hprefix tailTrace_905206
  have hstable : (prefixWord ++ tailWord_905206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905206).length < 2 ^ (prefixWord ++ tailWord_905206).sum := by decide
  have hdescent : baseEnd_905206 < baseStart_905206 := by decide
  rcases family_descends (prefixWord ++ tailWord_905206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905217 : List Nat := [1, 2, 4, 1, 2, 1, 2, 9]
def baseStart_905217 : Nat := 118140960795 + 905217 * 2 ^ 59
def prefixEnd_905217 : Nat := 4983230072969 + 3 ^ 40 * 905217 * 2
def baseEnd_905217 : Nat := 34430475379340005038851

theorem tailTrace_905217 : CollatzResearch.WordTrace tailWord_905217 prefixEnd_905217 34430475379340005038851 := by
  unfold tailWord_905217
  simp only [CollatzResearch.WordTrace]
  refine ⟨33015976361560882600473905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22010650907707255066982603 33015976361560882600473905)
  ·
    refine ⟨24761982271170661950355429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33015976361560882600473905 24761982271170661950355429)
    ·
      refine ⟨4642871675844499115691643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24761982271170661950355429 4642871675844499115691643)
      ·
        refine ⟨6964307513766748673537465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642871675844499115691643 6964307513766748673537465)
        ·
          refine ⟨5223230635325061505153099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6964307513766748673537465 5223230635325061505153099)
          ·
            refine ⟨7834845952987592257729649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223230635325061505153099 7834845952987592257729649)
            ·
              refine ⟨5876134464740694193297237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834845952987592257729649 5876134464740694193297237)
              ·
                refine ⟨34430475379340005038851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5876134464740694193297237 34430475379340005038851)
                ·
                  rfl

theorem cell22_905217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 9].length) (baseStart_905217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905217 prefixEnd_905217 := by exact prefixLift 905217
  have htrace : WordTrace (prefixWord ++ tailWord_905217) baseStart_905217 baseEnd_905217 := by
    simpa [prefixWord, tailWord_905217, baseEnd_905217] using wordTrace_append hprefix tailTrace_905217
  have hstable : (prefixWord ++ tailWord_905217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905217).length < 2 ^ (prefixWord ++ tailWord_905217).sum := by decide
  have hdescent : baseEnd_905217 < baseStart_905217 := by decide
  rcases family_descends (prefixWord ++ tailWord_905217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905266 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_905266 : Nat := 118140960795 + 905266 * 2 ^ 59
def prefixEnd_905266 : Nat := 4983230072969 + 3 ^ 40 * 905266 * 2
def baseEnd_905266 : Nat := 309891052115440250874509

theorem tailTrace_905266 : CollatzResearch.WordTrace tailWord_905266 prefixEnd_905266 309891052115440250874509 := by
  unfold tailWord_905266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8254440884595840992251913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22011842358922242646005101 8254440884595840992251913)
  ·
    refine ⟨6190830663446880744188935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8254440884595840992251913 6190830663446880744188935)
    ·
      refine ⟨9286245995170321116283403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6190830663446880744188935 9286245995170321116283403)
      ·
        refine ⟨13929368992755481674425105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286245995170321116283403 13929368992755481674425105)
        ·
          refine ⟨10447026744566611255818829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13929368992755481674425105 10447026744566611255818829)
          ·
            refine ⟨3917635029212479220932061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10447026744566611255818829 3917635029212479220932061)
            ·
              refine ⟨1469113135954679707849523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3917635029212479220932061 1469113135954679707849523)
              ·
                refine ⟨2203669703932019561774285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469113135954679707849523 2203669703932019561774285)
                ·
                  refine ⟨826376138974507335665357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2203669703932019561774285 826376138974507335665357)
                  ·
                    refine ⟨309891052115440250874509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826376138974507335665357 309891052115440250874509)
                    ·
                      rfl

theorem cell22_905266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_905266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905266 prefixEnd_905266 := by exact prefixLift 905266
  have htrace : WordTrace (prefixWord ++ tailWord_905266) baseStart_905266 baseEnd_905266 := by
    simpa [prefixWord, tailWord_905266, baseEnd_905266] using wordTrace_append hprefix tailTrace_905266
  have hstable : (prefixWord ++ tailWord_905266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905266).length < 2 ^ (prefixWord ++ tailWord_905266).sum := by decide
  have hdescent : baseEnd_905266 < baseStart_905266 := by decide
  rcases family_descends (prefixWord ++ tailWord_905266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905339 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 8, 3]
def baseStart_905339 : Nat := 118140960795 + 905339 * 2 ^ 59
def prefixEnd_905339 : Nat := 4983230072969 + 3 ^ 40 * 905339 * 2
def baseEnd_905339 : Nat := 309916041507292393799285

theorem tailTrace_905339 : CollatzResearch.WordTrace tailWord_905339 prefixEnd_905339 309916041507292393799285 := by
  unfold tailWord_905339
  simp only [CollatzResearch.WordTrace]
  refine ⟨33020426067118897436415071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22013617378079264957610047 33020426067118897436415071)
  ·
    refine ⟨49530639100678346154622607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33020426067118897436415071 49530639100678346154622607)
    ·
      refine ⟨74295958651017519231933911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49530639100678346154622607 74295958651017519231933911)
      ·
        refine ⟨111443937976526278847900867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74295958651017519231933911 111443937976526278847900867)
        ·
          refine ⟨167165906964789418271851301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111443937976526278847900867 167165906964789418271851301)
          ·
            refine ⟨31343607555898015925972119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167165906964789418271851301 31343607555898015925972119)
            ·
              refine ⟨47015411333847023888958179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31343607555898015925972119 47015411333847023888958179)
              ·
                refine ⟨70523117000770535833437269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47015411333847023888958179 70523117000770535833437269)
                ·
                  refine ⟨826442777352779716798093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 70523117000770535833437269 826442777352779716798093)
                  ·
                    refine ⟨309916041507292393799285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826442777352779716798093 309916041507292393799285)
                    ·
                      rfl

theorem cell22_905339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3].length) (baseStart_905339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905339 prefixEnd_905339 := by exact prefixLift 905339
  have htrace : WordTrace (prefixWord ++ tailWord_905339) baseStart_905339 baseEnd_905339 := by
    simpa [prefixWord, tailWord_905339, baseEnd_905339] using wordTrace_append hprefix tailTrace_905339
  have hstable : (prefixWord ++ tailWord_905339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905339).length < 2 ^ (prefixWord ++ tailWord_905339).sum := by decide
  have hdescent : baseEnd_905339 < baseStart_905339 := by decide
  rcases family_descends (prefixWord ++ tailWord_905339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905373 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_905373 : Nat := 118140960795 + 905373 * 2 ^ 59
def prefixEnd_905373 : Nat := 4983230072969 + 3 ^ 40 * 905373 * 2
def baseEnd_905373 : Nat := 309927680402127638449181

theorem tailTrace_905373 : CollatzResearch.WordTrace tailWord_905373 prefixEnd_905373 309927680402127638449181 := by
  unfold tailWord_905373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33021666148995721243152773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22014444099330480828768515 33021666148995721243152773)
  ·
    refine ⟨6191562402936697733091145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33021666148995721243152773 6191562402936697733091145)
    ·
      refine ⟨4643671802202523299818359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6191562402936697733091145 4643671802202523299818359)
      ·
        refine ⟨6965507703303784949727539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643671802202523299818359 6965507703303784949727539)
        ·
          refine ⟨10448261554955677424591309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965507703303784949727539 10448261554955677424591309)
          ·
            refine ⟨3918098083108379034221741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10448261554955677424591309 3918098083108379034221741)
            ·
              refine ⟨1469286781165642137833153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3918098083108379034221741 1469286781165642137833153)
              ·
                refine ⟨1101965085874231603374865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1469286781165642137833153 1101965085874231603374865)
                ·
                  refine ⟨826473814405673702531149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1101965085874231603374865 826473814405673702531149)
                  ·
                    refine ⟨309927680402127638449181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826473814405673702531149 309927680402127638449181)
                    ·
                      rfl

theorem cell22_905373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_905373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905373 prefixEnd_905373 := by exact prefixLift 905373
  have htrace : WordTrace (prefixWord ++ tailWord_905373) baseStart_905373 baseEnd_905373 := by
    simpa [prefixWord, tailWord_905373, baseEnd_905373] using wordTrace_append hprefix tailTrace_905373
  have hstable : (prefixWord ++ tailWord_905373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905373).length < 2 ^ (prefixWord ++ tailWord_905373).sum := by decide
  have hdescent : baseEnd_905373 < baseStart_905373 := by decide
  rcases family_descends (prefixWord ++ tailWord_905373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905401 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_905401 : Nat := 118140960795 + 905401 * 2 ^ 59
def prefixEnd_905401 : Nat := 4983230072969 + 3 ^ 40 * 905401 * 2
def baseEnd_905401 : Nat := 309937265374344898749095

theorem tailTrace_905401 : CollatzResearch.WordTrace tailWord_905401 prefixEnd_905401 309937265374344898749095 := by
  unfold tailWord_905401
  simp only [CollatzResearch.WordTrace]
  refine ⟨33022687392894282025172057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22015124928596188016781371 33022687392894282025172057)
  ·
    refine ⟨24767015544670711518879043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33022687392894282025172057 24767015544670711518879043)
    ·
      refine ⟨37150523317006067278318565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24767015544670711518879043 37150523317006067278318565)
      ·
        refine ⟨6965723121938637614684731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37150523317006067278318565 6965723121938637614684731)
        ·
          refine ⟨10448584682907956422027097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965723121938637614684731 10448584682907956422027097)
          ·
            refine ⟨7836438512180967316520323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448584682907956422027097 7836438512180967316520323)
            ·
              refine ⟨11754657768271450974780485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836438512180967316520323 11754657768271450974780485)
              ·
                refine ⟨2203998331550897057771341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11754657768271450974780485 2203998331550897057771341)
                ·
                  refine ⟨826499374331586396664253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2203998331550897057771341 826499374331586396664253)
                  ·
                    refine ⟨309937265374344898749095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826499374331586396664253 309937265374344898749095)
                    ·
                      rfl

theorem cell22_905401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_905401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905401 prefixEnd_905401 := by exact prefixLift 905401
  have htrace : WordTrace (prefixWord ++ tailWord_905401) baseStart_905401 baseEnd_905401 := by
    simpa [prefixWord, tailWord_905401, baseEnd_905401] using wordTrace_append hprefix tailTrace_905401
  have hstable : (prefixWord ++ tailWord_905401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905401).length < 2 ^ (prefixWord ++ tailWord_905401).sum := by decide
  have hdescent : baseEnd_905401 < baseStart_905401 := by decide
  rcases family_descends (prefixWord ++ tailWord_905401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905444 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_905444 : Nat := 118140960795 + 905444 * 2 ^ 59
def prefixEnd_905444 : Nat := 4983230072969 + 3 ^ 40 * 905444 * 2
def baseEnd_905444 : Nat := 309951985153107119923963

theorem tailTrace_905444 : CollatzResearch.WordTrace tailWord_905444 prefixEnd_905444 309951985153107119923963 := by
  unfold tailWord_905444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512127865869250184493693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22016170487825666912658257 16512127865869250184493693)
  ·
    refine ⟨6192047949700968819185135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16512127865869250184493693 6192047949700968819185135)
    ·
      refine ⟨9288071924551453228777703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6192047949700968819185135 9288071924551453228777703)
      ·
        refine ⟨13932107886827179843166555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9288071924551453228777703 13932107886827179843166555)
        ·
          refine ⟨20898161830240769764749833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13932107886827179843166555 20898161830240769764749833)
          ·
            refine ⟨15673621372680577323562375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20898161830240769764749833 15673621372680577323562375)
            ·
              refine ⟨23510432059020865985343563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15673621372680577323562375 23510432059020865985343563)
              ·
                refine ⟨35265648088531298978015345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23510432059020865985343563 35265648088531298978015345)
                ·
                  refine ⟨26449236066398474233511509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35265648088531298978015345 26449236066398474233511509)
                  ·
                    refine ⟨309951985153107119923963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26449236066398474233511509 309951985153107119923963)
                    ·
                      rfl

theorem cell22_905444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_905444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905444 prefixEnd_905444 := by exact prefixLift 905444
  have htrace : WordTrace (prefixWord ++ tailWord_905444) baseStart_905444 baseEnd_905444 := by
    simpa [prefixWord, tailWord_905444, baseEnd_905444] using wordTrace_append hprefix tailTrace_905444
  have hstable : (prefixWord ++ tailWord_905444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905444).length < 2 ^ (prefixWord ++ tailWord_905444).sum := by decide
  have hdescent : baseEnd_905444 < baseStart_905444 := by decide
  rcases family_descends (prefixWord ++ tailWord_905444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905448 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_905448 : Nat := 118140960795 + 905448 * 2 ^ 59
def prefixEnd_905448 : Nat := 4983230072969 + 3 ^ 40 * 905448 * 2
def baseEnd_905448 : Nat := 103317784811617480941317

theorem tailTrace_905448 : CollatzResearch.WordTrace tailWord_905448 prefixEnd_905448 103317784811617480941317 := by
  unfold tailWord_905448
  simp only [CollatzResearch.WordTrace]
  refine ⟨16512200811862004526066499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22016267749149339368088665 16512200811862004526066499)
  ·
    refine ⟨24768301217793006789099749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16512200811862004526066499 24768301217793006789099749)
    ·
      refine ⟨4644056478336188772956203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24768301217793006789099749 4644056478336188772956203)
      ·
        refine ⟨6966084717504283159434305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644056478336188772956203 6966084717504283159434305)
        ·
          refine ⟨5224563538128212369575729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6966084717504283159434305 5224563538128212369575729)
          ·
            refine ⟨3918422653596159277181797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224563538128212369575729 3918422653596159277181797)
            ·
              refine ⟨734704247549279864471587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3918422653596159277181797 734704247549279864471587)
              ·
                refine ⟨1102056371323919796707381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734704247549279864471587 1102056371323919796707381)
                ·
                  refine ⟨103317784811617480941317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1102056371323919796707381 103317784811617480941317)
                  ·
                    rfl

theorem cell22_905448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_905448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905448 prefixEnd_905448 := by exact prefixLift 905448
  have htrace : WordTrace (prefixWord ++ tailWord_905448) baseStart_905448 baseEnd_905448 := by
    simpa [prefixWord, tailWord_905448, baseEnd_905448] using wordTrace_append hprefix tailTrace_905448
  have hstable : (prefixWord ++ tailWord_905448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905448).length < 2 ^ (prefixWord ++ tailWord_905448).sum := by decide
  have hdescent : baseEnd_905448 < baseStart_905448 := by decide
  rcases family_descends (prefixWord ++ tailWord_905448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905459 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 8]
def baseStart_905459 : Nat := 118140960795 + 905459 * 2 ^ 59
def prefixEnd_905459 : Nat := 4983230072969 + 3 ^ 40 * 905459 * 2
def baseEnd_905459 : Nat := 103319039986550693599639

theorem tailTrace_905459 : CollatzResearch.WordTrace tailWord_905459 prefixEnd_905459 103319039986550693599639 := by
  unfold tailWord_905459
  simp only [CollatzResearch.WordTrace]
  refine ⟨33024802826684157930783431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22016535217789438620522287 33024802826684157930783431)
  ·
    refine ⟨49537204240026236896175147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33024802826684157930783431 49537204240026236896175147)
    ·
      refine ⟨74305806360039355344262721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49537204240026236896175147 74305806360039355344262721)
      ·
        refine ⟨55729354770029516508197041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74305806360039355344262721 55729354770029516508197041)
        ·
          refine ⟨41797016077522137381147781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55729354770029516508197041 41797016077522137381147781)
          ·
            refine ⟨7836940514535400758965209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41797016077522137381147781 7836940514535400758965209)
            ·
              refine ⟨5877705385901550569223907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7836940514535400758965209 5877705385901550569223907)
              ·
                refine ⟨8816558078852325853835861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5877705385901550569223907 8816558078852325853835861)
                ·
                  refine ⟨103319039986550693599639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8816558078852325853835861 103319039986550693599639)
                  ·
                    rfl

theorem cell22_905459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_905459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905459 prefixEnd_905459 := by exact prefixLift 905459
  have htrace : WordTrace (prefixWord ++ tailWord_905459) baseStart_905459 baseEnd_905459 := by
    simpa [prefixWord, tailWord_905459, baseEnd_905459] using wordTrace_append hprefix tailTrace_905459
  have hstable : (prefixWord ++ tailWord_905459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905459).length < 2 ^ (prefixWord ++ tailWord_905459).sum := by decide
  have hdescent : baseEnd_905459 < baseStart_905459 := by decide
  rcases family_descends (prefixWord ++ tailWord_905459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905491 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 4, 3]
def baseStart_905491 : Nat := 118140960795 + 905491 * 2 ^ 59
def prefixEnd_905491 : Nat := 4983230072969 + 3 ^ 40 * 905491 * 2
def baseEnd_905491 : Nat := 309968074213614663998819

theorem tailTrace_905491 : CollatzResearch.WordTrace tailWord_905491 prefixEnd_905491 309968074213614663998819 := by
  unfold tailWord_905491
  simp only [CollatzResearch.WordTrace]
  refine ⟨33025969962568227395948327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22017313308378818263965551 33025969962568227395948327)
  ·
    refine ⟨49538954943852341093922491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33025969962568227395948327 49538954943852341093922491)
    ·
      refine ⟨74308432415778511640883737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49538954943852341093922491 74308432415778511640883737)
      ·
        refine ⟨55731324311833883730662803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74308432415778511640883737 55731324311833883730662803)
        ·
          refine ⟨83596986467750825595994205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55731324311833883730662803 83596986467750825595994205)
          ·
            refine ⟨31348869925406559598497827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83596986467750825595994205 31348869925406559598497827)
            ·
              refine ⟨47023304888109839397746741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31348869925406559598497827 47023304888109839397746741)
              ·
                refine ⟨4408434833260297443538757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47023304888109839397746741 4408434833260297443538757)
                ·
                  refine ⟨826581531236305770663517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4408434833260297443538757 826581531236305770663517)
                  ·
                    refine ⟨309968074213614663998819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826581531236305770663517 309968074213614663998819)
                    ·
                      rfl

theorem cell22_905491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3].length) (baseStart_905491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905491 prefixEnd_905491 := by exact prefixLift 905491
  have htrace : WordTrace (prefixWord ++ tailWord_905491) baseStart_905491 baseEnd_905491 := by
    simpa [prefixWord, tailWord_905491, baseEnd_905491] using wordTrace_append hprefix tailTrace_905491
  have hstable : (prefixWord ++ tailWord_905491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905491).length < 2 ^ (prefixWord ++ tailWord_905491).sum := by decide
  have hdescent : baseEnd_905491 < baseStart_905491 := by decide
  rcases family_descends (prefixWord ++ tailWord_905491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905508 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_905508 : Nat := 118140960795 + 905508 * 2 ^ 59
def prefixEnd_905508 : Nat := 4983230072969 + 3 ^ 40 * 905508 * 2
def baseEnd_905508 : Nat := 309973893661032286323767

theorem tailTrace_905508 : CollatzResearch.WordTrace tailWord_905508 prefixEnd_905508 309973893661032286323767 := by
  unfold tailWord_905508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16513295001753319649658589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22017726669004426199544785 16513295001753319649658589)
  ·
    refine ⟨6192485625657494868621971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16513295001753319649658589 6192485625657494868621971)
    ·
      refine ⟨9288728438486242302932957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6192485625657494868621971 9288728438486242302932957)
      ·
        refine ⟨3483273164432340863599859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9288728438486242302932957 3483273164432340863599859)
        ·
          refine ⟨5224909746648511295399789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483273164432340863599859 5224909746648511295399789)
          ·
            refine ⟨1959341154993191735774921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5224909746648511295399789 1959341154993191735774921)
            ·
              refine ⟨1469505866244893801831191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959341154993191735774921 1469505866244893801831191)
              ·
                refine ⟨2204258799367340702746787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469505866244893801831191 2204258799367340702746787)
                ·
                  refine ⟨3306388199051011054120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204258799367340702746787 3306388199051011054120181)
                  ·
                    refine ⟨309973893661032286323767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3306388199051011054120181 309973893661032286323767)
                    ·
                      rfl

theorem cell22_905508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_905508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905508 prefixEnd_905508 := by exact prefixLift 905508
  have htrace : WordTrace (prefixWord ++ tailWord_905508) baseStart_905508 baseEnd_905508 := by
    simpa [prefixWord, tailWord_905508, baseEnd_905508] using wordTrace_append hprefix tailTrace_905508
  have hstable : (prefixWord ++ tailWord_905508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905508).length < 2 ^ (prefixWord ++ tailWord_905508).sum := by decide
  have hdescent : baseEnd_905508 < baseStart_905508 := by decide
  rcases family_descends (prefixWord ++ tailWord_905508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905553 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_905553 : Nat := 118140960795 + 905553 * 2 ^ 59
def prefixEnd_905553 : Nat := 4983230072969 + 3 ^ 40 * 905553 * 2
def baseEnd_905553 : Nat := 309989298080667168948629

theorem tailTrace_905553 : CollatzResearch.WordTrace tailWord_905553 prefixEnd_905553 309989298080667168948629 := by
  unfold tailWord_905553
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028231288343611984705313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22018820858895741323136875 33028231288343611984705313)
  ·
    refine ⟨24771173466257708988528985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33028231288343611984705313 24771173466257708988528985)
    ·
      refine ⟨18578380099693281741396739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24771173466257708988528985 18578380099693281741396739)
      ·
        refine ⟨27867570149539922612095109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18578380099693281741396739 27867570149539922612095109)
        ·
          refine ⟨5225169403038735489767833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27867570149539922612095109 5225169403038735489767833)
          ·
            refine ⟨3918877052279051617325875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225169403038735489767833 3918877052279051617325875)
            ·
              refine ⟨5878315578418577425988813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918877052279051617325875 5878315578418577425988813)
              ·
                refine ⟨2204368341906966534745805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5878315578418577425988813 2204368341906966534745805)
                ·
                  refine ⟨826638128215112450529677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2204368341906966534745805 826638128215112450529677)
                  ·
                    refine ⟨309989298080667168948629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826638128215112450529677 309989298080667168948629)
                    ·
                      rfl

theorem cell22_905553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_905553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905553 prefixEnd_905553 := by exact prefixLift 905553
  have htrace : WordTrace (prefixWord ++ tailWord_905553) baseStart_905553 baseEnd_905553 := by
    simpa [prefixWord, tailWord_905553, baseEnd_905553] using wordTrace_append hprefix tailTrace_905553
  have hstable : (prefixWord ++ tailWord_905553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905553).length < 2 ^ (prefixWord ++ tailWord_905553).sum := by decide
  have hdescent : baseEnd_905553 < baseStart_905553 := by decide
  rcases family_descends (prefixWord ++ tailWord_905553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905570 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_905570 : Nat := 118140960795 + 905570 * 2 ^ 59
def prefixEnd_905570 : Nat := 4983230072969 + 3 ^ 40 * 905570 * 2
def baseEnd_905570 : Nat := 309995117528084791273577

theorem tailTrace_905570 : CollatzResearch.WordTrace tailWord_905570 prefixEnd_905570 309995117528084791273577 := by
  unfold tailWord_905570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257212832320505972018541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22019234219521349258716109 8257212832320505972018541)
  ·
    refine ⟨3096454812120189739506953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8257212832320505972018541 3096454812120189739506953)
    ·
      refine ⟨2322341109090142304630215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3096454812120189739506953 2322341109090142304630215)
      ·
        refine ⟨3483511663635213456945323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322341109090142304630215 3483511663635213456945323)
        ·
          refine ⟨5225267495452820185417985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483511663635213456945323 5225267495452820185417985)
          ·
            refine ⟨3918950621589615139063489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5225267495452820185417985 3918950621589615139063489)
            ·
              refine ⟨2939212966192211354297617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3918950621589615139063489 2939212966192211354297617)
              ·
                refine ⟨2204409724644158515723213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939212966192211354297617 2204409724644158515723213)
                ·
                  refine ⟨826653646741559443396205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2204409724644158515723213 826653646741559443396205)
                  ·
                    refine ⟨309995117528084791273577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826653646741559443396205 309995117528084791273577)
                    ·
                      rfl

theorem cell22_905570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_905570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905570 prefixEnd_905570 := by exact prefixLift 905570
  have htrace : WordTrace (prefixWord ++ tailWord_905570) baseStart_905570 baseEnd_905570 := by
    simpa [prefixWord, tailWord_905570, baseEnd_905570] using wordTrace_append hprefix tailTrace_905570
  have hstable : (prefixWord ++ tailWord_905570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905570).length < 2 ^ (prefixWord ++ tailWord_905570).sum := by decide
  have hdescent : baseEnd_905570 < baseStart_905570 := by decide
  rcases family_descends (prefixWord ++ tailWord_905570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905641 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_905641 : Nat := 118140960795 + 905641 * 2 ^ 59
def prefixEnd_905641 : Nat := 4983230072969 + 3 ^ 40 * 905641 * 2
def baseEnd_905641 : Nat := 310019422279064272748359

theorem tailTrace_905641 : CollatzResearch.WordTrace tailWord_905641 prefixEnd_905641 310019422279064272748359 := by
  unfold tailWord_905641
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031440912024803013908777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22020960608016535342605851 33031440912024803013908777)
  ·
    refine ⟨24773580684018602260431583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33031440912024803013908777 24773580684018602260431583)
    ·
      refine ⟨37160371026027903390647375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24773580684018602260431583 37160371026027903390647375)
      ·
        refine ⟨55740556539041855085971063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37160371026027903390647375 55740556539041855085971063)
        ·
          refine ⟨83610834808562782628956595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55740556539041855085971063 83610834808562782628956595)
          ·
            refine ⟨125416252212844173943434893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83610834808562782628956595 125416252212844173943434893)
            ·
              refine ⟨47031094579816565228788085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125416252212844173943434893 47031094579816565228788085)
              ·
                refine ⟨4409165116857802990198883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47031094579816565228788085 4409165116857802990198883)
                ·
                  refine ⟨6613747675286704485298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4409165116857802990198883 6613747675286704485298325)
                  ·
                    refine ⟨310019422279064272748359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6613747675286704485298325 310019422279064272748359)
                    ·
                      rfl

theorem cell22_905641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_905641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905641 prefixEnd_905641 := by exact prefixLift 905641
  have htrace : WordTrace (prefixWord ++ tailWord_905641) baseStart_905641 baseEnd_905641 := by
    simpa [prefixWord, tailWord_905641, baseEnd_905641] using wordTrace_append hprefix tailTrace_905641
  have hstable : (prefixWord ++ tailWord_905641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905641).length < 2 ^ (prefixWord ++ tailWord_905641).sum := by decide
  have hdescent : baseEnd_905641 < baseStart_905641 := by decide
  rcases family_descends (prefixWord ++ tailWord_905641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905662 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_905662 : Nat := 118140960795 + 905662 * 2 ^ 59
def prefixEnd_905662 : Nat := 4983230072969 + 3 ^ 40 * 905662 * 2
def baseEnd_905662 : Nat := 103342203669409072657765

theorem tailTrace_905662 : CollatzResearch.WordTrace tailWord_905662 prefixEnd_905662 103342203669409072657765 := by
  unfold tailWord_905662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129025855618590450052905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22021471229965815733615493 4129025855618590450052905)
  ·
    refine ⟨3096769391713942837539679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4129025855618590450052905 3096769391713942837539679)
    ·
      refine ⟨4645154087570914256309519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3096769391713942837539679 4645154087570914256309519)
      ·
        refine ⟨6967731131356371384464279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645154087570914256309519 6967731131356371384464279)
        ·
          refine ⟨10451596697034557076696419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967731131356371384464279 10451596697034557076696419)
          ·
            refine ⟨15677395045551835615044629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451596697034557076696419 15677395045551835615044629)
            ·
              refine ⟨734877892760242294455217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15677395045551835615044629 734877892760242294455217)
              ·
                refine ⟨551158419570181720841413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734877892760242294455217 551158419570181720841413)
                ·
                  refine ⟨103342203669409072657765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551158419570181720841413 103342203669409072657765)
                  ·
                    rfl

theorem cell22_905662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_905662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905662 prefixEnd_905662 := by exact prefixLift 905662
  have htrace : WordTrace (prefixWord ++ tailWord_905662) baseStart_905662 baseEnd_905662 := by
    simpa [prefixWord, tailWord_905662, baseEnd_905662] using wordTrace_append hprefix tailTrace_905662
  have hstable : (prefixWord ++ tailWord_905662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905662).length < 2 ^ (prefixWord ++ tailWord_905662).sum := by decide
  have hdescent : baseEnd_905662 < baseStart_905662 := by decide
  rcases family_descends (prefixWord ++ tailWord_905662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905698 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_905698 : Nat := 118140960795 + 905698 * 2 ^ 59
def prefixEnd_905698 : Nat := 4983230072969 + 3 ^ 40 * 905698 * 2
def baseEnd_905698 : Nat := 310038934543935124073185

theorem tailTrace_905698 : CollatzResearch.WordTrace tailWord_905698 prefixEnd_905698 310038934543935124073185 := by
  unfold tailWord_905698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258379968204575437183437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22022346581878867832489165 8258379968204575437183437)
  ·
    refine ⟨3096892488076715788943789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8258379968204575437183437 3096892488076715788943789)
    ·
      refine ⟨1161334683028768420853921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3096892488076715788943789 1161334683028768420853921)
      ·
        refine ⟨871001012271576315640441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161334683028768420853921 871001012271576315640441)
        ·
          refine ⟨653250759203682236730331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871001012271576315640441 653250759203682236730331)
          ·
            refine ⟨979876138805523355095497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653250759203682236730331 979876138805523355095497)
            ·
              refine ⟨734907104104142516321623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979876138805523355095497 734907104104142516321623)
              ·
                refine ⟨1102360656156213774482435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734907104104142516321623 1102360656156213774482435)
                ·
                  refine ⟨1653540984234320661723653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102360656156213774482435 1653540984234320661723653)
                  ·
                    refine ⟨310038934543935124073185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1653540984234320661723653 310038934543935124073185)
                    ·
                      rfl

theorem cell22_905698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_905698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905698 prefixEnd_905698 := by exact prefixLift 905698
  have htrace : WordTrace (prefixWord ++ tailWord_905698) baseStart_905698 baseEnd_905698 := by
    simpa [prefixWord, tailWord_905698, baseEnd_905698] using wordTrace_append hprefix tailTrace_905698
  have hstable : (prefixWord ++ tailWord_905698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905698).length < 2 ^ (prefixWord ++ tailWord_905698).sum := by decide
  have hdescent : baseEnd_905698 < baseStart_905698 := by decide
  rcases family_descends (prefixWord ++ tailWord_905698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905733 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_905733 : Nat := 118140960795 + 905733 * 2 ^ 59
def prefixEnd_905733 : Nat := 4983230072969 + 3 ^ 40 * 905733 * 2
def baseEnd_905733 : Nat := 310050915759206699448077

theorem tailTrace_905733 : CollatzResearch.WordTrace tailWord_905733 prefixEnd_905733 310050915759206699448077 := by
  unfold tailWord_905733
  simp only [CollatzResearch.WordTrace]
  refine ⟨33034796427691502726257853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22023197618461001817505235 33034796427691502726257853)
  ·
    refine ⟨12388048660384313522346695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33034796427691502726257853 12388048660384313522346695)
    ·
      refine ⟨18582072990576470283520043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12388048660384313522346695 18582072990576470283520043)
      ·
        refine ⟨27873109485864705425280065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582072990576470283520043 27873109485864705425280065)
        ·
          refine ⟨20904832114398529068960049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27873109485864705425280065 20904832114398529068960049)
          ·
            refine ⟨15678624085798896801720037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20904832114398529068960049 15678624085798896801720037)
            ·
              refine ⟨2939742016087293150322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15678624085798896801720037 2939742016087293150322507)
              ·
                refine ⟨4409613024130939725483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939742016087293150322507 4409613024130939725483761)
                ·
                  refine ⟨3307209768098204794112821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4409613024130939725483761 3307209768098204794112821)
                  ·
                    refine ⟨310050915759206699448077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3307209768098204794112821 310050915759206699448077)
                    ·
                      rfl

theorem cell22_905733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_905733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905733 prefixEnd_905733 := by exact prefixLift 905733
  have htrace : WordTrace (prefixWord ++ tailWord_905733) baseStart_905733 baseEnd_905733 := by
    simpa [prefixWord, tailWord_905733, baseEnd_905733] using wordTrace_append hprefix tailTrace_905733
  have hstable : (prefixWord ++ tailWord_905733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905733).length < 2 ^ (prefixWord ++ tailWord_905733).sum := by decide
  have hdescent : baseEnd_905733 < baseStart_905733 := by decide
  rcases family_descends (prefixWord ++ tailWord_905733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905765 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_905765 : Nat := 118140960795 + 905765 * 2 ^ 59
def prefixEnd_905765 : Nat := 4983230072969 + 3 ^ 40 * 905765 * 2
def baseEnd_905765 : Nat := 310061870013169282647979

theorem tailTrace_905765 : CollatzResearch.WordTrace tailWord_905765 prefixEnd_905765 310061870013169282647979 := by
  unfold tailWord_905765
  simp only [CollatzResearch.WordTrace]
  refine ⟨33035963563575572191422749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22023975709050381460948499 33035963563575572191422749)
  ·
    refine ⟨12388486336340839571783531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33035963563575572191422749 12388486336340839571783531)
    ·
      refine ⟨18582729504511259357675297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12388486336340839571783531 18582729504511259357675297)
      ·
        refine ⟨13937047128383444518256473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18582729504511259357675297 13937047128383444518256473)
        ·
          refine ⟨10452785346287583388692355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13937047128383444518256473 10452785346287583388692355)
          ·
            refine ⟨15679178019431375083038533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452785346287583388692355 15679178019431375083038533)
            ·
              refine ⟨2939845878643382828069725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15679178019431375083038533 2939845878643382828069725)
              ·
                refine ⟨1102442204491268560526147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2939845878643382828069725 1102442204491268560526147)
                ·
                  refine ⟨1653663306736902840789221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102442204491268560526147 1653663306736902840789221)
                  ·
                    refine ⟨310061870013169282647979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1653663306736902840789221 310061870013169282647979)
                    ·
                      rfl

theorem cell22_905765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_905765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905765 prefixEnd_905765 := by exact prefixLift 905765
  have htrace : WordTrace (prefixWord ++ tailWord_905765) baseStart_905765 baseEnd_905765 := by
    simpa [prefixWord, tailWord_905765, baseEnd_905765] using wordTrace_append hprefix tailTrace_905765
  have hstable : (prefixWord ++ tailWord_905765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905765).length < 2 ^ (prefixWord ++ tailWord_905765).sum := by decide
  have hdescent : baseEnd_905765 < baseStart_905765 := by decide
  rcases family_descends (prefixWord ++ tailWord_905765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905773 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_905773 : Nat := 118140960795 + 905773 * 2 ^ 59
def prefixEnd_905773 : Nat := 4983230072969 + 3 ^ 40 * 905773 * 2
def baseEnd_905773 : Nat := 310064608576659928447955

theorem tailTrace_905773 : CollatzResearch.WordTrace tailWord_905773 prefixEnd_905773 310064608576659928447955 := by
  unfold tailWord_905773
  simp only [CollatzResearch.WordTrace]
  refine ⟨33036255347546589557713973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22024170231697726371809315 33036255347546589557713973)
  ·
    refine ⟨3097148938832492771035685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33036255347546589557713973 3097148938832492771035685)
    ·
      refine ⟨580715426031092394569191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3097148938832492771035685 580715426031092394569191)
      ·
        refine ⟨871073139046638591853787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580715426031092394569191 871073139046638591853787)
        ·
          refine ⟨1306609708569957887780681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871073139046638591853787 1306609708569957887780681)
          ·
            refine ⟨979957281427468415835511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306609708569957887780681 979957281427468415835511)
            ·
              refine ⟨1469935922141202623753267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979957281427468415835511 1469935922141202623753267)
              ·
                refine ⟨2204903883211803935629901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469935922141202623753267 2204903883211803935629901)
                ·
                  refine ⟨826838956204426475861213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2204903883211803935629901 826838956204426475861213)
                  ·
                    refine ⟨310064608576659928447955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826838956204426475861213 310064608576659928447955)
                    ·
                      rfl

theorem cell22_905773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_905773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905773 prefixEnd_905773 := by exact prefixLift 905773
  have htrace : WordTrace (prefixWord ++ tailWord_905773) baseStart_905773 baseEnd_905773 := by
    simpa [prefixWord, tailWord_905773, baseEnd_905773] using wordTrace_append hprefix tailTrace_905773
  have hstable : (prefixWord ++ tailWord_905773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905773).length < 2 ^ (prefixWord ++ tailWord_905773).sum := by decide
  have hdescent : baseEnd_905773 < baseStart_905773 := by decide
  rcases family_descends (prefixWord ++ tailWord_905773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905829 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_905829 : Nat := 118140960795 + 905829 * 2 ^ 59
def prefixEnd_905829 : Nat := 4983230072969 + 3 ^ 40 * 905829 * 2
def baseEnd_905829 : Nat := 310083778521094449047783

theorem tailTrace_905829 : CollatzResearch.WordTrace tailWord_905829 prefixEnd_905829 310083778521094449047783 := by
  unfold tailWord_905829
  simp only [CollatzResearch.WordTrace]
  refine ⟨33038297835343711121752541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22025531890229140747835027 33038297835343711121752541)
  ·
    refine ⟨12389361688253891670657203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33038297835343711121752541 12389361688253891670657203)
    ·
      refine ⟨18584042532380837505985805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389361688253891670657203 18584042532380837505985805)
      ·
        refine ⟨6969015949642814064744677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18584042532380837505985805 6969015949642814064744677)
        ·
          refine ⟨1306690490558027637139627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6969015949642814064744677 1306690490558027637139627)
          ·
            refine ⟨1960035735837041455709441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306690490558027637139627 1960035735837041455709441)
            ·
              refine ⟨1470026801877781091782081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960035735837041455709441 1470026801877781091782081)
              ·
                refine ⟨1102520101408335818836561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470026801877781091782081 1102520101408335818836561)
                ·
                  refine ⟨826890076056251864127421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1102520101408335818836561 826890076056251864127421)
                  ·
                    refine ⟨310083778521094449047783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826890076056251864127421 310083778521094449047783)
                    ·
                      rfl

theorem cell22_905829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_905829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905829 prefixEnd_905829 := by exact prefixLift 905829
  have htrace : WordTrace (prefixWord ++ tailWord_905829) baseStart_905829 baseEnd_905829 := by
    simpa [prefixWord, tailWord_905829, baseEnd_905829] using wordTrace_append hprefix tailTrace_905829
  have hstable : (prefixWord ++ tailWord_905829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905829).length < 2 ^ (prefixWord ++ tailWord_905829).sum := by decide
  have hdescent : baseEnd_905829 < baseStart_905829 := by decide
  rcases family_descends (prefixWord ++ tailWord_905829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905842 : List Nat := [3, 2, 1, 2, 4, 2, 1, 7]
def baseStart_905842 : Nat := 118140960795 + 905842 * 2 ^ 59
def prefixEnd_905842 : Nat := 4983230072969 + 3 ^ 40 * 905842 * 2
def baseEnd_905842 : Nat := 34454247631862972052527

theorem tailTrace_905842 : CollatzResearch.WordTrace tailWord_905842 prefixEnd_905842 34454247631862972052527 := by
  unfold tailWord_905842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259692996074153585493945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22025847989531076227983853 8259692996074153585493945)
  ·
    refine ⟨6194769747055615189120459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8259692996074153585493945 6194769747055615189120459)
    ·
      refine ⟨9292154620583422783680689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194769747055615189120459 9292154620583422783680689)
      ·
        refine ⟨6969115965437567087760517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9292154620583422783680689 6969115965437567087760517)
        ·
          refine ⟨1306709243519543828955097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6969115965437567087760517 1306709243519543828955097)
          ·
            refine ⟨980031932639657871716323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306709243519543828955097 980031932639657871716323)
            ·
              refine ⟨1470047898959486807574485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980031932639657871716323 1470047898959486807574485)
              ·
                refine ⟨34454247631862972052527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1470047898959486807574485 34454247631862972052527)
                ·
                  rfl

theorem cell22_905842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_905842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905842 prefixEnd_905842 := by exact prefixLift 905842
  have htrace : WordTrace (prefixWord ++ tailWord_905842) baseStart_905842 baseEnd_905842 := by
    simpa [prefixWord, tailWord_905842, baseEnd_905842] using wordTrace_append hprefix tailTrace_905842
  have hstable : (prefixWord ++ tailWord_905842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905842).length < 2 ^ (prefixWord ++ tailWord_905842).sum := by decide
  have hdescent : baseEnd_905842 < baseStart_905842 := by decide
  rcases family_descends (prefixWord ++ tailWord_905842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905857 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_905857 : Nat := 118140960795 + 905857 * 2 ^ 59
def prefixEnd_905857 : Nat := 4983230072969 + 3 ^ 40 * 905857 * 2
def baseEnd_905857 : Nat := 310093363493311709347697

theorem tailTrace_905857 : CollatzResearch.WordTrace tailWord_905857 prefixEnd_905857 310093363493311709347697 := by
  unfold tailWord_905857
  simp only [CollatzResearch.WordTrace]
  refine ⟨33039319079242271903771825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22026212719494847935847883 33039319079242271903771825)
  ·
    refine ⟨24779489309431703927828869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33039319079242271903771825 24779489309431703927828869)
    ·
      refine ⟨4646154245518444486467913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24779489309431703927828869 4646154245518444486467913)
      ·
        refine ⟨3484615684138833364850935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4646154245518444486467913 3484615684138833364850935)
        ·
          refine ⟨5226923526208250047276403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484615684138833364850935 5226923526208250047276403)
          ·
            refine ⟨7840385289312375070914605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226923526208250047276403 7840385289312375070914605)
            ·
              refine ⟨2940144483492140651592977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7840385289312375070914605 2940144483492140651592977)
              ·
                refine ⟨2205108362619105488694733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940144483492140651592977 2205108362619105488694733)
                ·
                  refine ⟨826915635982164558260525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2205108362619105488694733 826915635982164558260525)
                  ·
                    refine ⟨310093363493311709347697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826915635982164558260525 310093363493311709347697)
                    ·
                      rfl

theorem cell22_905857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_905857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905857 prefixEnd_905857 := by exact prefixLift 905857
  have htrace : WordTrace (prefixWord ++ tailWord_905857) baseStart_905857 baseEnd_905857 := by
    simpa [prefixWord, tailWord_905857, baseEnd_905857] using wordTrace_append hprefix tailTrace_905857
  have hstable : (prefixWord ++ tailWord_905857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905857).length < 2 ^ (prefixWord ++ tailWord_905857).sum := by decide
  have hdescent : baseEnd_905857 < baseStart_905857 := by decide
  rcases family_descends (prefixWord ++ tailWord_905857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905870 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_905870 : Nat := 118140960795 + 905870 * 2 ^ 59
def prefixEnd_905870 : Nat := 4983230072969 + 3 ^ 40 * 905870 * 2
def baseEnd_905870 : Nat := 103365937886328002924219

theorem tailTrace_905870 : CollatzResearch.WordTrace tailWord_905870 prefixEnd_905870 103365937886328002924219 := by
  unfold tailWord_905870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129974153524396890499383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22026528818796783415996709 4129974153524396890499383)
  ·
    refine ⟨6194961230286595335749075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129974153524396890499383 6194961230286595335749075)
    ·
      refine ⟨9292441845429893003623613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194961230286595335749075 9292441845429893003623613)
      ·
        refine ⟨3484665692036209876358855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9292441845429893003623613 3484665692036209876358855)
        ·
          refine ⟨5226998538054314814538283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484665692036209876358855 5226998538054314814538283)
          ·
            refine ⟨7840497807081472221807425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226998538054314814538283 7840497807081472221807425)
            ·
              refine ⟨5880373355311104166355569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7840497807081472221807425 5880373355311104166355569)
              ·
                refine ⟨4410280016483328124766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880373355311104166355569 4410280016483328124766677)
                ·
                  refine ⟨103365937886328002924219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4410280016483328124766677 103365937886328002924219)
                  ·
                    rfl

theorem cell22_905870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_905870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905870 prefixEnd_905870 := by exact prefixLift 905870
  have htrace : WordTrace (prefixWord ++ tailWord_905870) baseStart_905870 baseEnd_905870 := by
    simpa [prefixWord, tailWord_905870, baseEnd_905870] using wordTrace_append hprefix tailTrace_905870
  have hstable : (prefixWord ++ tailWord_905870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905870).length < 2 ^ (prefixWord ++ tailWord_905870).sum := by decide
  have hdescent : baseEnd_905870 < baseStart_905870 := by decide
  rcases family_descends (prefixWord ++ tailWord_905870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905883 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_905883 : Nat := 118140960795 + 905883 * 2 ^ 59
def prefixEnd_905883 : Nat := 4983230072969 + 3 ^ 40 * 905883 * 2
def baseEnd_905883 : Nat := 310102263824656308197617

theorem tailTrace_905883 : CollatzResearch.WordTrace tailWord_905883 prefixEnd_905883 310102263824656308197617 := by
  unfold tailWord_905883
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040267377148078344218303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22026844918098718896145535 33040267377148078344218303)
  ·
    refine ⟨49560401065722117516327455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33040267377148078344218303 49560401065722117516327455)
    ·
      refine ⟨74340601598583176274491183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49560401065722117516327455 74340601598583176274491183)
      ·
        refine ⟨111510902397874764411736775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74340601598583176274491183 111510902397874764411736775)
        ·
          refine ⟨167266353596812146617605163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111510902397874764411736775 167266353596812146617605163)
          ·
            refine ⟨250899530395218219926407745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167266353596812146617605163 250899530395218219926407745)
            ·
              refine ⟨188174647796413664944805809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250899530395218219926407745 188174647796413664944805809)
              ·
                refine ⟨141130985847310248708604357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188174647796413664944805809 141130985847310248708604357)
                ·
                  refine ⟨26462059846370671632863317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141130985847310248708604357 26462059846370671632863317)
                  ·
                    refine ⟨310102263824656308197617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26462059846370671632863317 310102263824656308197617)
                    ·
                      rfl

theorem cell22_905883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_905883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905883 prefixEnd_905883 := by exact prefixLift 905883
  have htrace : WordTrace (prefixWord ++ tailWord_905883) baseStart_905883 baseEnd_905883 := by
    simpa [prefixWord, tailWord_905883, baseEnd_905883] using wordTrace_append hprefix tailTrace_905883
  have hstable : (prefixWord ++ tailWord_905883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905883).length < 2 ^ (prefixWord ++ tailWord_905883).sum := by decide
  have hdescent : baseEnd_905883 < baseStart_905883 := by decide
  rcases family_descends (prefixWord ++ tailWord_905883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905885 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_905885 : Nat := 118140960795 + 905885 * 2 ^ 59
def prefixEnd_905885 : Nat := 4983230072969 + 3 ^ 40 * 905885 * 2
def baseEnd_905885 : Nat := 310102948465528969647611

theorem tailTrace_905885 : CollatzResearch.WordTrace tailWord_905885 prefixEnd_905885 310102948465528969647611 := by
  unfold tailWord_905885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040340323140832685791109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22026893548760555123860739 33040340323140832685791109)
  ·
    refine ⟨6195063810588906128585833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33040340323140832685791109 6195063810588906128585833)
    ·
      refine ⟨4646297857941679596439375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6195063810588906128585833 4646297857941679596439375)
      ·
        refine ⟨6969446786912519394659063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4646297857941679596439375 6969446786912519394659063)
        ·
          refine ⟨10454170180368779091988595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969446786912519394659063 10454170180368779091988595)
          ·
            refine ⟨15681255270553168637982893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454170180368779091988595 15681255270553168637982893)
            ·
              refine ⟨5880470726457438239243585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15681255270553168637982893 5880470726457438239243585)
              ·
                refine ⟨4410353044843078679432689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880470726457438239243585 4410353044843078679432689)
                ·
                  refine ⟨3307764783632309009574517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410353044843078679432689 3307764783632309009574517)
                  ·
                    refine ⟨310102948465528969647611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3307764783632309009574517 310102948465528969647611)
                    ·
                      rfl

theorem cell22_905885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_905885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905885 prefixEnd_905885 := by exact prefixLift 905885
  have htrace : WordTrace (prefixWord ++ tailWord_905885) baseStart_905885 baseEnd_905885 := by
    simpa [prefixWord, tailWord_905885, baseEnd_905885] using wordTrace_append hprefix tailTrace_905885
  have hstable : (prefixWord ++ tailWord_905885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905885).length < 2 ^ (prefixWord ++ tailWord_905885).sum := by decide
  have hdescent : baseEnd_905885 < baseStart_905885 := by decide
  rcases family_descends (prefixWord ++ tailWord_905885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905917 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_905917 : Nat := 118140960795 + 905917 * 2 ^ 59
def prefixEnd_905917 : Nat := 4983230072969 + 3 ^ 40 * 905917 * 2
def baseEnd_905917 : Nat := 310113902719491552847513

theorem tailTrace_905917 : CollatzResearch.WordTrace tailWord_905917 prefixEnd_905917 310113902719491552847513 := by
  unfold tailWord_905917
  simp only [CollatzResearch.WordTrace]
  refine ⟨33041507459024902150956005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22027671639349934767304003 33041507459024902150956005)
  ·
    refine ⟨6195282648567169153304251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33041507459024902150956005 6195282648567169153304251)
    ·
      refine ⟨9292923972850753729956377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6195282648567169153304251 9292923972850753729956377)
      ·
        refine ⟨6969692979638065297467283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9292923972850753729956377 6969692979638065297467283)
        ·
          refine ⟨10454539469457097946200925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969692979638065297467283 10454539469457097946200925)
          ·
            refine ⟨3920452301046411729825347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10454539469457097946200925 3920452301046411729825347)
            ·
              refine ⟨5880678451569617594738021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920452301046411729825347 5880678451569617594738021)
              ·
                refine ⟨1102627209669303299013379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5880678451569617594738021 1102627209669303299013379)
                ·
                  refine ⟨1653940814503954948520069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1102627209669303299013379 1653940814503954948520069)
                  ·
                    refine ⟨310113902719491552847513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1653940814503954948520069 310113902719491552847513)
                    ·
                      rfl

theorem cell22_905917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_905917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_905917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_905917 prefixEnd_905917 := by exact prefixLift 905917
  have htrace : WordTrace (prefixWord ++ tailWord_905917) baseStart_905917 baseEnd_905917 := by
    simpa [prefixWord, tailWord_905917, baseEnd_905917] using wordTrace_append hprefix tailTrace_905917
  have hstable : (prefixWord ++ tailWord_905917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905917).length < 2 ^ (prefixWord ++ tailWord_905917).sum := by decide
  have hdescent : baseEnd_905917 < baseStart_905917 := by decide
  rcases family_descends (prefixWord ++ tailWord_905917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906097 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_906097 : Nat := 118140960795 + 906097 * 2 ^ 59
def prefixEnd_906097 : Nat := 4983230072969 + 3 ^ 40 * 906097 * 2
def baseEnd_906097 : Nat := 310175520398031083346961

theorem tailTrace_906097 : CollatzResearch.WordTrace tailWord_906097 prefixEnd_906097 310175520398031083346961 := by
  unfold tailWord_906097
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048072598372792892508545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22032048398915195261672363 33048072598372792892508545)
  ·
    refine ⟨24786054448779594669381409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33048072598372792892508545 24786054448779594669381409)
    ·
      refine ⟨18589540836584696002036057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24786054448779594669381409 18589540836584696002036057)
      ·
        refine ⟨13942155627438522001527043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18589540836584696002036057 13942155627438522001527043)
        ·
          refine ⟨20913233441157783002290565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942155627438522001527043 20913233441157783002290565)
          ·
            refine ⟨3921231270217084312929481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20913233441157783002290565 3921231270217084312929481)
            ·
              refine ⟨2940923452662813234697111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921231270217084312929481 2940923452662813234697111)
              ·
                refine ⟨4411385178994219852045667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940923452662813234697111 4411385178994219852045667)
                ·
                  refine ⟨6617077768491329778068501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411385178994219852045667 6617077768491329778068501)
                  ·
                    refine ⟨310175520398031083346961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6617077768491329778068501 310175520398031083346961)
                    ·
                      rfl

theorem cell22_906097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_906097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906097 prefixEnd_906097 := by exact prefixLift 906097
  have htrace : WordTrace (prefixWord ++ tailWord_906097) baseStart_906097 baseEnd_906097 := by
    simpa [prefixWord, tailWord_906097, baseEnd_906097] using wordTrace_append hprefix tailTrace_906097
  have hstable : (prefixWord ++ tailWord_906097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906097).length < 2 ^ (prefixWord ++ tailWord_906097).sum := by decide
  have hdescent : baseEnd_906097 < baseStart_906097 := by decide
  rcases family_descends (prefixWord ++ tailWord_906097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906101 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 4]
def baseStart_906101 : Nat := 118140960795 + 906101 * 2 ^ 59
def prefixEnd_906101 : Nat := 4983230072969 + 3 ^ 40 * 906101 * 2
def baseEnd_906101 : Nat := 103392296559925468748983

theorem tailTrace_906101 : CollatzResearch.WordTrace tailWord_906101 prefixEnd_906101 103392296559925468748983 := by
  unfold tailWord_906101
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048218490358301575654157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22032145660238867717102771 33048218490358301575654157)
  ·
    refine ⟨12393081933884363090870309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33048218490358301575654157 12393081933884363090870309)
    ·
      refine ⟨2323702862603318079538183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12393081933884363090870309 2323702862603318079538183)
      ·
        refine ⟨3485554293904977119307275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323702862603318079538183 3485554293904977119307275)
        ·
          refine ⟨5228331440857465678960913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485554293904977119307275 5228331440857465678960913)
          ·
            refine ⟨3921248580643099259220685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5228331440857465678960913 3921248580643099259220685)
            ·
              refine ⟨1470468217741162222207757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3921248580643099259220685 1470468217741162222207757)
              ·
                refine ⟨551425581652935833327909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470468217741162222207757 551425581652935833327909)
                ·
                  refine ⟨103392296559925468748983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551425581652935833327909 103392296559925468748983)
                  ·
                    rfl

theorem cell22_906101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_906101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906101 prefixEnd_906101 := by exact prefixLift 906101
  have htrace : WordTrace (prefixWord ++ tailWord_906101) baseStart_906101 baseEnd_906101 := by
    simpa [prefixWord, tailWord_906101, baseEnd_906101] using wordTrace_append hprefix tailTrace_906101
  have hstable : (prefixWord ++ tailWord_906101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906101).length < 2 ^ (prefixWord ++ tailWord_906101).sum := by decide
  have hdescent : baseEnd_906101 < baseStart_906101 := by decide
  rcases family_descends (prefixWord ++ tailWord_906101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906133 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_906133 : Nat := 118140960795 + 906133 * 2 ^ 59
def prefixEnd_906133 : Nat := 4983230072969 + 3 ^ 40 * 906133 * 2
def baseEnd_906133 : Nat := 310187843933738989446851

theorem tailTrace_906133 : CollatzResearch.WordTrace tailWord_906133 prefixEnd_906133 310187843933738989446851 := by
  unfold tailWord_906133
  simp only [CollatzResearch.WordTrace]
  refine ⟨33049385626242371040819053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22032923750828247360546035 33049385626242371040819053)
  ·
    refine ⟨12393519609840889140307145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33049385626242371040819053 12393519609840889140307145)
    ·
      refine ⟨9295139707380666855230359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12393519609840889140307145 9295139707380666855230359)
      ·
        refine ⟨13942709561071000282845539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9295139707380666855230359 13942709561071000282845539)
        ·
          refine ⟨20914064341606500424268309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942709561071000282845539 20914064341606500424268309)
          ·
            refine ⟨980346766012804707387577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20914064341606500424268309 980346766012804707387577)
            ·
              refine ⟨735260074509603530540683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980346766012804707387577 735260074509603530540683)
              ·
                refine ⟨1102890111764405295811025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735260074509603530540683 1102890111764405295811025)
                ·
                  refine ⟨827167583823303971858269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1102890111764405295811025 827167583823303971858269)
                  ·
                    refine ⟨310187843933738989446851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827167583823303971858269 310187843933738989446851)
                    ·
                      rfl

theorem cell22_906133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_906133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906133 prefixEnd_906133 := by exact prefixLift 906133
  have htrace : WordTrace (prefixWord ++ tailWord_906133) baseStart_906133 baseEnd_906133 := by
    simpa [prefixWord, tailWord_906133, baseEnd_906133] using wordTrace_append hprefix tailTrace_906133
  have hstable : (prefixWord ++ tailWord_906133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906133).length < 2 ^ (prefixWord ++ tailWord_906133).sum := by decide
  have hdescent : baseEnd_906133 < baseStart_906133 := by decide
  rcases family_descends (prefixWord ++ tailWord_906133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906144 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_906144 : Nat := 118140960795 + 906144 * 2 ^ 59
def prefixEnd_906144 : Nat := 4983230072969 + 3 ^ 40 * 906144 * 2
def baseEnd_906144 : Nat := 310191609458538627421817

theorem tailTrace_906144 : CollatzResearch.WordTrace tailWord_906144 prefixEnd_906144 310191609458538627421817 := by
  unfold tailWord_906144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524893414601259959734743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22033191219468346612979657 16524893414601259959734743)
  ·
    refine ⟨24787340121901889939602115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16524893414601259959734743 24787340121901889939602115)
    ·
      refine ⟨37181010182852834909403173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24787340121901889939602115 37181010182852834909403173)
      ·
        refine ⟨6971439409284906545513095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37181010182852834909403173 6971439409284906545513095)
        ·
          refine ⟨10457159113927359818269643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971439409284906545513095 10457159113927359818269643)
          ·
            refine ⟨15685738670891039727404465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457159113927359818269643 15685738670891039727404465)
            ·
              refine ⟨11764304003168279795553349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15685738670891039727404465 11764304003168279795553349)
              ·
                refine ⟨2205807000594052461666253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11764304003168279795553349 2205807000594052461666253)
                ·
                  refine ⟨827177625222769673124845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2205807000594052461666253 827177625222769673124845)
                  ·
                    refine ⟨310191609458538627421817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827177625222769673124845 310191609458538627421817)
                    ·
                      rfl

theorem cell22_906144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_906144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906144 prefixEnd_906144 := by exact prefixLift 906144
  have htrace : WordTrace (prefixWord ++ tailWord_906144) baseStart_906144 baseEnd_906144 := by
    simpa [prefixWord, tailWord_906144, baseEnd_906144] using wordTrace_append hprefix tailTrace_906144
  have hstable : (prefixWord ++ tailWord_906144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906144).length < 2 ^ (prefixWord ++ tailWord_906144).sum := by decide
  have hdescent : baseEnd_906144 < baseStart_906144 := by decide
  rcases family_descends (prefixWord ++ tailWord_906144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906236 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_906236 : Nat := 118140960795 + 906236 * 2 ^ 59
def prefixEnd_906236 : Nat := 4983230072969 + 3 ^ 40 * 906236 * 2
def baseEnd_906236 : Nat := 103407700979560351373845

theorem tailTrace_906236 : CollatzResearch.WordTrace tailWord_906236 prefixEnd_906236 103407700979560351373845 := by
  unfold tailWord_906236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16526571172434609815909281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22035428229912813087879041 16526571172434609815909281)
  ·
    refine ⟨12394928379325957361931961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16526571172434609815909281 12394928379325957361931961)
    ·
      refine ⟨9296196284494468021448971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12394928379325957361931961 9296196284494468021448971)
      ·
        refine ⟨13944294426741702032173457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296196284494468021448971 13944294426741702032173457)
        ·
          refine ⟨10458220820056276524130093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13944294426741702032173457 10458220820056276524130093)
          ·
            refine ⟨3921832807521103696548785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10458220820056276524130093 3921832807521103696548785)
            ·
              refine ⟨2941374605640827772411589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921832807521103696548785 2941374605640827772411589)
              ·
                refine ⟨551507738557655207327173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2941374605640827772411589 551507738557655207327173)
                ·
                  refine ⟨103407700979560351373845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 551507738557655207327173 103407700979560351373845)
                  ·
                    rfl

theorem cell22_906236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_906236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906236 prefixEnd_906236 := by exact prefixLift 906236
  have htrace : WordTrace (prefixWord ++ tailWord_906236) baseStart_906236 baseEnd_906236 := by
    simpa [prefixWord, tailWord_906236, baseEnd_906236] using wordTrace_append hprefix tailTrace_906236
  have hstable : (prefixWord ++ tailWord_906236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906236).length < 2 ^ (prefixWord ++ tailWord_906236).sum := by decide
  have hdescent : baseEnd_906236 < baseStart_906236 := by decide
  rcases family_descends (prefixWord ++ tailWord_906236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906251 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 1, 5]
def baseStart_906251 : Nat := 118140960795 + 906251 * 2 ^ 59
def prefixEnd_906251 : Nat := 4983230072969 + 3 ^ 40 * 906251 * 2
def baseEnd_906251 : Nat := 310228237745226014996489

theorem tailTrace_906251 : CollatzResearch.WordTrace tailWord_906251 prefixEnd_906251 310228237745226014996489 := by
  unfold tailWord_906251
  simp only [CollatzResearch.WordTrace]
  refine ⟨33053689439814877193614607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22035792959876584795743071 33053689439814877193614607)
  ·
    refine ⟨49580534159722315790421911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33053689439814877193614607 49580534159722315790421911)
    ·
      refine ⟨74370801239583473685632867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49580534159722315790421911 74370801239583473685632867)
      ·
        refine ⟨111556201859375210528449301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74370801239583473685632867 111556201859375210528449301)
        ·
          refine ⟨5229196962158212993521061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111556201859375210528449301 5229196962158212993521061)
          ·
            refine ⟨980474430404664936285199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5229196962158212993521061 980474430404664936285199)
            ·
              refine ⟨1470711645606997404427799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980474430404664936285199 1470711645606997404427799)
              ·
                refine ⟨2206067468410496106641699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470711645606997404427799 2206067468410496106641699)
                ·
                  refine ⟨3309101202615744159962549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206067468410496106641699 3309101202615744159962549)
                  ·
                    refine ⟨310228237745226014996489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3309101202615744159962549 310228237745226014996489)
                    ·
                      rfl

theorem cell22_906251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5].length) (baseStart_906251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906251 prefixEnd_906251 := by exact prefixLift 906251
  have htrace : WordTrace (prefixWord ++ tailWord_906251) baseStart_906251 baseEnd_906251 := by
    simpa [prefixWord, tailWord_906251, baseEnd_906251] using wordTrace_append hprefix tailTrace_906251
  have hstable : (prefixWord ++ tailWord_906251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906251).length < 2 ^ (prefixWord ++ tailWord_906251).sum := by decide
  have hdescent : baseEnd_906251 < baseStart_906251 := by decide
  rcases family_descends (prefixWord ++ tailWord_906251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906264 : List Nat := [2, 1, 2, 3, 2, 3, 1, 8]
def baseStart_906264 : Nat := 118140960795 + 906264 * 2 ^ 59
def prefixEnd_906264 : Nat := 4983230072969 + 3 ^ 40 * 906264 * 2
def baseEnd_906264 : Nat := 34470298656766479380161

theorem tailTrace_906264 : CollatzResearch.WordTrace tailWord_906264 prefixEnd_906264 34470298656766479380161 := by
  unfold tailWord_906264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527081794383890206918923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22036109059178520275891897 16527081794383890206918923)
  ·
    refine ⟨24790622691575835310378385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16527081794383890206918923 24790622691575835310378385)
    ·
      refine ⟨18592967018681876482783789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24790622691575835310378385 18592967018681876482783789)
      ·
        refine ⟨6972362632005703681043921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18592967018681876482783789 6972362632005703681043921)
        ·
          refine ⟨5229271974004277760782941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972362632005703681043921 5229271974004277760782941)
          ·
            refine ⟨1960976990251604160293603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5229271974004277760782941 1960976990251604160293603)
            ·
              refine ⟨2941465485377406240440405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960976990251604160293603 2941465485377406240440405)
              ·
                refine ⟨34470298656766479380161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2941465485377406240440405 34470298656766479380161)
                ·
                  rfl

theorem cell22_906264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_906264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906264 prefixEnd_906264 := by exact prefixLift 906264
  have htrace : WordTrace (prefixWord ++ tailWord_906264) baseStart_906264 baseEnd_906264 := by
    simpa [prefixWord, tailWord_906264, baseEnd_906264] using wordTrace_append hprefix tailTrace_906264
  have hstable : (prefixWord ++ tailWord_906264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906264).length < 2 ^ (prefixWord ++ tailWord_906264).sum := by decide
  have hdescent : baseEnd_906264 < baseStart_906264 := by decide
  rcases family_descends (prefixWord ++ tailWord_906264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906302 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_906302 : Nat := 118140960795 + 906302 * 2 ^ 59
def prefixEnd_906302 : Nat := 4983230072969 + 3 ^ 40 * 906302 * 2
def baseEnd_906302 : Nat := 310245696087478881971333

theorem tailTrace_906302 : CollatzResearch.WordTrace tailWord_906302 prefixEnd_906302 310245696087478881971333 := by
  unfold tailWord_906302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131943695328764112965145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22037033041753408602480773 4131943695328764112965145)
  ·
    refine ⟨3098957771496573084723859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4131943695328764112965145 3098957771496573084723859)
    ·
      refine ⟨4648436657244859627085789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098957771496573084723859 4648436657244859627085789)
      ·
        refine ⟨1743163746466822360157171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4648436657244859627085789 1743163746466822360157171)
        ·
          refine ⟨2614745619700233540235757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743163746466822360157171 2614745619700233540235757)
          ·
            refine ⟨980529607387587577588409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2614745619700233540235757 980529607387587577588409)
            ·
              refine ⟨735397205540690683191307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980529607387587577588409 735397205540690683191307)
              ·
                refine ⟨1103095808311036024786961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735397205540690683191307 1103095808311036024786961)
                ·
                  refine ⟨827321856233277018590221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103095808311036024786961 827321856233277018590221)
                  ·
                    refine ⟨310245696087478881971333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827321856233277018590221 310245696087478881971333)
                    ·
                      rfl

theorem cell22_906302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_906302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906302 prefixEnd_906302 := by exact prefixLift 906302
  have htrace : WordTrace (prefixWord ++ tailWord_906302) baseStart_906302 baseEnd_906302 := by
    simpa [prefixWord, tailWord_906302, baseEnd_906302] using wordTrace_append hprefix tailTrace_906302
  have hstable : (prefixWord ++ tailWord_906302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906302).length < 2 ^ (prefixWord ++ tailWord_906302).sum := by decide
  have hdescent : baseEnd_906302 < baseStart_906302 := by decide
  rcases family_descends (prefixWord ++ tailWord_906302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906401 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_906401 : Nat := 118140960795 + 906401 * 2 ^ 59
def prefixEnd_906401 : Nat := 4983230072969 + 3 ^ 40 * 906401 * 2
def baseEnd_906401 : Nat := 310279585810675623746029

theorem tailTrace_906401 : CollatzResearch.WordTrace tailWord_906401 prefixEnd_906401 310279585810675623746029 := by
  unfold tailWord_906401
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059160389271452811575057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22039440259514301874383371 33059160389271452811575057)
  ·
    refine ⟨24794370291953589608681293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33059160389271452811575057 24794370291953589608681293)
    ·
      refine ⟨9297888859482596103255485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24794370291953589608681293 9297888859482596103255485)
      ·
        refine ⟨3486708322305973538720807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9297888859482596103255485 3486708322305973538720807)
        ·
          refine ⟨5230062483458960308081211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486708322305973538720807 5230062483458960308081211)
          ·
            refine ⟨7845093725188440462121817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230062483458960308081211 7845093725188440462121817)
            ·
              refine ⟨5883820293891330346591363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845093725188440462121817 5883820293891330346591363)
              ·
                refine ⟨8825730440836995519887045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883820293891330346591363 8825730440836995519887045)
                ·
                  refine ⟨1654824457656936659978821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8825730440836995519887045 1654824457656936659978821)
                  ·
                    refine ⟨310279585810675623746029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1654824457656936659978821 310279585810675623746029)
                    ·
                      rfl

theorem cell22_906401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_906401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906401 prefixEnd_906401 := by exact prefixLift 906401
  have htrace : WordTrace (prefixWord ++ tailWord_906401) baseStart_906401 baseEnd_906401 := by
    simpa [prefixWord, tailWord_906401, baseEnd_906401] using wordTrace_append hprefix tailTrace_906401
  have hstable : (prefixWord ++ tailWord_906401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906401).length < 2 ^ (prefixWord ++ tailWord_906401).sum := by decide
  have hdescent : baseEnd_906401 < baseStart_906401 := by decide
  rcases family_descends (prefixWord ++ tailWord_906401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906433 : List Nat := [1, 2, 6, 1, 1, 2, 1, 8]
def baseStart_906433 : Nat := 118140960795 + 906433 * 2 ^ 59
def prefixEnd_906433 : Nat := 4983230072969 + 3 ^ 40 * 906433 * 2
def baseEnd_906433 : Nat := 34476726673848689660659

theorem tailTrace_906433 : CollatzResearch.WordTrace tailWord_906433 prefixEnd_906433 34476726673848689660659 := by
  unfold tailWord_906433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33060327525155522276739953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22040218350103681517826635 33060327525155522276739953)
  ·
    refine ⟨24795245643866641707554965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33060327525155522276739953 24795245643866641707554965)
    ·
      refine ⟨1162277139556248830041639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24795245643866641707554965 1162277139556248830041639)
      ·
        refine ⟨1743415709334373245062459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162277139556248830041639 1743415709334373245062459)
        ·
          refine ⟨2615123564001559867593689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743415709334373245062459 2615123564001559867593689)
          ·
            refine ⟨1961342673001169900695267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615123564001559867593689 1961342673001169900695267)
            ·
              refine ⟨2942014009501754851042901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961342673001169900695267 2942014009501754851042901)
              ·
                refine ⟨34476726673848689660659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2942014009501754851042901 34476726673848689660659)
                ·
                  rfl

theorem cell22_906433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 8].length) (baseStart_906433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906433 prefixEnd_906433 := by exact prefixLift 906433
  have htrace : WordTrace (prefixWord ++ tailWord_906433) baseStart_906433 baseEnd_906433 := by
    simpa [prefixWord, tailWord_906433, baseEnd_906433] using wordTrace_append hprefix tailTrace_906433
  have hstable : (prefixWord ++ tailWord_906433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906433).length < 2 ^ (prefixWord ++ tailWord_906433).sum := by decide
  have hdescent : baseEnd_906433 < baseStart_906433 := by decide
  rcases family_descends (prefixWord ++ tailWord_906433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906465 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_906465 : Nat := 118140960795 + 906465 * 2 ^ 59
def prefixEnd_906465 : Nat := 4983230072969 + 3 ^ 40 * 906465 * 2
def baseEnd_906465 : Nat := 310301494318600790145833

theorem tailTrace_906465 : CollatzResearch.WordTrace tailWord_906465 prefixEnd_906465 310301494318600790145833 := by
  unfold tailWord_906465
  simp only [CollatzResearch.WordTrace]
  refine ⟨33061494661039591741904849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22040996440693061161269899 33061494661039591741904849)
  ·
    refine ⟨24796120995779693806428637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33061494661039591741904849 24796120995779693806428637)
    ·
      refine ⟨9298545373417385177410739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24796120995779693806428637 9298545373417385177410739)
      ·
        refine ⟨13947818060126077766116109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9298545373417385177410739 13947818060126077766116109)
        ·
          refine ⟨5230431772547279162293541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13947818060126077766116109 5230431772547279162293541)
          ·
            refine ⟨980705957352614842930039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5230431772547279162293541 980705957352614842930039)
            ·
              refine ⟨1471058936028922264395059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980705957352614842930039 1471058936028922264395059)
              ·
                refine ⟨2206588404043383396592589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471058936028922264395059 2206588404043383396592589)
                ·
                  refine ⟨827470651516268773722221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2206588404043383396592589 827470651516268773722221)
                  ·
                    refine ⟨310301494318600790145833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827470651516268773722221 310301494318600790145833)
                    ·
                      rfl

theorem cell22_906465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_906465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906465 prefixEnd_906465 := by exact prefixLift 906465
  have htrace : WordTrace (prefixWord ++ tailWord_906465) baseStart_906465 baseEnd_906465 := by
    simpa [prefixWord, tailWord_906465, baseEnd_906465] using wordTrace_append hprefix tailTrace_906465
  have hstable : (prefixWord ++ tailWord_906465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906465).length < 2 ^ (prefixWord ++ tailWord_906465).sum := by decide
  have hdescent : baseEnd_906465 < baseStart_906465 := by decide
  rcases family_descends (prefixWord ++ tailWord_906465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906572 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_906572 : Nat := 118140960795 + 906572 * 2 ^ 59
def prefixEnd_906572 : Nat := 4983230072969 + 3 ^ 40 * 906572 * 2
def baseEnd_906572 : Nat := 310338122605288177720505

theorem tailTrace_906572 : CollatzResearch.WordTrace tailWord_906572 prefixEnd_906572 310338122605288177720505 := by
  unfold tailWord_906572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532698635825974508024985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22043598181101299344033313 16532698635825974508024985)
  ·
    refine ⟨12399523976869480881018739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16532698635825974508024985 12399523976869480881018739)
    ·
      refine ⟨18599285965304221321528109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12399523976869480881018739 18599285965304221321528109)
      ·
        refine ⟨6974732236989082995573041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18599285965304221321528109 6974732236989082995573041)
        ·
          refine ⟨5231049177741812246679781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6974732236989082995573041 5231049177741812246679781)
          ·
            refine ⟨980821720826589796252459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5231049177741812246679781 980821720826589796252459)
            ·
              refine ⟨1471232581239884694378689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980821720826589796252459 1471232581239884694378689)
              ·
                refine ⟨1103424435929913520784017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471232581239884694378689 1103424435929913520784017)
                ·
                  refine ⟨827568326947435140588013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103424435929913520784017 827568326947435140588013)
                  ·
                    refine ⟨310338122605288177720505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827568326947435140588013 310338122605288177720505)
                    ·
                      rfl

theorem cell22_906572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_906572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906572 prefixEnd_906572 := by exact prefixLift 906572
  have htrace : WordTrace (prefixWord ++ tailWord_906572) baseStart_906572 baseEnd_906572 := by
    simpa [prefixWord, tailWord_906572, baseEnd_906572] using wordTrace_append hprefix tailTrace_906572
  have hstable : (prefixWord ++ tailWord_906572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906572).length < 2 ^ (prefixWord ++ tailWord_906572).sum := by decide
  have hdescent : baseEnd_906572 < baseStart_906572 := by decide
  rcases family_descends (prefixWord ++ tailWord_906572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906602 : List Nat := [3, 1, 3, 3, 2, 2, 2, 6]
def baseStart_906602 : Nat := 118140960795 + 906602 * 2 ^ 59
def prefixEnd_906602 : Nat := 4983230072969 + 3 ^ 40 * 906602 * 2
def baseEnd_906602 : Nat := 34483154690930899941157

theorem tailTrace_906602 : CollatzResearch.WordTrace tailWord_906602 prefixEnd_906602 34483154690930899941157 := by
  unfold tailWord_906602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266622865385816034910515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22044327641028842759761373 8266622865385816034910515)
  ·
    refine ⟨12399934298078724052365773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8266622865385816034910515 12399934298078724052365773)
    ·
      refine ⟨4649975361779521519637165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12399934298078724052365773 4649975361779521519637165)
      ·
        refine ⟨1743740760667320569863937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4649975361779521519637165 1743740760667320569863937)
        ·
          refine ⟨1307805570500490427397953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1743740760667320569863937 1307805570500490427397953)
          ·
            refine ⟨980854177875367820548465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307805570500490427397953 980854177875367820548465)
            ·
              refine ⟨735640633406525865411349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980854177875367820548465 735640633406525865411349)
              ·
                refine ⟨34483154690930899941157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 735640633406525865411349 34483154690930899941157)
                ·
                  rfl

theorem cell22_906602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_906602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906602 prefixEnd_906602 := by exact prefixLift 906602
  have htrace : WordTrace (prefixWord ++ tailWord_906602) baseStart_906602 baseEnd_906602 := by
    simpa [prefixWord, tailWord_906602, baseEnd_906602] using wordTrace_append hprefix tailTrace_906602
  have hstable : (prefixWord ++ tailWord_906602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906602).length < 2 ^ (prefixWord ++ tailWord_906602).sum := by decide
  have hdescent : baseEnd_906602 < baseStart_906602 := by decide
  rcases family_descends (prefixWord ++ tailWord_906602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906617 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 1, 3]
def baseStart_906617 : Nat := 118140960795 + 906617 * 2 ^ 59
def prefixEnd_906617 : Nat := 4983230072969 + 3 ^ 40 * 906617 * 2
def baseEnd_906617 : Nat := 310353527024923060345367

theorem tailTrace_906617 : CollatzResearch.WordTrace tailWord_906617 prefixEnd_906617 310353527024923060345367 := by
  unfold tailWord_906617
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067038556488921701438105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22044692370992614467625403 33067038556488921701438105)
  ·
    refine ⟨24800278917366691276078579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33067038556488921701438105 24800278917366691276078579)
    ·
      refine ⟨37200418376050036914117869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24800278917366691276078579 37200418376050036914117869)
      ·
        refine ⟨13950156891018763842794201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37200418376050036914117869 13950156891018763842794201)
        ·
          refine ⟨10462617668264072882095651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13950156891018763842794201 10462617668264072882095651)
          ·
            refine ⟨15693926502396109323143477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10462617668264072882095651 15693926502396109323143477)
            ·
              refine ⟨1471305609599635249044701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15693926502396109323143477 1471305609599635249044701)
              ·
                refine ⟨551739603599863218391763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1471305609599635249044701 551739603599863218391763)
                ·
                  refine ⟨827609405399794827587645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551739603599863218391763 827609405399794827587645)
                  ·
                    refine ⟨310353527024923060345367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827609405399794827587645 310353527024923060345367)
                    ·
                      rfl

theorem cell22_906617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_906617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906617 prefixEnd_906617 := by exact prefixLift 906617
  have htrace : WordTrace (prefixWord ++ tailWord_906617) baseStart_906617 baseEnd_906617 := by
    simpa [prefixWord, tailWord_906617, baseEnd_906617] using wordTrace_append hprefix tailTrace_906617
  have hstable : (prefixWord ++ tailWord_906617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906617).length < 2 ^ (prefixWord ++ tailWord_906617).sum := by decide
  have hdescent : baseEnd_906617 < baseStart_906617 := by decide
  rcases family_descends (prefixWord ++ tailWord_906617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906703 : List Nat := [1, 1, 2, 1, 1, 4, 5, 7]
def baseStart_906703 : Nat := 118140960795 + 906703 * 2 ^ 59
def prefixEnd_906703 : Nat := 4983230072969 + 3 ^ 40 * 906703 * 2
def baseEnd_906703 : Nat := 34486996286938611410567

theorem tailTrace_906703 : CollatzResearch.WordTrace tailWord_906703 prefixEnd_906703 34486996286938611410567 := by
  unfold tailWord_906703
  simp only [CollatzResearch.WordTrace]
  refine ⟨33070175234177358389068763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22046783489451572259379175 33070175234177358389068763)
  ·
    refine ⟨49605262851266037583603145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33070175234177358389068763 49605262851266037583603145)
    ·
      refine ⟨37203947138449528187702359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49605262851266037583603145 37203947138449528187702359)
      ·
        refine ⟨55805920707674292281553539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37203947138449528187702359 55805920707674292281553539)
        ·
          refine ⟨83708881061511438422330309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55805920707674292281553539 83708881061511438422330309)
          ·
            refine ⟨15695415199033394704186933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83708881061511438422330309 15695415199033394704186933)
            ·
              refine ⟨1471445174909380753517525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15695415199033394704186933 1471445174909380753517525)
              ·
                refine ⟨34486996286938611410567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1471445174909380753517525 34486996286938611410567)
                ·
                  rfl

theorem cell22_906703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 7].length) (baseStart_906703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906703 prefixEnd_906703 := by exact prefixLift 906703
  have htrace : WordTrace (prefixWord ++ tailWord_906703) baseStart_906703 baseEnd_906703 := by
    simpa [prefixWord, tailWord_906703, baseEnd_906703] using wordTrace_append hprefix tailTrace_906703
  have hstable : (prefixWord ++ tailWord_906703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906703).length < 2 ^ (prefixWord ++ tailWord_906703).sum := by decide
  have hdescent : baseEnd_906703 < baseStart_906703 := by decide
  rcases family_descends (prefixWord ++ tailWord_906703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906741 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_906741 : Nat := 118140960795 + 906741 * 2 ^ 59
def prefixEnd_906741 : Nat := 4983230072969 + 3 ^ 40 * 906741 * 2
def baseEnd_906741 : Nat := 310395974759028070244987

theorem tailTrace_906741 : CollatzResearch.WordTrace tailWord_906741 prefixEnd_906741 310395974759028070244987 := by
  unfold tailWord_906741
  simp only [CollatzResearch.WordTrace]
  refine ⟨33071561208039690878952077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22047707472026460585968051 33071561208039690878952077)
  ·
    refine ⟨12401835453014884079607029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33071561208039690878952077 12401835453014884079607029)
    ·
      refine ⟨1162672073720145382463159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12401835453014884079607029 1162672073720145382463159)
      ·
        refine ⟨1744008110580218073694739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162672073720145382463159 1744008110580218073694739)
        ·
          refine ⟨2616012165870327110542109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744008110580218073694739 2616012165870327110542109)
          ·
            refine ⟨981004562201372666453291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2616012165870327110542109 981004562201372666453291)
            ·
              refine ⟨1471506843302058999679937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981004562201372666453291 1471506843302058999679937)
              ·
                refine ⟨1103630132476544249759953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471506843302058999679937 1103630132476544249759953)
                ·
                  refine ⟨827722599357408187319965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1103630132476544249759953 827722599357408187319965)
                  ·
                    refine ⟨310395974759028070244987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827722599357408187319965 310395974759028070244987)
                    ·
                      rfl

theorem cell22_906741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_906741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906741 prefixEnd_906741 := by exact prefixLift 906741
  have htrace : WordTrace (prefixWord ++ tailWord_906741) baseStart_906741 baseEnd_906741 := by
    simpa [prefixWord, tailWord_906741, baseEnd_906741] using wordTrace_append hprefix tailTrace_906741
  have hstable : (prefixWord ++ tailWord_906741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906741).length < 2 ^ (prefixWord ++ tailWord_906741).sum := by decide
  have hdescent : baseEnd_906741 < baseStart_906741 := by decide
  rcases family_descends (prefixWord ++ tailWord_906741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
