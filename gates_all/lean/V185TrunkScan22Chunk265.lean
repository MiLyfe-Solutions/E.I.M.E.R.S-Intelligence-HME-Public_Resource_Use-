import V185TrunkScan22Chunk264

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2363044 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_2363044 : Nat := 118140960795 + 2363044 * 2 ^ 59
def prefixEnd_2363044 : Nat := 4983230072969 + 3 ^ 40 * 2363044 * 2
def baseEnd_2363044 : Nat := 808918253148771875455043

theorem tailTrace_2363044 : CollatzResearch.WordTrace tailWord_2363044 prefixEnd_2363044 808918253148771875455043 := by
  unfold tailWord_2363044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43093647625551319315000093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57458196834068425753333457 43093647625551319315000093)
  ·
    refine ⟨16160117859581744743125035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43093647625551319315000093 16160117859581744743125035)
    ·
      refine ⟨24240176789372617114687553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16160117859581744743125035 24240176789372617114687553)
      ·
        refine ⟨18180132592029462836015665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24240176789372617114687553 18180132592029462836015665)
        ·
          refine ⟨13635099444022097127011749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18180132592029462836015665 13635099444022097127011749)
          ·
            refine ⟨2556581145754143211314703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13635099444022097127011749 2556581145754143211314703)
            ·
              refine ⟨3834871718631214816972055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556581145754143211314703 3834871718631214816972055)
              ·
                refine ⟨5752307577946822225458083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834871718631214816972055 5752307577946822225458083)
                ·
                  refine ⟨8628461366920233338187125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752307577946822225458083 8628461366920233338187125)
                  ·
                    refine ⟨808918253148771875455043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8628461366920233338187125 808918253148771875455043)
                    ·
                      rfl

theorem cell22_2363044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_2363044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363044 prefixEnd_2363044 := by exact prefixLift 2363044
  have htrace : WordTrace (prefixWord ++ tailWord_2363044) baseStart_2363044 baseEnd_2363044 := by
    simpa [prefixWord, tailWord_2363044, baseEnd_2363044] using wordTrace_append hprefix tailTrace_2363044
  have hstable : (prefixWord ++ tailWord_2363044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363044).length < 2 ^ (prefixWord ++ tailWord_2363044).sum := by decide
  have hdescent : baseEnd_2363044 < baseStart_2363044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363055 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_2363055 : Nat := 118140960795 + 2363055 * 2 ^ 59
def prefixEnd_2363055 : Nat := 4983230072969 + 3 ^ 40 * 2363055 * 2
def baseEnd_2363055 : Nat := 808922018673571513430009

theorem tailTrace_2363055 : CollatzResearch.WordTrace tailWord_2363055 prefixEnd_2363055 808922018673571513430009 := by
  unfold tailWord_2363055
  simp only [CollatzResearch.WordTrace]
  refine ⟨86187696454062787508650619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57458464302708525005767079 86187696454062787508650619)
  ·
    refine ⟨129281544681094181262975929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86187696454062787508650619 129281544681094181262975929)
    ·
      refine ⟨96961158510820635947231947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129281544681094181262975929 96961158510820635947231947)
      ·
        refine ⟨145441737766230953920847921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96961158510820635947231947 145441737766230953920847921)
        ·
          refine ⟨109081303324673215440635941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145441737766230953920847921 109081303324673215440635941)
          ·
            refine ⟨20452744373376227895119239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109081303324673215440635941 20452744373376227895119239)
            ·
              refine ⟨30679116560064341842678859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20452744373376227895119239 30679116560064341842678859)
              ·
                refine ⟨46018674840096512764018289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30679116560064341842678859 46018674840096512764018289)
                ·
                  refine ⟨34514006130072384573013717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46018674840096512764018289 34514006130072384573013717)
                  ·
                    refine ⟨808922018673571513430009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34514006130072384573013717 808922018673571513430009)
                    ·
                      rfl

theorem cell22_2363055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_2363055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363055 prefixEnd_2363055 := by exact prefixLift 2363055
  have htrace : WordTrace (prefixWord ++ tailWord_2363055) baseStart_2363055 baseEnd_2363055 := by
    simpa [prefixWord, tailWord_2363055, baseEnd_2363055] using wordTrace_append hprefix tailTrace_2363055
  have hstable : (prefixWord ++ tailWord_2363055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363055).length < 2 ^ (prefixWord ++ tailWord_2363055).sum := by decide
  have hdescent : baseEnd_2363055 < baseStart_2363055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363078 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2363078 : Nat := 118140960795 + 2363078 * 2 ^ 59
def prefixEnd_2363078 : Nat := 4983230072969 + 3 ^ 40 * 2363078 * 2
def baseEnd_2363078 : Nat := 808929892043607120104939

theorem tailTrace_2363078 : CollatzResearch.WordTrace tailWord_2363078 prefixEnd_2363078 808929892043607120104939 := by
  unfold tailWord_2363078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693391729155608201148059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57459023555319641624491925 2693391729155608201148059)
  ·
    refine ⟨4040087593733412301722089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693391729155608201148059 4040087593733412301722089)
    ·
      refine ⟨3030065695300059226291567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4040087593733412301722089 3030065695300059226291567)
      ·
        refine ⟨4545098542950088839437351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030065695300059226291567 4545098542950088839437351)
        ·
          refine ⟨6817647814425133259156027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545098542950088839437351 6817647814425133259156027)
          ·
            refine ⟨10226471721637699888734041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6817647814425133259156027 10226471721637699888734041)
            ·
              refine ⟨7669853791228274916550531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10226471721637699888734041 7669853791228274916550531)
              ·
                refine ⟨11504780686842412374825797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7669853791228274916550531 11504780686842412374825797)
                ·
                  refine ⟨2157146378782952320279837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11504780686842412374825797 2157146378782952320279837)
                  ·
                    refine ⟨808929892043607120104939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157146378782952320279837 808929892043607120104939)
                    ·
                      rfl

theorem cell22_2363078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2363078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363078 prefixEnd_2363078 := by exact prefixLift 2363078
  have htrace : WordTrace (prefixWord ++ tailWord_2363078) baseStart_2363078 baseEnd_2363078 := by
    simpa [prefixWord, tailWord_2363078, baseEnd_2363078] using wordTrace_append hprefix tailTrace_2363078
  have hstable : (prefixWord ++ tailWord_2363078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363078).length < 2 ^ (prefixWord ++ tailWord_2363078).sum := by decide
  have hdescent : baseEnd_2363078 < baseStart_2363078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363089 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_2363089 : Nat := 118140960795 + 2363089 * 2 ^ 59
def prefixEnd_2363089 : Nat := 4983230072969 + 3 ^ 40 * 2363089 * 2
def baseEnd_2363089 : Nat := 808933657568406758079905

theorem tailTrace_2363089 : CollatzResearch.WordTrace tailWord_2363089 prefixEnd_2363089 808933657568406758079905 := by
  unfold tailWord_2363089
  simp only [CollatzResearch.WordTrace]
  refine ⟨86188936535939611315388321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57459291023959740876925547 86188936535939611315388321)
  ·
    refine ⟨64641702401954708486541241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86188936535939611315388321 64641702401954708486541241)
    ·
      refine ⟨48481276801466031364905931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64641702401954708486541241 48481276801466031364905931)
      ·
        refine ⟨72721915202199047047358897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48481276801466031364905931 72721915202199047047358897)
        ·
          refine ⟨54541436401649285285519173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72721915202199047047358897 54541436401649285285519173)
          ·
            refine ⟨10226519325309240991034845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54541436401649285285519173 10226519325309240991034845)
            ·
              refine ⟨3834944746990965371638067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10226519325309240991034845 3834944746990965371638067)
              ·
                refine ⟨5752417120486448057457101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834944746990965371638067 5752417120486448057457101)
                ·
                  refine ⟨2157156420182418021546413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5752417120486448057457101 2157156420182418021546413)
                  ·
                    refine ⟨808933657568406758079905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157156420182418021546413 808933657568406758079905)
                    ·
                      rfl

theorem cell22_2363089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_2363089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363089 prefixEnd_2363089 := by exact prefixLift 2363089
  have htrace : WordTrace (prefixWord ++ tailWord_2363089) baseStart_2363089 baseEnd_2363089 := by
    simpa [prefixWord, tailWord_2363089, baseEnd_2363089] using wordTrace_append hprefix tailTrace_2363089
  have hstable : (prefixWord ++ tailWord_2363089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363089).length < 2 ^ (prefixWord ++ tailWord_2363089).sum := by decide
  have hdescent : baseEnd_2363089 < baseStart_2363089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363140 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_2363140 : Nat := 118140960795 + 2363140 * 2 ^ 59
def prefixEnd_2363140 : Nat := 4983230072969 + 3 ^ 40 * 2363140 * 2
def baseEnd_2363140 : Nat := 808951115910659625054749

theorem tailTrace_2363140 : CollatzResearch.WordTrace tailWord_2363140 prefixEnd_2363140 808951115910659625054749 := by
  unfold tailWord_2363140
  simp only [CollatzResearch.WordTrace]
  refine ⟨43095398329377423512747437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57460531105836564683663249 43095398329377423512747437)
  ·
    refine ⟨16160774373516533817280289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43095398329377423512747437 16160774373516533817280289)
    ·
      refine ⟨12120580780137400362960217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16160774373516533817280289 12120580780137400362960217)
      ·
        refine ⟨9090435585103050272220163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12120580780137400362960217 9090435585103050272220163)
        ·
          refine ⟨13635653377654575408330245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9090435585103050272220163 13635653377654575408330245)
          ·
            refine ⟨2556685008310232889061921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13635653377654575408330245 2556685008310232889061921)
            ·
              refine ⟨1917513756232674666796441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556685008310232889061921 1917513756232674666796441)
              ·
                refine ⟨1438135317174506000097331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917513756232674666796441 1438135317174506000097331)
                ·
                  refine ⟨2157202975761759000145997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438135317174506000097331 2157202975761759000145997)
                  ·
                    refine ⟨808951115910659625054749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157202975761759000145997 808951115910659625054749)
                    ·
                      rfl

theorem cell22_2363140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_2363140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363140 prefixEnd_2363140 := by exact prefixLift 2363140
  have htrace : WordTrace (prefixWord ++ tailWord_2363140) baseStart_2363140 baseEnd_2363140 := by
    simpa [prefixWord, tailWord_2363140, baseEnd_2363140] using wordTrace_append hprefix tailTrace_2363140
  have hstable : (prefixWord ++ tailWord_2363140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363140).length < 2 ^ (prefixWord ++ tailWord_2363140).sum := by decide
  have hdescent : baseEnd_2363140 < baseStart_2363140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363142 : List Nat := [6, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2363142 : Nat := 118140960795 + 2363142 * 2 ^ 59
def prefixEnd_2363142 : Nat := 4983230072969 + 3 ^ 40 * 2363142 * 2
def baseEnd_2363142 : Nat := 89883533394614698500527

theorem tailTrace_2363142 : CollatzResearch.WordTrace tailWord_2363142 prefixEnd_2363142 89883533394614698500527 := by
  unfold tailWord_2363142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693464675148362542720865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57460579736498400911378453 2693464675148362542720865)
  ·
    refine ⟨2020098506361271907040649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2693464675148362542720865 2020098506361271907040649)
    ·
      refine ⟨1515073879770953930280487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2020098506361271907040649 1515073879770953930280487)
      ·
        refine ⟨2272610819656430895420731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515073879770953930280487 2272610819656430895420731)
        ·
          refine ⟨3408916229484646343131097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272610819656430895420731 3408916229484646343131097)
          ·
            refine ⟨2556687172113484757348323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408916229484646343131097 2556687172113484757348323)
            ·
              refine ⟨3835030758170227136022485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556687172113484757348323 3835030758170227136022485)
              ·
                refine ⟨89883533394614698500527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3835030758170227136022485 89883533394614698500527)
                ·
                  rfl

theorem cell22_2363142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2363142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363142 prefixEnd_2363142 := by exact prefixLift 2363142
  have htrace : WordTrace (prefixWord ++ tailWord_2363142) baseStart_2363142 baseEnd_2363142 := by
    simpa [prefixWord, tailWord_2363142, baseEnd_2363142] using wordTrace_append hprefix tailTrace_2363142
  have hstable : (prefixWord ++ tailWord_2363142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363142).length < 2 ^ (prefixWord ++ tailWord_2363142).sum := by decide
  have hdescent : baseEnd_2363142 < baseStart_2363142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363192 : List Nat := [2, 1, 2, 1, 3, 4, 9]
def baseStart_2363192 : Nat := 118140960795 + 2363192 * 2 ^ 59
def prefixEnd_2363192 : Nat := 4983230072969 + 3 ^ 40 * 2363192 * 2
def baseEnd_2363192 : Nat := 29961811724938845287207

theorem tailTrace_2363192 : CollatzResearch.WordTrace tailWord_2363192 prefixEnd_2363192 29961811724938845287207 := by
  unfold tailWord_2363192
  simp only [CollatzResearch.WordTrace]
  refine ⟨43096346627283229953193915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57461795503044306604258553 43096346627283229953193915)
  ·
    refine ⟨64644519940924844929790873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43096346627283229953193915 64644519940924844929790873)
    ·
      refine ⟨48483389955693633697343155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64644519940924844929790873 48483389955693633697343155)
      ·
        refine ⟨72725084933540450546014733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48483389955693633697343155 72725084933540450546014733)
        ·
          refine ⟨27271906850077668954755525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72725084933540450546014733 27271906850077668954755525)
          ·
            refine ⟨5113482534389562929016661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27271906850077668954755525 5113482534389562929016661)
            ·
              refine ⟨29961811724938845287207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5113482534389562929016661 29961811724938845287207)
              ·
                rfl

theorem cell22_2363192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 9].length) (baseStart_2363192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363192 prefixEnd_2363192 := by exact prefixLift 2363192
  have htrace : WordTrace (prefixWord ++ tailWord_2363192) baseStart_2363192 baseEnd_2363192 := by
    simpa [prefixWord, tailWord_2363192, baseEnd_2363192] using wordTrace_append hprefix tailTrace_2363192
  have hstable : (prefixWord ++ tailWord_2363192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363192).length < 2 ^ (prefixWord ++ tailWord_2363192).sum := by decide
  have hdescent : baseEnd_2363192 < baseStart_2363192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363196 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2363196 : Nat := 118140960795 + 2363196 * 2 ^ 59
def prefixEnd_2363196 : Nat := 4983230072969 + 3 ^ 40 * 2363196 * 2
def baseEnd_2363196 : Nat := 808970285855094145654577

theorem tailTrace_2363196 : CollatzResearch.WordTrace tailWord_2363196 prefixEnd_2363196 808970285855094145654577 := by
  unfold tailWord_2363196
  simp only [CollatzResearch.WordTrace]
  refine ⟨43096419573275984294766721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57461892764367979059688961 43096419573275984294766721)
  ·
    refine ⟨32322314679956988221075041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43096419573275984294766721 32322314679956988221075041)
    ·
      refine ⟨24241736009967741165806281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32322314679956988221075041 24241736009967741165806281)
      ·
        refine ⟨18181302007475805874354711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24241736009967741165806281 18181302007475805874354711)
        ·
          refine ⟨27271953011213708811532067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18181302007475805874354711 27271953011213708811532067)
          ·
            refine ⟨40907929516820563217298101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27271953011213708811532067 40907929516820563217298101)
            ·
              refine ⟨3835118392201927801621697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40907929516820563217298101 3835118392201927801621697)
              ·
                refine ⟨2876338794151445851216273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3835118392201927801621697 2876338794151445851216273)
                ·
                  refine ⟨2157254095613584388412205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876338794151445851216273 2157254095613584388412205)
                  ·
                    refine ⟨808970285855094145654577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157254095613584388412205 808970285855094145654577)
                    ·
                      rfl

theorem cell22_2363196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2363196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363196 prefixEnd_2363196 := by exact prefixLift 2363196
  have htrace : WordTrace (prefixWord ++ tailWord_2363196) baseStart_2363196 baseEnd_2363196 := by
    simpa [prefixWord, tailWord_2363196, baseEnd_2363196] using wordTrace_append hprefix tailTrace_2363196
  have hstable : (prefixWord ++ tailWord_2363196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363196).length < 2 ^ (prefixWord ++ tailWord_2363196).sum := by decide
  have hdescent : baseEnd_2363196 < baseStart_2363196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363213 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2363213 : Nat := 118140960795 + 2363213 * 2 ^ 59
def prefixEnd_2363213 : Nat := 4983230072969 + 3 ^ 40 * 2363213 * 2
def baseEnd_2363213 : Nat := 808976105302511767979525

theorem tailTrace_2363213 : CollatzResearch.WordTrace tailWord_2363213 prefixEnd_2363213 808976105302511767979525 := by
  unfold tailWord_2363213
  simp only [CollatzResearch.WordTrace]
  refine ⟨86193459187490380492902293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57462306124993586995268195 86193459187490380492902293)
  ·
    refine ⟨4040318399413611585604795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86193459187490380492902293 4040318399413611585604795)
    ·
      refine ⟨6060477599120417378407193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040318399413611585604795 6060477599120417378407193)
      ·
        refine ⟨4545358199340313033805395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6060477599120417378407193 4545358199340313033805395)
        ·
          refine ⟨6818037299010469550708093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545358199340313033805395 6818037299010469550708093)
          ·
            refine ⟨2556763987128926081515535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6818037299010469550708093 2556763987128926081515535)
            ·
              refine ⟨3835145980693389122273303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556763987128926081515535 3835145980693389122273303)
              ·
                refine ⟨5752718971040083683409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835145980693389122273303 5752718971040083683409955)
                ·
                  refine ⟨8629078456560125525114933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752718971040083683409955 8629078456560125525114933)
                  ·
                    refine ⟨808976105302511767979525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8629078456560125525114933 808976105302511767979525)
                    ·
                      rfl

theorem cell22_2363213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2363213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363213 prefixEnd_2363213 := by exact prefixLift 2363213
  have htrace : WordTrace (prefixWord ++ tailWord_2363213) baseStart_2363213 baseEnd_2363213 := by
    simpa [prefixWord, tailWord_2363213, baseEnd_2363213] using wordTrace_append hprefix tailTrace_2363213
  have hstable : (prefixWord ++ tailWord_2363213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363213).length < 2 ^ (prefixWord ++ tailWord_2363213).sum := by decide
  have hdescent : baseEnd_2363213 < baseStart_2363213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363271 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 5]
def baseStart_2363271 : Nat := 118140960795 + 2363271 * 2 ^ 59
def prefixEnd_2363271 : Nat := 4983230072969 + 3 ^ 40 * 2363271 * 2
def baseEnd_2363271 : Nat := 269665319962606316676449

theorem tailTrace_2363271 : CollatzResearch.WordTrace tailWord_2363271 prefixEnd_2363271 269665319962606316676449 := by
  unfold tailWord_2363271
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195574621280256398513667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57463716414186837599009111 86195574621280256398513667)
  ·
    refine ⟨129293361931920384597770501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86195574621280256398513667 129293361931920384597770501)
    ·
      refine ⟨24242505362235072112081969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129293361931920384597770501 24242505362235072112081969)
      ·
        refine ⟨18181879021676304084061477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24242505362235072112081969 18181879021676304084061477)
        ·
          refine ⟨3409102316564307015761527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18181879021676304084061477 3409102316564307015761527)
          ·
            refine ⟨5113653474846460523642291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409102316564307015761527 5113653474846460523642291)
            ·
              refine ⟨7670480212269690785463437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113653474846460523642291 7670480212269690785463437)
              ·
                refine ⟨2876430079601134044548789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7670480212269690785463437 2876430079601134044548789)
                ·
                  refine ⟨269665319962606316676449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2876430079601134044548789 269665319962606316676449)
                  ·
                    rfl

theorem cell22_2363271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 5].length) (baseStart_2363271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363271 prefixEnd_2363271 := by exact prefixLift 2363271
  have htrace : WordTrace (prefixWord ++ tailWord_2363271) baseStart_2363271 baseEnd_2363271 := by
    simpa [prefixWord, tailWord_2363271, baseEnd_2363271] using wordTrace_append hprefix tailTrace_2363271
  have hstable : (prefixWord ++ tailWord_2363271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363271).length < 2 ^ (prefixWord ++ tailWord_2363271).sum := by decide
  have hdescent : baseEnd_2363271 < baseStart_2363271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363376 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_2363376 : Nat := 118140960795 + 2363376 * 2 ^ 59
def prefixEnd_2363376 : Nat := 4983230072969 + 3 ^ 40 * 2363376 * 2
def baseEnd_2363376 : Nat := 809031903533633676154025

theorem tailTrace_2363376 : CollatzResearch.WordTrace tailWord_2363376 prefixEnd_2363376 809031903533633676154025 := by
  unfold tailWord_2363376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43099702142949929665542991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57466269523933239554057321 43099702142949929665542991)
  ·
    refine ⟨64649553214424894498314487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43099702142949929665542991 64649553214424894498314487)
    ·
      refine ⟨96974329821637341747471731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64649553214424894498314487 96974329821637341747471731)
      ·
        refine ⟨145461494732456012621207597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96974329821637341747471731 145461494732456012621207597)
        ·
          refine ⟨54548060524671004732952849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145461494732456012621207597 54548060524671004732952849)
          ·
            refine ⟨40911045393503253549714637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54548060524671004732952849 40911045393503253549714637)
            ·
              refine ⟨15341642022563720081142989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40911045393503253549714637 15341642022563720081142989)
              ·
                refine ⟨5753115758461395030428621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15341642022563720081142989 5753115758461395030428621)
                ·
                  refine ⟨2157418409423023136410733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5753115758461395030428621 2157418409423023136410733)
                  ·
                    refine ⟨809031903533633676154025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157418409423023136410733 809031903533633676154025)
                    ·
                      rfl

theorem cell22_2363376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_2363376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363376 prefixEnd_2363376 := by exact prefixLift 2363376
  have htrace : WordTrace (prefixWord ++ tailWord_2363376) baseStart_2363376 baseEnd_2363376 := by
    simpa [prefixWord, tailWord_2363376, baseEnd_2363376] using wordTrace_append hprefix tailTrace_2363376
  have hstable : (prefixWord ++ tailWord_2363376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363376).length < 2 ^ (prefixWord ++ tailWord_2363376).sum := by decide
  have hdescent : baseEnd_2363376 < baseStart_2363376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363382 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_2363382 : Nat := 118140960795 + 2363382 * 2 ^ 59
def prefixEnd_2363382 : Nat := 4983230072969 + 3 ^ 40 * 2363382 * 2
def baseEnd_2363382 : Nat := 809033957456251660504007

theorem tailTrace_2363382 : CollatzResearch.WordTrace tailWord_2363382 prefixEnd_2363382 809033957456251660504007 := by
  unfold tailWord_2363382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387476445242382647237775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57466415415918748237202933 5387476445242382647237775)
  ·
    refine ⟨8081214667863573970856663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5387476445242382647237775 8081214667863573970856663)
    ·
      refine ⟨12121822001795360956284995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8081214667863573970856663 12121822001795360956284995)
      ·
        refine ⟨18182733002693041434427493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12121822001795360956284995 18182733002693041434427493)
        ·
          refine ⟨3409262438004945268955155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18182733002693041434427493 3409262438004945268955155)
          ·
            refine ⟨5113893657007417903432733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409262438004945268955155 5113893657007417903432733)
            ·
              refine ⟨1917710121377781713787275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5113893657007417903432733 1917710121377781713787275)
              ·
                refine ⟨2876565182066672570680913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917710121377781713787275 2876565182066672570680913)
                ·
                  refine ⟨2157423886550004428010685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876565182066672570680913 2157423886550004428010685)
                  ·
                    refine ⟨809033957456251660504007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157423886550004428010685 809033957456251660504007)
                    ·
                      rfl

theorem cell22_2363382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_2363382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363382 prefixEnd_2363382 := by exact prefixLift 2363382
  have htrace : WordTrace (prefixWord ++ tailWord_2363382) baseStart_2363382 baseEnd_2363382 := by
    simpa [prefixWord, tailWord_2363382, baseEnd_2363382] using wordTrace_append hprefix tailTrace_2363382
  have hstable : (prefixWord ++ tailWord_2363382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363382).length < 2 ^ (prefixWord ++ tailWord_2363382).sum := by decide
  have hdescent : baseEnd_2363382 < baseStart_2363382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363470 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2363470 : Nat := 118140960795 + 2363470 * 2 ^ 59
def prefixEnd_2363470 : Nat := 4983230072969 + 3 ^ 40 * 2363470 * 2
def baseEnd_2363470 : Nat := 809064081654648764303737

theorem tailTrace_2363470 : CollatzResearch.WordTrace tailWord_2363470 prefixEnd_2363470 809064081654648764303737 := by
  unfold tailWord_2363470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775354093444914173125983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57468555165039542256671909 10775354093444914173125983)
  ·
    refine ⟨16163031140167371259688975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10775354093444914173125983 16163031140167371259688975)
    ·
      refine ⟨24244546710251056889533463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16163031140167371259688975 24244546710251056889533463)
      ·
        refine ⟨36366820065376585334300195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24244546710251056889533463 36366820065376585334300195)
        ·
          refine ⟨54550230098064878001450293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36366820065376585334300195 54550230098064878001450293)
          ·
            refine ⟨5114084071693582312635965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54550230098064878001450293 5114084071693582312635965)
            ·
              refine ⟨1917781526885093367238487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5114084071693582312635965 1917781526885093367238487)
              ·
                refine ⟨2876672290327640050857731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917781526885093367238487 2876672290327640050857731)
                ·
                  refine ⟨4315008435491460076286597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876672290327640050857731 4315008435491460076286597)
                  ·
                    refine ⟨809064081654648764303737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315008435491460076286597 809064081654648764303737)
                    ·
                      rfl

theorem cell22_2363470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2363470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363470 prefixEnd_2363470 := by exact prefixLift 2363470
  have htrace : WordTrace (prefixWord ++ tailWord_2363470) baseStart_2363470 baseEnd_2363470 := by
    simpa [prefixWord, tailWord_2363470, baseEnd_2363470] using wordTrace_append hprefix tailTrace_2363470
  have hstable : (prefixWord ++ tailWord_2363470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363470).length < 2 ^ (prefixWord ++ tailWord_2363470).sum := by decide
  have hdescent : baseEnd_2363470 < baseStart_2363470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363481 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_2363481 : Nat := 118140960795 + 2363481 * 2 ^ 59
def prefixEnd_2363481 : Nat := 4983230072969 + 3 ^ 40 * 2363481 * 2
def baseEnd_2363481 : Nat := 809067847179448402278703

theorem tailTrace_2363481 : CollatzResearch.WordTrace tailWord_2363481 prefixEnd_2363481 809067847179448402278703 := by
  unfold tailWord_2363481
  simp only [CollatzResearch.WordTrace]
  refine ⟨86203233950519462263658297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57468822633679641509105531 86203233950519462263658297)
  ·
    refine ⟨64652425462889596697743723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86203233950519462263658297 64652425462889596697743723)
    ·
      refine ⟨96978638194334395046615585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64652425462889596697743723 96978638194334395046615585)
      ·
        refine ⟨72733978645750796284961689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96978638194334395046615585 72733978645750796284961689)
        ·
          refine ⟨54550483984313097213721267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72733978645750796284961689 54550483984313097213721267)
          ·
            refine ⟨81825725976469645820581901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54550483984313097213721267 81825725976469645820581901)
            ·
              refine ⟨30684647241176117182718213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81825725976469645820581901 30684647241176117182718213)
              ·
                refine ⟨5753371357720521971759665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30684647241176117182718213 5753371357720521971759665)
                ·
                  refine ⟨4315028518290391478819749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753371357720521971759665 4315028518290391478819749)
                  ·
                    refine ⟨809067847179448402278703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315028518290391478819749 809067847179448402278703)
                    ·
                      rfl

theorem cell22_2363481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_2363481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363481 prefixEnd_2363481 := by exact prefixLift 2363481
  have htrace : WordTrace (prefixWord ++ tailWord_2363481) baseStart_2363481 baseEnd_2363481 := by
    simpa [prefixWord, tailWord_2363481, baseEnd_2363481] using wordTrace_append hprefix tailTrace_2363481
  have hstable : (prefixWord ++ tailWord_2363481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363481).length < 2 ^ (prefixWord ++ tailWord_2363481).sum := by decide
  have hdescent : baseEnd_2363481 < baseStart_2363481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363513 : List Nat := [1, 2, 1, 3, 4, 2, 3, 6]
def baseStart_2363513 : Nat := 118140960795 + 2363513 * 2 ^ 59
def prefixEnd_2363513 : Nat := 4983230072969 + 3 ^ 40 * 2363513 * 2
def baseEnd_2363513 : Nat := 89897644603712331719845

theorem tailTrace_2363513 : CollatzResearch.WordTrace tailWord_2363513 prefixEnd_2363513 89897644603712331719845 := by
  unfold tailWord_2363513
  simp only [CollatzResearch.WordTrace]
  refine ⟨86204401086403531728823193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57469600724269021152548795 86204401086403531728823193)
  ·
    refine ⟨64653300814802648796617395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86204401086403531728823193 64653300814802648796617395)
    ·
      refine ⟨96979951222203973194926093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64653300814802648796617395 96979951222203973194926093)
      ·
        refine ⟨36367481708326489948097285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96979951222203973194926093 36367481708326489948097285)
        ·
          refine ⟨6818902820311216865268241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36367481708326489948097285 6818902820311216865268241)
          ·
            refine ⟨5114177115233412648951181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6818902820311216865268241 5114177115233412648951181)
            ·
              refine ⟨1917816418212529743356693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5114177115233412648951181 1917816418212529743356693)
              ·
                refine ⟨89897644603712331719845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1917816418212529743356693 89897644603712331719845)
                ·
                  rfl

theorem cell22_2363513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 6].length) (baseStart_2363513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363513 prefixEnd_2363513 := by exact prefixLift 2363513
  have htrace : WordTrace (prefixWord ++ tailWord_2363513) baseStart_2363513 baseEnd_2363513 := by
    simpa [prefixWord, tailWord_2363513, baseEnd_2363513] using wordTrace_append hprefix tailTrace_2363513
  have hstable : (prefixWord ++ tailWord_2363513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363513).length < 2 ^ (prefixWord ++ tailWord_2363513).sum := by decide
  have hdescent : baseEnd_2363513 < baseStart_2363513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363534 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2363534 : Nat := 118140960795 + 2363534 * 2 ^ 59
def prefixEnd_2363534 : Nat := 4983230072969 + 3 ^ 40 * 2363534 * 2
def baseEnd_2363534 : Nat := 809085990162573930703541

theorem tailTrace_2363534 : CollatzResearch.WordTrace tailWord_2363534 prefixEnd_2363534 809085990162573930703541 := by
  unfold tailWord_2363534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775645877415931539417207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57470111346218301543558437 10775645877415931539417207)
  ·
    refine ⟨16163468816123897309125811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10775645877415931539417207 16163468816123897309125811)
    ·
      refine ⟨24245203224185845963688717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16163468816123897309125811 24245203224185845963688717)
      ·
        refine ⟨9091951209069692236383269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24245203224185845963688717 9091951209069692236383269)
        ·
          refine ⟨1704740851700567294321863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9091951209069692236383269 1704740851700567294321863)
          ·
            refine ⟨2557111277550850941482795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704740851700567294321863 2557111277550850941482795)
            ·
              refine ⟨3835666916326276412224193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557111277550850941482795 3835666916326276412224193)
              ·
                refine ⟨2876750187244707309168145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3835666916326276412224193 2876750187244707309168145)
                ·
                  refine ⟨2157562640433530481876109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876750187244707309168145 2157562640433530481876109)
                  ·
                    refine ⟨809085990162573930703541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157562640433530481876109 809085990162573930703541)
                    ·
                      rfl

theorem cell22_2363534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2363534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363534 prefixEnd_2363534 := by exact prefixLift 2363534
  have htrace : WordTrace (prefixWord ++ tailWord_2363534) baseStart_2363534 baseEnd_2363534 := by
    simpa [prefixWord, tailWord_2363534, baseEnd_2363534] using wordTrace_append hprefix tailTrace_2363534
  have hstable : (prefixWord ++ tailWord_2363534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363534).length < 2 ^ (prefixWord ++ tailWord_2363534).sum := by decide
  have hdescent : baseEnd_2363534 < baseStart_2363534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363541 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2363541 : Nat := 118140960795 + 2363541 * 2 ^ 59
def prefixEnd_2363541 : Nat := 4983230072969 + 3 ^ 40 * 2363541 * 2
def baseEnd_2363541 : Nat := 269696128801876081926173

theorem tailTrace_2363541 : CollatzResearch.WordTrace tailWord_2363541 prefixEnd_2363541 269696128801876081926173 := by
  unfold tailWord_2363541
  simp only [CollatzResearch.WordTrace]
  refine ⟨86205422330302092510842477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57470281553534728340561651 86205422330302092510842477)
  ·
    refine ⟨32327033373863284691565929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86205422330302092510842477 32327033373863284691565929)
    ·
      refine ⟨24245275030397463518674447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32327033373863284691565929 24245275030397463518674447)
      ·
        refine ⟨36367912545596195278011671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24245275030397463518674447 36367912545596195278011671)
        ·
          refine ⟨54551868818394292917017507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36367912545596195278011671 54551868818394292917017507)
          ·
            refine ⟨81827803227591439375526261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54551868818394292917017507 81827803227591439375526261)
            ·
              refine ⟨7671356552586697441455587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81827803227591439375526261 7671356552586697441455587)
              ·
                refine ⟨11507034828880046162183381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7671356552586697441455587 11507034828880046162183381)
                ·
                  refine ⟨269696128801876081926173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11507034828880046162183381 269696128801876081926173)
                  ·
                    rfl

theorem cell22_2363541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2363541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363541 prefixEnd_2363541 := by exact prefixLift 2363541
  have htrace : WordTrace (prefixWord ++ tailWord_2363541) baseStart_2363541 baseEnd_2363541 := by
    simpa [prefixWord, tailWord_2363541, baseEnd_2363541] using wordTrace_append hprefix tailTrace_2363541
  have hstable : (prefixWord ++ tailWord_2363541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363541).length < 2 ^ (prefixWord ++ tailWord_2363541).sum := by decide
  have hdescent : baseEnd_2363541 < baseStart_2363541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363596 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_2363596 : Nat := 118140960795 + 2363596 * 2 ^ 59
def prefixEnd_2363596 : Nat := 4983230072969 + 3 ^ 40 * 2363596 * 2
def baseEnd_2363596 : Nat := 809107214029626435653351

theorem tailTrace_2363596 : CollatzResearch.WordTrace tailWord_2363596 prefixEnd_2363596 809107214029626435653351 := by
  unfold tailWord_2363596
  simp only [CollatzResearch.WordTrace]
  refine ⟨43103714172551418452047321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57471618896735224602729761 43103714172551418452047321)
  ·
    refine ⟨32327785629413563839035491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43103714172551418452047321 32327785629413563839035491)
    ·
      refine ⟨48491678444120345758553237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32327785629413563839035491 48491678444120345758553237)
      ·
        refine ⟨2273047427068141207432183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48491678444120345758553237 2273047427068141207432183)
        ·
          refine ⟨3409571140602211811148275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273047427068141207432183 3409571140602211811148275)
          ·
            refine ⟨5114356710903317716722413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409571140602211811148275 5114356710903317716722413)
            ·
              refine ⟨1917883766588744143770905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5114356710903317716722413 1917883766588744143770905)
              ·
                refine ⟨1438412824941558107828179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917883766588744143770905 1438412824941558107828179)
                ·
                  refine ⟨2157619237412337161742269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438412824941558107828179 2157619237412337161742269)
                  ·
                    refine ⟨809107214029626435653351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157619237412337161742269 809107214029626435653351)
                    ·
                      rfl

theorem cell22_2363596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_2363596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363596 prefixEnd_2363596 := by exact prefixLift 2363596
  have htrace : WordTrace (prefixWord ++ tailWord_2363596) baseStart_2363596 baseEnd_2363596 := by
    simpa [prefixWord, tailWord_2363596, baseEnd_2363596] using wordTrace_append hprefix tailTrace_2363596
  have hstable : (prefixWord ++ tailWord_2363596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363596).length < 2 ^ (prefixWord ++ tailWord_2363596).sum := by decide
  have hdescent : baseEnd_2363596 < baseStart_2363596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363633 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2363633 : Nat := 118140960795 + 2363633 * 2 ^ 59
def prefixEnd_2363633 : Nat := 4983230072969 + 3 ^ 40 * 2363633 * 2
def baseEnd_2363633 : Nat := 809119879885770672478237

theorem tailTrace_2363633 : CollatzResearch.WordTrace tailWord_2363633 prefixEnd_2363633 809119879885770672478237 := by
  unfold tailWord_2363633
  simp only [CollatzResearch.WordTrace]
  refine ⟨86208777845968792223191553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57472518563979194815461035 86208777845968792223191553)
  ·
    refine ⟨64656583384476594167393665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86208777845968792223191553 64656583384476594167393665)
    ·
      refine ⟨48492437538357445625545249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64656583384476594167393665 48492437538357445625545249)
      ·
        refine ⟨36369328153768084219158937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48492437538357445625545249 36369328153768084219158937)
        ·
          refine ⟨27276996115326063164369203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36369328153768084219158937 27276996115326063164369203)
          ·
            refine ⟨40915494172989094746553805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27276996115326063164369203 40915494172989094746553805)
            ·
              refine ⟨15343310314870910529957677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40915494172989094746553805 15343310314870910529957677)
              ·
                refine ⟨5753741368076591448734129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15343310314870910529957677 5753741368076591448734129)
                ·
                  refine ⟨4315306026057443586550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753741368076591448734129 4315306026057443586550597)
                  ·
                    refine ⟨809119879885770672478237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315306026057443586550597 809119879885770672478237)
                    ·
                      rfl

theorem cell22_2363633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2363633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363633 prefixEnd_2363633 := by exact prefixLift 2363633
  have htrace : WordTrace (prefixWord ++ tailWord_2363633) baseStart_2363633 baseEnd_2363633 := by
    simpa [prefixWord, tailWord_2363633, baseEnd_2363633] using wordTrace_append hprefix tailTrace_2363633
  have hstable : (prefixWord ++ tailWord_2363633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363633).length < 2 ^ (prefixWord ++ tailWord_2363633).sum := by decide
  have hdescent : baseEnd_2363633 < baseStart_2363633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363663 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 7, 3]
def baseStart_2363663 : Nat := 118140960795 + 2363663 * 2 ^ 59
def prefixEnd_2363663 : Nat := 4983230072969 + 3 ^ 40 * 2363663 * 2
def baseEnd_2363663 : Nat := 809130149498860594228145

theorem tailTrace_2363663 : CollatzResearch.WordTrace tailWord_2363663 prefixEnd_2363663 809130149498860594228145 := by
  unfold tailWord_2363663
  simp only [CollatzResearch.WordTrace]
  refine ⟨86209872035860107346783643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57473248023906738231189095 86209872035860107346783643)
  ·
    refine ⟨129314808053790161020175465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86209872035860107346783643 129314808053790161020175465)
    ·
      refine ⟨96986106040342620765131599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129314808053790161020175465 96986106040342620765131599)
      ·
        refine ⟨145479159060513931147697399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96986106040342620765131599 145479159060513931147697399)
        ·
          refine ⟨218218738590770896721546099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145479159060513931147697399 218218738590770896721546099)
          ·
            refine ⟨327328107886156345082319149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218218738590770896721546099 327328107886156345082319149)
            ·
              refine ⟨122748040457308629405869681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327328107886156345082319149 122748040457308629405869681)
              ·
                refine ⟨92061030342981472054402261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122748040457308629405869681 92061030342981472054402261)
                ·
                  refine ⟨2157680398663628251275053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92061030342981472054402261 2157680398663628251275053)
                  ·
                    refine ⟨809130149498860594228145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157680398663628251275053 809130149498860594228145)
                    ·
                      rfl

theorem cell22_2363663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_2363663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363663 prefixEnd_2363663 := by exact prefixLift 2363663
  have htrace : WordTrace (prefixWord ++ tailWord_2363663) baseStart_2363663 baseEnd_2363663 := by
    simpa [prefixWord, tailWord_2363663, baseEnd_2363663] using wordTrace_append hprefix tailTrace_2363663
  have hstable : (prefixWord ++ tailWord_2363663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363663).length < 2 ^ (prefixWord ++ tailWord_2363663).sum := by decide
  have hdescent : baseEnd_2363663 < baseStart_2363663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363680 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_2363680 : Nat := 118140960795 + 2363680 * 2 ^ 59
def prefixEnd_2363680 : Nat := 4983230072969 + 3 ^ 40 * 2363680 * 2
def baseEnd_2363680 : Nat := 809135968946278216553093

theorem tailTrace_2363680 : CollatzResearch.WordTrace tailWord_2363680 prefixEnd_2363680 809135968946278216553093 := by
  unfold tailWord_2363680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43105246038399259625076247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57473661384532346166768329 43105246038399259625076247)
  ·
    refine ⟨64657869057598889437614371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43105246038399259625076247 64657869057598889437614371)
    ·
      refine ⟨96986803586398334156421557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64657869057598889437614371 96986803586398334156421557)
      ·
        refine ⟨9092512836224843827164521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96986803586398334156421557 9092512836224843827164521)
        ·
          refine ⟨6819384627168632870373391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9092512836224843827164521 6819384627168632870373391)
          ·
            refine ⟨10229076940752949305560087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6819384627168632870373391 10229076940752949305560087)
            ·
              refine ⟨15343615411129423958340131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10229076940752949305560087 15343615411129423958340131)
              ·
                refine ⟨23015423116694135937510197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15343615411129423958340131 23015423116694135937510197)
                ·
                  refine ⟨2157695917190075244141581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23015423116694135937510197 2157695917190075244141581)
                  ·
                    refine ⟨809135968946278216553093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157695917190075244141581 809135968946278216553093)
                    ·
                      rfl

theorem cell22_2363680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_2363680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363680 prefixEnd_2363680 := by exact prefixLift 2363680
  have htrace : WordTrace (prefixWord ++ tailWord_2363680) baseStart_2363680 baseEnd_2363680 := by
    simpa [prefixWord, tailWord_2363680, baseEnd_2363680] using wordTrace_append hprefix tailTrace_2363680
  have hstable : (prefixWord ++ tailWord_2363680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363680).length < 2 ^ (prefixWord ++ tailWord_2363680).sum := by decide
  have hdescent : baseEnd_2363680 < baseStart_2363680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363708 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2363708 : Nat := 118140960795 + 2363708 * 2 ^ 59
def prefixEnd_2363708 : Nat := 4983230072969 + 3 ^ 40 * 2363708 * 2
def baseEnd_2363708 : Nat := 809145553918495476853007

theorem tailTrace_2363708 : CollatzResearch.WordTrace tailWord_2363708 prefixEnd_2363708 809145553918495476853007 := by
  unfold tailWord_2363708
  simp only [CollatzResearch.WordTrace]
  refine ⟨43105756660348540016085889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57474342213798053354781185 43105756660348540016085889)
  ·
    refine ⟨32329317495261405012064417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43105756660348540016085889 32329317495261405012064417)
    ·
      refine ⟨24246988121446053759048313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32329317495261405012064417 24246988121446053759048313)
      ·
        refine ⟨18185241091084540319286235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24246988121446053759048313 18185241091084540319286235)
        ·
          refine ⟨27277861636626810478929353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18185241091084540319286235 27277861636626810478929353)
          ·
            refine ⟨20458396227470107859197015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27277861636626810478929353 20458396227470107859197015)
            ·
              refine ⟨30687594341205161788795523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20458396227470107859197015 30687594341205161788795523)
              ·
                refine ⟨46031391511807742683193285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30687594341205161788795523 46031391511807742683193285)
                ·
                  refine ⟨8630885908463951753098741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46031391511807742683193285 8630885908463951753098741)
                  ·
                    refine ⟨809145553918495476853007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8630885908463951753098741 809145553918495476853007)
                    ·
                      rfl

theorem cell22_2363708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2363708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363708 prefixEnd_2363708 := by exact prefixLift 2363708
  have htrace : WordTrace (prefixWord ++ tailWord_2363708) baseStart_2363708 baseEnd_2363708 := by
    simpa [prefixWord, tailWord_2363708, baseEnd_2363708] using wordTrace_append hprefix tailTrace_2363708
  have hstable : (prefixWord ++ tailWord_2363708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363708).length < 2 ^ (prefixWord ++ tailWord_2363708).sum := by decide
  have hdescent : baseEnd_2363708 < baseStart_2363708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363710 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2363710 : Nat := 118140960795 + 2363710 * 2 ^ 59
def prefixEnd_2363710 : Nat := 4983230072969 + 3 ^ 40 * 2363710 * 2
def baseEnd_2363710 : Nat := 269715412853122712767667

theorem tailTrace_2363710 : CollatzResearch.WordTrace tailWord_2363710 prefixEnd_2363710 269715412853122712767667 := by
  unfold tailWord_2363710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776448283336229296718073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57474390844459889582496389 10776448283336229296718073)
  ·
    refine ⟨8082336212502171972538555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10776448283336229296718073 8082336212502171972538555)
    ·
      refine ⟨12123504318753257958807833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8082336212502171972538555 12123504318753257958807833)
      ·
        refine ⟨9092628239064943469105875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12123504318753257958807833 9092628239064943469105875)
        ·
          refine ⟨13638942358597415203658813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9092628239064943469105875 13638942358597415203658813)
          ·
            refine ⟨5114603384474030701372055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13638942358597415203658813 5114603384474030701372055)
            ·
              refine ⟨7671905076711046052058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114603384474030701372055 7671905076711046052058083)
              ·
                refine ⟨11507857615066569078087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7671905076711046052058083 11507857615066569078087125)
                ·
                  refine ⟨269715412853122712767667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11507857615066569078087125 269715412853122712767667)
                  ·
                    rfl

theorem cell22_2363710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2363710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363710 prefixEnd_2363710 := by exact prefixLift 2363710
  have htrace : WordTrace (prefixWord ++ tailWord_2363710) baseStart_2363710 baseEnd_2363710 := by
    simpa [prefixWord, tailWord_2363710, baseEnd_2363710] using wordTrace_append hprefix tailTrace_2363710
  have hstable : (prefixWord ++ tailWord_2363710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363710).length < 2 ^ (prefixWord ++ tailWord_2363710).sum := by decide
  have hdescent : baseEnd_2363710 < baseStart_2363710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363723 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_2363723 : Nat := 118140960795 + 2363723 * 2 ^ 59
def prefixEnd_2363723 : Nat := 4983230072969 + 3 ^ 40 * 2363723 * 2
def baseEnd_2363723 : Nat := 809150688725040437727961

theorem tailTrace_2363723 : CollatzResearch.WordTrace tailWord_2363723 prefixEnd_2363723 809150688725040437727961 := by
  unfold tailWord_2363723
  simp only [CollatzResearch.WordTrace]
  refine ⟨86212060415642737593967823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57474706943761825062645215 86212060415642737593967823)
  ·
    refine ⟨129318090623464106390951735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86212060415642737593967823 129318090623464106390951735)
    ·
      refine ⟨193977135935196159586427603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129318090623464106390951735 193977135935196159586427603)
      ·
        refine ⟨290965703902794239379641405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193977135935196159586427603 290965703902794239379641405)
        ·
          refine ⟨109112138963547839767365527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290965703902794239379641405 109112138963547839767365527)
          ·
            refine ⟨163668208445321759651048291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109112138963547839767365527 163668208445321759651048291)
            ·
              refine ⟨245502312667982639476572437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163668208445321759651048291 245502312667982639476572437)
              ·
                refine ⟨11507920906311686225464333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 245502312667982639476572437 11507920906311686225464333)
                ·
                  refine ⟨4315470339866882334549125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11507920906311686225464333 4315470339866882334549125)
                  ·
                    refine ⟨809150688725040437727961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315470339866882334549125 809150688725040437727961)
                    ·
                      rfl

theorem cell22_2363723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_2363723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363723 prefixEnd_2363723 := by exact prefixLift 2363723
  have htrace : WordTrace (prefixWord ++ tailWord_2363723) baseStart_2363723 baseEnd_2363723 := by
    simpa [prefixWord, tailWord_2363723, baseEnd_2363723] using wordTrace_append hprefix tailTrace_2363723
  have hstable : (prefixWord ++ tailWord_2363723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363723).length < 2 ^ (prefixWord ++ tailWord_2363723).sum := by decide
  have hdescent : baseEnd_2363723 < baseStart_2363723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363753 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_2363753 : Nat := 118140960795 + 2363753 * 2 ^ 59
def prefixEnd_2363753 : Nat := 4983230072969 + 3 ^ 40 * 2363753 * 2
def baseEnd_2363753 : Nat := 809160958338130359477869

theorem tailTrace_2363753 : CollatzResearch.WordTrace tailWord_2363753 prefixEnd_2363753 809160958338130359477869 := by
  unfold tailWord_2363753
  simp only [CollatzResearch.WordTrace]
  refine ⟨86213154605534052717559913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57475436403689368478373275 86213154605534052717559913)
  ·
    refine ⟨64659865954150539538169935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86213154605534052717559913 64659865954150539538169935)
    ·
      refine ⟨96989798931225809307254903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64659865954150539538169935 96989798931225809307254903)
      ·
        refine ⟨145484698396838713960882355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96989798931225809307254903 145484698396838713960882355)
        ·
          refine ⟨218227047595258070941323533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145484698396838713960882355 218227047595258070941323533)
          ·
            refine ⟨81835142848221776602996325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218227047595258070941323533 81835142848221776602996325)
            ·
              refine ⟨15344089284041583113061811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81835142848221776602996325 15344089284041583113061811)
              ·
                refine ⟨23016133926062374669592717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15344089284041583113061811 23016133926062374669592717)
                ·
                  refine ⟨8631050222273390501097269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23016133926062374669592717 8631050222273390501097269)
                  ·
                    refine ⟨809160958338130359477869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8631050222273390501097269 809160958338130359477869)
                    ·
                      rfl

theorem cell22_2363753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_2363753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363753 prefixEnd_2363753 := by exact prefixLift 2363753
  have htrace : WordTrace (prefixWord ++ tailWord_2363753) baseStart_2363753 baseEnd_2363753 := by
    simpa [prefixWord, tailWord_2363753, baseEnd_2363753] using wordTrace_append hprefix tailTrace_2363753
  have hstable : (prefixWord ++ tailWord_2363753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363753).length < 2 ^ (prefixWord ++ tailWord_2363753).sum := by decide
  have hdescent : baseEnd_2363753 < baseStart_2363753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363778 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2363778 : Nat := 118140960795 + 2363778 * 2 ^ 59
def prefixEnd_2363778 : Nat := 4983230072969 + 3 ^ 40 * 2363778 * 2
def baseEnd_2363778 : Nat := 269723172116346209200931

theorem tailTrace_2363778 : CollatzResearch.WordTrace tailWord_2363778 prefixEnd_2363778 269723172116346209200931 := by
  unfold tailWord_2363778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21553516607610870496804997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57476044286962321324813325 21553516607610870496804997)
  ·
    refine ⟨4041284363927038218150937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21553516607610870496804997 4041284363927038218150937)
    ·
      refine ⟨3030963272945278663613203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4041284363927038218150937 3030963272945278663613203)
      ·
        refine ⟨4546444909417917995419805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030963272945278663613203 4546444909417917995419805)
        ·
          refine ⟨1704916841031719248282427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4546444909417917995419805 1704916841031719248282427)
          ·
            refine ⟨2557375261547578872423641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704916841031719248282427 2557375261547578872423641)
            ·
              refine ⟨1918031446160684154317731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2557375261547578872423641 1918031446160684154317731)
              ·
                refine ⟨2877047169241026231476597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918031446160684154317731 2877047169241026231476597)
                ·
                  refine ⟨269723172116346209200931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2877047169241026231476597 269723172116346209200931)
                  ·
                    rfl

theorem cell22_2363778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2363778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363778 prefixEnd_2363778 := by exact prefixLift 2363778
  have htrace : WordTrace (prefixWord ++ tailWord_2363778) baseStart_2363778 baseEnd_2363778 := by
    simpa [prefixWord, tailWord_2363778, baseEnd_2363778] using wordTrace_append hprefix tailTrace_2363778
  have hstable : (prefixWord ++ tailWord_2363778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363778).length < 2 ^ (prefixWord ++ tailWord_2363778).sum := by decide
  have hdescent : baseEnd_2363778 < baseStart_2363778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363787 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 2, 3]
def baseStart_2363787 : Nat := 118140960795 + 2363787 * 2 ^ 59
def prefixEnd_2363787 : Nat := 4983230072969 + 3 ^ 40 * 2363787 * 2
def baseEnd_2363787 : Nat := 809172597232965604127765

theorem tailTrace_2363787 : CollatzResearch.WordTrace tailWord_2363787 prefixEnd_2363787 809172597232965604127765 := by
  unfold tailWord_2363787
  simp only [CollatzResearch.WordTrace]
  refine ⟨86214394687410876524297615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57476263124940584349531743 86214394687410876524297615)
  ·
    refine ⟨129321592031116314786446423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86214394687410876524297615 129321592031116314786446423)
    ·
      refine ⟨193982388046674472179669635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129321592031116314786446423 193982388046674472179669635)
      ·
        refine ⟨290973582070011708269504453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193982388046674472179669635 290973582070011708269504453)
        ·
          refine ⟨54557546638127195300532085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290973582070011708269504453 54557546638127195300532085)
          ·
            refine ⟨5114769997324424559424883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54557546638127195300532085 5114769997324424559424883)
            ·
              refine ⟨7672154995986636839137325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114769997324424559424883 7672154995986636839137325)
              ·
                refine ⟨2877058123494988814676497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7672154995986636839137325 2877058123494988814676497)
                ·
                  refine ⟨2157793592621241611007373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877058123494988814676497 2157793592621241611007373)
                  ·
                    refine ⟨809172597232965604127765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157793592621241611007373 809172597232965604127765)
                    ·
                      rfl

theorem cell22_2363787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3].length) (baseStart_2363787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363787 prefixEnd_2363787 := by exact prefixLift 2363787
  have htrace : WordTrace (prefixWord ++ tailWord_2363787) baseStart_2363787 baseEnd_2363787 := by
    simpa [prefixWord, tailWord_2363787, baseEnd_2363787] using wordTrace_append hprefix tailTrace_2363787
  have hstable : (prefixWord ++ tailWord_2363787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363787).length < 2 ^ (prefixWord ++ tailWord_2363787).sum := by decide
  have hdescent : baseEnd_2363787 < baseStart_2363787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363800 : List Nat := [2, 1, 2, 5, 1, 1, 2, 8]
def baseStart_2363800 : Nat := 118140960795 + 2363800 * 2 ^ 59
def prefixEnd_2363800 : Nat := 4983230072969 + 3 ^ 40 * 2363800 * 2
def baseEnd_2363800 : Nat := 89908560822070878172525

theorem tailTrace_2363800 : CollatzResearch.WordTrace tailWord_2363800 prefixEnd_2363800 89908560822070878172525 := by
  unfold tailWord_2363800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43107434418181889872260427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57476579224242519829680569 43107434418181889872260427)
  ·
    refine ⟨64661151627272834808390641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43107434418181889872260427 64661151627272834808390641)
    ·
      refine ⟨48495863720454626106292981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64661151627272834808390641 48495863720454626106292981)
      ·
        refine ⟨4546487223792621197464967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48495863720454626106292981 4546487223792621197464967)
        ·
          refine ⟨6819730835688931796197451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4546487223792621197464967 6819730835688931796197451)
          ·
            refine ⟨10229596253533397694296177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6819730835688931796197451 10229596253533397694296177)
            ·
              refine ⟨7672197190150048270722133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10229596253533397694296177 7672197190150048270722133)
              ·
                refine ⟨89908560822070878172525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7672197190150048270722133 89908560822070878172525)
                ·
                  rfl

theorem cell22_2363800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_2363800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363800 prefixEnd_2363800 := by exact prefixLift 2363800
  have htrace : WordTrace (prefixWord ++ tailWord_2363800) baseStart_2363800 baseEnd_2363800 := by
    simpa [prefixWord, tailWord_2363800, baseEnd_2363800] using wordTrace_append hprefix tailTrace_2363800
  have hstable : (prefixWord ++ tailWord_2363800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363800).length < 2 ^ (prefixWord ++ tailWord_2363800).sum := by decide
  have hdescent : baseEnd_2363800 < baseStart_2363800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363802 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_2363802 : Nat := 118140960795 + 2363802 * 2 ^ 59
def prefixEnd_2363802 : Nat := 4983230072969 + 3 ^ 40 * 2363802 * 2
def baseEnd_2363802 : Nat := 809177732039510565002719

theorem tailTrace_2363802 : CollatzResearch.WordTrace tailWord_2363802 prefixEnd_2363802 809177732039510565002719 := by
  unfold tailWord_2363802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21553735445589133521523415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57476627854904356057395773 21553735445589133521523415)
  ·
    refine ⟨32330603168383700282285123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21553735445589133521523415 32330603168383700282285123)
    ·
      refine ⟨48495904752575550423427685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32330603168383700282285123 48495904752575550423427685)
      ·
        refine ⟨9092982141107915704392691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48495904752575550423427685 9092982141107915704392691)
        ·
          refine ⟨13639473211661873556589037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9092982141107915704392691 13639473211661873556589037)
          ·
            refine ⟨5114802454373202583720889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13639473211661873556589037 5114802454373202583720889)
            ·
              refine ⟨3836101840779901937790667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114802454373202583720889 3836101840779901937790667)
              ·
                refine ⟨5754152761169852906686001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3836101840779901937790667 5754152761169852906686001)
                ·
                  refine ⟨4315614570877389680014501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754152761169852906686001 4315614570877389680014501)
                  ·
                    refine ⟨809177732039510565002719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315614570877389680014501 809177732039510565002719)
                    ·
                      rfl

theorem cell22_2363802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_2363802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363802 prefixEnd_2363802 := by exact prefixLift 2363802
  have htrace : WordTrace (prefixWord ++ tailWord_2363802) baseStart_2363802 baseEnd_2363802 := by
    simpa [prefixWord, tailWord_2363802, baseEnd_2363802] using wordTrace_append hprefix tailTrace_2363802
  have hstable : (prefixWord ++ tailWord_2363802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363802).length < 2 ^ (prefixWord ++ tailWord_2363802).sum := by decide
  have hdescent : baseEnd_2363802 < baseStart_2363802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363821 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2363821 : Nat := 118140960795 + 2363821 * 2 ^ 59
def prefixEnd_2363821 : Nat := 4983230072969 + 3 ^ 40 * 2363821 * 2
def baseEnd_2363821 : Nat := 809184236127800848777661

theorem tailTrace_2363821 : CollatzResearch.WordTrace tailWord_2363821 prefixEnd_2363821 809184236127800848777661 := by
  unfold tailWord_2363821
  simp only [CollatzResearch.WordTrace]
  refine ⟨86215634769287700331035317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57477089846191800220690211 86215634769287700331035317)
  ·
    refine ⟨8082715759620721906034561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86215634769287700331035317 8082715759620721906034561)
    ·
      refine ⟨6062036819715541429525921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8082715759620721906034561 6062036819715541429525921)
      ·
        refine ⟨4546527614786656072144441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6062036819715541429525921 4546527614786656072144441)
        ·
          refine ⟨3409895711089992054108331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4546527614786656072144441 3409895711089992054108331)
          ·
            refine ⟨5114843566634988081162497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409895711089992054108331 5114843566634988081162497)
            ·
              refine ⟨3836132674976241060871873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114843566634988081162497 3836132674976241060871873)
              ·
                refine ⟨2877099506232180795653905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836132674976241060871873 2877099506232180795653905)
                ·
                  refine ⟨2157824629674135596740429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877099506232180795653905 2157824629674135596740429)
                  ·
                    refine ⟨809184236127800848777661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157824629674135596740429 809184236127800848777661)
                    ·
                      rfl

theorem cell22_2363821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2363821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363821 prefixEnd_2363821 := by exact prefixLift 2363821
  have htrace : WordTrace (prefixWord ++ tailWord_2363821) baseStart_2363821 baseEnd_2363821 := by
    simpa [prefixWord, tailWord_2363821, baseEnd_2363821] using wordTrace_append hprefix tailTrace_2363821
  have hstable : (prefixWord ++ tailWord_2363821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363821).length < 2 ^ (prefixWord ++ tailWord_2363821).sum := by decide
  have hdescent : baseEnd_2363821 < baseStart_2363821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363862 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2363862 : Nat := 118140960795 + 2363862 * 2 ^ 59
def prefixEnd_2363862 : Nat := 4983230072969 + 3 ^ 40 * 2363862 * 2
def baseEnd_2363862 : Nat := 269732757088563469500845

theorem tailTrace_2363862 : CollatzResearch.WordTrace tailWord_2363862 prefixEnd_2363862 269732757088563469500845 := by
  unfold tailWord_2363862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388570635133697770829865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57478086774759442888851893 5388570635133697770829865)
  ·
    refine ⟨4041427976350273328122399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5388570635133697770829865 4041427976350273328122399)
    ·
      refine ⟨6062141964525409992183599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4041427976350273328122399 6062141964525409992183599)
      ·
        refine ⟨9093212946788114988275399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6062141964525409992183599 9093212946788114988275399)
        ·
          refine ⟨13639819420182172482413099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9093212946788114988275399 13639819420182172482413099)
          ·
            refine ⟨20459729130273258723619649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13639819420182172482413099 20459729130273258723619649)
            ·
              refine ⟨15344796847704944042714737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20459729130273258723619649 15344796847704944042714737)
              ·
                refine ⟨11508597635778708032036053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15344796847704944042714737 11508597635778708032036053)
                ·
                  refine ⟨269732757088563469500845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11508597635778708032036053 269732757088563469500845)
                  ·
                    rfl

theorem cell22_2363862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2363862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363862 prefixEnd_2363862 := by exact prefixLift 2363862
  have htrace : WordTrace (prefixWord ++ tailWord_2363862) baseStart_2363862 baseEnd_2363862 := by
    simpa [prefixWord, tailWord_2363862, baseEnd_2363862] using wordTrace_append hprefix tailTrace_2363862
  have hstable : (prefixWord ++ tailWord_2363862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363862).length < 2 ^ (prefixWord ++ tailWord_2363862).sum := by decide
  have hdescent : baseEnd_2363862 < baseStart_2363862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363937 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2363937 : Nat := 118140960795 + 2363937 * 2 ^ 59
def prefixEnd_2363937 : Nat := 4983230072969 + 3 ^ 40 * 2363937 * 2
def baseEnd_2363937 : Nat := 809223945298415212877305

theorem tailTrace_2363937 : CollatzResearch.WordTrace tailWord_2363937 prefixEnd_2363937 809223945298415212877305 := by
  unfold tailWord_2363937
  simp only [CollatzResearch.WordTrace]
  refine ⟨86219865636867452142258065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57479910424578301428172043 86219865636867452142258065)
  ·
    refine ⟨64664899227650589106693549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86219865636867452142258065 64664899227650589106693549)
    ·
      refine ⟨24249337210368970915010081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64664899227650589106693549 24249337210368970915010081)
      ·
        refine ⟨18187002907776728186257561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24249337210368970915010081 18187002907776728186257561)
        ·
          refine ⟨13640252180832546139693171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18187002907776728186257561 13640252180832546139693171)
          ·
            refine ⟨20460378271248819209539757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13640252180832546139693171 20460378271248819209539757)
            ·
              refine ⟨7672641851718307203577409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20460378271248819209539757 7672641851718307203577409)
              ·
                refine ⟨5754481388788730402683057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7672641851718307203577409 5754481388788730402683057)
                ·
                  refine ⟨4315861041591547802012293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754481388788730402683057 4315861041591547802012293)
                  ·
                    refine ⟨809223945298415212877305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315861041591547802012293 809223945298415212877305)
                    ·
                      rfl

theorem cell22_2363937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2363937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363937 prefixEnd_2363937 := by exact prefixLift 2363937
  have htrace : WordTrace (prefixWord ++ tailWord_2363937) baseStart_2363937 baseEnd_2363937 := by
    simpa [prefixWord, tailWord_2363937, baseEnd_2363937] using wordTrace_append hprefix tailTrace_2363937
  have hstable : (prefixWord ++ tailWord_2363937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363937).length < 2 ^ (prefixWord ++ tailWord_2363937).sum := by decide
  have hdescent : baseEnd_2363937 < baseStart_2363937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363967 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 5, 3]
def baseStart_2363967 : Nat := 118140960795 + 2363967 * 2 ^ 59
def prefixEnd_2363967 : Nat := 4983230072969 + 3 ^ 40 * 2363967 * 2
def baseEnd_2363967 : Nat := 809234214911505134627213

theorem tailTrace_2363967 : CollatzResearch.WordTrace tailWord_2363967 prefixEnd_2363967 809234214911505134627213 := by
  unfold tailWord_2363967
  simp only [CollatzResearch.WordTrace]
  refine ⟨86220959826758767265850155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57480639884505844843900103 86220959826758767265850155)
  ·
    refine ⟨129331439740138150898775233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86220959826758767265850155 129331439740138150898775233)
    ·
      refine ⟨96998579805103613174081425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129331439740138150898775233 96998579805103613174081425)
      ·
        refine ⟨72748934853827709880561069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96998579805103613174081425 72748934853827709880561069)
        ·
          refine ⟨27280850570185391205210401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72748934853827709880561069 27280850570185391205210401)
          ·
            refine ⟨20460637927639043403907801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27280850570185391205210401 20460637927639043403907801)
            ·
              refine ⟨15345478445729282552930851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20460637927639043403907801 15345478445729282552930851)
              ·
                refine ⟨23018217668593923829396277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15345478445729282552930851 23018217668593923829396277)
                ·
                  refine ⟨2157957906430680359005901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23018217668593923829396277 2157957906430680359005901)
                  ·
                    refine ⟨809234214911505134627213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157957906430680359005901 809234214911505134627213)
                    ·
                      rfl

theorem cell22_2363967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_2363967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2363967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2363967 prefixEnd_2363967 := by exact prefixLift 2363967
  have htrace : WordTrace (prefixWord ++ tailWord_2363967) baseStart_2363967 baseEnd_2363967 := by
    simpa [prefixWord, tailWord_2363967, baseEnd_2363967] using wordTrace_append hprefix tailTrace_2363967
  have hstable : (prefixWord ++ tailWord_2363967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363967).length < 2 ^ (prefixWord ++ tailWord_2363967).sum := by decide
  have hdescent : baseEnd_2363967 < baseStart_2363967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364001 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2364001 : Nat := 118140960795 + 2364001 * 2 ^ 59
def prefixEnd_2364001 : Nat := 4983230072969 + 3 ^ 40 * 2364001 * 2
def baseEnd_2364001 : Nat := 809245853806340379277109

theorem tailTrace_2364001 : CollatzResearch.WordTrace tailWord_2364001 prefixEnd_2364001 809245853806340379277109 := by
  unfold tailWord_2364001
  simp only [CollatzResearch.WordTrace]
  refine ⟨86222199908635591072587857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57481466605757060715058571 86222199908635591072587857)
  ·
    refine ⟨64666649931476693304440893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86222199908635591072587857 64666649931476693304440893)
    ·
      refine ⟨24249993724303759989165335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64666649931476693304440893 24249993724303759989165335)
      ·
        refine ⟨36374990586455639983748003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24249993724303759989165335 36374990586455639983748003)
        ·
          refine ⟨54562485879683459975622005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36374990586455639983748003 54562485879683459975622005)
          ·
            refine ⟨5115233051220324372714563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54562485879683459975622005 5115233051220324372714563)
            ·
              refine ⟨7672849576830486559071845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115233051220324372714563 7672849576830486559071845)
              ·
                refine ⟨1438659295655716229825971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7672849576830486559071845 1438659295655716229825971)
                ·
                  refine ⟨2157988943483574344738957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438659295655716229825971 2157988943483574344738957)
                  ·
                    refine ⟨809245853806340379277109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157988943483574344738957 809245853806340379277109)
                    ·
                      rfl

theorem cell22_2364001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2364001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364001 prefixEnd_2364001 := by exact prefixLift 2364001
  have htrace : WordTrace (prefixWord ++ tailWord_2364001) baseStart_2364001 baseEnd_2364001 := by
    simpa [prefixWord, tailWord_2364001, baseEnd_2364001] using wordTrace_append hprefix tailTrace_2364001
  have hstable : (prefixWord ++ tailWord_2364001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364001).length < 2 ^ (prefixWord ++ tailWord_2364001).sum := by decide
  have hdescent : baseEnd_2364001 < baseStart_2364001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364014 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_2364014 : Nat := 118140960795 + 2364014 * 2 ^ 59
def prefixEnd_2364014 : Nat := 4983230072969 + 3 ^ 40 * 2364014 * 2
def baseEnd_2364014 : Nat := 269750101324004226234023

theorem tailTrace_2364014 : CollatzResearch.WordTrace tailWord_2364014 prefixEnd_2364014 269750101324004226234023 := by
  unfold tailWord_2364014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777834257198561786601387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57481782705058996195207397 10777834257198561786601387)
  ·
    refine ⟨16166751385797842679902081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10777834257198561786601387 16166751385797842679902081)
    ·
      refine ⟨12125063539348382009926561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16166751385797842679902081 12125063539348382009926561)
      ·
        refine ⟨9093797654511286507444921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12125063539348382009926561 9093797654511286507444921)
        ·
          refine ⟨6820348240883464880583691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9093797654511286507444921 6820348240883464880583691)
          ·
            refine ⟨10230522361325197320875537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6820348240883464880583691 10230522361325197320875537)
            ·
              refine ⟨7672891770993897990656653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10230522361325197320875537 7672891770993897990656653)
              ·
                refine ⟨2877334414122711746496245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7672891770993897990656653 2877334414122711746496245)
                ·
                  refine ⟨269750101324004226234023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2877334414122711746496245 269750101324004226234023)
                  ·
                    rfl

theorem cell22_2364014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_2364014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364014 prefixEnd_2364014 := by exact prefixLift 2364014
  have htrace : WordTrace (prefixWord ++ tailWord_2364014) baseStart_2364014 baseEnd_2364014 := by
    simpa [prefixWord, tailWord_2364014, baseEnd_2364014] using wordTrace_append hprefix tailTrace_2364014
  have hstable : (prefixWord ++ tailWord_2364014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364014).length < 2 ^ (prefixWord ++ tailWord_2364014).sum := by decide
  have hdescent : baseEnd_2364014 < baseStart_2364014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364078 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2364078 : Nat := 118140960795 + 2364078 * 2 ^ 59
def prefixEnd_2364078 : Nat := 4983230072969 + 3 ^ 40 * 2364078 * 2
def baseEnd_2364078 : Nat := 809272212479937845101873

theorem tailTrace_2364078 : CollatzResearch.WordTrace tailWord_2364078 prefixEnd_2364078 809272212479937845101873 := by
  unfold tailWord_2364078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778126041169579152892611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57483338886237755482093925 10778126041169579152892611)
  ·
    refine ⟨16167189061754368729338917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10778126041169579152892611 16167189061754368729338917)
    ·
      refine ⟨3031347949078944136751047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16167189061754368729338917 3031347949078944136751047)
      ·
        refine ⟨4547021923618416205126571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031347949078944136751047 4547021923618416205126571)
        ·
          refine ⟨6820532885427624307689857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4547021923618416205126571 6820532885427624307689857)
          ·
            refine ⟨5115399664070718230767393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6820532885427624307689857 5115399664070718230767393)
            ·
              refine ⟨3836549748053038673075545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5115399664070718230767393 3836549748053038673075545)
              ·
                refine ⟨2877412311039779004806659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836549748053038673075545 2877412311039779004806659)
                ·
                  refine ⟨4316118466559668507209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877412311039779004806659 4316118466559668507209989)
                  ·
                    refine ⟨809272212479937845101873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316118466559668507209989 809272212479937845101873)
                    ·
                      rfl

theorem cell22_2364078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2364078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364078 prefixEnd_2364078 := by exact prefixLift 2364078
  have htrace : WordTrace (prefixWord ++ tailWord_2364078) baseStart_2364078 baseEnd_2364078 := by
    simpa [prefixWord, tailWord_2364078, baseEnd_2364078] using wordTrace_append hprefix tailTrace_2364078
  have hstable : (prefixWord ++ tailWord_2364078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364078).length < 2 ^ (prefixWord ++ tailWord_2364078).sum := by decide
  have hdescent : baseEnd_2364078 < baseStart_2364078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364147 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_2364147 : Nat := 118140960795 + 2364147 * 2 ^ 59
def prefixEnd_2364147 : Nat := 4983230072969 + 3 ^ 40 * 2364147 * 2
def baseEnd_2364147 : Nat := 809295832590044665126661

theorem tailTrace_2364147 : CollatzResearch.WordTrace tailWord_2364147 prefixEnd_2364147 809295832590044665126661 := by
  unfold tailWord_2364147
  simp only [CollatzResearch.WordTrace]
  refine ⟨86227524966106658007402695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57485016644071105338268463 86227524966106658007402695)
  ·
    refine ⟨129341287449159987011104043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86227524966106658007402695 129341287449159987011104043)
    ·
      refine ⟨194011931173739980516656065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129341287449159987011104043 194011931173739980516656065)
      ·
        refine ⟨145508948380304985387492049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194011931173739980516656065 145508948380304985387492049)
        ·
          refine ⟨109131711285228739040619037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145508948380304985387492049 109131711285228739040619037)
          ·
            refine ⟨40924391731960777140232139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109131711285228739040619037 40924391731960777140232139)
            ·
              refine ⟨61386587597941165710348209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40924391731960777140232139 61386587597941165710348209)
              ·
                refine ⟨46039940698455874282761157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61386587597941165710348209 46039940698455874282761157)
                ·
                  refine ⟨8632488880960476428017717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46039940698455874282761157 8632488880960476428017717)
                  ·
                    refine ⟨809295832590044665126661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8632488880960476428017717 809295832590044665126661)
                    ·
                      rfl

theorem cell22_2364147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_2364147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364147 prefixEnd_2364147 := by exact prefixLift 2364147
  have htrace : WordTrace (prefixWord ++ tailWord_2364147) baseStart_2364147 baseEnd_2364147 := by
    simpa [prefixWord, tailWord_2364147, baseEnd_2364147] using wordTrace_append hprefix tailTrace_2364147
  have hstable : (prefixWord ++ tailWord_2364147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364147).length < 2 ^ (prefixWord ++ tailWord_2364147).sum := by decide
  have hdescent : baseEnd_2364147 < baseStart_2364147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364164 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2364164 : Nat := 118140960795 + 2364164 * 2 ^ 59
def prefixEnd_2364164 : Nat := 4983230072969 + 3 ^ 40 * 2364164 * 2
def baseEnd_2364164 : Nat := 809301652037462287451609

theorem tailTrace_2364164 : CollatzResearch.WordTrace tailWord_2364164 prefixEnd_2364164 809301652037462287451609 := by
  unfold tailWord_2364164
  simp only [CollatzResearch.WordTrace]
  refine ⟨43114072503522534955385773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57485430004696713273847697 43114072503522534955385773)
  ·
    refine ⟨16167777188820950608269665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43114072503522534955385773 16167777188820950608269665)
    ·
      refine ⟨12125832891615712956202249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16167777188820950608269665 12125832891615712956202249)
      ·
        refine ⟨9094374668711784717151687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12125832891615712956202249 9094374668711784717151687)
        ·
          refine ⟨13641562003067677075727531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9094374668711784717151687 13641562003067677075727531)
          ·
            refine ⟨20462343004601515613591297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13641562003067677075727531 20462343004601515613591297)
            ·
              refine ⟨15346757253451136710193473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20462343004601515613591297 15346757253451136710193473)
              ·
                refine ⟨11510067940088352532645105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15346757253451136710193473 11510067940088352532645105)
                ·
                  refine ⟨8632550955066264399483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11510067940088352532645105 8632550955066264399483829)
                  ·
                    refine ⟨809301652037462287451609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8632550955066264399483829 809301652037462287451609)
                    ·
                      rfl

theorem cell22_2364164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2364164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364164 prefixEnd_2364164 := by exact prefixLift 2364164
  have htrace : WordTrace (prefixWord ++ tailWord_2364164) baseStart_2364164 baseEnd_2364164 := by
    simpa [prefixWord, tailWord_2364164, baseEnd_2364164] using wordTrace_append hprefix tailTrace_2364164
  have hstable : (prefixWord ++ tailWord_2364164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364164).length < 2 ^ (prefixWord ++ tailWord_2364164).sum := by decide
  have hdescent : baseEnd_2364164 < baseStart_2364164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364194 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2364194 : Nat := 118140960795 + 2364194 * 2 ^ 59
def prefixEnd_2364194 : Nat := 4983230072969 + 3 ^ 40 * 2364194 * 2
def baseEnd_2364194 : Nat := 269770640550184069733839

theorem tailTrace_2364194 : CollatzResearch.WordTrace tailWord_2364194 prefixEnd_2364194 269770640550184069733839 := by
  unfold tailWord_2364194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21557309799234096258590909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57486159464624256689575757 21557309799234096258590909)
  ·
    refine ⟨8083991174712786096971591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21557309799234096258590909 8083991174712786096971591)
    ·
      refine ⟨12125986762069179145457387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8083991174712786096971591 12125986762069179145457387)
      ·
        refine ⟨18188980143103768718186081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12125986762069179145457387 18188980143103768718186081)
        ·
          refine ⟨13641735107327826538639561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18188980143103768718186081 13641735107327826538639561)
          ·
            refine ⟨10231301330495869903979671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13641735107327826538639561 10231301330495869903979671)
            ·
              refine ⟨15346951995743804855969507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231301330495869903979671 15346951995743804855969507)
              ·
                refine ⟨23020427993615707283954261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15346951995743804855969507 23020427993615707283954261)
                ·
                  refine ⟨269770640550184069733839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23020427993615707283954261 269770640550184069733839)
                  ·
                    rfl

theorem cell22_2364194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2364194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364194 prefixEnd_2364194 := by exact prefixLift 2364194
  have htrace : WordTrace (prefixWord ++ tailWord_2364194) baseStart_2364194 baseEnd_2364194 := by
    simpa [prefixWord, tailWord_2364194, baseEnd_2364194] using wordTrace_append hprefix tailTrace_2364194
  have hstable : (prefixWord ++ tailWord_2364194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364194).length < 2 ^ (prefixWord ++ tailWord_2364194).sum := by decide
  have hdescent : baseEnd_2364194 < baseStart_2364194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364209 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2364209 : Nat := 118140960795 + 2364209 * 2 ^ 59
def prefixEnd_2364209 : Nat := 4983230072969 + 3 ^ 40 * 2364209 * 2
def baseEnd_2364209 : Nat := 809317056457097170076471

theorem tailTrace_2364209 : CollatzResearch.WordTrace tailWord_2364209 prefixEnd_2364209 809317056457097170076471 := by
  unfold tailWord_2364209
  simp only [CollatzResearch.WordTrace]
  refine ⟨86229786291882042596159681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57486524194588028397439787 86229786291882042596159681)
  ·
    refine ⟨64672339718911531947119761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86229786291882042596159681 64672339718911531947119761)
    ·
      refine ⟨48504254789183648960339821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64672339718911531947119761 48504254789183648960339821)
      ·
        refine ⟨18189095545943868360127433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48504254789183648960339821 18189095545943868360127433)
        ·
          refine ⟨13641821659457901270095575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18189095545943868360127433 13641821659457901270095575)
          ·
            refine ⟨20462732489186851905143363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13641821659457901270095575 20462732489186851905143363)
            ·
              refine ⟨30694098733780277857715045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20462732489186851905143363 30694098733780277857715045)
              ·
                refine ⟨5755143512583802098321571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30694098733780277857715045 5755143512583802098321571)
                ·
                  refine ⟨8632715268875703147482357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755143512583802098321571 8632715268875703147482357)
                  ·
                    refine ⟨809317056457097170076471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8632715268875703147482357 809317056457097170076471)
                    ·
                      rfl

theorem cell22_2364209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2364209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364209 prefixEnd_2364209 := by exact prefixLift 2364209
  have htrace : WordTrace (prefixWord ++ tailWord_2364209) baseStart_2364209 baseEnd_2364209 := by
    simpa [prefixWord, tailWord_2364209, baseEnd_2364209] using wordTrace_append hprefix tailTrace_2364209
  have hstable : (prefixWord ++ tailWord_2364209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364209).length < 2 ^ (prefixWord ++ tailWord_2364209).sum := by decide
  have hdescent : baseEnd_2364209 < baseStart_2364209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364211 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 4]
def baseStart_2364211 : Nat := 118140960795 + 2364211 * 2 ^ 59
def prefixEnd_2364211 : Nat := 4983230072969 + 3 ^ 40 * 2364211 * 2
def baseEnd_2364211 : Nat := 269772580365989943842155

theorem tailTrace_2364211 : CollatzResearch.WordTrace tailWord_2364211 prefixEnd_2364211 269772580365989943842155 := by
  unfold tailWord_2364211
  simp only [CollatzResearch.WordTrace]
  refine ⟨86229859237874796937732487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57486572825249864625154991 86229859237874796937732487)
  ·
    refine ⟨129344788856812195406598731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86229859237874796937732487 129344788856812195406598731)
    ·
      refine ⟨194017183285218293109898097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129344788856812195406598731 194017183285218293109898097)
      ·
        refine ⟨145512887463913719832423573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194017183285218293109898097 145512887463913719832423573)
        ·
          refine ⟨6820916599870955617144855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145512887463913719832423573 6820916599870955617144855)
          ·
            refine ⟨10231374899806433425717283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6820916599870955617144855 10231374899806433425717283)
            ·
              refine ⟨15347062349709650138575925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231374899806433425717283 15347062349709650138575925)
              ·
                refine ⟨1438787095285279700491493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15347062349709650138575925 1438787095285279700491493)
                ·
                  refine ⟨269772580365989943842155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1438787095285279700491493 269772580365989943842155)
                  ·
                    rfl

theorem cell22_2364211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 4].length) (baseStart_2364211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364211 prefixEnd_2364211 := by exact prefixLift 2364211
  have htrace : WordTrace (prefixWord ++ tailWord_2364211) baseStart_2364211 baseEnd_2364211 := by
    simpa [prefixWord, tailWord_2364211, baseEnd_2364211] using wordTrace_append hprefix tailTrace_2364211
  have hstable : (prefixWord ++ tailWord_2364211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364211).length < 2 ^ (prefixWord ++ tailWord_2364211).sum := by decide
  have hdescent : baseEnd_2364211 < baseStart_2364211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364213 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2364213 : Nat := 118140960795 + 2364213 * 2 ^ 59
def prefixEnd_2364213 : Nat := 4983230072969 + 3 ^ 40 * 2364213 * 2
def baseEnd_2364213 : Nat := 809318425738842492976459

theorem tailTrace_2364213 : CollatzResearch.WordTrace tailWord_2364213 prefixEnd_2364213 809318425738842492976459 := by
  unfold tailWord_2364213
  simp only [CollatzResearch.WordTrace]
  refine ⟨86229932183867551279305293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57486621455911700852870195 86229932183867551279305293)
  ·
    refine ⟨32336224568950331729739485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86229932183867551279305293 32336224568950331729739485)
    ·
      refine ⟨12126084213356374398652307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32336224568950331729739485 12126084213356374398652307)
      ·
        refine ⟨18189126320034561597978461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12126084213356374398652307 18189126320034561597978461)
        ·
          refine ⟨6820922370012960599241923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18189126320034561597978461 6820922370012960599241923)
          ·
            refine ⟨10231383555019440898862885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6820922370012960599241923 10231383555019440898862885)
            ·
              refine ⟨1918384416566145168536791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10231383555019440898862885 1918384416566145168536791)
              ·
                refine ⟨2877576624849217752805187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918384416566145168536791 2877576624849217752805187)
                ·
                  refine ⟨4316364937273826629207781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877576624849217752805187 4316364937273826629207781)
                  ·
                    refine ⟨809318425738842492976459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316364937273826629207781 809318425738842492976459)
                    ·
                      rfl

theorem cell22_2364213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2364213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364213 prefixEnd_2364213 := by exact prefixLift 2364213
  have htrace : WordTrace (prefixWord ++ tailWord_2364213) baseStart_2364213 baseEnd_2364213 := by
    simpa [prefixWord, tailWord_2364213, baseEnd_2364213] using wordTrace_append hprefix tailTrace_2364213
  have hstable : (prefixWord ++ tailWord_2364213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364213).length < 2 ^ (prefixWord ++ tailWord_2364213).sum := by decide
  have hdescent : baseEnd_2364213 < baseStart_2364213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364224 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_2364224 : Nat := 118140960795 + 2364224 * 2 ^ 59
def prefixEnd_2364224 : Nat := 4983230072969 + 3 ^ 40 * 2364224 * 2
def baseEnd_2364224 : Nat := 809322191263642130951425

theorem tailTrace_2364224 : CollatzResearch.WordTrace tailWord_2364224 prefixEnd_2364224 809322191263642130951425 := by
  unfold tailWord_2364224
  simp only [CollatzResearch.WordTrace]
  refine ⟨43115166693413850078977863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57486888924551800105303817 43115166693413850078977863)
  ·
    refine ⟨64672750040120775118466795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43115166693413850078977863 64672750040120775118466795)
    ·
      refine ⟨97009125060181162677700193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64672750040120775118466795 97009125060181162677700193)
      ·
        refine ⟨72756843795135872008275145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97009125060181162677700193 72756843795135872008275145)
        ·
          refine ⟨54567632846351904006206359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72756843795135872008275145 54567632846351904006206359)
          ·
            refine ⟨81851449269527856009309539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54567632846351904006206359 81851449269527856009309539)
            ·
              refine ⟨122777173904291784013964309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81851449269527856009309539 122777173904291784013964309)
              ·
                refine ⟨5755180026763677375654577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122777173904291784013964309 5755180026763677375654577)
                ·
                  refine ⟨4316385020072758031740933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5755180026763677375654577 4316385020072758031740933)
                  ·
                    refine ⟨809322191263642130951425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316385020072758031740933 809322191263642130951425)
                    ·
                      rfl

theorem cell22_2364224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_2364224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364224 prefixEnd_2364224 := by exact prefixLift 2364224
  have htrace : WordTrace (prefixWord ++ tailWord_2364224) baseStart_2364224 baseEnd_2364224 := by
    simpa [prefixWord, tailWord_2364224, baseEnd_2364224] using wordTrace_append hprefix tailTrace_2364224
  have hstable : (prefixWord ++ tailWord_2364224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364224).length < 2 ^ (prefixWord ++ tailWord_2364224).sum := by decide
  have hdescent : baseEnd_2364224 < baseStart_2364224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364269 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2364269 : Nat := 118140960795 + 2364269 * 2 ^ 59
def prefixEnd_2364269 : Nat := 4983230072969 + 3 ^ 40 * 2364269 * 2
def baseEnd_2364269 : Nat := 809337595683277013576287

theorem tailTrace_2364269 : CollatzResearch.WordTrace tailWord_2364269 prefixEnd_2364269 809337595683277013576287 := by
  unfold tailWord_2364269
  simp only [CollatzResearch.WordTrace]
  refine ⟨86231974671664672843343861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57487983114443115228895907 86231974671664672843343861)
  ·
    refine ⟨8084247625468563079063487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86231974671664672843343861 8084247625468563079063487)
    ·
      refine ⟨12126371438202844618595231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084247625468563079063487 12126371438202844618595231)
      ·
        refine ⟨18189557157304266927892847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12126371438202844618595231 18189557157304266927892847)
        ·
          refine ⟨27284335735956400391839271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18189557157304266927892847 27284335735956400391839271)
          ·
            refine ⟨40926503603934600587758907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27284335735956400391839271 40926503603934600587758907)
            ·
              refine ⟨61389755405901900881638361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40926503603934600587758907 61389755405901900881638361)
              ·
                refine ⟨46042316554426425661228771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61389755405901900881638361 46042316554426425661228771)
                ·
                  refine ⟨69063474831639638491843157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46042316554426425661228771 69063474831639638491843157)
                  ·
                    refine ⟨809337595683277013576287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69063474831639638491843157 809337595683277013576287)
                    ·
                      rfl

theorem cell22_2364269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2364269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364269 prefixEnd_2364269 := by exact prefixLift 2364269
  have htrace : WordTrace (prefixWord ++ tailWord_2364269) baseStart_2364269 baseEnd_2364269 := by
    simpa [prefixWord, tailWord_2364269, baseEnd_2364269] using wordTrace_append hprefix tailTrace_2364269
  have hstable : (prefixWord ++ tailWord_2364269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364269).length < 2 ^ (prefixWord ++ tailWord_2364269).sum := by decide
  have hdescent : baseEnd_2364269 < baseStart_2364269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364290 : List Nat := [3, 4, 2, 2, 1, 1, 2, 7]
def baseStart_2364290 : Nat := 118140960795 + 2364290 * 2 ^ 59
def prefixEnd_2364290 : Nat := 4983230072969 + 3 ^ 40 * 2364290 * 2
def baseEnd_2364290 : Nat := 89927198268048884311247

theorem tailTrace_2364290 : CollatzResearch.WordTrace tailWord_2364290 prefixEnd_2364290 89927198268048884311247 := by
  unfold tailWord_2364290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21558185151147148357464581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57488493736392395619905549 21558185151147148357464581)
  ·
    refine ⟨4042159715840090317024609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21558185151147148357464581 4042159715840090317024609)
    ·
      refine ⟨3031619786880067737768457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4042159715840090317024609 3031619786880067737768457)
      ·
        refine ⟨2273714840160050803326343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3031619786880067737768457 2273714840160050803326343)
        ·
          refine ⟨3410572260240076204989515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273714840160050803326343 3410572260240076204989515)
          ·
            refine ⟨5115858390360114307484273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410572260240076204989515 5115858390360114307484273)
            ·
              refine ⟨3836893792770085730613205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5115858390360114307484273 3836893792770085730613205)
              ·
                refine ⟨89927198268048884311247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3836893792770085730613205 89927198268048884311247)
                ·
                  rfl

theorem cell22_2364290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_2364290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364290 prefixEnd_2364290 := by exact prefixLift 2364290
  have htrace : WordTrace (prefixWord ++ tailWord_2364290) baseStart_2364290 baseEnd_2364290 := by
    simpa [prefixWord, tailWord_2364290, baseEnd_2364290] using wordTrace_append hprefix tailTrace_2364290
  have hstable : (prefixWord ++ tailWord_2364290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364290).length < 2 ^ (prefixWord ++ tailWord_2364290).sum := by decide
  have hdescent : baseEnd_2364290 < baseStart_2364290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364299 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_2364299 : Nat := 118140960795 + 2364299 * 2 ^ 59
def prefixEnd_2364299 : Nat := 4983230072969 + 3 ^ 40 * 2364299 * 2
def baseEnd_2364299 : Nat := 809347865296366935326195

theorem tailTrace_2364299 : CollatzResearch.WordTrace tailWord_2364299 prefixEnd_2364299 809347865296366935326195 := by
  unfold tailWord_2364299
  simp only [CollatzResearch.WordTrace]
  refine ⟨86233068861555987966935951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57488712574370658644623967 86233068861555987966935951)
  ·
    refine ⟨129349603292333981950403927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86233068861555987966935951 129349603292333981950403927)
    ·
      refine ⟨194024404938500972925605891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129349603292333981950403927 194024404938500972925605891)
      ·
        refine ⟨291036607407751459388408837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194024404938500972925605891 291036607407751459388408837)
        ·
          refine ⟨54569363888953398635326657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291036607407751459388408837 54569363888953398635326657)
          ·
            refine ⟨40927022916715048976494993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54569363888953398635326657 40927022916715048976494993)
            ·
              refine ⟨30695267187536286732371245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40927022916715048976494993 30695267187536286732371245)
              ·
                refine ⟨11510725195326107524639217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30695267187536286732371245 11510725195326107524639217)
                ·
                  refine ⟨8633043896494580643479413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11510725195326107524639217 8633043896494580643479413)
                  ·
                    refine ⟨809347865296366935326195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8633043896494580643479413 809347865296366935326195)
                    ·
                      rfl

theorem cell22_2364299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_2364299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364299 prefixEnd_2364299 := by exact prefixLift 2364299
  have htrace : WordTrace (prefixWord ++ tailWord_2364299) baseStart_2364299 baseEnd_2364299 := by
    simpa [prefixWord, tailWord_2364299, baseEnd_2364299] using wordTrace_append hprefix tailTrace_2364299
  have hstable : (prefixWord ++ tailWord_2364299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364299).length < 2 ^ (prefixWord ++ tailWord_2364299).sum := by decide
  have hdescent : baseEnd_2364299 < baseStart_2364299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364376 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_2364376 : Nat := 118140960795 + 2364376 * 2 ^ 59
def prefixEnd_2364376 : Nat := 4983230072969 + 3 ^ 40 * 2364376 * 2
def baseEnd_2364376 : Nat := 809374223969964401150959

theorem tailTrace_2364376 : CollatzResearch.WordTrace tailWord_2364376 prefixEnd_2364376 809374223969964401150959 := by
  unfold tailWord_2364376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43117938641138515058744491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57490584854851353411659321 43117938641138515058744491)
  ·
    refine ⟨64676907961707772588116737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43117938641138515058744491 64676907961707772588116737)
    ·
      refine ⟨48507680971280829441087553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64676907961707772588116737 48507680971280829441087553)
      ·
        refine ⟨36380760728460622080815665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48507680971280829441087553 36380760728460622080815665)
        ·
          refine ⟨27285570546345466560611749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36380760728460622080815665 27285570546345466560611749)
          ·
            refine ⟨5116044477439774980114703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27285570546345466560611749 5116044477439774980114703)
            ·
              refine ⟨7674066716159662470172055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116044477439774980114703 7674066716159662470172055)
              ·
                refine ⟨11511100074239493705258083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674066716159662470172055 11511100074239493705258083)
                ·
                  refine ⟨17266650111359240557887125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11511100074239493705258083 17266650111359240557887125)
                  ·
                    refine ⟨809374223969964401150959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17266650111359240557887125 809374223969964401150959)
                    ·
                      rfl

theorem cell22_2364376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_2364376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364376 prefixEnd_2364376 := by exact prefixLift 2364376
  have htrace : WordTrace (prefixWord ++ tailWord_2364376) baseStart_2364376 baseEnd_2364376 := by
    simpa [prefixWord, tailWord_2364376, baseEnd_2364376] using wordTrace_append hprefix tailTrace_2364376
  have hstable : (prefixWord ++ tailWord_2364376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364376).length < 2 ^ (prefixWord ++ tailWord_2364376).sum := by decide
  have hdescent : baseEnd_2364376 < baseStart_2364376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364391 : List Nat := [1, 1, 5, 2, 2, 2, 9]
def baseStart_2364391 : Nat := 118140960795 + 2364391 * 2 ^ 59
def prefixEnd_2364391 : Nat := 4983230072969 + 3 ^ 40 * 2364391 * 2
def baseEnd_2364391 : Nat := 29977013288018865260219

theorem tailTrace_2364391 : CollatzResearch.WordTrace tailWord_2364391 prefixEnd_2364391 29977013288018865260219 := by
  unfold tailWord_2364391
  simp only [CollatzResearch.WordTrace]
  refine ⟨86236424377222687679285027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57490949584815125119523351 86236424377222687679285027)
  ·
    refine ⟨129354636565834031518927541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86236424377222687679285027 129354636565834031518927541)
    ·
      refine ⟨12126997178046940454899457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129354636565834031518927541 12126997178046940454899457)
      ·
        refine ⟨9095247883535205341174593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12126997178046940454899457 9095247883535205341174593)
        ·
          refine ⟨6821435912651404005880945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9095247883535205341174593 6821435912651404005880945)
          ·
            refine ⟨5116076934488553004410709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6821435912651404005880945 5116076934488553004410709)
            ·
              refine ⟨29977013288018865260219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5116076934488553004410709 29977013288018865260219)
              ·
                rfl

theorem cell22_2364391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 9].length) (baseStart_2364391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364391 prefixEnd_2364391 := by exact prefixLift 2364391
  have htrace : WordTrace (prefixWord ++ tailWord_2364391) baseStart_2364391 baseEnd_2364391 := by
    simpa [prefixWord, tailWord_2364391, baseEnd_2364391] using wordTrace_append hprefix tailTrace_2364391
  have hstable : (prefixWord ++ tailWord_2364391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364391).length < 2 ^ (prefixWord ++ tailWord_2364391).sum := by decide
  have hdescent : baseEnd_2364391 < baseStart_2364391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364423 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 3, 3]
def baseStart_2364423 : Nat := 118140960795 + 2364423 * 2 ^ 59
def prefixEnd_2364423 : Nat := 4983230072969 + 3 ^ 40 * 2364423 * 2
def baseEnd_2364423 : Nat := 809390313030471945225815

theorem tailTrace_2364423 : CollatzResearch.WordTrace tailWord_2364423 prefixEnd_2364423 809390313030471945225815 := by
  unfold tailWord_2364423
  simp only [CollatzResearch.WordTrace]
  refine ⟨86237591513106757144449923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57491727675404504762966615 86237591513106757144449923)
  ·
    refine ⟨129356387269660135716674885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86237591513106757144449923 129356387269660135716674885)
    ·
      refine ⟨24254322613061275446876541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129356387269660135716674885 24254322613061275446876541)
      ·
        refine ⟨9095370979897978292578703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24254322613061275446876541 9095370979897978292578703)
        ·
          refine ⟨13643056469846967438868055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9095370979897978292578703 13643056469846967438868055)
          ·
            refine ⟨20464584704770451158302083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13643056469846967438868055 20464584704770451158302083)
            ·
              refine ⟨30696877057155676737453125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20464584704770451158302083 30696877057155676737453125)
              ·
                refine ⟨5755664448216689388272461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30696877057155676737453125 5755664448216689388272461)
                ·
                  refine ⟨2158374168081258520602173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5755664448216689388272461 2158374168081258520602173)
                  ·
                    refine ⟨809390313030471945225815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158374168081258520602173 809390313030471945225815)
                    ·
                      rfl

theorem cell22_2364423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_2364423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364423 prefixEnd_2364423 := by exact prefixLift 2364423
  have htrace : WordTrace (prefixWord ++ tailWord_2364423) baseStart_2364423 baseEnd_2364423 := by
    simpa [prefixWord, tailWord_2364423, baseEnd_2364423] using wordTrace_append hprefix tailTrace_2364423
  have hstable : (prefixWord ++ tailWord_2364423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364423).length < 2 ^ (prefixWord ++ tailWord_2364423).sum := by decide
  have hdescent : baseEnd_2364423 < baseStart_2364423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364470 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2364470 : Nat := 118140960795 + 2364470 * 2 ^ 59
def prefixEnd_2364470 : Nat := 4983230072969 + 3 ^ 40 * 2364470 * 2
def baseEnd_2364470 : Nat := 269802134030326496433557

theorem tailTrace_2364470 : CollatzResearch.WordTrace tailWord_2364470 prefixEnd_2364470 269802134030326496433557 := by
  unfold tailWord_2364470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389956608996030260713179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57492870495957656114273909 5389956608996030260713179)
  ·
    refine ⟨8084934913494045391069769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5389956608996030260713179 8084934913494045391069769)
    ·
      refine ⟨6063701185120534043302327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8084934913494045391069769 6063701185120534043302327)
      ·
        refine ⟨9095551777680801064953491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6063701185120534043302327 9095551777680801064953491)
        ·
          refine ⟨13643327666521201597430237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9095551777680801064953491 13643327666521201597430237)
          ·
            refine ⟨5116247874945450599036339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13643327666521201597430237 5116247874945450599036339)
            ·
              refine ⟨7674371812418175898554509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116247874945450599036339 7674371812418175898554509)
              ·
                refine ⟨2877889429656815961957941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7674371812418175898554509 2877889429656815961957941)
                ·
                  refine ⟨269802134030326496433557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2877889429656815961957941 269802134030326496433557)
                  ·
                    rfl

theorem cell22_2364470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2364470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364470 prefixEnd_2364470 := by exact prefixLift 2364470
  have htrace : WordTrace (prefixWord ++ tailWord_2364470) baseStart_2364470 baseEnd_2364470 := by
    simpa [prefixWord, tailWord_2364470, baseEnd_2364470] using wordTrace_append hprefix tailTrace_2364470
  have hstable : (prefixWord ++ tailWord_2364470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364470).length < 2 ^ (prefixWord ++ tailWord_2364470).sum := by decide
  have hdescent : baseEnd_2364470 < baseStart_2364470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364513 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2364513 : Nat := 118140960795 + 2364513 * 2 ^ 59
def prefixEnd_2364513 : Nat := 4983230072969 + 3 ^ 40 * 2364513 * 2
def baseEnd_2364513 : Nat := 809421121869741710475539

theorem tailTrace_2364513 : CollatzResearch.WordTrace tailWord_2364513 prefixEnd_2364513 809421121869741710475539 := by
  unfold tailWord_2364513
  simp only [CollatzResearch.WordTrace]
  refine ⟨86240874082780702515226193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57493916055187135010150795 86240874082780702515226193)
  ·
    refine ⟨64680655562085526886419645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86240874082780702515226193 64680655562085526886419645)
    ·
      refine ⟨24255245835782072582407367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64680655562085526886419645 24255245835782072582407367)
      ·
        refine ⟨36382868753673108873611051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24255245835782072582407367 36382868753673108873611051)
        ·
          refine ⟨54574303130509663310416577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36382868753673108873611051 54574303130509663310416577)
          ·
            refine ⟨40930727347882247482812433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54574303130509663310416577 40930727347882247482812433)
            ·
              refine ⟨30698045510911685612109325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40930727347882247482812433 30698045510911685612109325)
              ·
                refine ⟨11511767066591882104540997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30698045510911685612109325 11511767066591882104540997)
                ·
                  refine ⟨2158456324985977894601437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11511767066591882104540997 2158456324985977894601437)
                  ·
                    refine ⟨809421121869741710475539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158456324985977894601437 809421121869741710475539)
                    ·
                      rfl

theorem cell22_2364513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2364513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364513 prefixEnd_2364513 := by exact prefixLift 2364513
  have htrace : WordTrace (prefixWord ++ tailWord_2364513) baseStart_2364513 baseEnd_2364513 := by
    simpa [prefixWord, tailWord_2364513, baseEnd_2364513] using wordTrace_append hprefix tailTrace_2364513
  have hstable : (prefixWord ++ tailWord_2364513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364513).length < 2 ^ (prefixWord ++ tailWord_2364513).sum := by decide
  have hdescent : baseEnd_2364513 < baseStart_2364513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364530 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_2364530 : Nat := 118140960795 + 2364530 * 2 ^ 59
def prefixEnd_2364530 : Nat := 4983230072969 + 3 ^ 40 * 2364530 * 2
def baseEnd_2364530 : Nat := 809426941317159332800487

theorem tailTrace_2364530 : CollatzResearch.WordTrace tailWord_2364530 prefixEnd_2364530 809426941317159332800487 := by
  unfold tailWord_2364530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21560373530929778604648761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57494329415812742945730029 21560373530929778604648761)
  ·
    refine ⟨16170280148197333953486571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21560373530929778604648761 16170280148197333953486571)
    ·
      refine ⟨24255420222296000930229857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16170280148197333953486571 24255420222296000930229857)
      ·
        refine ⟨18191565166722000697672393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24255420222296000930229857 18191565166722000697672393)
        ·
          refine ⟨13643673875041500523254295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18191565166722000697672393 13643673875041500523254295)
          ·
            refine ⟨20465510812562250784881443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13643673875041500523254295 20465510812562250784881443)
            ·
              refine ⟨30698266218843376177322165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20465510812562250784881443 30698266218843376177322165)
              ·
                refine ⟨2877962458016566516623953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30698266218843376177322165 2877962458016566516623953)
                ·
                  refine ⟨2158471843512424887467965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877962458016566516623953 2158471843512424887467965)
                  ·
                    refine ⟨809426941317159332800487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158471843512424887467965 809426941317159332800487)
                    ·
                      rfl

theorem cell22_2364530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_2364530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364530 prefixEnd_2364530 := by exact prefixLift 2364530
  have htrace : WordTrace (prefixWord ++ tailWord_2364530) baseStart_2364530 baseEnd_2364530 := by
    simpa [prefixWord, tailWord_2364530, baseEnd_2364530] using wordTrace_append hprefix tailTrace_2364530
  have hstable : (prefixWord ++ tailWord_2364530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364530).length < 2 ^ (prefixWord ++ tailWord_2364530).sum := by decide
  have hdescent : baseEnd_2364530 < baseStart_2364530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364545 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2364545 : Nat := 118140960795 + 2364545 * 2 ^ 59
def prefixEnd_2364545 : Nat := 4983230072969 + 3 ^ 40 * 2364545 * 2
def baseEnd_2364545 : Nat := 809432076123704293675441

theorem tailTrace_2364545 : CollatzResearch.WordTrace tailWord_2364545 prefixEnd_2364545 809432076123704293675441 := by
  unfold tailWord_2364545
  simp only [CollatzResearch.WordTrace]
  refine ⟨86242041218664771980391089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57494694145776514653594059 86242041218664771980391089)
  ·
    refine ⟨64681530913998578985293317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86242041218664771980391089 64681530913998578985293317)
    ·
      refine ⟨12127787046374733559742497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64681530913998578985293317 12127787046374733559742497)
      ·
        refine ⟨9095840284781050169806873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12127787046374733559742497 9095840284781050169806873)
        ·
          refine ⟨6821880213585787627355155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9095840284781050169806873 6821880213585787627355155)
          ·
            refine ⟨10232820320378681441032733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821880213585787627355155 10232820320378681441032733)
            ·
              refine ⟨3837307620142005540387275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10232820320378681441032733 3837307620142005540387275)
              ·
                refine ⟨5755961430213008310580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837307620142005540387275 5755961430213008310580913)
                ·
                  refine ⟨4316971072659756232935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5755961430213008310580913 4316971072659756232935685)
                  ·
                    refine ⟨809432076123704293675441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316971072659756232935685 809432076123704293675441)
                    ·
                      rfl

theorem cell22_2364545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2364545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364545 prefixEnd_2364545 := by exact prefixLift 2364545
  have htrace : WordTrace (prefixWord ++ tailWord_2364545) baseStart_2364545 baseEnd_2364545 := by
    simpa [prefixWord, tailWord_2364545, baseEnd_2364545] using wordTrace_append hprefix tailTrace_2364545
  have hstable : (prefixWord ++ tailWord_2364545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364545).length < 2 ^ (prefixWord ++ tailWord_2364545).sum := by decide
  have hdescent : baseEnd_2364545 < baseStart_2364545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364652 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_2364652 : Nat := 118140960795 + 2364652 * 2 ^ 59
def prefixEnd_2364652 : Nat := 4983230072969 + 3 ^ 40 * 2364652 * 2
def baseEnd_2364652 : Nat := 809468704410391681250113

theorem tailTrace_2364652 : CollatzResearch.WordTrace tailWord_2364652 prefixEnd_2364652 809468704410391681250113 := by
  unfold tailWord_2364652
  simp only [CollatzResearch.WordTrace]
  refine ⟨43122971914638564627268105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57497295886184752836357473 43122971914638564627268105)
  ·
    refine ⟨32342228935978923470451079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43122971914638564627268105 32342228935978923470451079)
    ·
      refine ⟨48513343403968385205676619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32342228935978923470451079 48513343403968385205676619)
      ·
        refine ⟨72770015105952577808514929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48513343403968385205676619 72770015105952577808514929)
        ·
          refine ⟨54577511329464433356386197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72770015105952577808514929 54577511329464433356386197)
          ·
            refine ⟨2558320843568645313580603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54577511329464433356386197 2558320843568645313580603)
            ·
              refine ⟨3837481265352967970370905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558320843568645313580603 3837481265352967970370905)
              ·
                refine ⟨2878110949014725977778179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837481265352967970370905 2878110949014725977778179)
                ·
                  refine ⟨4317166423522088966667269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878110949014725977778179 4317166423522088966667269)
                  ·
                    refine ⟨809468704410391681250113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317166423522088966667269 809468704410391681250113)
                    ·
                      rfl

theorem cell22_2364652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_2364652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364652 prefixEnd_2364652 := by exact prefixLift 2364652
  have htrace : WordTrace (prefixWord ++ tailWord_2364652) baseStart_2364652 baseEnd_2364652 := by
    simpa [prefixWord, tailWord_2364652, baseEnd_2364652] using wordTrace_append hprefix tailTrace_2364652
  have hstable : (prefixWord ++ tailWord_2364652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364652).length < 2 ^ (prefixWord ++ tailWord_2364652).sum := by decide
  have hdescent : baseEnd_2364652 < baseStart_2364652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2364663 : Nat := 118140960795 + 2364663 * 2 ^ 59
def prefixEnd_2364663 : Nat := 4983230072969 + 3 ^ 40 * 2364663 * 2
def baseEnd_2364663 : Nat := 809472469935191319225079

theorem tailTrace_2364663 : CollatzResearch.WordTrace tailWord_2364663 prefixEnd_2364663 809472469935191319225079 := by
  unfold tailWord_2364663
  simp only [CollatzResearch.WordTrace]
  refine ⟨86246345032237278133186643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57497563354824852088791095 86246345032237278133186643)
  ·
    refine ⟨129369517548355917199779965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86246345032237278133186643 129369517548355917199779965)
    ·
      refine ⟨48513569080633468949917487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129369517548355917199779965 48513569080633468949917487)
      ·
        refine ⟨72770353620950203424876231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48513569080633468949917487 72770353620950203424876231)
        ·
          refine ⟨109155530431425305137314347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72770353620950203424876231 109155530431425305137314347)
          ·
            refine ⟨163733295647137957705971521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109155530431425305137314347 163733295647137957705971521)
            ·
              refine ⟨122799971735353468279478641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163733295647137957705971521 122799971735353468279478641)
              ·
                refine ⟨92099978801515101209608981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122799971735353468279478641 92099978801515101209608981)
                ·
                  refine ⟨4317186506321020369200421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92099978801515101209608981 4317186506321020369200421)
                  ·
                    refine ⟨809472469935191319225079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317186506321020369200421 809472469935191319225079)
                    ·
                      rfl

theorem cell22_2364663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2364663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364663 prefixEnd_2364663 := by exact prefixLift 2364663
  have htrace : WordTrace (prefixWord ++ tailWord_2364663) baseStart_2364663 baseEnd_2364663 := by
    simpa [prefixWord, tailWord_2364663, baseEnd_2364663] using wordTrace_append hprefix tailTrace_2364663
  have hstable : (prefixWord ++ tailWord_2364663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364663).length < 2 ^ (prefixWord ++ tailWord_2364663).sum := by decide
  have hdescent : baseEnd_2364663 < baseStart_2364663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364684 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_2364684 : Nat := 118140960795 + 2364684 * 2 ^ 59
def prefixEnd_2364684 : Nat := 4983230072969 + 3 ^ 40 * 2364684 * 2
def baseEnd_2364684 : Nat := 269826552888118088150005

theorem tailTrace_2364684 : CollatzResearch.WordTrace tailWord_2364684 prefixEnd_2364684 269826552888118088150005 := by
  unfold tailWord_2364684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43123555482580599359850553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57498073976774132479800737 43123555482580599359850553)
  ·
    refine ⟨32342666611935449519887915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43123555482580599359850553 32342666611935449519887915)
    ·
      refine ⟨48513999917903174279831873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32342666611935449519887915 48513999917903174279831873)
      ·
        refine ⟨36385499938427380709873905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48513999917903174279831873 36385499938427380709873905)
        ·
          refine ⟨27289124953820535532405429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36385499938427380709873905 27289124953820535532405429)
          ·
            refine ⟨2558355464420675206163009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27289124953820535532405429 2558355464420675206163009)
            ·
              refine ⟨1918766598315506404622257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558355464420675206163009 1918766598315506404622257)
              ·
                refine ⟨1439074948736629803466693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918766598315506404622257 1439074948736629803466693)
                ·
                  refine ⟨269826552888118088150005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439074948736629803466693 269826552888118088150005)
                  ·
                    rfl

theorem cell22_2364684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_2364684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364684 prefixEnd_2364684 := by exact prefixLift 2364684
  have htrace : WordTrace (prefixWord ++ tailWord_2364684) baseStart_2364684 baseEnd_2364684 := by
    simpa [prefixWord, tailWord_2364684, baseEnd_2364684] using wordTrace_append hprefix tailTrace_2364684
  have hstable : (prefixWord ++ tailWord_2364684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364684).length < 2 ^ (prefixWord ++ tailWord_2364684).sum := by decide
  have hdescent : baseEnd_2364684 < baseStart_2364684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364693 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2364693 : Nat := 118140960795 + 2364693 * 2 ^ 59
def prefixEnd_2364693 : Nat := 4983230072969 + 3 ^ 40 * 2364693 * 2
def baseEnd_2364693 : Nat := 809482739548281240974987

theorem tailTrace_2364693 : CollatzResearch.WordTrace tailWord_2364693 prefixEnd_2364693 809482739548281240974987 := by
  unfold tailWord_2364693
  simp only [CollatzResearch.WordTrace]
  refine ⟨86247439222128593256778733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57498292814752395504519155 86247439222128593256778733)
  ·
    refine ⟨32342789708298222471292025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86247439222128593256778733 32342789708298222471292025)
    ·
      refine ⟨24257092281223666853469019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32342789708298222471292025 24257092281223666853469019)
      ·
        refine ⟨36385638421835500280203529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24257092281223666853469019 36385638421835500280203529)
        ·
          refine ⟨27289228816376625210152647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36385638421835500280203529 27289228816376625210152647)
          ·
            refine ⟨40933843224564937815228971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27289228816376625210152647 40933843224564937815228971)
            ·
              refine ⟨61400764836847406722843457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40933843224564937815228971 61400764836847406722843457)
              ·
                refine ⟨46050573627635555042132593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61400764836847406722843457 46050573627635555042132593)
                ·
                  refine ⟨34537930220726666281599445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46050573627635555042132593 34537930220726666281599445)
                  ·
                    refine ⟨809482739548281240974987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34537930220726666281599445 809482739548281240974987)
                    ·
                      rfl

theorem cell22_2364693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2364693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364693 prefixEnd_2364693 := by exact prefixLift 2364693
  have htrace : WordTrace (prefixWord ++ tailWord_2364693) baseStart_2364693 baseEnd_2364693 := by
    simpa [prefixWord, tailWord_2364693, baseEnd_2364693] using wordTrace_append hprefix tailTrace_2364693
  have hstable : (prefixWord ++ tailWord_2364693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364693).length < 2 ^ (prefixWord ++ tailWord_2364693).sum := by decide
  have hdescent : baseEnd_2364693 < baseStart_2364693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364712 : List Nat := [2, 1, 5, 1, 2, 2, 3, 6]
def baseStart_2364712 : Nat := 118140960795 + 2364712 * 2 ^ 59
def prefixEnd_2364712 : Nat := 4983230072969 + 3 ^ 40 * 2364712 * 2
def baseEnd_2364712 : Nat := 89943249292952391638881

theorem tailTrace_2364712 : CollatzResearch.WordTrace tailWord_2364712 prefixEnd_2364712 89943249292952391638881 := by
  unfold tailWord_2364712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43124066104529879750860195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57498754806039839667813593 43124066104529879750860195)
  ·
    refine ⟨64686099156794819626290293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43124066104529879750860195 64686099156794819626290293)
    ·
      refine ⟨6064321795949514339964715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64686099156794819626290293 6064321795949514339964715)
      ·
        refine ⟨9096482693924271509947073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6064321795949514339964715 9096482693924271509947073)
        ·
          refine ⟨6822362020443203632460305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9096482693924271509947073 6822362020443203632460305)
          ·
            refine ⟨5116771515332402724345229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6822362020443203632460305 5116771515332402724345229)
            ·
              refine ⟨1918789318249651021629461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5116771515332402724345229 1918789318249651021629461)
              ·
                refine ⟨89943249292952391638881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1918789318249651021629461 89943249292952391638881)
                ·
                  rfl

theorem cell22_2364712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_2364712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364712 prefixEnd_2364712 := by exact prefixLift 2364712
  have htrace : WordTrace (prefixWord ++ tailWord_2364712) baseStart_2364712 baseEnd_2364712 := by
    simpa [prefixWord, tailWord_2364712, baseEnd_2364712] using wordTrace_append hprefix tailTrace_2364712
  have hstable : (prefixWord ++ tailWord_2364712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364712).length < 2 ^ (prefixWord ++ tailWord_2364712).sum := by decide
  have hdescent : baseEnd_2364712 < baseStart_2364712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364714 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2364714 : Nat := 118140960795 + 2364714 * 2 ^ 59
def prefixEnd_2364714 : Nat := 4983230072969 + 3 ^ 40 * 2364714 * 2
def baseEnd_2364714 : Nat := 809489928277444186199923

theorem tailTrace_2364714 : CollatzResearch.WordTrace tailWord_2364714 prefixEnd_2364714 809489928277444186199923 := by
  unfold tailWord_2364714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562051288763128460823299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57498803436701675895528797 21562051288763128460823299)
  ·
    refine ⟨32343076933144692691234949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562051288763128460823299 32343076933144692691234949)
    ·
      refine ⟨6064326924964629879606553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32343076933144692691234949 6064326924964629879606553)
      ·
        refine ⟨4548245193723472409704915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6064326924964629879606553 4548245193723472409704915)
        ·
          refine ⟨6822367790585208614557373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548245193723472409704915 6822367790585208614557373)
          ·
            refine ⟨2558387921469453230459015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6822367790585208614557373 2558387921469453230459015)
            ·
              refine ⟨3837581882204179845688523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558387921469453230459015 3837581882204179845688523)
              ·
                refine ⟨5756372823306269768532785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837581882204179845688523 5756372823306269768532785)
                ·
                  refine ⟨4317279617479702326399589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5756372823306269768532785 4317279617479702326399589)
                  ·
                    refine ⟨809489928277444186199923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317279617479702326399589 809489928277444186199923)
                    ·
                      rfl

theorem cell22_2364714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2364714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364714 prefixEnd_2364714 := by exact prefixLift 2364714
  have htrace : WordTrace (prefixWord ++ tailWord_2364714) baseStart_2364714 baseEnd_2364714 := by
    simpa [prefixWord, tailWord_2364714, baseEnd_2364714] using wordTrace_append hprefix tailTrace_2364714
  have hstable : (prefixWord ++ tailWord_2364714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364714).length < 2 ^ (prefixWord ++ tailWord_2364714).sum := by decide
  have hdescent : baseEnd_2364714 < baseStart_2364714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364733 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_2364733 : Nat := 118140960795 + 2364733 * 2 ^ 59
def prefixEnd_2364733 : Nat := 4983230072969 + 3 ^ 40 * 2364733 * 2
def baseEnd_2364733 : Nat := 809496432365734469974865

theorem tailTrace_2364733 : CollatzResearch.WordTrace tailWord_2364733 prefixEnd_2364733 809496432365734469974865 := by
  unfold tailWord_2364733
  simp only [CollatzResearch.WordTrace]
  refine ⟨86248898141983680088234853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57499265427989120058823235 86248898141983680088234853)
  ·
    refine ⟨16171668401621940016544035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86248898141983680088234853 16171668401621940016544035)
    ·
      refine ⟨24257502602432910024816053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16171668401621940016544035 24257502602432910024816053)
      ·
        refine ⟨2274140868978085314826505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24257502602432910024816053 2274140868978085314826505)
        ·
          refine ⟨1705605651733563986119879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274140868978085314826505 1705605651733563986119879)
          ·
            refine ⟨2558408477600345979179819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705605651733563986119879 2558408477600345979179819)
            ·
              refine ⟨3837612716400518968769729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558408477600345979179819 3837612716400518968769729)
              ·
                refine ⟨2878209537300389226577297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837612716400518968769729 2878209537300389226577297)
                ·
                  refine ⟨2158657152975291919932973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878209537300389226577297 2158657152975291919932973)
                  ·
                    refine ⟨809496432365734469974865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158657152975291919932973 809496432365734469974865)
                    ·
                      rfl

theorem cell22_2364733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_2364733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364733 prefixEnd_2364733 := by exact prefixLift 2364733
  have htrace : WordTrace (prefixWord ++ tailWord_2364733) baseStart_2364733 baseEnd_2364733 := by
    simpa [prefixWord, tailWord_2364733, baseEnd_2364733] using wordTrace_append hprefix tailTrace_2364733
  have hstable : (prefixWord ++ tailWord_2364733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364733).length < 2 ^ (prefixWord ++ tailWord_2364733).sum := by decide
  have hdescent : baseEnd_2364733 < baseStart_2364733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364778 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2364778 : Nat := 118140960795 + 2364778 * 2 ^ 59
def prefixEnd_2364778 : Nat := 4983230072969 + 3 ^ 40 * 2364778 * 2
def baseEnd_2364778 : Nat := 809511836785369352599727

theorem tailTrace_2364778 : CollatzResearch.WordTrace tailWord_2364778 prefixEnd_2364778 809511836785369352599727 := by
  unfold tailWord_2364778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562634856705163193405747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57500359617880435182415325 21562634856705163193405747)
  ·
    refine ⟨32343952285057744790108621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562634856705163193405747 32343952285057744790108621)
    ·
      refine ⟨12128982106896654296290733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32343952285057744790108621 12128982106896654296290733)
      ·
        refine ⟨4548368290086245361109025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12128982106896654296290733 4548368290086245361109025)
        ·
          refine ⟨3411276217564684020831769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548368290086245361109025 3411276217564684020831769)
          ·
            refine ⟨2558457163173513015623827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3411276217564684020831769 2558457163173513015623827)
            ·
              refine ⟨3837685744760269523435741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558457163173513015623827 3837685744760269523435741)
              ·
                refine ⟨1439132154285101071288403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3837685744760269523435741 1439132154285101071288403)
                ·
                  refine ⟨2158698231427651606932605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439132154285101071288403 2158698231427651606932605)
                  ·
                    refine ⟨809511836785369352599727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158698231427651606932605 809511836785369352599727)
                    ·
                      rfl

theorem cell22_2364778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2364778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364778 prefixEnd_2364778 := by exact prefixLift 2364778
  have htrace : WordTrace (prefixWord ++ tailWord_2364778) baseStart_2364778 baseEnd_2364778 := by
    simpa [prefixWord, tailWord_2364778, baseEnd_2364778] using wordTrace_append hprefix tailTrace_2364778
  have hstable : (prefixWord ++ tailWord_2364778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364778).length < 2 ^ (prefixWord ++ tailWord_2364778).sum := by decide
  have hdescent : baseEnd_2364778 < baseStart_2364778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364817 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_2364817 : Nat := 118140960795 + 2364817 * 2 ^ 59
def prefixEnd_2364817 : Nat := 4983230072969 + 3 ^ 40 * 2364817 * 2
def baseEnd_2364817 : Nat := 809525187282386250874607

theorem tailTrace_2364817 : CollatzResearch.WordTrace tailWord_2364817 prefixEnd_2364817 809525187282386250874607 := by
  unfold tailWord_2364817
  simp only [CollatzResearch.WordTrace]
  refine ⟨86251961873679362434292705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57501307915786241622861803 86251961873679362434292705)
  ·
    refine ⟨64688971405259521825719529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86251961873679362434292705 64688971405259521825719529)
    ·
      refine ⟨48516728553944641369289647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64688971405259521825719529 48516728553944641369289647)
      ·
        refine ⟨72775092830916962053934471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48516728553944641369289647 72775092830916962053934471)
        ·
          refine ⟨109162639246375443080901707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72775092830916962053934471 109162639246375443080901707)
          ·
            refine ⟨163743958869563164621352561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109162639246375443080901707 163743958869563164621352561)
            ·
              refine ⟨122807969152172373466014421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163743958869563164621352561 122807969152172373466014421)
              ·
                refine ⟨2878311777004040003109713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122807969152172373466014421 2878311777004040003109713)
                ·
                  refine ⟨2158733832753030002332285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878311777004040003109713 2158733832753030002332285)
                  ·
                    refine ⟨809525187282386250874607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158733832753030002332285 809525187282386250874607)
                    ·
                      rfl

theorem cell22_2364817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_2364817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364817 prefixEnd_2364817 := by exact prefixLift 2364817
  have htrace : WordTrace (prefixWord ++ tailWord_2364817) baseStart_2364817 baseEnd_2364817 := by
    simpa [prefixWord, tailWord_2364817, baseEnd_2364817] using wordTrace_append hprefix tailTrace_2364817
  have hstable : (prefixWord ++ tailWord_2364817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364817).length < 2 ^ (prefixWord ++ tailWord_2364817).sum := by decide
  have hdescent : baseEnd_2364817 < baseStart_2364817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364832 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_2364832 : Nat := 118140960795 + 2364832 * 2 ^ 59
def prefixEnd_2364832 : Nat := 4983230072969 + 3 ^ 40 * 2364832 * 2
def baseEnd_2364832 : Nat := 809530322088931211749561

theorem tailTrace_2364832 : CollatzResearch.WordTrace tailWord_2364832 prefixEnd_2364832 809530322088931211749561 := by
  unfold tailWord_2364832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43126254484312509998044375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57501672645750013330725833 43126254484312509998044375)
  ·
    refine ⟨64689381726468764997066563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43126254484312509998044375 64689381726468764997066563)
    ·
      refine ⟨97034072589703147495599845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64689381726468764997066563 97034072589703147495599845)
      ·
        refine ⟨18193888610569340155424971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97034072589703147495599845 18193888610569340155424971)
        ·
          refine ⟨27290832915854010233137457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18193888610569340155424971 27290832915854010233137457)
          ·
            refine ⟨20468124686890507674853093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27290832915854010233137457 20468124686890507674853093)
            ·
              refine ⟨3837773378791970189034955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20468124686890507674853093 3837773378791970189034955)
              ·
                refine ⟨5756660068187955283552433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837773378791970189034955 5756660068187955283552433)
                ·
                  refine ⟨4317495051140966462664325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5756660068187955283552433 4317495051140966462664325)
                  ·
                    refine ⟨809530322088931211749561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317495051140966462664325 809530322088931211749561)
                    ·
                      rfl

theorem cell22_2364832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_2364832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364832 prefixEnd_2364832 := by exact prefixLift 2364832
  have htrace : WordTrace (prefixWord ++ tailWord_2364832) baseStart_2364832 baseEnd_2364832 := by
    simpa [prefixWord, tailWord_2364832, baseEnd_2364832] using wordTrace_append hprefix tailTrace_2364832
  have hstable : (prefixWord ++ tailWord_2364832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364832).length < 2 ^ (prefixWord ++ tailWord_2364832).sum := by decide
  have hdescent : baseEnd_2364832 < baseStart_2364832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364909 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2364909 : Nat := 118140960795 + 2364909 * 2 ^ 59
def prefixEnd_2364909 : Nat := 4983230072969 + 3 ^ 40 * 2364909 * 2
def baseEnd_2364909 : Nat := 269852226920842892524775

theorem tailTrace_2364909 : CollatzResearch.WordTrace tailWord_2364909 prefixEnd_2364909 269852226920842892524775 := by
  unfold tailWord_2364909
  simp only [CollatzResearch.WordTrace]
  refine ⟨86255317389346062146641781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57503544926230708097761187 86255317389346062146641781)
  ·
    refine ⟨8086436005251193326247667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86255317389346062146641781 8086436005251193326247667)
    ·
      refine ⟨12129654007876789989371501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8086436005251193326247667 12129654007876789989371501)
      ·
        refine ⟨4548620252953796246014313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12129654007876789989371501 4548620252953796246014313)
        ·
          refine ⟨3411465189715347184510735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548620252953796246014313 3411465189715347184510735)
          ·
            refine ⟨5117197784573020776766103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411465189715347184510735 5117197784573020776766103)
            ·
              refine ⟨7675796676859531165149155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117197784573020776766103 7675796676859531165149155)
              ·
                refine ⟨11513695015289296747723733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7675796676859531165149155 11513695015289296747723733)
                ·
                  refine ⟨269852226920842892524775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11513695015289296747723733 269852226920842892524775)
                  ·
                    rfl

theorem cell22_2364909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2364909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2364909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2364909 prefixEnd_2364909 := by exact prefixLift 2364909
  have htrace : WordTrace (prefixWord ++ tailWord_2364909) baseStart_2364909 baseEnd_2364909 := by
    simpa [prefixWord, tailWord_2364909, baseEnd_2364909] using wordTrace_append hprefix tailTrace_2364909
  have hstable : (prefixWord ++ tailWord_2364909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364909).length < 2 ^ (prefixWord ++ tailWord_2364909).sum := by decide
  have hdescent : baseEnd_2364909 < baseStart_2364909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365089 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 6]
def baseStart_2365089 : Nat := 118140960795 + 2365089 * 2 ^ 59
def prefixEnd_2365089 : Nat := 4983230072969 + 3 ^ 40 * 2365089 * 2
def baseEnd_2365089 : Nat := 269872766147022736024591

theorem tailTrace_2365089 : CollatzResearch.WordTrace tailWord_2365089 prefixEnd_2365089 269872766147022736024591 := by
  unfold tailWord_2365089
  simp only [CollatzResearch.WordTrace]
  refine ⟨86261882528693952888194321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57507921685795968592129547 86261882528693952888194321)
  ·
    refine ⟨64696411896520464666145741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86261882528693952888194321 64696411896520464666145741)
    ·
      refine ⟨24261154461195174249804653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64696411896520464666145741 24261154461195174249804653)
      ·
        refine ⟨9097932922948190343676745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24261154461195174249804653 9097932922948190343676745)
        ·
          refine ⟨6823449692211142757757559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9097932922948190343676745 6823449692211142757757559)
          ·
            refine ⟨10235174538316714136636339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823449692211142757757559 10235174538316714136636339)
            ·
              refine ⟨15352761807475071204954509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235174538316714136636339 15352761807475071204954509)
              ·
                refine ⟨5757285677803151701857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15352761807475071204954509 5757285677803151701857941)
                ·
                  refine ⟨269872766147022736024591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5757285677803151701857941 269872766147022736024591)
                  ·
                    rfl

theorem cell22_2365089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_2365089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365089 prefixEnd_2365089 := by exact prefixLift 2365089
  have htrace : WordTrace (prefixWord ++ tailWord_2365089) baseStart_2365089 baseEnd_2365089 := by
    simpa [prefixWord, tailWord_2365089, baseEnd_2365089] using wordTrace_append hprefix tailTrace_2365089
  have hstable : (prefixWord ++ tailWord_2365089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365089).length < 2 ^ (prefixWord ++ tailWord_2365089).sum := by decide
  have hdescent : baseEnd_2365089 < baseStart_2365089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365104 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_2365104 : Nat := 118140960795 + 2365104 * 2 ^ 59
def prefixEnd_2365104 : Nat := 4983230072969 + 3 ^ 40 * 2365104 * 2
def baseEnd_2365104 : Nat := 809623433247613168948727

theorem tailTrace_2365104 : CollatzResearch.WordTrace tailWord_2365104 prefixEnd_2365104 809623433247613168948727 := by
  unfold tailWord_2365104
  simp only [CollatzResearch.WordTrace]
  refine ⟨43131214811819805224995183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57508286415759740299993577 43131214811819805224995183)
  ·
    refine ⟨64696822217729707837492775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43131214811819805224995183 64696822217729707837492775)
    ·
      refine ⟨97045233326594561756239163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64696822217729707837492775 97045233326594561756239163)
      ·
        refine ⟨145567849989891842634358745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97045233326594561756239163 145567849989891842634358745)
        ·
          refine ⟨109175887492418881975769059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145567849989891842634358745 109175887492418881975769059)
          ·
            refine ⟨163763831238628322963653589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109175887492418881975769059 163763831238628322963653589)
            ·
              refine ⟨3838214794655351319460631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 163763831238628322963653589 3838214794655351319460631)
              ·
                refine ⟨5757322191983026979190947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838214794655351319460631 5757322191983026979190947)
                ·
                  refine ⟨8635983287974540468786421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757322191983026979190947 8635983287974540468786421)
                  ·
                    refine ⟨809623433247613168948727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8635983287974540468786421 809623433247613168948727)
                    ·
                      rfl

theorem cell22_2365104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_2365104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365104 prefixEnd_2365104 := by exact prefixLift 2365104
  have htrace : WordTrace (prefixWord ++ tailWord_2365104) baseStart_2365104 baseEnd_2365104 := by
    simpa [prefixWord, tailWord_2365104, baseEnd_2365104] using wordTrace_append hprefix tailTrace_2365104
  have hstable : (prefixWord ++ tailWord_2365104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365104).length < 2 ^ (prefixWord ++ tailWord_2365104).sum := by decide
  have hdescent : baseEnd_2365104 < baseStart_2365104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365119 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_2365119 : Nat := 118140960795 + 2365119 * 2 ^ 59
def prefixEnd_2365119 : Nat := 4983230072969 + 3 ^ 40 * 2365119 * 2
def baseEnd_2365119 : Nat := 809628568054158129823681

theorem tailTrace_2365119 : CollatzResearch.WordTrace tailWord_2365119 prefixEnd_2365119 809628568054158129823681 := by
  unfold tailWord_2365119
  simp only [CollatzResearch.WordTrace]
  refine ⟨86262976718585268011786411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57508651145723512007857607 86262976718585268011786411)
  ·
    refine ⟨129394465077877902017679617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86262976718585268011786411 129394465077877902017679617)
    ·
      refine ⟨97045848808408426513259713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129394465077877902017679617 97045848808408426513259713)
      ·
        refine ⟨72784386606306319884944785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97045848808408426513259713 72784386606306319884944785)
        ·
          refine ⟨54588289954729739913708589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72784386606306319884944785 54588289954729739913708589)
          ·
            refine ⟨20470608733023652467640721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54588289954729739913708589 20470608733023652467640721)
            ·
              refine ⟨15352956549767739350730541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20470608733023652467640721 15352956549767739350730541)
              ·
                refine ⟨5757358706162902256523953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15352956549767739350730541 5757358706162902256523953)
                ·
                  refine ⟨4318019029622176692392965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5757358706162902256523953 4318019029622176692392965)
                  ·
                    refine ⟨809628568054158129823681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318019029622176692392965 809628568054158129823681)
                    ·
                      rfl

theorem cell22_2365119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_2365119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365119 prefixEnd_2365119 := by exact prefixLift 2365119
  have htrace : WordTrace (prefixWord ++ tailWord_2365119) baseStart_2365119 baseEnd_2365119 := by
    simpa [prefixWord, tailWord_2365119, baseEnd_2365119] using wordTrace_append hprefix tailTrace_2365119
  have hstable : (prefixWord ++ tailWord_2365119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365119).length < 2 ^ (prefixWord ++ tailWord_2365119).sum := by decide
  have hdescent : baseEnd_2365119 < baseStart_2365119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365140 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2365140 : Nat := 118140960795 + 2365140 * 2 ^ 59
def prefixEnd_2365140 : Nat := 4983230072969 + 3 ^ 40 * 2365140 * 2
def baseEnd_2365140 : Nat := 269878585594440358349539

theorem tailTrace_2365140 : CollatzResearch.WordTrace tailWord_2365140 prefixEnd_2365140 269878585594440358349539 := by
  unfold tailWord_2365140
  simp only [CollatzResearch.WordTrace]
  refine ⟨43131871325754594299150437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57509161767672792398867249 43131871325754594299150437)
  ·
    refine ⟨8087225873578986431090707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43131871325754594299150437 8087225873578986431090707)
    ·
      refine ⟨12130838810368479646636061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8087225873578986431090707 12130838810368479646636061)
      ·
        refine ⟨4549064553888179867488523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12130838810368479646636061 4549064553888179867488523)
        ·
          refine ⟨6823596830832269801232785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549064553888179867488523 6823596830832269801232785)
          ·
            refine ⟨5117697623124202350924589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6823596830832269801232785 5117697623124202350924589)
            ·
              refine ⟨1919136608671575881596721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5117697623124202350924589 1919136608671575881596721)
              ·
                refine ⟨1439352456503681911197541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919136608671575881596721 1439352456503681911197541)
                ·
                  refine ⟨269878585594440358349539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439352456503681911197541 269878585594440358349539)
                  ·
                    rfl

theorem cell22_2365140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2365140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365140 prefixEnd_2365140 := by exact prefixLift 2365140
  have htrace : WordTrace (prefixWord ++ tailWord_2365140) baseStart_2365140 baseEnd_2365140 := by
    simpa [prefixWord, tailWord_2365140, baseEnd_2365140] using wordTrace_append hprefix tailTrace_2365140
  have hstable : (prefixWord ++ tailWord_2365140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365140).length < 2 ^ (prefixWord ++ tailWord_2365140).sum := by decide
  have hdescent : baseEnd_2365140 < baseStart_2365140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365166 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2365166 : Nat := 118140960795 + 2365166 * 2 ^ 59
def prefixEnd_2365166 : Nat := 4983230072969 + 3 ^ 40 * 2365166 * 2
def baseEnd_2365166 : Nat := 809644657114665673898537

theorem tailTrace_2365166 : CollatzResearch.WordTrace tailWord_2365166 prefixEnd_2365166 809644657114665673898537 := by
  unfold tailWord_2365166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10783086368676874379843419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57509793966276663359164901 10783086368676874379843419)
  ·
    refine ⟨16174629553015311569765129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10783086368676874379843419 16174629553015311569765129)
    ·
      refine ⟨12130972164761483677323847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16174629553015311569765129 12130972164761483677323847)
      ·
        refine ⟨18196458247142225515985771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12130972164761483677323847 18196458247142225515985771)
        ·
          refine ⟨27294687370713338273978657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18196458247142225515985771 27294687370713338273978657)
          ·
            refine ⟨20471015528035003705483993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27294687370713338273978657 20471015528035003705483993)
            ·
              refine ⟨15353261646026252779112995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20471015528035003705483993 15353261646026252779112995)
              ·
                refine ⟨23029892469039379168669493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15353261646026252779112995 23029892469039379168669493)
                ·
                  refine ⟨2159052418972441797062765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23029892469039379168669493 2159052418972441797062765)
                  ·
                    refine ⟨809644657114665673898537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159052418972441797062765 809644657114665673898537)
                    ·
                      rfl

theorem cell22_2365166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2365166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365166 prefixEnd_2365166 := by exact prefixLift 2365166
  have htrace : WordTrace (prefixWord ++ tailWord_2365166) baseStart_2365166 baseEnd_2365166 := by
    simpa [prefixWord, tailWord_2365166, baseEnd_2365166] using wordTrace_append hprefix tailTrace_2365166
  have hstable : (prefixWord ++ tailWord_2365166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365166).length < 2 ^ (prefixWord ++ tailWord_2365166).sum := by decide
  have hdescent : baseEnd_2365166 < baseStart_2365166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365239 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2365239 : Nat := 118140960795 + 2365239 * 2 ^ 59
def prefixEnd_2365239 : Nat := 4983230072969 + 3 ^ 40 * 2365239 * 2
def baseEnd_2365239 : Nat := 809669646506517816823313

theorem tailTrace_2365239 : CollatzResearch.WordTrace tailWord_2365239 prefixEnd_2365239 809669646506517816823313 := by
  unfold tailWord_2365239
  simp only [CollatzResearch.WordTrace]
  refine ⟨86267353478150528506154771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57511568985433685670769847 86267353478150528506154771)
  ·
    refine ⟨129401030217225792759232157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86267353478150528506154771 129401030217225792759232157)
    ·
      refine ⟨48525386331459672284712059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129401030217225792759232157 48525386331459672284712059)
      ·
        refine ⟨72788079497189508427068089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48525386331459672284712059 72788079497189508427068089)
        ·
          refine ⟨54591059622892131320301067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72788079497189508427068089 54591059622892131320301067)
          ·
            refine ⟨81886589434338196980451601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54591059622892131320301067 81886589434338196980451601)
            ·
              refine ⟨61414942075753647735338701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81886589434338196980451601 61414942075753647735338701)
              ·
                refine ⟨23030603278407617900752013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61414942075753647735338701 23030603278407617900752013)
                ·
                  refine ⟨8636476229402856712782005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23030603278407617900752013 8636476229402856712782005)
                  ·
                    refine ⟨809669646506517816823313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8636476229402856712782005 809669646506517816823313)
                    ·
                      rfl

theorem cell22_2365239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2365239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365239 prefixEnd_2365239 := by exact prefixLift 2365239
  have htrace : WordTrace (prefixWord ++ tailWord_2365239) baseStart_2365239 baseEnd_2365239 := by
    simpa [prefixWord, tailWord_2365239, baseEnd_2365239] using wordTrace_append hprefix tailTrace_2365239
  have hstable : (prefixWord ++ tailWord_2365239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365239).length < 2 ^ (prefixWord ++ tailWord_2365239).sum := by decide
  have hdescent : baseEnd_2365239 < baseStart_2365239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365299 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_2365299 : Nat := 118140960795 + 2365299 * 2 ^ 59
def prefixEnd_2365299 : Nat := 4983230072969 + 3 ^ 40 * 2365299 * 2
def baseEnd_2365299 : Nat := 809690185732697660323129

theorem tailTrace_2365299 : CollatzResearch.WordTrace tailWord_2365299 prefixEnd_2365299 809690185732697660323129 := by
  unfold tailWord_2365299
  simp only [CollatzResearch.WordTrace]
  refine ⟨86269541857933158753338951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57513027905288772502225967 86269541857933158753338951)
  ·
    refine ⟨129404312786899738130008427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86269541857933158753338951 129404312786899738130008427)
    ·
      refine ⟨194106469180349607195012641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129404312786899738130008427 194106469180349607195012641)
      ·
        refine ⟨145579851885262205396259481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194106469180349607195012641 145579851885262205396259481)
        ·
          refine ⟨109184888913946654047194611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145579851885262205396259481 109184888913946654047194611)
          ·
            refine ⟨163777333370919981070791917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109184888913946654047194611 163777333370919981070791917)
            ·
              refine ⟨61416500014094992901546969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163777333370919981070791917 61416500014094992901546969)
              ·
                refine ⟨46062375010571244676160227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61416500014094992901546969 46062375010571244676160227)
                ·
                  refine ⟨69093562515856867014240341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46062375010571244676160227 69093562515856867014240341)
                  ·
                    refine ⟨809690185732697660323129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69093562515856867014240341 809690185732697660323129)
                    ·
                      rfl

theorem cell22_2365299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_2365299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365299 prefixEnd_2365299 := by exact prefixLift 2365299
  have htrace : WordTrace (prefixWord ++ tailWord_2365299) baseStart_2365299 baseEnd_2365299 := by
    simpa [prefixWord, tailWord_2365299, baseEnd_2365299] using wordTrace_append hprefix tailTrace_2365299
  have hstable : (prefixWord ++ tailWord_2365299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365299).length < 2 ^ (prefixWord ++ tailWord_2365299).sum := by decide
  have hdescent : baseEnd_2365299 < baseStart_2365299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365376 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_2365376 : Nat := 118140960795 + 2365376 * 2 ^ 59
def prefixEnd_2365376 : Nat := 4983230072969 + 3 ^ 40 * 2365376 * 2
def baseEnd_2365376 : Nat := 269905514802098375382631

theorem tailTrace_2365376 : CollatzResearch.WordTrace tailWord_2365376 prefixEnd_2365376 269905514802098375382631 := by
  unfold tailWord_2365376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43136175139327100451945991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57514900185769467269261321 43136175139327100451945991)
  ·
    refine ⟨64704262708990650677918987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43136175139327100451945991 64704262708990650677918987)
    ·
      refine ⟨97056394063485976016878481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64704262708990650677918987 97056394063485976016878481)
      ·
        refine ⟨72792295547614482012658861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97056394063485976016878481 72792295547614482012658861)
        ·
          refine ⟨27297110830355430754747073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72792295547614482012658861 27297110830355430754747073)
          ·
            refine ⟨20472833122766573066060305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27297110830355430754747073 20472833122766573066060305)
            ·
              refine ⟨15354624842074929799545229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20472833122766573066060305 15354624842074929799545229)
              ·
                refine ⟨5757984315778098674829461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15354624842074929799545229 5757984315778098674829461)
                ·
                  refine ⟨269905514802098375382631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5757984315778098674829461 269905514802098375382631)
                  ·
                    rfl

theorem cell22_2365376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_2365376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365376 prefixEnd_2365376 := by exact prefixLift 2365376
  have htrace : WordTrace (prefixWord ++ tailWord_2365376) baseStart_2365376 baseEnd_2365376 := by
    simpa [prefixWord, tailWord_2365376, baseEnd_2365376] using wordTrace_append hprefix tailTrace_2365376
  have hstable : (prefixWord ++ tailWord_2365376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365376).length < 2 ^ (prefixWord ++ tailWord_2365376).sum := by decide
  have hdescent : baseEnd_2365376 < baseStart_2365376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365425 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2365425 : Nat := 118140960795 + 2365425 * 2 ^ 59
def prefixEnd_2365425 : Nat := 4983230072969 + 3 ^ 40 * 2365425 * 2
def baseEnd_2365425 : Nat := 809733318107675331672743

theorem tailTrace_2365425 : CollatzResearch.WordTrace tailWord_2365425 prefixEnd_2365425 809733318107675331672743 := by
  unfold tailWord_2365425
  simp only [CollatzResearch.WordTrace]
  refine ⟨86274137455476682272425729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57516091636984454848283819 86274137455476682272425729)
  ·
    refine ⟨64705603091607511704319297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86274137455476682272425729 64705603091607511704319297)
    ·
      refine ⟨48529202318705633778239473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64705603091607511704319297 48529202318705633778239473)
      ·
        refine ⟨36396901739029225333679605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48529202318705633778239473 36396901739029225333679605)
        ·
          refine ⟨3412209538033989875032463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36396901739029225333679605 3412209538033989875032463)
          ·
            refine ⟨5118314307050984812548695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412209538033989875032463 5118314307050984812548695)
            ·
              refine ⟨7677471460576477218823043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118314307050984812548695 7677471460576477218823043)
              ·
                refine ⟨11516207190864715828234565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7677471460576477218823043 11516207190864715828234565)
                ·
                  refine ⟨2159288848287134217793981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11516207190864715828234565 2159288848287134217793981)
                  ·
                    refine ⟨809733318107675331672743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159288848287134217793981 809733318107675331672743)
                    ·
                      rfl

theorem cell22_2365425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2365425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365425 prefixEnd_2365425 := by exact prefixLift 2365425
  have htrace : WordTrace (prefixWord ++ tailWord_2365425) baseStart_2365425 baseEnd_2365425 := by
    simpa [prefixWord, tailWord_2365425, baseEnd_2365425] using wordTrace_append hprefix tailTrace_2365425
  have hstable : (prefixWord ++ tailWord_2365425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365425).length < 2 ^ (prefixWord ++ tailWord_2365425).sum := by decide
  have hdescent : baseEnd_2365425 < baseStart_2365425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365513 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_2365513 : Nat := 118140960795 + 2365513 * 2 ^ 59
def prefixEnd_2365513 : Nat := 4983230072969 + 3 ^ 40 * 2365513 * 2
def baseEnd_2365513 : Nat := 809763442306072435472473

theorem tailTrace_2365513 : CollatzResearch.WordTrace tailWord_2365513 prefixEnd_2365513 809763442306072435472473 := by
  unfold tailWord_2365513
  simp only [CollatzResearch.WordTrace]
  refine ⟨86277347079157873301629193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57518231386105248867752795 86277347079157873301629193)
  ·
    refine ⟨64708010309368404976221895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86277347079157873301629193 64708010309368404976221895)
    ·
      refine ⟨97062015464052607464332843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64708010309368404976221895 97062015464052607464332843)
      ·
        refine ⟨145593023196078911196499265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97062015464052607464332843 145593023196078911196499265)
        ·
          refine ⟨109194767397059183397374449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145593023196078911196499265 109194767397059183397374449)
          ·
            refine ⟨81896075547794387548030837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109194767397059183397374449 81896075547794387548030837)
            ·
              refine ⟨7677757082605723832627891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81896075547794387548030837 7677757082605723832627891)
              ·
                refine ⟨11516635623908585748941837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7677757082605723832627891 11516635623908585748941837)
                ·
                  refine ⟨4318738358965719655853189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11516635623908585748941837 4318738358965719655853189)
                  ·
                    refine ⟨809763442306072435472473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318738358965719655853189 809763442306072435472473)
                    ·
                      rfl

theorem cell22_2365513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_2365513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365513 prefixEnd_2365513 := by exact prefixLift 2365513
  have htrace : WordTrace (prefixWord ++ tailWord_2365513) baseStart_2365513 baseEnd_2365513 := by
    simpa [prefixWord, tailWord_2365513, baseEnd_2365513] using wordTrace_append hprefix tailTrace_2365513
  have hstable : (prefixWord ++ tailWord_2365513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365513).length < 2 ^ (prefixWord ++ tailWord_2365513).sum := by decide
  have hdescent : baseEnd_2365513 < baseStart_2365513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365538 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2365538 : Nat := 118140960795 + 2365538 * 2 ^ 59
def prefixEnd_2365538 : Nat := 4983230072969 + 3 ^ 40 * 2365538 * 2
def baseEnd_2365538 : Nat := 809772000316980703597397

theorem tailTrace_2365538 : CollatzResearch.WordTrace tailWord_2365538 prefixEnd_2365538 809772000316980703597397 := by
  unfold tailWord_2365538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569564726016825642822317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57518839269378201714192845 21569564726016825642822317)
  ·
    refine ⟨8088586772256309616058369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21569564726016825642822317 8088586772256309616058369)
    ·
      refine ⟨6066440079192232212043777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8088586772256309616058369 6066440079192232212043777)
      ·
        refine ⟨4549830059394174159032833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066440079192232212043777 4549830059394174159032833)
        ·
          refine ⟨3412372544545630619274625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4549830059394174159032833 3412372544545630619274625)
          ·
            refine ⟨2559279408409222964455969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412372544545630619274625 2559279408409222964455969)
            ·
              refine ⟨1919459556306917223341977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559279408409222964455969 1919459556306917223341977)
              ·
                refine ⟨1439594667230187917506483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919459556306917223341977 1439594667230187917506483)
                ·
                  refine ⟨2159392000845281876259725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439594667230187917506483 2159392000845281876259725)
                  ·
                    refine ⟨809772000316980703597397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159392000845281876259725 809772000316980703597397)
                    ·
                      rfl

theorem cell22_2365538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2365538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365538 prefixEnd_2365538 := by exact prefixLift 2365538
  have htrace : WordTrace (prefixWord ++ tailWord_2365538) baseStart_2365538 baseEnd_2365538 := by
    simpa [prefixWord, tailWord_2365538, baseEnd_2365538] using wordTrace_append hprefix tailTrace_2365538
  have hstable : (prefixWord ++ tailWord_2365538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365538).length < 2 ^ (prefixWord ++ tailWord_2365538).sum := by decide
  have hdescent : baseEnd_2365538 < baseStart_2365538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365543 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2365543 : Nat := 118140960795 + 2365543 * 2 ^ 59
def prefixEnd_2365543 : Nat := 4983230072969 + 3 ^ 40 * 2365543 * 2
def baseEnd_2365543 : Nat := 809773711919162357222381

theorem tailTrace_2365543 : CollatzResearch.WordTrace tailWord_2365543 prefixEnd_2365543 809773711919162357222381 := by
  unfold tailWord_2365543
  simp only [CollatzResearch.WordTrace]
  refine ⟨86278441269049188425221283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57518960846032792283480855 86278441269049188425221283)
  ·
    refine ⟨129417661903573782637831925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86278441269049188425221283 129417661903573782637831925)
    ·
      refine ⟨12132905803460042122296743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129417661903573782637831925 12132905803460042122296743)
      ·
        refine ⟨18199358705190063183445115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12132905803460042122296743 18199358705190063183445115)
        ·
          refine ⟨27299038057785094775167673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18199358705190063183445115 27299038057785094775167673)
          ·
            refine ⟨20474278543338821081375755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27299038057785094775167673 20474278543338821081375755)
            ·
              refine ⟨30711417815008231622063633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20474278543338821081375755 30711417815008231622063633)
              ·
                refine ⟨23033563361256173716547725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30711417815008231622063633 23033563361256173716547725)
                ·
                  refine ⟨8637586260471065143705397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23033563361256173716547725 8637586260471065143705397)
                  ·
                    refine ⟨809773711919162357222381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8637586260471065143705397 809773711919162357222381)
                    ·
                      rfl

theorem cell22_2365543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2365543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365543 prefixEnd_2365543 := by exact prefixLift 2365543
  have htrace : WordTrace (prefixWord ++ tailWord_2365543) baseStart_2365543 baseEnd_2365543 := by
    simpa [prefixWord, tailWord_2365543, baseEnd_2365543] using wordTrace_append hprefix tailTrace_2365543
  have hstable : (prefixWord ++ tailWord_2365543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365543).length < 2 ^ (prefixWord ++ tailWord_2365543).sum := by decide
  have hdescent : baseEnd_2365543 < baseStart_2365543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365545 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 4]
def baseStart_2365545 : Nat := 118140960795 + 2365545 * 2 ^ 59
def prefixEnd_2365545 : Nat := 4983230072969 + 3 ^ 40 * 2365545 * 2
def baseEnd_2365545 : Nat := 269924798853345006224125

theorem tailTrace_2365545 : CollatzResearch.WordTrace tailWord_2365545 prefixEnd_2365545 269924798853345006224125 := by
  unfold tailWord_2365545
  simp only [CollatzResearch.WordTrace]
  refine ⟨86278514215041942766794089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57519009476694628511196059 86278514215041942766794089)
  ·
    refine ⟨64708885661281457075095567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86278514215041942766794089 64708885661281457075095567)
    ·
      refine ⟨97063328491922185612643351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64708885661281457075095567 97063328491922185612643351)
      ·
        refine ⟨145594992737883278418965027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97063328491922185612643351 145594992737883278418965027)
        ·
          refine ⟨218392489106824917628447541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145594992737883278418965027 218392489106824917628447541)
          ·
            refine ⟨20474295853764836027666957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218392489106824917628447541 20474295853764836027666957)
            ·
              refine ⟨7677860945161813510375109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20474295853764836027666957 7677860945161813510375109)
              ·
                refine ⟨1439598927217840033195333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7677860945161813510375109 1439598927217840033195333)
                ·
                  refine ⟨269924798853345006224125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439598927217840033195333 269924798853345006224125)
                  ·
                    rfl

theorem cell22_2365545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_2365545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365545 prefixEnd_2365545 := by exact prefixLift 2365545
  have htrace : WordTrace (prefixWord ++ tailWord_2365545) baseStart_2365545 baseEnd_2365545 := by
    simpa [prefixWord, tailWord_2365545, baseEnd_2365545] using wordTrace_append hprefix tailTrace_2365545
  have hstable : (prefixWord ++ tailWord_2365545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365545).length < 2 ^ (prefixWord ++ tailWord_2365545).sum := by decide
  have hdescent : baseEnd_2365545 < baseStart_2365545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365575 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2365575 : Nat := 118140960795 + 2365575 * 2 ^ 59
def prefixEnd_2365575 : Nat := 4983230072969 + 3 ^ 40 * 2365575 * 2
def baseEnd_2365575 : Nat := 809784666173124940422283

theorem tailTrace_2365575 : CollatzResearch.WordTrace tailWord_2365575 prefixEnd_2365575 809784666173124940422283 := by
  unfold tailWord_2365575
  simp only [CollatzResearch.WordTrace]
  refine ⟨86279608404933257890386179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57519738936622171926924119 86279608404933257890386179)
  ·
    refine ⟨129419412607399886835579269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86279608404933257890386179 129419412607399886835579269)
    ·
      refine ⟨24266139863887478781671113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129419412607399886835579269 24266139863887478781671113)
      ·
        refine ⟨18199604897915609086253335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24266139863887478781671113 18199604897915609086253335)
        ·
          refine ⟨27299407346873413629380003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18199604897915609086253335 27299407346873413629380003)
          ·
            refine ⟨40949111020310120444070005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27299407346873413629380003 40949111020310120444070005)
            ·
              refine ⟨3838979158154073791631563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40949111020310120444070005 3838979158154073791631563)
              ·
                refine ⟨5758468737231110687447345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838979158154073791631563 5758468737231110687447345)
                ·
                  refine ⟨4318851552923333015585509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5758468737231110687447345 4318851552923333015585509)
                  ·
                    refine ⟨809784666173124940422283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318851552923333015585509 809784666173124940422283)
                    ·
                      rfl

theorem cell22_2365575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2365575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365575 prefixEnd_2365575 := by exact prefixLift 2365575
  have htrace : WordTrace (prefixWord ++ tailWord_2365575) baseStart_2365575 baseEnd_2365575 := by
    simpa [prefixWord, tailWord_2365575, baseEnd_2365575] using wordTrace_append hprefix tailTrace_2365575
  have hstable : (prefixWord ++ tailWord_2365575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365575).length < 2 ^ (prefixWord ++ tailWord_2365575).sum := by decide
  have hdescent : baseEnd_2365575 < baseStart_2365575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365656 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 1, 3]
def baseStart_2365656 : Nat := 118140960795 + 2365656 * 2 ^ 59
def prefixEnd_2365656 : Nat := 4983230072969 + 3 ^ 40 * 2365656 * 2
def baseEnd_2365656 : Nat := 809812394128467729147035

theorem tailTrace_2365656 : CollatzResearch.WordTrace tailWord_2365656 prefixEnd_2365656 809812394128467729147035 := by
  unfold tailWord_2365656
  simp only [CollatzResearch.WordTrace]
  refine ⟨43141281358819904362042411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57521708478426539149389881 43141281358819904362042411)
  ·
    refine ⟨64711922038229856543063617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43141281358819904362042411 64711922038229856543063617)
    ·
      refine ⟨48533941528672392407297713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64711922038229856543063617 48533941528672392407297713)
      ·
        refine ⟨36400456146504294305473285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48533941528672392407297713 36400456146504294305473285)
        ·
          refine ⟨6825085527469555182276241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36400456146504294305473285 6825085527469555182276241)
          ·
            refine ⟨5118814145602166386707181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6825085527469555182276241 5118814145602166386707181)
            ·
              refine ⟨1919555304600812395015193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5118814145602166386707181 1919555304600812395015193)
              ·
                refine ⟨1439666478450609296261395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919555304600812395015193 1439666478450609296261395)
                ·
                  refine ⟨2159499717675913944392093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439666478450609296261395 2159499717675913944392093)
                  ·
                    refine ⟨809812394128467729147035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159499717675913944392093 809812394128467729147035)
                    ·
                      rfl

theorem cell22_2365656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_2365656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365656 prefixEnd_2365656 := by exact prefixLift 2365656
  have htrace : WordTrace (prefixWord ++ tailWord_2365656) baseStart_2365656 baseEnd_2365656 := by
    simpa [prefixWord, tailWord_2365656, baseEnd_2365656] using wordTrace_append hprefix tailTrace_2365656
  have hstable : (prefixWord ++ tailWord_2365656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365656).length < 2 ^ (prefixWord ++ tailWord_2365656).sum := by decide
  have hdescent : baseEnd_2365656 < baseStart_2365656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365665 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2365665 : Nat := 118140960795 + 2365665 * 2 ^ 59
def prefixEnd_2365665 : Nat := 4983230072969 + 3 ^ 40 * 2365665 * 2
def baseEnd_2365665 : Nat := 809815475012394705672007

theorem tailTrace_2365665 : CollatzResearch.WordTrace tailWord_2365665 prefixEnd_2365665 809815475012394705672007 := by
  unfold tailWord_2365665
  simp only [CollatzResearch.WordTrace]
  refine ⟨86282890974607203261162449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57521927316404802174108299 86282890974607203261162449)
  ·
    refine ⟨64712168230955402445871837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86282890974607203261162449 64712168230955402445871837)
    ·
      refine ⟨24267063086608275917201939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64712168230955402445871837 24267063086608275917201939)
      ·
        refine ⟨36400594629912413875802909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24267063086608275917201939 36400594629912413875802909)
        ·
          refine ⟨13650222986217155203426091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36400594629912413875802909 13650222986217155203426091)
          ·
            refine ⟨20475334479325732805139137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13650222986217155203426091 20475334479325732805139137)
            ·
              refine ⟨15356500859494299603854353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20475334479325732805139137 15356500859494299603854353)
              ·
                refine ⟨11517375644620724702890765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15356500859494299603854353 11517375644620724702890765)
                ·
                  refine ⟨4319015866732771763584037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11517375644620724702890765 4319015866732771763584037)
                  ·
                    refine ⟨809815475012394705672007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319015866732771763584037 809815475012394705672007)
                    ·
                      rfl

theorem cell22_2365665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2365665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365665 prefixEnd_2365665 := by exact prefixLift 2365665
  have htrace : WordTrace (prefixWord ++ tailWord_2365665) baseStart_2365665 baseEnd_2365665 := by
    simpa [prefixWord, tailWord_2365665, baseEnd_2365665] using wordTrace_append hprefix tailTrace_2365665
  have hstable : (prefixWord ++ tailWord_2365665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365665).length < 2 ^ (prefixWord ++ tailWord_2365665).sum := by decide
  have hdescent : baseEnd_2365665 < baseStart_2365665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365669 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 5]
def baseStart_2365669 : Nat := 118140960795 + 2365669 * 2 ^ 59
def prefixEnd_2365669 : Nat := 4983230072969 + 3 ^ 40 * 2365669 * 2
def baseEnd_2365669 : Nat := 269938948098046676190665

theorem tailTrace_2365669 : CollatzResearch.WordTrace tailWord_2365669 prefixEnd_2365669 269938948098046676190665 := by
  unfold tailWord_2365669
  simp only [CollatzResearch.WordTrace]
  refine ⟨86283036866592711944308061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57522024577728474629538707 86283036866592711944308061)
  ·
    refine ⟨32356138824972266979115523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86283036866592711944308061 32356138824972266979115523)
    ·
      refine ⟨48534208237458400468673285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32356138824972266979115523 48534208237458400468673285)
      ·
        refine ⟨9100164044523450087876241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48534208237458400468673285 9100164044523450087876241)
        ·
          refine ⟨6825123033392587565907181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9100164044523450087876241 6825123033392587565907181)
          ·
            refine ⟨2559421137522220337215193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6825123033392587565907181 2559421137522220337215193)
            ·
              refine ⟨1919565853141665252911395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559421137522220337215193 1919565853141665252911395)
              ·
                refine ⟨2879348779712497879367093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919565853141665252911395 2879348779712497879367093)
                ·
                  refine ⟨269938948098046676190665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879348779712497879367093 269938948098046676190665)
                  ·
                    rfl

theorem cell22_2365669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_2365669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365669 prefixEnd_2365669 := by exact prefixLift 2365669
  have htrace : WordTrace (prefixWord ++ tailWord_2365669) baseStart_2365669 baseEnd_2365669 := by
    simpa [prefixWord, tailWord_2365669, baseEnd_2365669] using wordTrace_append hprefix tailTrace_2365669
  have hstable : (prefixWord ++ tailWord_2365669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365669).length < 2 ^ (prefixWord ++ tailWord_2365669).sum := by decide
  have hdescent : baseEnd_2365669 < baseStart_2365669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365682 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2365682 : Nat := 118140960795 + 2365682 * 2 ^ 59
def prefixEnd_2365682 : Nat := 4983230072969 + 3 ^ 40 * 2365682 * 2
def baseEnd_2365682 : Nat := 809821294459812327996955

theorem tailTrace_2365682 : CollatzResearch.WordTrace tailWord_2365682 prefixEnd_2365682 809821294459812327996955 := by
  unfold tailWord_2365682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570877753886403791132825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57522340677030410109687533 21570877753886403791132825)
  ·
    refine ⟨16178158315414802843349619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21570877753886403791132825 16178158315414802843349619)
    ·
      refine ⟨24267237473122204265024429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16178158315414802843349619 24267237473122204265024429)
      ·
        refine ⟨9100214052420826599384161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24267237473122204265024429 9100214052420826599384161)
        ·
          refine ⟨6825160539315619949538121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9100214052420826599384161 6825160539315619949538121)
          ·
            refine ⟨5118870404486714962153591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6825160539315619949538121 5118870404486714962153591)
            ·
              refine ⟨7678305606730072443230387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118870404486714962153591 7678305606730072443230387)
              ·
                refine ⟨11517458410095108664845581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7678305606730072443230387 11517458410095108664845581)
                ·
                  refine ⟨4319046903785665749317093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11517458410095108664845581 4319046903785665749317093)
                  ·
                    refine ⟨809821294459812327996955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319046903785665749317093 809821294459812327996955)
                    ·
                      rfl

theorem cell22_2365682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2365682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365682 prefixEnd_2365682 := by exact prefixLift 2365682
  have htrace : WordTrace (prefixWord ++ tailWord_2365682) baseStart_2365682 baseEnd_2365682 := by
    simpa [prefixWord, tailWord_2365682, baseEnd_2365682] using wordTrace_append hprefix tailTrace_2365682
  have hstable : (prefixWord ++ tailWord_2365682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365682).length < 2 ^ (prefixWord ++ tailWord_2365682).sum := by decide
  have hdescent : baseEnd_2365682 < baseStart_2365682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365695 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_2365695 : Nat := 118140960795 + 2365695 * 2 ^ 59
def prefixEnd_2365695 : Nat := 4983230072969 + 3 ^ 40 * 2365695 * 2
def baseEnd_2365695 : Nat := 809825744625484627421915

theorem tailTrace_2365695 : CollatzResearch.WordTrace tailWord_2365695 prefixEnd_2365695 809825744625484627421915 := by
  unfold tailWord_2365695
  simp only [CollatzResearch.WordTrace]
  refine ⟨86283985164498518384754539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57522656776332345589836359 86283985164498518384754539)
  ·
    refine ⟨129425977746747777577131809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86283985164498518384754539 129425977746747777577131809)
    ·
      refine ⟨97069483310060833182848857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129425977746747777577131809 97069483310060833182848857)
      ·
        refine ⟨72802112482545624887136643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97069483310060833182848857 72802112482545624887136643)
        ·
          refine ⟨109203168723818437330704965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72802112482545624887136643 109203168723818437330704965)
          ·
            refine ⟨20475594135715956999507181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109203168723818437330704965 20475594135715956999507181)
            ·
              refine ⟨7678347800893483874815193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20475594135715956999507181 7678347800893483874815193)
              ·
                refine ⟨5758760850670112906111395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7678347800893483874815193 5758760850670112906111395)
                ·
                  refine ⟨8638141276005169359167093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5758760850670112906111395 8638141276005169359167093)
                  ·
                    refine ⟨809825744625484627421915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8638141276005169359167093 809825744625484627421915)
                    ·
                      rfl

theorem cell22_2365695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_2365695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365695 prefixEnd_2365695 := by exact prefixLift 2365695
  have htrace : WordTrace (prefixWord ++ tailWord_2365695) baseStart_2365695 baseEnd_2365695 := by
    simpa [prefixWord, tailWord_2365695, baseEnd_2365695] using wordTrace_append hprefix tailTrace_2365695
  have hstable : (prefixWord ++ tailWord_2365695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365695).length < 2 ^ (prefixWord ++ tailWord_2365695).sum := by decide
  have hdescent : baseEnd_2365695 < baseStart_2365695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365697 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 4]
def baseStart_2365697 : Nat := 118140960795 + 2365697 * 2 ^ 59
def prefixEnd_2365697 : Nat := 4983230072969 + 3 ^ 40 * 2365697 * 2
def baseEnd_2365697 : Nat := 269942143088785762957303

theorem tailTrace_2365697 : CollatzResearch.WordTrace tailWord_2365697 prefixEnd_2365697 269942143088785762957303 := by
  unfold tailWord_2365697
  simp only [CollatzResearch.WordTrace]
  refine ⟨86284058110491272726327345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57522705406994181817551563 86284058110491272726327345)
  ·
    refine ⟨64713043582868454544745509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86284058110491272726327345 64713043582868454544745509)
    ·
      refine ⟨12133695671787835227139783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64713043582868454544745509 12133695671787835227139783)
      ·
        refine ⟨18200543507681752840709675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12133695671787835227139783 18200543507681752840709675)
        ·
          refine ⟨27300815261522629261064513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18200543507681752840709675 27300815261522629261064513)
          ·
            refine ⟨20475611446141971945798385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27300815261522629261064513 20475611446141971945798385)
            ·
              refine ⟨15356708584606478959348789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20475611446141971945798385 15356708584606478959348789)
              ·
                refine ⟨1439691429806857402438949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15356708584606478959348789 1439691429806857402438949)
                ·
                  refine ⟨269942143088785762957303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439691429806857402438949 269942143088785762957303)
                  ·
                    rfl

theorem cell22_2365697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_2365697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365697 prefixEnd_2365697 := by exact prefixLift 2365697
  have htrace : WordTrace (prefixWord ++ tailWord_2365697) baseStart_2365697 baseEnd_2365697 := by
    simpa [prefixWord, tailWord_2365697, baseEnd_2365697] using wordTrace_append hprefix tailTrace_2365697
  have hstable : (prefixWord ++ tailWord_2365697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365697).length < 2 ^ (prefixWord ++ tailWord_2365697).sum := by decide
  have hdescent : baseEnd_2365697 < baseStart_2365697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365864 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2365864 : Nat := 118140960795 + 2365864 * 2 ^ 59
def prefixEnd_2365864 : Nat := 4983230072969 + 3 ^ 40 * 2365864 * 2
def baseEnd_2365864 : Nat := 809883596779224519946397

theorem tailTrace_2365864 : CollatzResearch.WordTrace tailWord_2365864 prefixEnd_2365864 809883596779224519946397 := by
  unfold tailWord_2365864
  simp only [CollatzResearch.WordTrace]
  refine ⟨43145074550443130123828323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57526766067257506831771097 43145074550443130123828323)
  ·
    refine ⟨64717611825664695185742485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43145074550443130123828323 64717611825664695185742485)
    ·
      refine ⟨3033638054328032586831679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64717611825664695185742485 3033638054328032586831679)
      ·
        refine ⟨4550457081492048880247519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033638054328032586831679 4550457081492048880247519)
        ·
          refine ⟨6825685622238073320371279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4550457081492048880247519 6825685622238073320371279)
          ·
            refine ⟨10238528433357109980556919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825685622238073320371279 10238528433357109980556919)
            ·
              refine ⟨15357792650035664970835379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10238528433357109980556919 15357792650035664970835379)
              ·
                refine ⟨23036688975053497456253069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15357792650035664970835379 23036688975053497456253069)
                ·
                  refine ⟨8638758365645061546094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23036688975053497456253069 8638758365645061546094901)
                  ·
                    refine ⟨809883596779224519946397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8638758365645061546094901 809883596779224519946397)
                    ·
                      rfl

theorem cell22_2365864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2365864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365864 prefixEnd_2365864 := by exact prefixLift 2365864
  have htrace : WordTrace (prefixWord ++ tailWord_2365864) baseStart_2365864 baseEnd_2365864 := by
    simpa [prefixWord, tailWord_2365864, baseEnd_2365864] using wordTrace_append hprefix tailTrace_2365864
  have hstable : (prefixWord ++ tailWord_2365864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365864).length < 2 ^ (prefixWord ++ tailWord_2365864).sum := by decide
  have hdescent : baseEnd_2365864 < baseStart_2365864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365877 : List Nat := [1, 3, 3, 2, 3, 10]
def baseStart_2365877 : Nat := 118140960795 + 2365877 * 2 ^ 59
def prefixEnd_2365877 : Nat := 4983230072969 + 3 ^ 40 * 2365877 * 2
def baseEnd_2365877 : Nat := 9998617863517244683597

theorem tailTrace_2365877 : CollatzResearch.WordTrace tailWord_2365877 prefixEnd_2365877 9998617863517244683597 := by
  unfold tailWord_2365877
  simp only [CollatzResearch.WordTrace]
  refine ⟨86290623249839163467879885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57527082166559442311919923 86290623249839163467879885)
  ·
    refine ⟨32358983718689686300454957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86290623249839163467879885 32358983718689686300454957)
    ·
      refine ⟨12134618894508632362670609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32358983718689686300454957 12134618894508632362670609)
      ·
        refine ⟨9100964170881474272002957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12134618894508632362670609 9100964170881474272002957)
        ·
          refine ⟨3412861564080552852001109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9100964170881474272002957 3412861564080552852001109)
          ·
            refine ⟨9998617863517244683597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3412861564080552852001109 9998617863517244683597)
            ·
              rfl

theorem cell22_2365877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 10].length) (baseStart_2365877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365877 prefixEnd_2365877 := by exact prefixLift 2365877
  have htrace : WordTrace (prefixWord ++ tailWord_2365877) baseStart_2365877 baseEnd_2365877 := by
    simpa [prefixWord, tailWord_2365877, baseEnd_2365877] using wordTrace_append hprefix tailTrace_2365877
  have hstable : (prefixWord ++ tailWord_2365877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365877).length < 2 ^ (prefixWord ++ tailWord_2365877).sum := by decide
  have hdescent : baseEnd_2365877 < baseStart_2365877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365881 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_2365881 : Nat := 118140960795 + 2365881 * 2 ^ 59
def prefixEnd_2365881 : Nat := 4983230072969 + 3 ^ 40 * 2365881 * 2
def baseEnd_2365881 : Nat := 809889416226642142271345

theorem tailTrace_2365881 : CollatzResearch.WordTrace tailWord_2365881 prefixEnd_2365881 809889416226642142271345 := by
  unfold tailWord_2365881
  simp only [CollatzResearch.WordTrace]
  refine ⟨86290769141824672151025497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57527179427883114767350331 86290769141824672151025497)
  ·
    refine ⟨64718076856368504113269123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86290769141824672151025497 64718076856368504113269123)
    ·
      refine ⟨97077115284552756169903685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64718076856368504113269123 97077115284552756169903685)
      ·
        refine ⟨18201959115853641781856941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97077115284552756169903685 18201959115853641781856941)
        ·
          refine ⟨6825734668445115668196353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18201959115853641781856941 6825734668445115668196353)
          ·
            refine ⟨5119301001333836751147265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6825734668445115668196353 5119301001333836751147265)
            ·
              refine ⟨3839475751000377563360449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119301001333836751147265 3839475751000377563360449)
              ·
                refine ⟨2879606813250283172520337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839475751000377563360449 2879606813250283172520337)
                ·
                  refine ⟨2159705109937712379390253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2879606813250283172520337 2159705109937712379390253)
                  ·
                    refine ⟨809889416226642142271345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159705109937712379390253 809889416226642142271345)
                    ·
                      rfl

theorem cell22_2365881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_2365881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365881 prefixEnd_2365881 := by exact prefixLift 2365881
  have htrace : WordTrace (prefixWord ++ tailWord_2365881) baseStart_2365881 baseEnd_2365881 := by
    simpa [prefixWord, tailWord_2365881, baseEnd_2365881] using wordTrace_append hprefix tailTrace_2365881
  have hstable : (prefixWord ++ tailWord_2365881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365881).length < 2 ^ (prefixWord ++ tailWord_2365881).sum := by decide
  have hdescent : baseEnd_2365881 < baseStart_2365881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365909 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2365909 : Nat := 118140960795 + 2365909 * 2 ^ 59
def prefixEnd_2365909 : Nat := 4983230072969 + 3 ^ 40 * 2365909 * 2
def baseEnd_2365909 : Nat := 809899001198859402571259

theorem tailTrace_2365909 : CollatzResearch.WordTrace tailWord_2365909 prefixEnd_2365909 809899001198859402571259 := by
  unfold tailWord_2365909
  simp only [CollatzResearch.WordTrace]
  refine ⟨86291790385723232933044781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57527860257148821955363187 86291790385723232933044781)
  ·
    refine ⟨32359421394646212349891793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86291790385723232933044781 32359421394646212349891793)
    ·
      refine ⟨24269566045984659262418845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32359421394646212349891793 24269566045984659262418845)
      ·
        refine ⟨9101087267244247223407067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24269566045984659262418845 9101087267244247223407067)
        ·
          refine ⟨13651630900866370835110601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9101087267244247223407067 13651630900866370835110601)
          ·
            refine ⟨10238723175649778126332951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13651630900866370835110601 10238723175649778126332951)
            ·
              refine ⟨15358084763474667189499427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10238723175649778126332951 15358084763474667189499427)
              ·
                refine ⟨23037127145212000784249141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15358084763474667189499427 23037127145212000784249141)
                ·
                  refine ⟨2159730669863625073523357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23037127145212000784249141 2159730669863625073523357)
                  ·
                    refine ⟨809899001198859402571259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159730669863625073523357 809899001198859402571259)
                    ·
                      rfl

theorem cell22_2365909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2365909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365909 prefixEnd_2365909 := by exact prefixLift 2365909
  have htrace : WordTrace (prefixWord ++ tailWord_2365909) baseStart_2365909 baseEnd_2365909 := by
    simpa [prefixWord, tailWord_2365909, baseEnd_2365909] using wordTrace_append hprefix tailTrace_2365909
  have hstable : (prefixWord ++ tailWord_2365909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365909).length < 2 ^ (prefixWord ++ tailWord_2365909).sum := by decide
  have hdescent : baseEnd_2365909 < baseStart_2365909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365937 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2365937 : Nat := 118140960795 + 2365937 * 2 ^ 59
def prefixEnd_2365937 : Nat := 4983230072969 + 3 ^ 40 * 2365937 * 2
def baseEnd_2365937 : Nat := 809908586171076662871173

theorem tailTrace_2365937 : CollatzResearch.WordTrace tailWord_2365937 prefixEnd_2365937 809908586171076662871173 := by
  unfold tailWord_2365937
  simp only [CollatzResearch.WordTrace]
  refine ⟨86292811629621793715064065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57528541086414529143376043 86292811629621793715064065)
  ·
    refine ⟨64719608722216345286298049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86292811629621793715064065 64719608722216345286298049)
    ·
      refine ⟨48539706541662258964723537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64719608722216345286298049 48539706541662258964723537)
      ·
        refine ⟨36404779906246694223542653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48539706541662258964723537 36404779906246694223542653)
        ·
          refine ⟨13651792464842510333828495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36404779906246694223542653 13651792464842510333828495)
          ·
            refine ⟨20477688697263765500742743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13651792464842510333828495 20477688697263765500742743)
            ·
              refine ⟨30716533045895648251114115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20477688697263765500742743 30716533045895648251114115)
              ·
                refine ⟨46074799568843472376671173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30716533045895648251114115 46074799568843472376671173)
                ·
                  refine ⟨8639024919158151070625845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46074799568843472376671173 8639024919158151070625845)
                  ·
                    refine ⟨809908586171076662871173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8639024919158151070625845 809908586171076662871173)
                    ·
                      rfl

theorem cell22_2365937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2365937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2365937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2365937 prefixEnd_2365937 := by exact prefixLift 2365937
  have htrace : WordTrace (prefixWord ++ tailWord_2365937) baseStart_2365937 baseEnd_2365937 := by
    simpa [prefixWord, tailWord_2365937, baseEnd_2365937] using wordTrace_append hprefix tailTrace_2365937
  have hstable : (prefixWord ++ tailWord_2365937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365937).length < 2 ^ (prefixWord ++ tailWord_2365937).sum := by decide
  have hdescent : baseEnd_2365937 < baseStart_2365937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366020 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2366020 : Nat := 118140960795 + 2366020 * 2 ^ 59
def prefixEnd_2366020 : Nat := 4983230072969 + 3 ^ 40 * 2366020 * 2
def baseEnd_2366020 : Nat := 809936998767292113045919

theorem tailTrace_2366020 : CollatzResearch.WordTrace tailWord_2366020 prefixEnd_2366020 809936998767292113045919 := by
  unfold tailWord_2366020
  simp only [CollatzResearch.WordTrace]
  refine ⟨43147919444160549445167757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57530559258880732593557009 43147919444160549445167757)
  ·
    refine ⟨16180469791560206041937909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43147919444160549445167757 16180469791560206041937909)
    ·
      refine ⟨1516919042958769316431679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16180469791560206041937909 1516919042958769316431679)
      ·
        refine ⟨2275378564438153974647519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516919042958769316431679 2275378564438153974647519)
        ·
          refine ⟨3413067846657230961971279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275378564438153974647519 3413067846657230961971279)
          ·
            refine ⟨5119601769985846442956919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413067846657230961971279 5119601769985846442956919)
            ·
              refine ⟨7679402654978769664435379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119601769985846442956919 7679402654978769664435379)
              ·
                refine ⟨11519103982468154496653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679402654978769664435379 11519103982468154496653069)
                ·
                  refine ⟨4319663993425557936244901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11519103982468154496653069 4319663993425557936244901)
                  ·
                    refine ⟨809936998767292113045919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319663993425557936244901 809936998767292113045919)
                    ·
                      rfl

theorem cell22_2366020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2366020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366020 prefixEnd_2366020 := by exact prefixLift 2366020
  have htrace : WordTrace (prefixWord ++ tailWord_2366020) baseStart_2366020 baseEnd_2366020 := by
    simpa [prefixWord, tailWord_2366020, baseEnd_2366020] using wordTrace_append hprefix tailTrace_2366020
  have hstable : (prefixWord ++ tailWord_2366020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366020).length < 2 ^ (prefixWord ++ tailWord_2366020).sum := by decide
  have hdescent : baseEnd_2366020 < baseStart_2366020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366027 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_2366027 : Nat := 118140960795 + 2366027 * 2 ^ 59
def prefixEnd_2366027 : Nat := 4983230072969 + 3 ^ 40 * 2366027 * 2
def baseEnd_2366027 : Nat := 809939395010346428120897

theorem tailTrace_2366027 : CollatzResearch.WordTrace tailWord_2366027 prefixEnd_2366027 809939395010346428120897 := by
  unfold tailWord_2366027
  simp only [CollatzResearch.WordTrace]
  refine ⟨86296094199295739085840335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57530729466197159390560223 86296094199295739085840335)
  ·
    refine ⟨129444141298943608628760503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86296094199295739085840335 129444141298943608628760503)
    ·
      refine ⟨194166211948415412943140755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129444141298943608628760503 194166211948415412943140755)
      ·
        refine ⟨291249317922623119414711133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194166211948415412943140755 291249317922623119414711133)
        ·
          refine ⟨109218494220983669780516675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291249317922623119414711133 109218494220983669780516675)
          ·
            refine ⟨163827741331475504670775013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109218494220983669780516675 163827741331475504670775013)
            ·
              refine ⟨30717701499651657125770315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163827741331475504670775013 30717701499651657125770315)
              ·
                refine ⟨46076552249477485688655473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30717701499651657125770315 46076552249477485688655473)
                ·
                  refine ⟨34557414187108114266491605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46076552249477485688655473 34557414187108114266491605)
                  ·
                    refine ⟨809939395010346428120897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34557414187108114266491605 809939395010346428120897)
                    ·
                      rfl

theorem cell22_2366027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_2366027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366027 prefixEnd_2366027 := by exact prefixLift 2366027
  have htrace : WordTrace (prefixWord ++ tailWord_2366027) baseStart_2366027 baseEnd_2366027 := by
    simpa [prefixWord, tailWord_2366027, baseEnd_2366027] using wordTrace_append hprefix tailTrace_2366027
  have hstable : (prefixWord ++ tailWord_2366027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366027).length < 2 ^ (prefixWord ++ tailWord_2366027).sum := by decide
  have hdescent : baseEnd_2366027 < baseStart_2366027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366108 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_2366108 : Nat := 118140960795 + 2366108 * 2 ^ 59
def prefixEnd_2366108 : Nat := 4983230072969 + 3 ^ 40 * 2366108 * 2
def baseEnd_2366108 : Nat := 269989040988563072281883

theorem tailTrace_2366108 : CollatzResearch.WordTrace tailWord_2366108 prefixEnd_2366108 269989040988563072281883 := by
  unfold tailWord_2366108
  simp only [CollatzResearch.WordTrace]
  refine ⟨43149524256001144959769489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57532699008001526613025985 43149524256001144959769489)
  ·
    refine ⟨32362143192000858719827117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43149524256001144959769489 32362143192000858719827117)
    ·
      refine ⟨12135803697000322019935169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32362143192000858719827117 12135803697000322019935169)
      ·
        refine ⟨9101852772750241514951377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12135803697000322019935169 9101852772750241514951377)
        ·
          refine ⟨6826389579562681136213533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9101852772750241514951377 6826389579562681136213533)
          ·
            refine ⟨2559896092336005426080075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6826389579562681136213533 2559896092336005426080075)
            ·
              refine ⟨3839844138504008139120113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559896092336005426080075 3839844138504008139120113)
              ·
                refine ⟨2879883103878006104340085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839844138504008139120113 2879883103878006104340085)
                ·
                  refine ⟨269989040988563072281883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879883103878006104340085 269989040988563072281883)
                  ·
                    rfl

theorem cell22_2366108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_2366108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366108 prefixEnd_2366108 := by exact prefixLift 2366108
  have htrace : WordTrace (prefixWord ++ tailWord_2366108) baseStart_2366108 baseEnd_2366108 := by
    simpa [prefixWord, tailWord_2366108, baseEnd_2366108] using wordTrace_append hprefix tailTrace_2366108
  have hstable : (prefixWord ++ tailWord_2366108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366108).length < 2 ^ (prefixWord ++ tailWord_2366108).sum := by decide
  have hdescent : baseEnd_2366108 < baseStart_2366108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366181 : List Nat := [1, 3, 1, 4, 1, 3, 2, 7]
def baseStart_2366181 : Nat := 118140960795 + 2366181 * 2 ^ 59
def prefixEnd_2366181 : Nat := 4983230072969 + 3 ^ 40 * 2366181 * 2
def baseEnd_2366181 : Nat := 89999123595282373307825

theorem tailTrace_2366181 : CollatzResearch.WordTrace tailWord_2366181 prefixEnd_2366181 89999123595282373307825 := by
  unfold tailWord_2366181
  simp only [CollatzResearch.WordTrace]
  refine ⟨86301711040737823386946397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57534474027158548924630931 86301711040737823386946397)
  ·
    refine ⟨32363141640276683770104899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86301711040737823386946397 32363141640276683770104899)
    ·
      refine ⟨48544712460415025655157349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32363141640276683770104899 48544712460415025655157349)
      ·
        refine ⟨9102133586327817310342003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48544712460415025655157349 9102133586327817310342003)
        ·
          refine ⟨13653200379491725965513005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9102133586327817310342003 13653200379491725965513005)
          ·
            refine ⟨5119950142309397237067377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13653200379491725965513005 5119950142309397237067377)
            ·
              refine ⟨3839962606732047927800533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119950142309397237067377 3839962606732047927800533)
              ·
                refine ⟨89999123595282373307825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3839962606732047927800533 89999123595282373307825)
                ·
                  rfl

theorem cell22_2366181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 7].length) (baseStart_2366181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366181 prefixEnd_2366181 := by exact prefixLift 2366181
  have htrace : WordTrace (prefixWord ++ tailWord_2366181) baseStart_2366181 baseEnd_2366181 := by
    simpa [prefixWord, tailWord_2366181, baseEnd_2366181] using wordTrace_append hprefix tailTrace_2366181
  have hstable : (prefixWord ++ tailWord_2366181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366181).length < 2 ^ (prefixWord ++ tailWord_2366181).sum := by decide
  have hdescent : baseEnd_2366181 < baseStart_2366181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366241 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2366241 : Nat := 118140960795 + 2366241 * 2 ^ 59
def prefixEnd_2366241 : Nat := 4983230072969 + 3 ^ 40 * 2366241 * 2
def baseEnd_2366241 : Nat := 810012651583721203270241

theorem tailTrace_2366241 : CollatzResearch.WordTrace tailWord_2366241 prefixEnd_2366241 810012651583721203270241 := by
  unfold tailWord_2366241
  simp only [CollatzResearch.WordTrace]
  refine ⟨86303899420520453634130577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57535932947013635756087051 86303899420520453634130577)
  ·
    refine ⟨64727924565390340225597933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86303899420520453634130577 64727924565390340225597933)
    ·
      refine ⟨24272971712021377584599225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64727924565390340225597933 24272971712021377584599225)
      ·
        refine ⟨18204728784016033188449419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24272971712021377584599225 18204728784016033188449419)
        ·
          refine ⟨27307093176024049782674129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18204728784016033188449419 27307093176024049782674129)
          ·
            refine ⟨20480319882018037337005597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27307093176024049782674129 20480319882018037337005597)
            ·
              refine ⟨7680119955756764001377099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20480319882018037337005597 7680119955756764001377099)
              ·
                refine ⟨11520179933635146002065649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7680119955756764001377099 11520179933635146002065649)
                ·
                  refine ⟨8640134950226359501549237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11520179933635146002065649 8640134950226359501549237)
                  ·
                    refine ⟨810012651583721203270241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8640134950226359501549237 810012651583721203270241)
                    ·
                      rfl

theorem cell22_2366241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2366241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366241 prefixEnd_2366241 := by exact prefixLift 2366241
  have htrace : WordTrace (prefixWord ++ tailWord_2366241) baseStart_2366241 baseEnd_2366241 := by
    simpa [prefixWord, tailWord_2366241, baseEnd_2366241] using wordTrace_append hprefix tailTrace_2366241
  have hstable : (prefixWord ++ tailWord_2366241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366241).length < 2 ^ (prefixWord ++ tailWord_2366241).sum := by decide
  have hdescent : baseEnd_2366241 < baseStart_2366241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366286 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2366286 : Nat := 118140960795 + 2366286 * 2 ^ 59
def prefixEnd_2366286 : Nat := 4983230072969 + 3 ^ 40 * 2366286 * 2
def baseEnd_2366286 : Nat := 810028056003356085895103

theorem tailTrace_2366286 : CollatzResearch.WordTrace tailWord_2366286 prefixEnd_2366286 810028056003356085895103 := by
  unfold tailWord_2366286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10788192588169678289939839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57537027136904950879679141 10788192588169678289939839)
  ·
    refine ⟨16182288882254517434909759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10788192588169678289939839 16182288882254517434909759)
    ·
      refine ⟨24273433323381776152364639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16182288882254517434909759 24273433323381776152364639)
      ·
        refine ⟨36410149985072664228546959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24273433323381776152364639 36410149985072664228546959)
        ·
          refine ⟨54615224977608996342820439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36410149985072664228546959 54615224977608996342820439)
          ·
            refine ⟨81922837466413494514230659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54615224977608996342820439 81922837466413494514230659)
            ·
              refine ⟨122884256199620241771345989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81922837466413494514230659 122884256199620241771345989)
              ·
                refine ⟨23040798037428795332127373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122884256199620241771345989 23040798037428795332127373)
                ·
                  refine ⟨8640299264035798249547765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23040798037428795332127373 8640299264035798249547765)
                  ·
                    refine ⟨810028056003356085895103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8640299264035798249547765 810028056003356085895103)
                    ·
                      rfl

theorem cell22_2366286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2366286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366286 prefixEnd_2366286 := by exact prefixLift 2366286
  have htrace : WordTrace (prefixWord ++ tailWord_2366286) baseStart_2366286 baseEnd_2366286 := by
    simpa [prefixWord, tailWord_2366286, baseEnd_2366286] using wordTrace_append hprefix tailTrace_2366286
  have hstable : (prefixWord ++ tailWord_2366286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366286).length < 2 ^ (prefixWord ++ tailWord_2366286).sum := by decide
  have hdescent : baseEnd_2366286 < baseStart_2366286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366288 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_2366288 : Nat := 118140960795 + 2366288 * 2 ^ 59
def prefixEnd_2366288 : Nat := 4983230072969 + 3 ^ 40 * 2366288 * 2
def baseEnd_2366288 : Nat := 270009580214742915781699

theorem tailTrace_2366288 : CollatzResearch.WordTrace tailWord_2366288 prefixEnd_2366288 270009580214742915781699 := by
  unfold tailWord_2366288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43152806825675090330545759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57537075767566787107394345 43152806825675090330545759)
  ·
    refine ⟨64729210238512635495818639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43152806825675090330545759 64729210238512635495818639)
    ·
      refine ⟨97093815357768953243727959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64729210238512635495818639 97093815357768953243727959)
      ·
        refine ⟨145640723036653429865591939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97093815357768953243727959 145640723036653429865591939)
        ·
          refine ⟨218461084554980144798387909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145640723036653429865591939 218461084554980144798387909)
          ·
            refine ⟨40961453354058777149697733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218461084554980144798387909 40961453354058777149697733)
            ·
              refine ⟨7680272503886020715568325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40961453354058777149697733 7680272503886020715568325)
              ·
                refine ⟨1440051094478628884169061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7680272503886020715568325 1440051094478628884169061)
                ·
                  refine ⟨270009580214742915781699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440051094478628884169061 270009580214742915781699)
                  ·
                    rfl

theorem cell22_2366288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_2366288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366288 prefixEnd_2366288 := by exact prefixLift 2366288
  have htrace : WordTrace (prefixWord ++ tailWord_2366288) baseStart_2366288 baseEnd_2366288 := by
    simpa [prefixWord, tailWord_2366288, baseEnd_2366288] using wordTrace_append hprefix tailTrace_2366288
  have hstable : (prefixWord ++ tailWord_2366288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366288).length < 2 ^ (prefixWord ++ tailWord_2366288).sum := by decide
  have hdescent : baseEnd_2366288 < baseStart_2366288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366316 : List Nat := [2, 2, 1, 1, 4, 1, 3, 8]
def baseStart_2366316 : Nat := 118140960795 + 2366316 * 2 ^ 59
def prefixEnd_2366316 : Nat := 4983230072969 + 3 ^ 40 * 2366316 * 2
def baseEnd_2366316 : Nat := 90004258401827334182779

theorem tailTrace_2366316 : CollatzResearch.WordTrace tailWord_2366316 prefixEnd_2366316 90004258401827334182779 := by
  unfold tailWord_2366316
  simp only [CollatzResearch.WordTrace]
  refine ⟨43153317447624370721555401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57537756596832494295407201 43153317447624370721555401)
  ·
    refine ⟨32364988085718278041166551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43153317447624370721555401 32364988085718278041166551)
    ·
      refine ⟨48547482128577417061749827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32364988085718278041166551 48547482128577417061749827)
      ·
        refine ⟨72821223192866125592624741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48547482128577417061749827 72821223192866125592624741)
        ·
          refine ⟨13653979348662398548617139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72821223192866125592624741 13653979348662398548617139)
          ·
            refine ⟨20480969022993597822925709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13653979348662398548617139 20480969022993597822925709)
            ·
              refine ⟨7680363383622599183597141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20480969022993597822925709 7680363383622599183597141)
              ·
                refine ⟨90004258401827334182779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7680363383622599183597141 90004258401827334182779)
                ·
                  rfl

theorem cell22_2366316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_2366316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366316 prefixEnd_2366316 := by exact prefixLift 2366316
  have htrace : WordTrace (prefixWord ++ tailWord_2366316) baseStart_2366316 baseEnd_2366316 := by
    simpa [prefixWord, tailWord_2366316, baseEnd_2366316] using wordTrace_append hprefix tailTrace_2366316
  have hstable : (prefixWord ++ tailWord_2366316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366316).length < 2 ^ (prefixWord ++ tailWord_2366316).sum := by decide
  have hdescent : baseEnd_2366316 < baseStart_2366316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366390 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_2366390 : Nat := 118140960795 + 2366390 * 2 ^ 59
def prefixEnd_2366390 : Nat := 4983230072969 + 3 ^ 40 * 2366390 * 2
def baseEnd_2366390 : Nat := 270021219109578160431595

theorem tailTrace_2366390 : CollatzResearch.WordTrace tailWord_2366390 prefixEnd_2366390 270021219109578160431595 := by
  unfold tailWord_2366390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394333368561290755081539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57539555931320434720869749 5394333368561290755081539)
  ·
    refine ⟨8091500052841936132622309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5394333368561290755081539 8091500052841936132622309)
    ·
      refine ⟨1517156259907863024866683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8091500052841936132622309 1517156259907863024866683)
      ·
        refine ⟨2275734389861794537300025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517156259907863024866683 2275734389861794537300025)
        ·
          refine ⟨1706800792396345902975019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275734389861794537300025 1706800792396345902975019)
          ·
            refine ⟨2560201188594518854462529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706800792396345902975019 2560201188594518854462529)
            ·
              refine ⟨1920150891445889140846897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560201188594518854462529 1920150891445889140846897)
              ·
                refine ⟨1440113168584416855635173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920150891445889140846897 1440113168584416855635173)
                ·
                  refine ⟨270021219109578160431595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440113168584416855635173 270021219109578160431595)
                  ·
                    rfl

theorem cell22_2366390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_2366390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366390 prefixEnd_2366390 := by exact prefixLift 2366390
  have htrace : WordTrace (prefixWord ++ tailWord_2366390) baseStart_2366390 baseEnd_2366390 := by
    simpa [prefixWord, tailWord_2366390, baseEnd_2366390] using wordTrace_append hprefix tailTrace_2366390
  have hstable : (prefixWord ++ tailWord_2366390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366390).length < 2 ^ (prefixWord ++ tailWord_2366390).sum := by decide
  have hdescent : baseEnd_2366390 < baseStart_2366390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366440 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_2366440 : Nat := 118140960795 + 2366440 * 2 ^ 59
def prefixEnd_2366440 : Nat := 4983230072969 + 3 ^ 40 * 2366440 * 2
def baseEnd_2366440 : Nat := 270026924450183672514877

theorem tailTrace_2366440 : CollatzResearch.WordTrace tailWord_2366440 prefixEnd_2366440 270026924450183672514877 := by
  unfold tailWord_2366440
  simp only [CollatzResearch.WordTrace]
  refine ⟨43155578773399755310312387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57540771697866340413749849 43155578773399755310312387)
  ·
    refine ⟨64733368160099632965468581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43155578773399755310312387 64733368160099632965468581)
    ·
      refine ⟨12137506530018681181025359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64733368160099632965468581 12137506530018681181025359)
      ·
        refine ⟨18206259795028021771538039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12137506530018681181025359 18206259795028021771538039)
        ·
          refine ⟨27309389692542032657307059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18206259795028021771538039 27309389692542032657307059)
          ·
            refine ⟨40964084538813048985960589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27309389692542032657307059 40964084538813048985960589)
            ·
              refine ⟨15361531702054893369735221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40964084538813048985960589 15361531702054893369735221)
              ·
                refine ⟨1440143597067646253412677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15361531702054893369735221 1440143597067646253412677)
                ·
                  refine ⟨270026924450183672514877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440143597067646253412677 270026924450183672514877)
                  ·
                    rfl

theorem cell22_2366440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_2366440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366440 prefixEnd_2366440 := by exact prefixLift 2366440
  have htrace : WordTrace (prefixWord ++ tailWord_2366440) baseStart_2366440 baseEnd_2366440 := by
    simpa [prefixWord, tailWord_2366440, baseEnd_2366440] using wordTrace_append hprefix tailTrace_2366440
  have hstable : (prefixWord ++ tailWord_2366440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366440).length < 2 ^ (prefixWord ++ tailWord_2366440).sum := by decide
  have hdescent : baseEnd_2366440 < baseStart_2366440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366442 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2366442 : Nat := 118140960795 + 2366442 * 2 ^ 59
def prefixEnd_2366442 : Nat := 4983230072969 + 3 ^ 40 * 2366442 * 2
def baseEnd_2366442 : Nat := 810081457991423678994625

theorem tailTrace_2366442 : CollatzResearch.WordTrace tailWord_2366442 prefixEnd_2366442 810081457991423678994625 := by
  unfold tailWord_2366442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21577807623198066240549395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57540820328528176641465053 21577807623198066240549395)
  ·
    refine ⟨32366711434797099360824093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21577807623198066240549395 32366711434797099360824093)
    ·
      refine ⟨12137516788048912260309035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32366711434797099360824093 12137516788048912260309035)
      ·
        refine ⟨18206275182073368390463553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12137516788048912260309035 18206275182073368390463553)
        ·
          refine ⟨13654706386555026292847665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18206275182073368390463553 13654706386555026292847665)
          ·
            refine ⟨10241029789916269719635749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13654706386555026292847665 10241029789916269719635749)
            ·
              refine ⟨1920193085609300572431703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10241029789916269719635749 1920193085609300572431703)
              ·
                refine ⟨2880289628413950858647555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920193085609300572431703 2880289628413950858647555)
                ·
                  refine ⟨4320434442620926287971333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880289628413950858647555 4320434442620926287971333)
                  ·
                    refine ⟨810081457991423678994625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320434442620926287971333 810081457991423678994625)
                    ·
                      rfl

theorem cell22_2366442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2366442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366442 prefixEnd_2366442 := by exact prefixLift 2366442
  have htrace : WordTrace (prefixWord ++ tailWord_2366442) baseStart_2366442 baseEnd_2366442 := by
    simpa [prefixWord, tailWord_2366442, baseEnd_2366442] using wordTrace_append hprefix tailTrace_2366442
  have hstable : (prefixWord ++ tailWord_2366442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366442).length < 2 ^ (prefixWord ++ tailWord_2366442).sum := by decide
  have hdescent : baseEnd_2366442 < baseStart_2366442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366485 : List Nat := [1, 3, 2, 1, 4, 1, 4, 6]
def baseStart_2366485 : Nat := 118140960795 + 2366485 * 2 ^ 59
def prefixEnd_2366485 : Nat := 4983230072969 + 3 ^ 40 * 2366485 * 2
def baseEnd_2366485 : Nat := 90010686418909544463277

theorem tailTrace_2366485 : CollatzResearch.WordTrace tailWord_2366485 prefixEnd_2366485 90010686418909544463277 := by
  unfold tailWord_2366485
  simp only [CollatzResearch.WordTrace]
  refine ⟨86312798831636483306012909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57541865887757655537341939 86312798831636483306012909)
  ·
    refine ⟨32367299561863681239754841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86312798831636483306012909 32367299561863681239754841)
    ·
      refine ⟨24275474671397760929816131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32367299561863681239754841 24275474671397760929816131)
      ·
        refine ⟨36413212007096641394724197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24275474671397760929816131 36413212007096641394724197)
        ·
          refine ⟨6827477251330620261510787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36413212007096641394724197 6827477251330620261510787)
          ·
            refine ⟨10241215876995930392266181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827477251330620261510787 10241215876995930392266181)
            ·
              refine ⟨1920227976936736948549909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10241215876995930392266181 1920227976936736948549909)
              ·
                refine ⟨90010686418909544463277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1920227976936736948549909 90010686418909544463277)
                ·
                  rfl

theorem cell22_2366485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 6].length) (baseStart_2366485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366485 prefixEnd_2366485 := by exact prefixLift 2366485
  have htrace : WordTrace (prefixWord ++ tailWord_2366485) baseStart_2366485 baseEnd_2366485 := by
    simpa [prefixWord, tailWord_2366485, baseEnd_2366485] using wordTrace_append hprefix tailTrace_2366485
  have hstable : (prefixWord ++ tailWord_2366485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366485).length < 2 ^ (prefixWord ++ tailWord_2366485).sum := by decide
  have hdescent : baseEnd_2366485 < baseStart_2366485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366513 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 7]
def baseStart_2366513 : Nat := 118140960795 + 2366513 * 2 ^ 59
def prefixEnd_2366513 : Nat := 4983230072969 + 3 ^ 40 * 2366513 * 2
def baseEnd_2366513 : Nat := 270035254247467720156469

theorem tailTrace_2366513 : CollatzResearch.WordTrace tailWord_2366513 prefixEnd_2366513 270035254247467720156469 := by
  unfold tailWord_2366513
  simp only [CollatzResearch.WordTrace]
  refine ⟨86313820075535044088032193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57542546717023362725354795 86313820075535044088032193)
  ·
    refine ⟨64735365056651283066024145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86313820075535044088032193 64735365056651283066024145)
    ·
      refine ⟨48551523792488462299518109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64735365056651283066024145 48551523792488462299518109)
      ·
        refine ⟨18206821422183173362319291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48551523792488462299518109 18206821422183173362319291)
        ·
          refine ⟨27310232133274760043478937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18206821422183173362319291 27310232133274760043478937)
          ·
            refine ⟨20482674099956070032609203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27310232133274760043478937 20482674099956070032609203)
            ·
              refine ⟨30724011149934105048913805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20482674099956070032609203 30724011149934105048913805)
              ·
                refine ⟨11521504181225289393342677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30724011149934105048913805 11521504181225289393342677)
                ·
                  refine ⟨270035254247467720156469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11521504181225289393342677 270035254247467720156469)
                  ·
                    rfl

theorem cell22_2366513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_2366513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366513 prefixEnd_2366513 := by exact prefixLift 2366513
  have htrace : WordTrace (prefixWord ++ tailWord_2366513) baseStart_2366513 baseEnd_2366513 := by
    simpa [prefixWord, tailWord_2366513, baseEnd_2366513] using wordTrace_append hprefix tailTrace_2366513
  have hstable : (prefixWord ++ tailWord_2366513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366513).length < 2 ^ (prefixWord ++ tailWord_2366513).sum := by decide
  have hdescent : baseEnd_2366513 < baseStart_2366513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366528 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_2366528 : Nat := 118140960795 + 2366528 * 2 ^ 59
def prefixEnd_2366528 : Nat := 4983230072969 + 3 ^ 40 * 2366528 * 2
def baseEnd_2366528 : Nat := 810110897548948121344361

theorem tailTrace_2366528 : CollatzResearch.WordTrace tailWord_2366528 prefixEnd_2366528 810110897548948121344361 := by
  unfold tailWord_2366528
  simp only [CollatzResearch.WordTrace]
  refine ⟨43157183585240350824914119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57542911446987134433218825 43157183585240350824914119)
  ·
    refine ⟨64735775377860526237371179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43157183585240350824914119 64735775377860526237371179)
    ·
      refine ⟨97103663066790789356056769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64735775377860526237371179 97103663066790789356056769)
      ·
        refine ⟨72827747300093092017042577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97103663066790789356056769 72827747300093092017042577)
        ·
          refine ⟨54620810475069819012781933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72827747300093092017042577 54620810475069819012781933)
          ·
            refine ⟨20482803928151182129793225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54620810475069819012781933 20482803928151182129793225)
            ·
              refine ⟨15362102946113386597344919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20482803928151182129793225 15362102946113386597344919)
              ·
                refine ⟨23043154419170079896017379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15362102946113386597344919 23043154419170079896017379)
                ·
                  refine ⟨34564731628755119844026069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23043154419170079896017379 34564731628755119844026069)
                  ·
                    refine ⟨810110897548948121344361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34564731628755119844026069 810110897548948121344361)
                    ·
                      rfl

theorem cell22_2366528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_2366528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366528 prefixEnd_2366528 := by exact prefixLift 2366528
  have htrace : WordTrace (prefixWord ++ tailWord_2366528) baseStart_2366528 baseEnd_2366528 := by
    simpa [prefixWord, tailWord_2366528, baseEnd_2366528] using wordTrace_append hprefix tailTrace_2366528
  have hstable : (prefixWord ++ tailWord_2366528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366528).length < 2 ^ (prefixWord ++ tailWord_2366528).sum := by decide
  have hdescent : baseEnd_2366528 < baseStart_2366528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366603 : List Nat := [1, 1, 1, 1, 4, 1, 1, 12]
def baseStart_2366603 : Nat := 118140960795 + 2366603 * 2 ^ 59
def prefixEnd_2366603 : Nat := 4983230072969 + 3 ^ 40 * 2366603 * 2
def baseEnd_2366603 : Nat := 90015174620185880635459

theorem tailTrace_2366603 : CollatzResearch.WordTrace tailWord_2366603 prefixEnd_2366603 90015174620185880635459 := by
  unfold tailWord_2366603
  simp only [CollatzResearch.WordTrace]
  refine ⟨86317102645208989458808463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57544735096805992972538975 86317102645208989458808463)
  ·
    refine ⟨129475653967813484188212695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86317102645208989458808463 129475653967813484188212695)
    ·
      refine ⟨194213480951720226282319043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129475653967813484188212695 194213480951720226282319043)
      ·
        refine ⟨291320221427580339423478565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194213480951720226282319043 291320221427580339423478565)
        ·
          refine ⟨54622541517671313641902231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291320221427580339423478565 54622541517671313641902231)
          ·
            refine ⟨81933812276506970462853347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54622541517671313641902231 81933812276506970462853347)
            ·
              refine ⟨122900718414760455694280021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81933812276506970462853347 122900718414760455694280021)
              ·
                refine ⟨90015174620185880635459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 122900718414760455694280021 90015174620185880635459)
                ·
                  rfl

theorem cell22_2366603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 12].length) (baseStart_2366603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366603 prefixEnd_2366603 := by exact prefixLift 2366603
  have htrace : WordTrace (prefixWord ++ tailWord_2366603) baseStart_2366603 baseEnd_2366603 := by
    simpa [prefixWord, tailWord_2366603, baseEnd_2366603] using wordTrace_append hprefix tailTrace_2366603
  have hstable : (prefixWord ++ tailWord_2366603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366603).length < 2 ^ (prefixWord ++ tailWord_2366603).sum := by decide
  have hdescent : baseEnd_2366603 < baseStart_2366603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366620 : List Nat := [2, 2, 3, 2, 1, 3, 9]
def baseStart_2366620 : Nat := 118140960795 + 2366620 * 2 ^ 59
def prefixEnd_2366620 : Nat := 4983230072969 + 3 ^ 40 * 2366620 * 2
def baseEnd_2366620 : Nat := 30005273741818168446077

theorem tailTrace_2366620 : CollatzResearch.WordTrace tailWord_2366620 prefixEnd_2366620 30005273741818168446077 := by
  unfold tailWord_2366620
  simp only [CollatzResearch.WordTrace]
  refine ⟨43158861343073700681088657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57545148457431600908118209 43158861343073700681088657)
  ·
    refine ⟨32369146007305275510816493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43158861343073700681088657 32369146007305275510816493)
    ·
      refine ⟨12138429752739478316556185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32369146007305275510816493 12138429752739478316556185)
      ·
        refine ⟨9103822314554608737417139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12138429752739478316556185 9103822314554608737417139)
        ·
          refine ⟨13655733471831913106125709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103822314554608737417139 13655733471831913106125709)
          ·
            refine ⟨5120900051936967414797141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13655733471831913106125709 5120900051936967414797141)
            ·
              refine ⟨30005273741818168446077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5120900051936967414797141 30005273741818168446077)
              ·
                rfl

theorem cell22_2366620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 9].length) (baseStart_2366620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366620 prefixEnd_2366620 := by exact prefixLift 2366620
  have htrace : WordTrace (prefixWord ++ tailWord_2366620) baseStart_2366620 baseEnd_2366620 := by
    simpa [prefixWord, tailWord_2366620, baseEnd_2366620] using wordTrace_append hprefix tailTrace_2366620
  have hstable : (prefixWord ++ tailWord_2366620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366620).length < 2 ^ (prefixWord ++ tailWord_2366620).sum := by decide
  have hdescent : baseEnd_2366620 < baseStart_2366620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366641 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_2366641 : Nat := 118140960795 + 2366641 * 2 ^ 59
def prefixEnd_2366641 : Nat := 4983230072969 + 3 ^ 40 * 2366641 * 2
def baseEnd_2366641 : Nat := 810149579758253493269015

theorem tailTrace_2366641 : CollatzResearch.WordTrace tailWord_2366641 prefixEnd_2366641 810149579758253493269015 := by
  unfold tailWord_2366641
  simp only [CollatzResearch.WordTrace]
  refine ⟨86318488619071321948691777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57545659079380881299127851 86318488619071321948691777)
  ·
    refine ⟨64738866464303491461518833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86318488619071321948691777 64738866464303491461518833)
    ·
      refine ⟨48554149848227618596139125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64738866464303491461518833 48554149848227618596139125)
      ·
        refine ⟨4551951548271339243388043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48554149848227618596139125 4551951548271339243388043)
        ·
          refine ⟨6827927322407008865082065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551951548271339243388043 6827927322407008865082065)
          ·
            refine ⟨5120945491805256648811549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827927322407008865082065 5120945491805256648811549)
            ·
              refine ⟨1920354559426971243304331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5120945491805256648811549 1920354559426971243304331)
              ·
                refine ⟨2880531839140456864956497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920354559426971243304331 2880531839140456864956497)
                ·
                  refine ⟨2160398879355342648717373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2880531839140456864956497 2160398879355342648717373)
                  ·
                    refine ⟨810149579758253493269015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2160398879355342648717373 810149579758253493269015)
                    ·
                      rfl

theorem cell22_2366641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_2366641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366641 prefixEnd_2366641 := by exact prefixLift 2366641
  have htrace : WordTrace (prefixWord ++ tailWord_2366641) baseStart_2366641 baseEnd_2366641 := by
    simpa [prefixWord, tailWord_2366641, baseEnd_2366641] using wordTrace_append hprefix tailTrace_2366641
  have hstable : (prefixWord ++ tailWord_2366641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366641).length < 2 ^ (prefixWord ++ tailWord_2366641).sum := by decide
  have hdescent : baseEnd_2366641 < baseStart_2366641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366654 : List Nat := [4, 2, 1, 1, 3, 3, 2, 6]
def baseStart_2366654 : Nat := 118140960795 + 2366654 * 2 ^ 59
def prefixEnd_2366654 : Nat := 4983230072969 + 3 ^ 40 * 2366654 * 2
def baseEnd_2366654 : Nat := 90017114435991754743775

theorem tailTrace_2366654 : CollatzResearch.WordTrace tailWord_2366654 prefixEnd_2366654 90017114435991754743775 := by
  unfold tailWord_2366654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789870346003028146114377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57545975178682816779276677 10789870346003028146114377)
  ·
    refine ⟨8092402759502271109585783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10789870346003028146114377 8092402759502271109585783)
    ·
      refine ⟨12138604139253406664378675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8092402759502271109585783 12138604139253406664378675)
      ·
        refine ⟨18207906208880109996568013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12138604139253406664378675 18207906208880109996568013)
        ·
          refine ⟨6827964828330041248713005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18207906208880109996568013 6827964828330041248713005)
          ·
            refine ⟨2560486810623765468267377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6827964828330041248713005 2560486810623765468267377)
            ·
              refine ⟨1920365107967824101200533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560486810623765468267377 1920365107967824101200533)
              ·
                refine ⟨90017114435991754743775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1920365107967824101200533 90017114435991754743775)
                ·
                  rfl

theorem cell22_2366654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_2366654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366654 prefixEnd_2366654 := by exact prefixLift 2366654
  have htrace : WordTrace (prefixWord ++ tailWord_2366654) baseStart_2366654 baseEnd_2366654 := by
    simpa [prefixWord, tailWord_2366654, baseEnd_2366654] using wordTrace_append hprefix tailTrace_2366654
  have hstable : (prefixWord ++ tailWord_2366654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366654).length < 2 ^ (prefixWord ++ tailWord_2366654).sum := by decide
  have hdescent : baseEnd_2366654 < baseStart_2366654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366699 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 5]
def baseStart_2366699 : Nat := 118140960795 + 2366699 * 2 ^ 59
def prefixEnd_2366699 : Nat := 4983230072969 + 3 ^ 40 * 2366699 * 2
def baseEnd_2366699 : Nat := 270056478114520225106279

theorem tailTrace_2366699 : CollatzResearch.WordTrace tailWord_2366699 prefixEnd_2366699 270056478114520225106279 := by
  unfold tailWord_2366699
  simp only [CollatzResearch.WordTrace]
  refine ⟨86320604052861197854303151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57547069368574131902868767 86320604052861197854303151)
  ·
    refine ⟨129480906079291796781454727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86320604052861197854303151 129480906079291796781454727)
    ·
      refine ⟨194221359118937695172182091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129480906079291796781454727 194221359118937695172182091)
      ·
        refine ⟨291332038678406542758273137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194221359118937695172182091 291332038678406542758273137)
        ·
          refine ⟨218499029008804907068704853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291332038678406542758273137 218499029008804907068704853)
          ·
            refine ⟨2560535496196932504711385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 218499029008804907068704853 2560535496196932504711385)
            ·
              refine ⟨1920401622147699378533539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560535496196932504711385 1920401622147699378533539)
              ·
                refine ⟨2880602433221549067800309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920401622147699378533539 2880602433221549067800309)
                ·
                  refine ⟨270056478114520225106279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880602433221549067800309 270056478114520225106279)
                  ·
                    rfl

theorem cell22_2366699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 5].length) (baseStart_2366699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366699 prefixEnd_2366699 := by exact prefixLift 2366699
  have htrace : WordTrace (prefixWord ++ tailWord_2366699) baseStart_2366699 baseEnd_2366699 := by
    simpa [prefixWord, tailWord_2366699, baseEnd_2366699] using wordTrace_append hprefix tailTrace_2366699
  have hstable : (prefixWord ++ tailWord_2366699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366699).length < 2 ^ (prefixWord ++ tailWord_2366699).sum := by decide
  have hdescent : baseEnd_2366699 < baseStart_2366699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366729 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_2366729 : Nat := 118140960795 + 2366729 * 2 ^ 59
def prefixEnd_2366729 : Nat := 4983230072969 + 3 ^ 40 * 2366729 * 2
def baseEnd_2366729 : Nat := 810179703956650597068745

theorem tailTrace_2366729 : CollatzResearch.WordTrace tailWord_2366729 prefixEnd_2366729 810179703956650597068745 := by
  unfold tailWord_2366729
  simp only [CollatzResearch.WordTrace]
  refine ⟨86321698242752512977895241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57547798828501675318596827 86321698242752512977895241)
  ·
    refine ⟨64741273682064384733421431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86321698242752512977895241 64741273682064384733421431)
    ·
      refine ⟨97111910523096577100132147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64741273682064384733421431 97111910523096577100132147)
      ·
        refine ⟨145667865784644865650198221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97111910523096577100132147 145667865784644865650198221)
        ·
          refine ⟨54625449669241824618824333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145667865784644865650198221 54625449669241824618824333)
          ·
            refine ⟨20484543625965684232059125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54625449669241824618824333 20484543625965684232059125)
            ·
              refine ⟨1920425964934282896755543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20484543625965684232059125 1920425964934282896755543)
              ·
                refine ⟨2880638947401424345133315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920425964934282896755543 2880638947401424345133315)
                ·
                  refine ⟨4320958421102136517699973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880638947401424345133315 4320958421102136517699973)
                  ·
                    refine ⟨810179703956650597068745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4320958421102136517699973 810179703956650597068745)
                    ·
                      rfl

theorem cell22_2366729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_2366729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366729 prefixEnd_2366729 := by exact prefixLift 2366729
  have htrace : WordTrace (prefixWord ++ tailWord_2366729) baseStart_2366729 baseEnd_2366729 := by
    simpa [prefixWord, tailWord_2366729, baseEnd_2366729] using wordTrace_append hprefix tailTrace_2366729
  have hstable : (prefixWord ++ tailWord_2366729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366729).length < 2 ^ (prefixWord ++ tailWord_2366729).sum := by decide
  have hdescent : baseEnd_2366729 < baseStart_2366729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366744 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_2366744 : Nat := 118140960795 + 2366744 * 2 ^ 59
def prefixEnd_2366744 : Nat := 4983230072969 + 3 ^ 40 * 2366744 * 2
def baseEnd_2366744 : Nat := 270061612921065185981233

theorem tailTrace_2366744 : CollatzResearch.WordTrace tailWord_2366744 prefixEnd_2366744 270061612921065185981233 := by
  unfold tailWord_2366744
  simp only [CollatzResearch.WordTrace]
  refine ⟨43161122668849085269845643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57548163558465447026460857 43161122668849085269845643)
  ·
    refine ⟨64741684003273627904768465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43161122668849085269845643 64741684003273627904768465)
    ·
      refine ⟨48556263002455220928576349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64741684003273627904768465 48556263002455220928576349)
      ·
        refine ⟨18208598625920707848216131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48556263002455220928576349 18208598625920707848216131)
        ·
          refine ⟨27312897938881061772324197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208598625920707848216131 27312897938881061772324197)
          ·
            refine ⟨5121168363540199082310787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27312897938881061772324197 5121168363540199082310787)
            ·
              refine ⟨7681752545310298623466181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121168363540199082310787 7681752545310298623466181)
              ·
                refine ⟨1440328602245680991899909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7681752545310298623466181 1440328602245680991899909)
                ·
                  refine ⟨270061612921065185981233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440328602245680991899909 270061612921065185981233)
                  ·
                    rfl

theorem cell22_2366744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_2366744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366744 prefixEnd_2366744 := by exact prefixLift 2366744
  have htrace : WordTrace (prefixWord ++ tailWord_2366744) baseStart_2366744 baseEnd_2366744 := by
    simpa [prefixWord, tailWord_2366744, baseEnd_2366744] using wordTrace_append hprefix tailTrace_2366744
  have hstable : (prefixWord ++ tailWord_2366744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366744).length < 2 ^ (prefixWord ++ tailWord_2366744).sum := by decide
  have hdescent : baseEnd_2366744 < baseStart_2366744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366787 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 7, 3]
def baseStart_2366787 : Nat := 118140960795 + 2366787 * 2 ^ 59
def prefixEnd_2366787 : Nat := 4983230072969 + 3 ^ 40 * 2366787 * 2
def baseEnd_2366787 : Nat := 810199558541957779118567

theorem tailTrace_2366787 : CollatzResearch.WordTrace tailWord_2366787 prefixEnd_2366787 810199558541957779118567 := by
  unfold tailWord_2366787
  simp only [CollatzResearch.WordTrace]
  refine ⟨86323813676542388883506615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57549209117694925922337743 86323813676542388883506615)
  ·
    refine ⟨129485720514813583325259923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86323813676542388883506615 129485720514813583325259923)
    ·
      refine ⟨194228580772220374987889885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129485720514813583325259923 194228580772220374987889885)
      ·
        refine ⟨72835717789582640620458707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194228580772220374987889885 72835717789582640620458707)
        ·
          refine ⟨109253576684373960930688061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72835717789582640620458707 109253576684373960930688061)
          ·
            refine ⟨40970091256640235349008023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109253576684373960930688061 40970091256640235349008023)
            ·
              refine ⟨61455136884960353023512035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40970091256640235349008023 61455136884960353023512035)
              ·
                refine ⟨92182705327440529535268053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61455136884960353023512035 92182705327440529535268053)
                ·
                  refine ⟨2160532156111887410982845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92182705327440529535268053 2160532156111887410982845)
                  ·
                    refine ⟨810199558541957779118567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2160532156111887410982845 810199558541957779118567)
                    ·
                      rfl

theorem cell22_2366787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3].length) (baseStart_2366787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366787 prefixEnd_2366787 := by exact prefixLift 2366787
  have htrace : WordTrace (prefixWord ++ tailWord_2366787) baseStart_2366787 baseEnd_2366787 := by
    simpa [prefixWord, tailWord_2366787, baseEnd_2366787] using wordTrace_append hprefix tailTrace_2366787
  have hstable : (prefixWord ++ tailWord_2366787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366787).length < 2 ^ (prefixWord ++ tailWord_2366787).sum := by decide
  have hdescent : baseEnd_2366787 < baseStart_2366787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366817 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 5]
def baseStart_2366817 : Nat := 118140960795 + 2366817 * 2 ^ 59
def prefixEnd_2366817 : Nat := 4983230072969 + 3 ^ 40 * 2366817 * 2
def baseEnd_2366817 : Nat := 270069942718349233622825

theorem tailTrace_2366817 : CollatzResearch.WordTrace tailWord_2366817 prefixEnd_2366817 270069942718349233622825 := by
  unfold tailWord_2366817
  simp only [CollatzResearch.WordTrace]
  refine ⟨86324907866433704007098705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57549938577622469338065803 86324907866433704007098705)
  ·
    refine ⟨64743680899825278005324029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86324907866433704007098705 64743680899825278005324029)
    ·
      refine ⟨24278880337434479251996511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64743680899825278005324029 24278880337434479251996511)
      ·
        refine ⟨36418320506151718877994767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24278880337434479251996511 36418320506151718877994767)
        ·
          refine ⟨54627480759227578316992151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36418320506151718877994767 54627480759227578316992151)
          ·
            refine ⟨81941221138841367475488227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54627480759227578316992151 81941221138841367475488227)
            ·
              refine ⟨122911831708262051213232341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81941221138841367475488227 122911831708262051213232341)
              ·
                refine ⟨2880746055662391825310133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122911831708262051213232341 2880746055662391825310133)
                ·
                  refine ⟨270069942718349233622825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880746055662391825310133 270069942718349233622825)
                  ·
                    rfl

theorem cell22_2366817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_2366817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366817 prefixEnd_2366817 := by exact prefixLift 2366817
  have htrace : WordTrace (prefixWord ++ tailWord_2366817) baseStart_2366817 baseEnd_2366817 := by
    simpa [prefixWord, tailWord_2366817, baseEnd_2366817] using wordTrace_append hprefix tailTrace_2366817
  have hstable : (prefixWord ++ tailWord_2366817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366817).length < 2 ^ (prefixWord ++ tailWord_2366817).sum := by decide
  have hdescent : baseEnd_2366817 < baseStart_2366817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366868 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2366868 : Nat := 118140960795 + 2366868 * 2 ^ 59
def prefixEnd_2366868 : Nat := 4983230072969 + 3 ^ 40 * 2366868 * 2
def baseEnd_2366868 : Nat := 270075762165766855947773

theorem tailTrace_2366868 : CollatzResearch.WordTrace tailWord_2366868 prefixEnd_2366868 270075762165766855947773 := by
  unfold tailWord_2366868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43163383994624469858602629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57551178659499293144803505 43163383994624469858602629)
  ·
    refine ⟨8093134498992088098487993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43163383994624469858602629 8093134498992088098487993)
    ·
      refine ⟨6069850874244066073865995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8093134498992088098487993 6069850874244066073865995)
      ·
        refine ⟨9104776311366099110798993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069850874244066073865995 9104776311366099110798993)
        ·
          refine ⟨6828582233524574333099245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9104776311366099110798993 6828582233524574333099245)
          ·
            refine ⟨2560718337571715374912217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6828582233524574333099245 2560718337571715374912217)
            ·
              refine ⟨1920538753178786531184163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560718337571715374912217 1920538753178786531184163)
              ·
                refine ⟨2880808129768179796776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920538753178786531184163 2880808129768179796776245)
                ·
                  refine ⟨270075762165766855947773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880808129768179796776245 270075762165766855947773)
                  ·
                    rfl

theorem cell22_2366868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2366868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366868 prefixEnd_2366868 := by exact prefixLift 2366868
  have htrace : WordTrace (prefixWord ++ tailWord_2366868) baseStart_2366868 baseEnd_2366868 := by
    simpa [prefixWord, tailWord_2366868, baseEnd_2366868] using wordTrace_append hprefix tailTrace_2366868
  have hstable : (prefixWord ++ tailWord_2366868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366868).length < 2 ^ (prefixWord ++ tailWord_2366868).sum := by decide
  have hdescent : baseEnd_2366868 < baseStart_2366868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366892 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_2366892 : Nat := 118140960795 + 2366892 * 2 ^ 59
def prefixEnd_2366892 : Nat := 4983230072969 + 3 ^ 40 * 2366892 * 2
def baseEnd_2366892 : Nat := 810235502187772505243245

theorem tailTrace_2366892 : CollatzResearch.WordTrace tailWord_2366892 prefixEnd_2366892 810235502187772505243245 := by
  unfold tailWord_2366892
  simp only [CollatzResearch.WordTrace]
  refine ⟨43163821670580995908039465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57551762227441327877385953 43163821670580995908039465)
  ·
    refine ⟨32372866252935746931029599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43163821670580995908039465 32372866252935746931029599)
    ·
      refine ⟨48559299379403620396544399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32372866252935746931029599 48559299379403620396544399)
      ·
        refine ⟨72838949069105430594816599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48559299379403620396544399 72838949069105430594816599)
        ·
          refine ⟨109258423603658145892224899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72838949069105430594816599 109258423603658145892224899)
          ·
            refine ⟨163887635405487218838337349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109258423603658145892224899 163887635405487218838337349)
            ·
              refine ⟨30728931638528853532188253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163887635405487218838337349 30728931638528853532188253)
              ·
                refine ⟨11523349364448320074570595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30728931638528853532188253 11523349364448320074570595)
                ·
                  refine ⟨17285024046672480111855893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11523349364448320074570595 17285024046672480111855893)
                  ·
                    refine ⟨810235502187772505243245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17285024046672480111855893 810235502187772505243245)
                    ·
                      rfl

theorem cell22_2366892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_2366892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366892 prefixEnd_2366892 := by exact prefixLift 2366892
  have htrace : WordTrace (prefixWord ++ tailWord_2366892) baseStart_2366892 baseEnd_2366892 := by
    simpa [prefixWord, tailWord_2366892, baseEnd_2366892] using wordTrace_append hprefix tailTrace_2366892
  have hstable : (prefixWord ++ tailWord_2366892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366892).length < 2 ^ (prefixWord ++ tailWord_2366892).sum := by decide
  have hdescent : baseEnd_2366892 < baseStart_2366892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366909 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2366909 : Nat := 118140960795 + 2366909 * 2 ^ 59
def prefixEnd_2366909 : Nat := 4983230072969 + 3 ^ 40 * 2366909 * 2
def baseEnd_2366909 : Nat := 810241321635190127568193

theorem tailTrace_2366909 : CollatzResearch.WordTrace tailWord_2366909 prefixEnd_2366909 810241321635190127568193 := by
  unfold tailWord_2366909
  simp only [CollatzResearch.WordTrace]
  refine ⟨86328263382100403719447781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57552175588066935812965187 86328263382100403719447781)
  ·
    refine ⟨16186549384143825697396459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86328263382100403719447781 16186549384143825697396459)
    ·
      refine ⟨24279824076215738546094689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16186549384143825697396459 24279824076215738546094689)
      ·
        refine ⟨18209868057161803909571017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24279824076215738546094689 18209868057161803909571017)
        ·
          refine ⟨13657401042871352932178263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18209868057161803909571017 13657401042871352932178263)
          ·
            refine ⟨20486101564307029398267395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13657401042871352932178263 20486101564307029398267395)
            ·
              refine ⟨30729152346460544097401093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20486101564307029398267395 30729152346460544097401093)
              ·
                refine ⟨5761716064961352018262705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30729152346460544097401093 5761716064961352018262705)
                ·
                  refine ⟨4321287048721014013697029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5761716064961352018262705 4321287048721014013697029)
                  ·
                    refine ⟨810241321635190127568193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4321287048721014013697029 810241321635190127568193)
                    ·
                      rfl

theorem cell22_2366909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2366909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366909 prefixEnd_2366909 := by exact prefixLift 2366909
  have htrace : WordTrace (prefixWord ++ tailWord_2366909) baseStart_2366909 baseEnd_2366909 := by
    simpa [prefixWord, tailWord_2366909, baseEnd_2366909] using wordTrace_append hprefix tailTrace_2366909
  have hstable : (prefixWord ++ tailWord_2366909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366909).length < 2 ^ (prefixWord ++ tailWord_2366909).sum := by decide
  have hdescent : baseEnd_2366909 < baseStart_2366909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366924 : List Nat := [2, 2, 1, 4, 2, 1, 3, 7]
def baseStart_2366924 : Nat := 118140960795 + 2366924 * 2 ^ 59
def prefixEnd_2366924 : Nat := 4983230072969 + 3 ^ 40 * 2366924 * 2
def baseEnd_2366924 : Nat := 90027384049081676493683

theorem tailTrace_2366924 : CollatzResearch.WordTrace tailWord_2366924 prefixEnd_2366924 90027384049081676493683 := by
  unfold tailWord_2366924
  simp only [CollatzResearch.WordTrace]
  refine ⟨43164405238523030640621913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57552540318030707520829217 43164405238523030640621913)
  ·
    refine ⟨32373303928892272980466435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43164405238523030640621913 32373303928892272980466435)
    ·
      refine ⟨48559955893338409470699653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32373303928892272980466435 48559955893338409470699653)
      ·
        refine ⟨9104991730000951775756185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48559955893338409470699653 9104991730000951775756185)
        ·
          refine ⟨6828743797500713831817139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9104991730000951775756185 6828743797500713831817139)
          ·
            refine ⟨10243115696251070747725709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6828743797500713831817139 10243115696251070747725709)
            ·
              refine ⟨3841168386094151530397141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10243115696251070747725709 3841168386094151530397141)
              ·
                refine ⟨90027384049081676493683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3841168386094151530397141 90027384049081676493683)
                ·
                  rfl

theorem cell22_2366924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_2366924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366924 prefixEnd_2366924 := by exact prefixLift 2366924
  have htrace : WordTrace (prefixWord ++ tailWord_2366924) baseStart_2366924 baseEnd_2366924 := by
    simpa [prefixWord, tailWord_2366924, baseEnd_2366924] using wordTrace_append hprefix tailTrace_2366924
  have hstable : (prefixWord ++ tailWord_2366924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366924).length < 2 ^ (prefixWord ++ tailWord_2366924).sum := by decide
  have hdescent : baseEnd_2366924 < baseStart_2366924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366941 : List Nat := [1, 4, 3, 1, 1, 3, 3, 6]
def baseStart_2366941 : Nat := 118140960795 + 2366941 * 2 ^ 59
def prefixEnd_2366941 : Nat := 4983230072969 + 3 ^ 40 * 2366941 * 2
def baseEnd_2366941 : Nat := 90028030654350301196455

theorem tailTrace_2366941 : CollatzResearch.WordTrace tailWord_2366941 prefixEnd_2366941 90028030654350301196455 := by
  unfold tailWord_2366941
  simp only [CollatzResearch.WordTrace]
  refine ⟨86329430517984473184612677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57552953678656315456408451 86329430517984473184612677)
  ·
    refine ⟨16186768222122088722114877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86329430517984473184612677 16186768222122088722114877)
    ·
      refine ⟨6070038083295783270793079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16186768222122088722114877 6070038083295783270793079)
      ·
        refine ⟨9105057124943674906189619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6070038083295783270793079 9105057124943674906189619)
        ·
          refine ⟨13657585687415512359284429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105057124943674906189619 13657585687415512359284429)
          ·
            refine ⟨5121594632780817134731661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13657585687415512359284429 5121594632780817134731661)
            ·
              refine ⟨1920597987292806425524373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5121594632780817134731661 1920597987292806425524373)
              ·
                refine ⟨90028030654350301196455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1920597987292806425524373 90028030654350301196455)
                ·
                  rfl

theorem cell22_2366941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 6].length) (baseStart_2366941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366941 prefixEnd_2366941 := by exact prefixLift 2366941
  have htrace : WordTrace (prefixWord ++ tailWord_2366941) baseStart_2366941 baseEnd_2366941 := by
    simpa [prefixWord, tailWord_2366941, baseEnd_2366941] using wordTrace_append hprefix tailTrace_2366941
  have hstable : (prefixWord ++ tailWord_2366941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366941).length < 2 ^ (prefixWord ++ tailWord_2366941).sum := by decide
  have hdescent : baseEnd_2366941 < baseStart_2366941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366973 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_2366973 : Nat := 118140960795 + 2366973 * 2 ^ 59
def prefixEnd_2366973 : Nat := 4983230072969 + 3 ^ 40 * 2366973 * 2
def baseEnd_2366973 : Nat := 810263230143115293967997

theorem tailTrace_2366973 : CollatzResearch.WordTrace tailWord_2366973 prefixEnd_2366973 810263230143115293967997 := by
  unfold tailWord_2366973
  simp only [CollatzResearch.WordTrace]
  refine ⟨86330597653868542649777573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57553731769245695099851715 86330597653868542649777573)
  ·
    refine ⟨16186987060100351746833295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86330597653868542649777573 16186987060100351746833295)
    ·
      refine ⟨24280480590150527620249943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16186987060100351746833295 24280480590150527620249943)
      ·
        refine ⟨36420720885225791430374915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24280480590150527620249943 36420720885225791430374915)
        ·
          refine ⟨54631081327838687145562373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36420720885225791430374915 54631081327838687145562373)
          ·
            refine ⟨10243327748969753839792945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54631081327838687145562373 10243327748969753839792945)
            ·
              refine ⟨7682495811727315379844709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10243327748969753839792945 7682495811727315379844709)
              ·
                refine ⟨1440467964698871633720883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7682495811727315379844709 1440467964698871633720883)
                ·
                  refine ⟨2160701947048307450581325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440467964698871633720883 2160701947048307450581325)
                  ·
                    refine ⟨810263230143115293967997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2160701947048307450581325 810263230143115293967997)
                    ·
                      rfl

theorem cell22_2366973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_2366973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366973 prefixEnd_2366973 := by exact prefixLift 2366973
  have htrace : WordTrace (prefixWord ++ tailWord_2366973) baseStart_2366973 baseEnd_2366973 := by
    simpa [prefixWord, tailWord_2366973, baseEnd_2366973] using wordTrace_append hprefix tailTrace_2366973
  have hstable : (prefixWord ++ tailWord_2366973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366973).length < 2 ^ (prefixWord ++ tailWord_2366973).sum := by decide
  have hdescent : baseEnd_2366973 < baseStart_2366973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366984 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2366984 : Nat := 118140960795 + 2366984 * 2 ^ 59
def prefixEnd_2366984 : Nat := 4983230072969 + 3 ^ 40 * 2366984 * 2
def baseEnd_2366984 : Nat := 810266995667914931942963

theorem tailTrace_2366984 : CollatzResearch.WordTrace tailWord_2366984 prefixEnd_2366984 810266995667914931942963 := by
  unfold tailWord_2366984
  simp only [CollatzResearch.WordTrace]
  refine ⟨43165499428414345764214003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57553999237885794352285337 43165499428414345764214003)
  ·
    refine ⟨64748249142621518646321005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43165499428414345764214003 64748249142621518646321005)
    ·
      refine ⟨24280593428483069492370377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64748249142621518646321005 24280593428483069492370377)
      ·
        refine ⟨18210445071362302119277783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24280593428483069492370377 18210445071362302119277783)
        ·
          refine ⟨27315667607043453178916675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18210445071362302119277783 27315667607043453178916675)
          ·
            refine ⟨40973501410565179768375013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27315667607043453178916675 40973501410565179768375013)
            ·
              refine ⟨7682531514480971206570315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40973501410565179768375013 7682531514480971206570315)
              ·
                refine ⟨11523797271721456809855473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7682531514480971206570315 11523797271721456809855473)
                ·
                  refine ⟨8642847953791092607391605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11523797271721456809855473 8642847953791092607391605)
                  ·
                    refine ⟨810266995667914931942963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8642847953791092607391605 810266995667914931942963)
                    ·
                      rfl

theorem cell22_2366984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2366984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2366984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2366984 prefixEnd_2366984 := by exact prefixLift 2366984
  have htrace : WordTrace (prefixWord ++ tailWord_2366984) baseStart_2366984 baseEnd_2366984 := by
    simpa [prefixWord, tailWord_2366984, baseEnd_2366984] using wordTrace_append hprefix tailTrace_2366984
  have hstable : (prefixWord ++ tailWord_2366984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366984).length < 2 ^ (prefixWord ++ tailWord_2366984).sum := by decide
  have hdescent : baseEnd_2366984 < baseStart_2366984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367031 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 6]
def baseStart_2367031 : Nat := 118140960795 + 2367031 * 2 ^ 59
def prefixEnd_2367031 : Nat := 4983230072969 + 3 ^ 40 * 2367031 * 2
def baseEnd_2367031 : Nat := 270094361576140825339273

theorem tailTrace_2367031 : CollatzResearch.WordTrace tailWord_2367031 prefixEnd_2367031 270094361576140825339273 := by
  unfold tailWord_2367031
  simp only [CollatzResearch.WordTrace]
  refine ⟨86332713087658418555388947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57555142058438945703592631 86332713087658418555388947)
  ·
    refine ⟨129499069631487627833083421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86332713087658418555388947 129499069631487627833083421)
    ·
      refine ⟨48562151111807860437406283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129499069631487627833083421 48562151111807860437406283)
      ·
        refine ⟨72843226667711790656109425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48562151111807860437406283 72843226667711790656109425)
        ·
          refine ⟨54632420000783842992082069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72843226667711790656109425 54632420000783842992082069)
          ·
            refine ⟨2560894687536742640253847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54632420000783842992082069 2560894687536742640253847)
            ·
              refine ⟨3841342031305113960380771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560894687536742640253847 3841342031305113960380771)
              ·
                refine ⟨5762013046957670940571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841342031305113960380771 5762013046957670940571157)
                ·
                  refine ⟨270094361576140825339273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5762013046957670940571157 270094361576140825339273)
                  ·
                    rfl

theorem cell22_2367031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 6].length) (baseStart_2367031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367031 prefixEnd_2367031 := by exact prefixLift 2367031
  have htrace : WordTrace (prefixWord ++ tailWord_2367031) baseStart_2367031 baseEnd_2367031 := by
    simpa [prefixWord, tailWord_2367031, baseEnd_2367031] using wordTrace_append hprefix tailTrace_2367031
  have hstable : (prefixWord ++ tailWord_2367031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367031).length < 2 ^ (prefixWord ++ tailWord_2367031).sum := by decide
  have hdescent : baseEnd_2367031 < baseStart_2367031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367080 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2367080 : Nat := 118140960795 + 2367080 * 2 ^ 59
def prefixEnd_2367080 : Nat := 4983230072969 + 3 ^ 40 * 2367080 * 2
def baseEnd_2367080 : Nat := 810299858429802681542669

theorem tailTrace_2367080 : CollatzResearch.WordTrace tailWord_2367080 prefixEnd_2367080 810299858429802681542669 := by
  unfold tailWord_2367080
  simp only [CollatzResearch.WordTrace]
  refine ⟨43167250132240449961961347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57556333509653933282615129 43167250132240449961961347)
  ·
    refine ⟨64750875198360674942942021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43167250132240449961961347 64750875198360674942942021)
    ·
      refine ⟨12140789099692626551801629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64750875198360674942942021 12140789099692626551801629)
      ·
        refine ⟨4552795912384734956925611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12140789099692626551801629 4552795912384734956925611)
        ·
          refine ⟨6829193868577102435388417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552795912384734956925611 6829193868577102435388417)
          ·
            refine ⟨5121895401432826826541313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6829193868577102435388417 5121895401432826826541313)
            ·
              refine ⟨3841421551074620119905985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5121895401432826826541313 3841421551074620119905985)
              ·
                refine ⟨2881066163305965089929489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841421551074620119905985 2881066163305965089929489)
                ·
                  refine ⟨2160799622479473817447117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881066163305965089929489 2160799622479473817447117)
                  ·
                    refine ⟨810299858429802681542669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2160799622479473817447117 810299858429802681542669)
                    ·
                      rfl

theorem cell22_2367080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2367080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367080 prefixEnd_2367080 := by exact prefixLift 2367080
  have htrace : WordTrace (prefixWord ++ tailWord_2367080) baseStart_2367080 baseEnd_2367080 := by
    simpa [prefixWord, tailWord_2367080, baseEnd_2367080] using wordTrace_append hprefix tailTrace_2367080
  have hstable : (prefixWord ++ tailWord_2367080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367080).length < 2 ^ (prefixWord ++ tailWord_2367080).sum := by decide
  have hdescent : baseEnd_2367080 < baseStart_2367080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367093 : List Nat := [1, 3, 4, 2, 1, 3, 1, 7]
def baseStart_2367093 : Nat := 118140960795 + 2367093 * 2 ^ 59
def prefixEnd_2367093 : Nat := 4983230072969 + 3 ^ 40 * 2367093 * 2
def baseEnd_2367093 : Nat := 90033812066163886774181

theorem tailTrace_2367093 : CollatzResearch.WordTrace tailWord_2367093 prefixEnd_2367093 90033812066163886774181 := by
  unfold tailWord_2367093
  simp only [CollatzResearch.WordTrace]
  refine ⟨86334974413433803144145933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57556649608955868762763955 86334974413433803144145933)
  ·
    refine ⟨32375615405037676179054725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86334974413433803144145933 32375615405037676179054725)
    ·
      refine ⟨6070427888444564283572761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32375615405037676179054725 6070427888444564283572761)
      ·
        refine ⟨4552820916333423212679571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6070427888444564283572761 4552820916333423212679571)
        ·
          refine ⟨6829231374500134819019357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552820916333423212679571 6829231374500134819019357)
          ·
            refine ⟨2560961765437550557132259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6829231374500134819019357 2560961765437550557132259)
            ·
              refine ⟨3841442648156325835698389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560961765437550557132259 3841442648156325835698389)
              ·
                refine ⟨90033812066163886774181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3841442648156325835698389 90033812066163886774181)
                ·
                  rfl

theorem cell22_2367093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 7].length) (baseStart_2367093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367093 prefixEnd_2367093 := by exact prefixLift 2367093
  have htrace : WordTrace (prefixWord ++ tailWord_2367093) baseStart_2367093 baseEnd_2367093 := by
    simpa [prefixWord, tailWord_2367093, baseEnd_2367093] using wordTrace_append hprefix tailTrace_2367093
  have hstable : (prefixWord ++ tailWord_2367093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367093).length < 2 ^ (prefixWord ++ tailWord_2367093).sum := by decide
  have hdescent : baseEnd_2367093 < baseStart_2367093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367112 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_2367112 : Nat := 118140960795 + 2367112 * 2 ^ 59
def prefixEnd_2367112 : Nat := 4983230072969 + 3 ^ 40 * 2367112 * 2
def baseEnd_2367112 : Nat := 810310812683765264742571

theorem tailTrace_2367112 : CollatzResearch.WordTrace tailWord_2367112 prefixEnd_2367112 810310812683765264742571 := by
  unfold tailWord_2367112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43167833700182484694543795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57557111600243312926058393 43167833700182484694543795)
  ·
    refine ⟨64751750550273727041815693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43167833700182484694543795 64751750550273727041815693)
    ·
      refine ⟨24281906456352647640680885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64751750550273727041815693 24281906456352647640680885)
      ·
        refine ⟨2276428730283060716313833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24281906456352647640680885 2276428730283060716313833)
        ·
          refine ⟨1707321547712295537235375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276428730283060716313833 1707321547712295537235375)
          ·
            refine ⟨2560982321568443305853063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707321547712295537235375 2560982321568443305853063)
            ·
              refine ⟨3841473482352664958779595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560982321568443305853063 3841473482352664958779595)
              ·
                refine ⟨5762210223528997438169393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841473482352664958779595 5762210223528997438169393)
                ·
                  refine ⟨4321657667646748078627045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5762210223528997438169393 4321657667646748078627045)
                  ·
                    refine ⟨810310812683765264742571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4321657667646748078627045 810310812683765264742571)
                    ·
                      rfl

theorem cell22_2367112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_2367112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367112 prefixEnd_2367112 := by exact prefixLift 2367112
  have htrace : WordTrace (prefixWord ++ tailWord_2367112) baseStart_2367112 baseEnd_2367112 := by
    simpa [prefixWord, tailWord_2367112, baseEnd_2367112] using wordTrace_append hprefix tailTrace_2367112
  have hstable : (prefixWord ++ tailWord_2367112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367112).length < 2 ^ (prefixWord ++ tailWord_2367112).sum := by decide
  have hdescent : baseEnd_2367112 < baseStart_2367112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367119 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2367119 : Nat := 118140960795 + 2367119 * 2 ^ 59
def prefixEnd_2367119 : Nat := 4983230072969 + 3 ^ 40 * 2367119 * 2
def baseEnd_2367119 : Nat := 810313208926819579817549

theorem tailTrace_2367119 : CollatzResearch.WordTrace tailWord_2367119 prefixEnd_2367119 810313208926819579817549 := by
  unfold tailWord_2367119
  simp only [CollatzResearch.WordTrace]
  refine ⟨86335922711339609584592411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57557281807559739723061607 86335922711339609584592411)
  ·
    refine ⟨129503884067009414376888617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86335922711339609584592411 129503884067009414376888617)
    ·
      refine ⟨97127913050257060782666463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129503884067009414376888617 97127913050257060782666463)
      ·
        refine ⟨145691869575385591173999695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97127913050257060782666463 145691869575385591173999695)
        ·
          refine ⟨218537804363078386760999543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145691869575385591173999695 218537804363078386760999543)
          ·
            refine ⟨327806706544617580141499315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218537804363078386760999543 327806706544617580141499315)
            ·
              refine ⟨491710059816926370212248973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327806706544617580141499315 491710059816926370212248973)
              ·
                refine ⟨184391272431347388829593365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491710059816926370212248973 184391272431347388829593365)
                ·
                  refine ⟨8643340895219408851387189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184391272431347388829593365 8643340895219408851387189)
                  ·
                    refine ⟨810313208926819579817549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8643340895219408851387189 810313208926819579817549)
                    ·
                      rfl

theorem cell22_2367119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2367119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367119 prefixEnd_2367119 := by exact prefixLift 2367119
  have htrace : WordTrace (prefixWord ++ tailWord_2367119) baseStart_2367119 baseEnd_2367119 := by
    simpa [prefixWord, tailWord_2367119, baseEnd_2367119] using wordTrace_append hprefix tailTrace_2367119
  have hstable : (prefixWord ++ tailWord_2367119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367119).length < 2 ^ (prefixWord ++ tailWord_2367119).sum := by decide
  have hdescent : baseEnd_2367119 < baseStart_2367119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367136 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_2367136 : Nat := 118140960795 + 2367136 * 2 ^ 59
def prefixEnd_2367136 : Nat := 4983230072969 + 3 ^ 40 * 2367136 * 2
def baseEnd_2367136 : Nat := 810319028374237202142497

theorem tailTrace_2367136 : CollatzResearch.WordTrace tailWord_2367136 prefixEnd_2367136 810319028374237202142497 := by
  unfold tailWord_2367136
  simp only [CollatzResearch.WordTrace]
  refine ⟨43168271376139010743980631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57557695168185347658640841 43168271376139010743980631)
  ·
    refine ⟨64752407064208516115970947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43168271376139010743980631 64752407064208516115970947)
    ·
      refine ⟨97128610596312774173956421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64752407064208516115970947 97128610596312774173956421)
      ·
        refine ⟨18211614486808645157616829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97128610596312774173956421 18211614486808645157616829)
        ·
          refine ⟨6829355432553241934106311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18211614486808645157616829 6829355432553241934106311)
          ·
            refine ⟨10244033148829862901159467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6829355432553241934106311 10244033148829862901159467)
            ·
              refine ⟨15366049723244794351739201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10244033148829862901159467 15366049723244794351739201)
              ·
                refine ⟨11524537292433595763804401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15366049723244794351739201 11524537292433595763804401)
                ·
                  refine ⟨8643402969325196822853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11524537292433595763804401 8643402969325196822853301)
                  ·
                    refine ⟨810319028374237202142497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8643402969325196822853301 810319028374237202142497)
                    ·
                      rfl

theorem cell22_2367136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_2367136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367136 prefixEnd_2367136 := by exact prefixLift 2367136
  have htrace : WordTrace (prefixWord ++ tailWord_2367136) baseStart_2367136 baseEnd_2367136 := by
    simpa [prefixWord, tailWord_2367136, baseEnd_2367136] using wordTrace_append hprefix tailTrace_2367136
  have hstable : (prefixWord ++ tailWord_2367136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367136).length < 2 ^ (prefixWord ++ tailWord_2367136).sum := by decide
  have hdescent : baseEnd_2367136 < baseStart_2367136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367168 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_2367168 : Nat := 118140960795 + 2367168 * 2 ^ 59
def prefixEnd_2367168 : Nat := 4983230072969 + 3 ^ 40 * 2367168 * 2
def baseEnd_2367168 : Nat := 810329982628199785342399

theorem tailTrace_2367168 : CollatzResearch.WordTrace tailWord_2367168 prefixEnd_2367168 810329982628199785342399 := by
  unfold tailWord_2367168
  simp only [CollatzResearch.WordTrace]
  refine ⟨43168854944081045476563079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57558473258774727302084105 43168854944081045476563079)
  ·
    refine ⟨64753282416121568214844619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43168854944081045476563079 64753282416121568214844619)
    ·
      refine ⟨97129923624182352322266929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64753282416121568214844619 97129923624182352322266929)
      ·
        refine ⟨72847442718136764241700197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97129923624182352322266929 72847442718136764241700197)
        ·
          refine ⟨13658895509650643295318787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72847442718136764241700197 13658895509650643295318787)
          ·
            refine ⟨20488343264475964942978181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13658895509650643295318787 20488343264475964942978181)
            ·
              refine ⟨3841564362089243426808409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20488343264475964942978181 3841564362089243426808409)
              ·
                refine ⟨2881173271566932570106307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841564362089243426808409 2881173271566932570106307)
                ·
                  refine ⟨4321759907350398855159461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881173271566932570106307 4321759907350398855159461)
                  ·
                    refine ⟨810329982628199785342399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4321759907350398855159461 810329982628199785342399)
                    ·
                      rfl

theorem cell22_2367168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_2367168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367168 prefixEnd_2367168 := by exact prefixLift 2367168
  have htrace : WordTrace (prefixWord ++ tailWord_2367168) baseStart_2367168 baseEnd_2367168 := by
    simpa [prefixWord, tailWord_2367168, baseEnd_2367168] using wordTrace_append hprefix tailTrace_2367168
  have hstable : (prefixWord ++ tailWord_2367168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367168).length < 2 ^ (prefixWord ++ tailWord_2367168).sum := by decide
  have hdescent : baseEnd_2367168 < baseStart_2367168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367256 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_2367256 : Nat := 118140960795 + 2367256 * 2 ^ 59
def prefixEnd_2367256 : Nat := 4983230072969 + 3 ^ 40 * 2367256 * 2
def baseEnd_2367256 : Nat := 270120035608865629714043

theorem tailTrace_2367256 : CollatzResearch.WordTrace tailWord_2367256 prefixEnd_2367256 270120035608865629714043 := by
  unfold tailWord_2367256
  simp only [CollatzResearch.WordTrace]
  refine ⟨43170459755921640991164811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57560613007895521321553081 43170459755921640991164811)
  ·
    refine ⟨64755689633882461486747217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43170459755921640991164811 64755689633882461486747217)
    ·
      refine ⟨48566767225411846115060413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64755689633882461486747217 48566767225411846115060413)
      ·
        refine ⟨18212537709529442293147655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48566767225411846115060413 18212537709529442293147655)
        ·
          refine ⟨27318806564294163439721483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18212537709529442293147655 27318806564294163439721483)
          ·
            refine ⟨40978209846441245159582225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27318806564294163439721483 40978209846441245159582225)
            ·
              refine ⟨30733657384830933869686669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40978209846441245159582225 30733657384830933869686669)
              ·
                refine ⟨11525121519311600201132501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30733657384830933869686669 11525121519311600201132501)
                ·
                  refine ⟨270120035608865629714043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11525121519311600201132501 270120035608865629714043)
                  ·
                    rfl

theorem cell22_2367256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_2367256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367256 prefixEnd_2367256 := by exact prefixLift 2367256
  have htrace : WordTrace (prefixWord ++ tailWord_2367256) baseStart_2367256 baseEnd_2367256 := by
    simpa [prefixWord, tailWord_2367256, baseEnd_2367256] using wordTrace_append hprefix tailTrace_2367256
  have hstable : (prefixWord ++ tailWord_2367256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367256).length < 2 ^ (prefixWord ++ tailWord_2367256).sum := by decide
  have hdescent : baseEnd_2367256 < baseStart_2367256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367294 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_2367294 : Nat := 118140960795 + 2367294 * 2 ^ 59
def prefixEnd_2367294 : Nat := 4983230072969 + 3 ^ 40 * 2367294 * 2
def baseEnd_2367294 : Nat := 810373115003177456692013

theorem tailTrace_2367294 : CollatzResearch.WordTrace tailWord_2367294 prefixEnd_2367294 810373115003177456692013 := by
  unfold tailWord_2367294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10792788185713201809026617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57561536990470409648141957 10792788185713201809026617)
  ·
    refine ⟨8094591139284901356769963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10792788185713201809026617 8094591139284901356769963)
    ·
      refine ⟨12141886708927352035154945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8094591139284901356769963 12141886708927352035154945)
      ·
        refine ⟨9106415031695514026366209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12141886708927352035154945 9106415031695514026366209)
        ·
          refine ⟨6829811273771635519774657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9106415031695514026366209 6829811273771635519774657)
          ·
            refine ⟨5122358455328726639830993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6829811273771635519774657 5122358455328726639830993)
            ·
              refine ⟨3841768841496544979873245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5122358455328726639830993 3841768841496544979873245)
              ·
                refine ⟨1440663315561204367452467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3841768841496544979873245 1440663315561204367452467)
                ·
                  refine ⟨2160994973341806551178701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440663315561204367452467 2160994973341806551178701)
                  ·
                    refine ⟨810373115003177456692013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2160994973341806551178701 810373115003177456692013)
                    ·
                      rfl

theorem cell22_2367294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_2367294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367294 prefixEnd_2367294 := by exact prefixLift 2367294
  have htrace : WordTrace (prefixWord ++ tailWord_2367294) baseStart_2367294 baseEnd_2367294 := by
    simpa [prefixWord, tailWord_2367294, baseEnd_2367294] using wordTrace_append hprefix tailTrace_2367294
  have hstable : (prefixWord ++ tailWord_2367294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367294).length < 2 ^ (prefixWord ++ tailWord_2367294).sum := by decide
  have hdescent : baseEnd_2367294 < baseStart_2367294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367301 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 8]
def baseStart_2367301 : Nat := 118140960795 + 2367301 * 2 ^ 59
def prefixEnd_2367301 : Nat := 4983230072969 + 3 ^ 40 * 2367301 * 2
def baseEnd_2367301 : Nat := 270125170415410590588997

theorem tailTrace_2367301 : CollatzResearch.WordTrace tailWord_2367301 prefixEnd_2367301 270125170415410590588997 := by
  unfold tailWord_2367301
  simp only [CollatzResearch.WordTrace]
  refine ⟨86342560796680254667717757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57561707197786836445145171 86342560796680254667717757)
  ·
    refine ⟨32378460298755095500394159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86342560796680254667717757 32378460298755095500394159)
    ·
      refine ⟨48567690448132643250591239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32378460298755095500394159 48567690448132643250591239)
      ·
        refine ⟨72851535672198964875886859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48567690448132643250591239 72851535672198964875886859)
        ·
          refine ⟨109277303508298447313830289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72851535672198964875886859 109277303508298447313830289)
          ·
            refine ⟨81957977631223835485372717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109277303508298447313830289 81957977631223835485372717)
            ·
              refine ⟨30734241611708938307014769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81957977631223835485372717 30734241611708938307014769)
              ·
                refine ⟨23050681208781703730261077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30734241611708938307014769 23050681208781703730261077)
                ·
                  refine ⟨270125170415410590588997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23050681208781703730261077 270125170415410590588997)
                  ·
                    rfl

theorem cell22_2367301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_2367301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367301 prefixEnd_2367301 := by exact prefixLift 2367301
  have htrace : WordTrace (prefixWord ++ tailWord_2367301) baseStart_2367301 baseEnd_2367301 := by
    simpa [prefixWord, tailWord_2367301, baseEnd_2367301] using wordTrace_append hprefix tailTrace_2367301
  have hstable : (prefixWord ++ tailWord_2367301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367301).length < 2 ^ (prefixWord ++ tailWord_2367301).sum := by decide
  have hdescent : baseEnd_2367301 < baseStart_2367301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367363 : List Nat := [1, 1, 1, 3, 4, 4, 8]
def baseStart_2367363 : Nat := 118140960795 + 2367363 * 2 ^ 59
def prefixEnd_2367363 : Nat := 4983230072969 + 3 ^ 40 * 2367363 * 2
def baseEnd_2367363 : Nat := 30014693893084602841363

theorem tailTrace_2367363 : CollatzResearch.WordTrace tailWord_2367363 prefixEnd_2367363 30014693893084602841363 := by
  unfold tailWord_2367363
  simp only [CollatzResearch.WordTrace]
  refine ⟨86344822122455639256474743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57563214748303759504316495 86344822122455639256474743)
  ·
    refine ⟨129517233183683458884712115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86344822122455639256474743 129517233183683458884712115)
    ·
      refine ⟨194275849775525188327068173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129517233183683458884712115 194275849775525188327068173)
      ·
        refine ⟨72853443665821945622650565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194275849775525188327068173 72853443665821945622650565)
        ·
          refine ⟨13660020687341614804246981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72853443665821945622650565 13660020687341614804246981)
          ·
            refine ⟨2561253878876552775796309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13660020687341614804246981 2561253878876552775796309)
            ·
              refine ⟨30014693893084602841363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2561253878876552775796309 30014693893084602841363)
              ·
                rfl

theorem cell22_2367363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 8].length) (baseStart_2367363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367363 prefixEnd_2367363 := by exact prefixLift 2367363
  have htrace : WordTrace (prefixWord ++ tailWord_2367363) baseStart_2367363 baseEnd_2367363 := by
    simpa [prefixWord, tailWord_2367363, baseEnd_2367363] using wordTrace_append hprefix tailTrace_2367363
  have hstable : (prefixWord ++ tailWord_2367363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367363).length < 2 ^ (prefixWord ++ tailWord_2367363).sum := by decide
  have hdescent : baseEnd_2367363 < baseStart_2367363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367380 : List Nat := [2, 4, 2, 1, 1, 3, 2, 7]
def baseStart_2367380 : Nat := 118140960795 + 2367380 * 2 ^ 59
def prefixEnd_2367380 : Nat := 4983230072969 + 3 ^ 40 * 2367380 * 2
def baseEnd_2367380 : Nat := 90044728284522433226861

theorem tailTrace_2367380 : CollatzResearch.WordTrace tailWord_2367380 prefixEnd_2367380 90044728284522433226861 := by
  unfold tailWord_2367380
  simp only [CollatzResearch.WordTrace]
  refine ⟨43172721081697025579921797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57563628108929367439895729 43172721081697025579921797)
  ·
    refine ⟨8094885202818192296235337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43172721081697025579921797 8094885202818192296235337)
    ·
      refine ⟨6071163902113644222176503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8094885202818192296235337 6071163902113644222176503)
      ·
        refine ⟨9106745853170466333264755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6071163902113644222176503 9106745853170466333264755)
        ·
          refine ⟨13660118779755699499897133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106745853170466333264755 13660118779755699499897133)
          ·
            refine ⟨5122544542408387312461425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13660118779755699499897133 5122544542408387312461425)
            ·
              refine ⟨3841908406806290484346069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5122544542408387312461425 3841908406806290484346069)
              ·
                refine ⟨90044728284522433226861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3841908406806290484346069 90044728284522433226861)
                ·
                  rfl

theorem cell22_2367380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_2367380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367380 prefixEnd_2367380 := by exact prefixLift 2367380
  have htrace : WordTrace (prefixWord ++ tailWord_2367380) baseStart_2367380 baseEnd_2367380 := by
    simpa [prefixWord, tailWord_2367380, baseEnd_2367380] using wordTrace_append hprefix tailTrace_2367380
  have hstable : (prefixWord ++ tailWord_2367380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367380).length < 2 ^ (prefixWord ++ tailWord_2367380).sum := by decide
  have hdescent : baseEnd_2367380 < baseStart_2367380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367384 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_2367384 : Nat := 118140960795 + 2367384 * 2 ^ 59
def prefixEnd_2367384 : Nat := 4983230072969 + 3 ^ 40 * 2367384 * 2
def baseEnd_2367384 : Nat := 810403923842447221941737

theorem tailTrace_2367384 : CollatzResearch.WordTrace tailWord_2367384 prefixEnd_2367384 810403923842447221941737 := by
  unfold tailWord_2367384
  simp only [CollatzResearch.WordTrace]
  refine ⟨43172794027689779921494603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57563725370253039895326137 43172794027689779921494603)
  ·
    refine ⟨64759191041534669882241905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43172794027689779921494603 64759191041534669882241905)
    ·
      refine ⟨48569393281151002411681429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64759191041534669882241905 48569393281151002411681429)
      ·
        refine ⟨2276690310053953238047567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48569393281151002411681429 2276690310053953238047567)
        ·
          refine ⟨3415035465080929857071351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276690310053953238047567 3415035465080929857071351)
          ·
            refine ⟨5122553197621394785607027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415035465080929857071351 5122553197621394785607027)
            ·
              refine ⟨7683829796432092178410541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122553197621394785607027 7683829796432092178410541)
              ·
                refine ⟨2881436173662034566903953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7683829796432092178410541 2881436173662034566903953)
                ·
                  refine ⟨2161077130246525925177965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881436173662034566903953 2161077130246525925177965)
                  ·
                    refine ⟨810403923842447221941737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161077130246525925177965 810403923842447221941737)
                    ·
                      rfl

theorem cell22_2367384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_2367384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367384 prefixEnd_2367384 := by exact prefixLift 2367384
  have htrace : WordTrace (prefixWord ++ tailWord_2367384) baseStart_2367384 baseEnd_2367384 := by
    simpa [prefixWord, tailWord_2367384, baseEnd_2367384] using wordTrace_append hprefix tailTrace_2367384
  have hstable : (prefixWord ++ tailWord_2367384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367384).length < 2 ^ (prefixWord ++ tailWord_2367384).sum := by decide
  have hdescent : baseEnd_2367384 < baseStart_2367384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367423 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_2367423 : Nat := 118140960795 + 2367423 * 2 ^ 59
def prefixEnd_2367423 : Nat := 4983230072969 + 3 ^ 40 * 2367423 * 2
def baseEnd_2367423 : Nat := 810417274339464120216617

theorem tailTrace_2367423 : CollatzResearch.WordTrace tailWord_2367423 prefixEnd_2367423 810417274339464120216617 := by
  unfold tailWord_2367423
  simp only [CollatzResearch.WordTrace]
  refine ⟨86347010502238269503658923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57564673668158846335772615 86347010502238269503658923)
  ·
    refine ⟨129520515753357404255488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86347010502238269503658923 129520515753357404255488385)
    ·
      refine ⟨97140386815018053191616289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129520515753357404255488385 97140386815018053191616289)
      ·
        refine ⟨72855290111263539893712217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97140386815018053191616289 72855290111263539893712217)
        ·
          refine ⟨54641467583447654920284163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72855290111263539893712217 54641467583447654920284163)
          ·
            refine ⟨81962201375171482380426245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54641467583447654920284163 81962201375171482380426245)
            ·
              refine ⟨15367912757844652946329921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81962201375171482380426245 15367912757844652946329921)
              ·
                refine ⟨11525934568383489709747441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15367912757844652946329921 11525934568383489709747441)
                ·
                  refine ⟨8644450926287617282310581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11525934568383489709747441 8644450926287617282310581)
                  ·
                    refine ⟨810417274339464120216617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8644450926287617282310581 810417274339464120216617)
                    ·
                      rfl

theorem cell22_2367423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_2367423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367423 prefixEnd_2367423 := by exact prefixLift 2367423
  have htrace : WordTrace (prefixWord ++ tailWord_2367423) baseStart_2367423 baseEnd_2367423 := by
    simpa [prefixWord, tailWord_2367423, baseEnd_2367423] using wordTrace_append hprefix tailTrace_2367423
  have hstable : (prefixWord ++ tailWord_2367423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367423).length < 2 ^ (prefixWord ++ tailWord_2367423).sum := by decide
  have hdescent : baseEnd_2367423 < baseStart_2367423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367455 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_2367455 : Nat := 118140960795 + 2367455 * 2 ^ 59
def prefixEnd_2367455 : Nat := 4983230072969 + 3 ^ 40 * 2367455 * 2
def baseEnd_2367455 : Nat := 810428228593426703416519

theorem tailTrace_2367455 : CollatzResearch.WordTrace tailWord_2367455 prefixEnd_2367455 810428228593426703416519 := by
  unfold tailWord_2367455
  simp only [CollatzResearch.WordTrace]
  refine ⟨86348177638122338968823819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57565451758748225979215879 86348177638122338968823819)
  ·
    refine ⟨129522266457183508453235729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86348177638122338968823819 129522266457183508453235729)
    ·
      refine ⟨97141699842887631339926797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129522266457183508453235729 97141699842887631339926797)
      ·
        refine ⟨36428137441082861752472549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97141699842887631339926797 36428137441082861752472549)
        ·
          refine ⟨6830275770203036578588603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36428137441082861752472549 6830275770203036578588603)
          ·
            refine ⟨10245413655304554867882905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6830275770203036578588603 10245413655304554867882905)
            ·
              refine ⟨7684060241478416150912179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10245413655304554867882905 7684060241478416150912179)
              ·
                refine ⟨11526090362217624226368269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7684060241478416150912179 11526090362217624226368269)
                ·
                  refine ⟨4322283885831609084888101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11526090362217624226368269 4322283885831609084888101)
                  ·
                    refine ⟨810428228593426703416519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4322283885831609084888101 810428228593426703416519)
                    ·
                      rfl

theorem cell22_2367455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_2367455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367455 prefixEnd_2367455 := by exact prefixLift 2367455
  have htrace : WordTrace (prefixWord ++ tailWord_2367455) baseStart_2367455 baseEnd_2367455 := by
    simpa [prefixWord, tailWord_2367455, baseEnd_2367455] using wordTrace_append hprefix tailTrace_2367455
  have hstable : (prefixWord ++ tailWord_2367455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367455).length < 2 ^ (prefixWord ++ tailWord_2367455).sum := by decide
  have hdescent : baseEnd_2367455 < baseStart_2367455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367472 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_2367472 : Nat := 118140960795 + 2367472 * 2 ^ 59
def prefixEnd_2367472 : Nat := 4983230072969 + 3 ^ 40 * 2367472 * 2
def baseEnd_2367472 : Nat := 810434048040844325741467

theorem tailTrace_2367472 : CollatzResearch.WordTrace tailWord_2367472 prefixEnd_2367472 810434048040844325741467 := by
  unfold tailWord_2367472
  simp only [CollatzResearch.WordTrace]
  refine ⟨43174398839530375436096335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57565865119373833914795113 43174398839530375436096335)
  ·
    refine ⟨64761598259295563154144503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43174398839530375436096335 64761598259295563154144503)
    ·
      refine ⟨97142397388943344731216755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64761598259295563154144503 97142397388943344731216755)
      ·
        refine ⟨145713596083415017096825133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97142397388943344731216755 145713596083415017096825133)
        ·
          refine ⟨54642598531280631411309425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145713596083415017096825133 54642598531280631411309425)
          ·
            refine ⟨40981948898460473558482069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54642598531280631411309425 40981948898460473558482069)
            ·
              refine ⟨1921028854615334698053847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40981948898460473558482069 1921028854615334698053847)
              ·
                refine ⟨2881543281923002047080771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921028854615334698053847 2881543281923002047080771)
                ·
                  refine ⟨4322314922884503070621157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881543281923002047080771 4322314922884503070621157)
                  ·
                    refine ⟨810434048040844325741467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4322314922884503070621157 810434048040844325741467)
                    ·
                      rfl

theorem cell22_2367472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_2367472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367472 prefixEnd_2367472 := by exact prefixLift 2367472
  have htrace : WordTrace (prefixWord ++ tailWord_2367472) baseStart_2367472 baseEnd_2367472 := by
    simpa [prefixWord, tailWord_2367472, baseEnd_2367472] using wordTrace_append hprefix tailTrace_2367472
  have hstable : (prefixWord ++ tailWord_2367472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367472).length < 2 ^ (prefixWord ++ tailWord_2367472).sum := by decide
  have hdescent : baseEnd_2367472 < baseStart_2367472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367513 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_2367513 : Nat := 118140960795 + 2367513 * 2 ^ 59
def prefixEnd_2367513 : Nat := 4983230072969 + 3 ^ 40 * 2367513 * 2
def baseEnd_2367513 : Nat := 810448083178733885466341

theorem tailTrace_2367513 : CollatzResearch.WordTrace tailWord_2367513 prefixEnd_2367513 810448083178733885466341 := by
  unfold tailWord_2367513
  simp only [CollatzResearch.WordTrace]
  refine ⟨86350293071912214874435193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57566862047941476582956795 86350293071912214874435193)
  ·
    refine ⟨64762719803934161155826395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86350293071912214874435193 64762719803934161155826395)
    ·
      refine ⟨97144079705901241733739593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64762719803934161155826395 97144079705901241733739593)
      ·
        refine ⟨72858059779425931300304695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97144079705901241733739593 72858059779425931300304695)
        ·
          refine ⟨109287089669138896950457043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72858059779425931300304695 109287089669138896950457043)
          ·
            refine ⟨163930634503708345425685565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109287089669138896950457043 163930634503708345425685565)
            ·
              refine ⟨61473987938890629534632087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163930634503708345425685565 61473987938890629534632087)
              ·
                refine ⟨92210981908335944301948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61473987938890629534632087 92210981908335944301948131)
                ·
                  refine ⟨138316472862503916452922197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92210981908335944301948131 138316472862503916452922197)
                  ·
                    refine ⟨810448083178733885466341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138316472862503916452922197 810448083178733885466341)
                    ·
                      rfl

theorem cell22_2367513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_2367513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367513 prefixEnd_2367513 := by exact prefixLift 2367513
  have htrace : WordTrace (prefixWord ++ tailWord_2367513) baseStart_2367513 baseEnd_2367513 := by
    simpa [prefixWord, tailWord_2367513, baseEnd_2367513] using wordTrace_append hprefix tailTrace_2367513
  have hstable : (prefixWord ++ tailWord_2367513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367513).length < 2 ^ (prefixWord ++ tailWord_2367513).sum := by decide
  have hdescent : baseEnd_2367513 < baseStart_2367513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367521 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 4]
def baseStart_2367521 : Nat := 118140960795 + 2367521 * 2 ^ 59
def prefixEnd_2367521 : Nat := 4983230072969 + 3 ^ 40 * 2367521 * 2
def baseEnd_2367521 : Nat := 270150273914074843755439

theorem tailTrace_2367521 : CollatzResearch.WordTrace tailWord_2367521 prefixEnd_2367521 270150273914074843755439 := by
  unfold tailWord_2367521
  simp only [CollatzResearch.WordTrace]
  refine ⟨86350584855883232240726417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57567056570588821493817611 86350584855883232240726417)
  ·
    refine ⟨64762938641912424180544813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86350584855883232240726417 64762938641912424180544813)
    ·
      refine ⟨24286101990717159067704305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64762938641912424180544813 24286101990717159067704305)
      ·
        refine ⟨18214576493037869300778229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24286101990717159067704305 18214576493037869300778229)
        ·
          refine ⟨1707616546222300246947959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18214576493037869300778229 1707616546222300246947959)
          ·
            refine ⟨2561424819333450370421939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707616546222300246947959 2561424819333450370421939)
            ·
              refine ⟨3842137229000175555632909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561424819333450370421939 3842137229000175555632909)
              ·
                refine ⟨1440801460875065833362341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3842137229000175555632909 1440801460875065833362341)
                ·
                  refine ⟨270150273914074843755439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440801460875065833362341 270150273914074843755439)
                  ·
                    rfl

theorem cell22_2367521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_2367521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367521 prefixEnd_2367521 := by exact prefixLift 2367521
  have htrace : WordTrace (prefixWord ++ tailWord_2367521) baseStart_2367521 baseEnd_2367521 := by
    simpa [prefixWord, tailWord_2367521, baseEnd_2367521] using wordTrace_append hprefix tailTrace_2367521
  have hstable : (prefixWord ++ tailWord_2367521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367521).length < 2 ^ (prefixWord ++ tailWord_2367521).sum := by decide
  have hdescent : baseEnd_2367521 < baseStart_2367521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367594 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_2367594 : Nat := 118140960795 + 2367594 * 2 ^ 59
def prefixEnd_2367594 : Nat := 4983230072969 + 3 ^ 40 * 2367594 * 2
def baseEnd_2367594 : Nat := 270158603711358891397031

theorem tailTrace_2367594 : CollatzResearch.WordTrace tailWord_2367594 prefixEnd_2367594 270158603711358891397031 := by
  unfold tailWord_2367594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21588311846154691427033459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57568831589745843805422557 21588311846154691427033459)
  ·
    refine ⟨32382467769232037140550189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21588311846154691427033459 32382467769232037140550189)
    ·
      refine ⟨12143425413462013927706321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32382467769232037140550189 12143425413462013927706321)
      ·
        refine ⟨9107569060096510445779741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12143425413462013927706321 9107569060096510445779741)
        ·
          refine ⟨3415338397536191417167403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9107569060096510445779741 3415338397536191417167403)
          ·
            refine ⟨5123007596304287125751105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415338397536191417167403 5123007596304287125751105)
            ·
              refine ⟨3842255697228215344313329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123007596304287125751105 3842255697228215344313329)
              ·
                refine ⟨2881691772921161508234997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842255697228215344313329 2881691772921161508234997)
                ·
                  refine ⟨270158603711358891397031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2881691772921161508234997 270158603711358891397031)
                  ·
                    rfl

theorem cell22_2367594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_2367594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367594 prefixEnd_2367594 := by exact prefixLift 2367594
  have htrace : WordTrace (prefixWord ++ tailWord_2367594) baseStart_2367594 baseEnd_2367594 := by
    simpa [prefixWord, tailWord_2367594, baseEnd_2367594] using wordTrace_append hprefix tailTrace_2367594
  have hstable : (prefixWord ++ tailWord_2367594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367594).length < 2 ^ (prefixWord ++ tailWord_2367594).sum := by decide
  have hdescent : baseEnd_2367594 < baseStart_2367594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367637 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2367637 : Nat := 118140960795 + 2367637 * 2 ^ 59
def prefixEnd_2367637 : Nat := 4983230072969 + 3 ^ 40 * 2367637 * 2
def baseEnd_2367637 : Nat := 810490530912838895365961

theorem tailTrace_2367637 : CollatzResearch.WordTrace tailWord_2367637 prefixEnd_2367637 810490530912838895365961 := by
  unfold tailWord_2367637
  simp only [CollatzResearch.WordTrace]
  refine ⟨86354815723462984051949165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57569877148975322701299443 86354815723462984051949165)
  ·
    refine ⟨32383055896298619019480937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86354815723462984051949165 32383055896298619019480937)
    ·
      refine ⟨24287291922223964264610703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32383055896298619019480937 24287291922223964264610703)
      ·
        refine ⟨36430937883335946396916055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24287291922223964264610703 36430937883335946396916055)
        ·
          refine ⟨54646406825003919595374083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36430937883335946396916055 54646406825003919595374083)
          ·
            refine ⟨81969610237505879393061125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54646406825003919595374083 81969610237505879393061125)
            ·
              refine ⟨15369301919532352386198961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81969610237505879393061125 15369301919532352386198961)
              ·
                refine ⟨11526976439649264289649221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15369301919532352386198961 11526976439649264289649221)
                ·
                  refine ⟨2161308082434237054309229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11526976439649264289649221 2161308082434237054309229)
                  ·
                    refine ⟨810490530912838895365961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161308082434237054309229 810490530912838895365961)
                    ·
                      rfl

theorem cell22_2367637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2367637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367637 prefixEnd_2367637 := by exact prefixLift 2367637
  have htrace : WordTrace (prefixWord ++ tailWord_2367637) baseStart_2367637 baseEnd_2367637 := by
    simpa [prefixWord, tailWord_2367637, baseEnd_2367637] using wordTrace_append hprefix tailTrace_2367637
  have hstable : (prefixWord ++ tailWord_2367637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367637).length < 2 ^ (prefixWord ++ tailWord_2367637).sum := by decide
  have hdescent : baseEnd_2367637 < baseStart_2367637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367671 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 2, 3]
def baseStart_2367671 : Nat := 118140960795 + 2367671 * 2 ^ 59
def prefixEnd_2367671 : Nat := 4983230072969 + 3 ^ 40 * 2367671 * 2
def baseEnd_2367671 : Nat := 810502169807674140015857

theorem tailTrace_2367671 : CollatzResearch.WordTrace tailWord_2367671 prefixEnd_2367671 810502169807674140015857 := by
  unfold tailWord_2367671
  simp only [CollatzResearch.WordTrace]
  refine ⟨86356055805339807858686867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57570703870226538572457911 86356055805339807858686867)
  ·
    refine ⟨129534083708009711788030301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86356055805339807858686867 129534083708009711788030301)
    ·
      refine ⟨48575281390503641920511363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129534083708009711788030301 48575281390503641920511363)
      ·
        refine ⟨72862922085755462880767045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48575281390503641920511363 72862922085755462880767045)
        ·
          refine ⟨13661797891079149290143821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72862922085755462880767045 13661797891079149290143821)
          ·
            refine ⟨5123174209154680983803933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13661797891079149290143821 5123174209154680983803933)
            ·
              refine ⟨1921190328433005368926475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5123174209154680983803933 1921190328433005368926475)
              ·
                refine ⟨2881785492649508053389713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921190328433005368926475 2881785492649508053389713)
                ·
                  refine ⟨2161339119487131040042285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881785492649508053389713 2161339119487131040042285)
                  ·
                    refine ⟨810502169807674140015857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161339119487131040042285 810502169807674140015857)
                    ·
                      rfl

theorem cell22_2367671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_2367671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367671 prefixEnd_2367671 := by exact prefixLift 2367671
  have htrace : WordTrace (prefixWord ++ tailWord_2367671) baseStart_2367671 baseEnd_2367671 := by
    simpa [prefixWord, tailWord_2367671, baseEnd_2367671] using wordTrace_append hprefix tailTrace_2367671
  have hstable : (prefixWord ++ tailWord_2367671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367671).length < 2 ^ (prefixWord ++ tailWord_2367671).sum := by decide
  have hdescent : baseEnd_2367671 < baseStart_2367671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367684 : List Nat := [2, 3, 3, 1, 2, 1, 4, 6]
def baseStart_2367684 : Nat := 118140960795 + 2367684 * 2 ^ 59
def prefixEnd_2367684 : Nat := 4983230072969 + 3 ^ 40 * 2367684 * 2
def baseEnd_2367684 : Nat := 90056291108149604382313

theorem tailTrace_2367684 : CollatzResearch.WordTrace tailWord_2367684 prefixEnd_2367684 90056291108149604382313 := by
  unfold tailWord_2367684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43178264977146355539455053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57571019969528474052606737 43178264977146355539455053)
  ·
    refine ⟨16191849366429883327295645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43178264977146355539455053 16191849366429883327295645)
    ·
      refine ⟨6071943512411206247735867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16191849366429883327295645 6071943512411206247735867)
      ·
        refine ⟨9107915268616809371603801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6071943512411206247735867 9107915268616809371603801)
        ·
          refine ⟨6830936451462607028702851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9107915268616809371603801 6830936451462607028702851)
          ·
            refine ⟨10246404677193910543054277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6830936451462607028702851 10246404677193910543054277)
            ·
              refine ⟨1921200876973858226822677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10246404677193910543054277 1921200876973858226822677)
              ·
                refine ⟨90056291108149604382313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1921200876973858226822677 90056291108149604382313)
                ·
                  rfl

theorem cell22_2367684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_2367684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367684 prefixEnd_2367684 := by exact prefixLift 2367684
  have htrace : WordTrace (prefixWord ++ tailWord_2367684) baseStart_2367684 baseEnd_2367684 := by
    simpa [prefixWord, tailWord_2367684, baseEnd_2367684] using wordTrace_append hprefix tailTrace_2367684
  have hstable : (prefixWord ++ tailWord_2367684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367684).length < 2 ^ (prefixWord ++ tailWord_2367684).sum := by decide
  have hdescent : baseEnd_2367684 < baseStart_2367684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367695 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 9]
def baseStart_2367695 : Nat := 118140960795 + 2367695 * 2 ^ 59
def prefixEnd_2367695 : Nat := 4983230072969 + 3 ^ 40 * 2367695 * 2
def baseEnd_2367695 : Nat := 270170128499382025805261

theorem tailTrace_2367695 : CollatzResearch.WordTrace tailWord_2367695 prefixEnd_2367695 270170128499382025805261 := by
  unfold tailWord_2367695
  simp only [CollatzResearch.WordTrace]
  refine ⟨86356931157252859957560539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57571287438168573305040359 86356931157252859957560539)
  ·
    refine ⟨129535396735879289936340809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86356931157252859957560539 129535396735879289936340809)
    ·
      refine ⟨97151547551909467452255607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129535396735879289936340809 97151547551909467452255607)
      ·
        refine ⟨145727321327864201178383411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97151547551909467452255607 145727321327864201178383411)
        ·
          refine ⟨218590981991796301767575117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145727321327864201178383411 218590981991796301767575117)
          ·
            refine ⟨81971618246923613162840669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218590981991796301767575117 81971618246923613162840669)
            ·
              refine ⟨30739356842596354936065251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81971618246923613162840669 30739356842596354936065251)
              ·
                refine ⟨46109035263894532404097877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30739356842596354936065251 46109035263894532404097877)
                ·
                  refine ⟨270170128499382025805261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46109035263894532404097877 270170128499382025805261)
                  ·
                    rfl

theorem cell22_2367695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_2367695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367695 prefixEnd_2367695 := by exact prefixLift 2367695
  have htrace : WordTrace (prefixWord ++ tailWord_2367695) baseStart_2367695 baseEnd_2367695 := by
    simpa [prefixWord, tailWord_2367695, baseEnd_2367695] using wordTrace_append hprefix tailTrace_2367695
  have hstable : (prefixWord ++ tailWord_2367695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367695).length < 2 ^ (prefixWord ++ tailWord_2367695).sum := by decide
  have hdescent : baseEnd_2367695 < baseStart_2367695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367712 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_2367712 : Nat := 118140960795 + 2367712 * 2 ^ 59
def prefixEnd_2367712 : Nat := 4983230072969 + 3 ^ 40 * 2367712 * 2
def baseEnd_2367712 : Nat := 270172068315187899913577

theorem tailTrace_2367712 : CollatzResearch.WordTrace tailWord_2367712 prefixEnd_2367712 270172068315187899913577 := by
  unfold tailWord_2367712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43178775599095635930464695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57571700798794181240619593 43178775599095635930464695)
  ·
    refine ⟨64768163398643453895697043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43178775599095635930464695 64768163398643453895697043)
    ·
      refine ⟨97152245097965180843545565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64768163398643453895697043 97152245097965180843545565)
      ·
        refine ⟨36432091911736942816329587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97152245097965180843545565 36432091911736942816329587)
        ·
          refine ⟨54648137867605414224494381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36432091911736942816329587 54648137867605414224494381)
          ·
            refine ⟨20493051700352030334185393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54648137867605414224494381 20493051700352030334185393)
            ·
              refine ⟨15369788775264022750639045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20493051700352030334185393 15369788775264022750639045)
              ·
                refine ⟨2881835395362004265744821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15369788775264022750639045 2881835395362004265744821)
                ·
                  refine ⟨270172068315187899913577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2881835395362004265744821 270172068315187899913577)
                  ·
                    rfl

theorem cell22_2367712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_2367712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367712 prefixEnd_2367712 := by exact prefixLift 2367712
  have htrace : WordTrace (prefixWord ++ tailWord_2367712) baseStart_2367712 baseEnd_2367712 := by
    simpa [prefixWord, tailWord_2367712, baseEnd_2367712] using wordTrace_append hprefix tailTrace_2367712
  have hstable : (prefixWord ++ tailWord_2367712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367712).length < 2 ^ (prefixWord ++ tailWord_2367712).sum := by decide
  have hdescent : baseEnd_2367712 < baseStart_2367712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367729 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 5]
def baseStart_2367729 : Nat := 118140960795 + 2367729 * 2 ^ 59
def prefixEnd_2367729 : Nat := 4983230072969 + 3 ^ 40 * 2367729 * 2
def baseEnd_2367729 : Nat := 270174008130993774021893

theorem tailTrace_2367729 : CollatzResearch.WordTrace tailWord_2367729 prefixEnd_2367729 270174008130993774021893 := by
  unfold tailWord_2367729
  simp only [CollatzResearch.WordTrace]
  refine ⟨86358171239129683764298241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57572114159419789176198827 86358171239129683764298241)
  ·
    refine ⟨64768628429347262823223681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86358171239129683764298241 64768628429347262823223681)
    ·
      refine ⟨48576471322010447117417761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64768628429347262823223681 48576471322010447117417761)
      ·
        refine ⟨36432353491507835338063321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48576471322010447117417761 36432353491507835338063321)
        ·
          refine ⟨27324265118630876503547491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36432353491507835338063321 27324265118630876503547491)
          ·
            refine ⟨40986397677946314755321237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27324265118630876503547491 40986397677946314755321237)
            ·
              refine ⟨1921237391153733504155683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40986397677946314755321237 1921237391153733504155683)
              ·
                refine ⟨2881856086730600256233525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921237391153733504155683 2881856086730600256233525)
                ·
                  refine ⟨270174008130993774021893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2881856086730600256233525 270174008130993774021893)
                  ·
                    rfl

theorem cell22_2367729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_2367729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367729 prefixEnd_2367729 := by exact prefixLift 2367729
  have htrace : WordTrace (prefixWord ++ tailWord_2367729) baseStart_2367729 baseEnd_2367729 := by
    simpa [prefixWord, tailWord_2367729, baseEnd_2367729] using wordTrace_append hprefix tailTrace_2367729
  have hstable : (prefixWord ++ tailWord_2367729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367729).length < 2 ^ (prefixWord ++ tailWord_2367729).sum := by decide
  have hdescent : baseEnd_2367729 < baseStart_2367729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367772 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2367772 : Nat := 118140960795 + 2367772 * 2 ^ 59
def prefixEnd_2367772 : Nat := 4983230072969 + 3 ^ 40 * 2367772 * 2
def baseEnd_2367772 : Nat := 810536744171743543240547

theorem tailTrace_2367772 : CollatzResearch.WordTrace tailWord_2367772 prefixEnd_2367772 810536744171743543240547 := by
  unfold tailWord_2367772
  simp only [CollatzResearch.WordTrace]
  refine ⟨43179869788986951054056785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57573159718649268072075713 43179869788986951054056785)
  ·
    refine ⟨32384902341740213290542589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43179869788986951054056785 32384902341740213290542589)
    ·
      refine ⟨12144338378152579983953471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32384902341740213290542589 12144338378152579983953471)
      ·
        refine ⟨18216507567228869975930207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12144338378152579983953471 18216507567228869975930207)
        ·
          refine ⟨27324761350843304963895311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18216507567228869975930207 27324761350843304963895311)
          ·
            refine ⟨40987142026264957445842967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27324761350843304963895311 40987142026264957445842967)
            ·
              refine ⟨61480713039397436168764451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40987142026264957445842967 61480713039397436168764451)
              ·
                refine ⟨92221069559096154253146677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61480713039397436168764451 92221069559096154253146677)
                ·
                  refine ⟨8645725271165264461232501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92221069559096154253146677 8645725271165264461232501)
                  ·
                    refine ⟨810536744171743543240547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8645725271165264461232501 810536744171743543240547)
                    ·
                      rfl

theorem cell22_2367772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2367772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367772 prefixEnd_2367772 := by exact prefixLift 2367772
  have htrace : WordTrace (prefixWord ++ tailWord_2367772) baseStart_2367772 baseEnd_2367772 := by
    simpa [prefixWord, tailWord_2367772, baseEnd_2367772] using wordTrace_append hprefix tailTrace_2367772
  have hstable : (prefixWord ++ tailWord_2367772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367772).length < 2 ^ (prefixWord ++ tailWord_2367772).sum := by decide
  have hdescent : baseEnd_2367772 < baseStart_2367772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367832 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_2367832 : Nat := 118140960795 + 2367832 * 2 ^ 59
def prefixEnd_2367832 : Nat := 4983230072969 + 3 ^ 40 * 2367832 * 2
def baseEnd_2367832 : Nat := 810557283397923386740363

theorem tailTrace_2367832 : CollatzResearch.WordTrace tailWord_2367832 prefixEnd_2367832 810557283397923386740363 := by
  unfold tailWord_2367832
  simp only [CollatzResearch.WordTrace]
  refine ⟨43180963978878266177648875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57574618638504354903531833 43180963978878266177648875)
  ·
    refine ⟨64771445968317399266473313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43180963978878266177648875 64771445968317399266473313)
    ·
      refine ⟨48578584476238049449854985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64771445968317399266473313 48578584476238049449854985)
      ·
        refine ⟨36433938357178537087391239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48578584476238049449854985 36433938357178537087391239)
        ·
          refine ⟨54650907535767805631086859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36433938357178537087391239 54650907535767805631086859)
          ·
            refine ⟨81976361303651708446630289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54650907535767805631086859 81976361303651708446630289)
            ·
              refine ⟨61482270977738781334972717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81976361303651708446630289 61482270977738781334972717)
              ·
                refine ⟨23055851616652043000614769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61482270977738781334972717 23055851616652043000614769)
                ·
                  refine ⟨17291888712489032250461077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23055851616652043000614769 17291888712489032250461077)
                  ·
                    refine ⟨810557283397923386740363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17291888712489032250461077 810557283397923386740363)
                    ·
                      rfl

theorem cell22_2367832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_2367832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367832 prefixEnd_2367832 := by exact prefixLift 2367832
  have htrace : WordTrace (prefixWord ++ tailWord_2367832) baseStart_2367832 baseEnd_2367832 := by
    simpa [prefixWord, tailWord_2367832, baseEnd_2367832] using wordTrace_append hprefix tailTrace_2367832
  have hstable : (prefixWord ++ tailWord_2367832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367832).length < 2 ^ (prefixWord ++ tailWord_2367832).sum := by decide
  have hdescent : baseEnd_2367832 < baseStart_2367832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367898 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_2367898 : Nat := 118140960795 + 2367898 * 2 ^ 59
def prefixEnd_2367898 : Nat := 4983230072969 + 3 ^ 40 * 2367898 * 2
def baseEnd_2367898 : Nat := 270193292182240404863387

theorem tailTrace_2367898 : CollatzResearch.WordTrace tailWord_2367898 prefixEnd_2367898 270193292182240404863387 := by
  unfold tailWord_2367898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591083793879356406800087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57576223450344950418133565 21591083793879356406800087)
  ·
    refine ⟨32386625690819034610200131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21591083793879356406800087 32386625690819034610200131)
    ·
      refine ⟨48579938536228551915300197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32386625690819034610200131 48579938536228551915300197)
      ·
        refine ⟨9108738475542853484118787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48579938536228551915300197 9108738475542853484118787)
        ·
          refine ⟨13663107713314280226178181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108738475542853484118787 13663107713314280226178181)
          ·
            refine ⟨2561832696246427542408409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13663107713314280226178181 2561832696246427542408409)
            ·
              refine ⟨1921374522184820656806307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561832696246427542408409 1921374522184820656806307)
              ·
                refine ⟨2882061783277230985209461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921374522184820656806307 2882061783277230985209461)
                ·
                  refine ⟨270193292182240404863387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2882061783277230985209461 270193292182240404863387)
                  ·
                    rfl

theorem cell22_2367898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_2367898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367898 prefixEnd_2367898 := by exact prefixLift 2367898
  have htrace : WordTrace (prefixWord ++ tailWord_2367898) baseStart_2367898 baseEnd_2367898 := by
    simpa [prefixWord, tailWord_2367898, baseEnd_2367898] using wordTrace_append hprefix tailTrace_2367898
  have hstable : (prefixWord ++ tailWord_2367898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367898).length < 2 ^ (prefixWord ++ tailWord_2367898).sum := by decide
  have hdescent : baseEnd_2367898 < baseStart_2367898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367911 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2367911 : Nat := 118140960795 + 2367911 * 2 ^ 59
def prefixEnd_2367911 : Nat := 4983230072969 + 3 ^ 40 * 2367911 * 2
def baseEnd_2367911 : Nat := 810584326712393514015121

theorem tailTrace_2367911 : CollatzResearch.WordTrace tailWord_2367911 prefixEnd_2367911 810584326712393514015121 := by
  unfold tailWord_2367911
  simp only [CollatzResearch.WordTrace]
  refine ⟨86364809324470328847423587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57576539549646885898282391 86364809324470328847423587)
  ·
    refine ⟨129547213986705493271135381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86364809324470328847423587 129547213986705493271135381)
    ·
      refine ⟨6072525655626819997084471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129547213986705493271135381 6072525655626819997084471)
      ·
        refine ⟨9108788483440229995626707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072525655626819997084471 9108788483440229995626707)
        ·
          refine ⟨13663182725160344993440061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108788483440229995626707 13663182725160344993440061)
          ·
            refine ⟨5123693521935129372540023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13663182725160344993440061 5123693521935129372540023)
            ·
              refine ⟨7685540282902694058810035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123693521935129372540023 7685540282902694058810035)
              ·
                refine ⟨11528310424354041088215053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685540282902694058810035 11528310424354041088215053)
                ·
                  refine ⟨4323116409132765408080645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11528310424354041088215053 4323116409132765408080645)
                  ·
                    refine ⟨810584326712393514015121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4323116409132765408080645 810584326712393514015121)
                    ·
                      rfl

theorem cell22_2367911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2367911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367911 prefixEnd_2367911 := by exact prefixLift 2367911
  have htrace : WordTrace (prefixWord ++ tailWord_2367911) baseStart_2367911 baseEnd_2367911 := by
    simpa [prefixWord, tailWord_2367911, baseEnd_2367911] using wordTrace_append hprefix tailTrace_2367911
  have hstable : (prefixWord ++ tailWord_2367911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367911).length < 2 ^ (prefixWord ++ tailWord_2367911).sum := by decide
  have hdescent : baseEnd_2367911 < baseStart_2367911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367943 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 4]
def baseStart_2367943 : Nat := 118140960795 + 2367943 * 2 ^ 59
def prefixEnd_2367943 : Nat := 4983230072969 + 3 ^ 40 * 2367943 * 2
def baseEnd_2367943 : Nat := 270198426988785365738341

theorem tailTrace_2367943 : CollatzResearch.WordTrace tailWord_2367943 prefixEnd_2367943 270198426988785365738341 := by
  unfold tailWord_2367943
  simp only [CollatzResearch.WordTrace]
  refine ⟨86365976460354398312588483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57577317640236265541725655 86365976460354398312588483)
  ·
    refine ⟨129548964690531597468882725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86365976460354398312588483 129548964690531597468882725)
    ·
      refine ⟨24290430879474674525415511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129548964690531597468882725 24290430879474674525415511)
      ·
        refine ⟨36435646319212011788123267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24290430879474674525415511 36435646319212011788123267)
        ·
          refine ⟨54653469478818017682184901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36435646319212011788123267 54653469478818017682184901)
          ·
            refine ⟨10247525527278378315409669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54653469478818017682184901 10247525527278378315409669)
            ·
              refine ⟨1921411036364695934139313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10247525527278378315409669 1921411036364695934139313)
              ·
                refine ⟨1441058277273521950604485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921411036364695934139313 1441058277273521950604485)
                ·
                  refine ⟨270198426988785365738341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441058277273521950604485 270198426988785365738341)
                  ·
                    rfl

theorem cell22_2367943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 4].length) (baseStart_2367943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367943 prefixEnd_2367943 := by exact prefixLift 2367943
  have htrace : WordTrace (prefixWord ++ tailWord_2367943) baseStart_2367943 baseEnd_2367943 := by
    simpa [prefixWord, tailWord_2367943, baseEnd_2367943] using wordTrace_append hprefix tailTrace_2367943
  have hstable : (prefixWord ++ tailWord_2367943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367943).length < 2 ^ (prefixWord ++ tailWord_2367943).sum := by decide
  have hdescent : baseEnd_2367943 < baseStart_2367943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367958 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2367958 : Nat := 118140960795 + 2367958 * 2 ^ 59
def prefixEnd_2367958 : Nat := 4983230072969 + 3 ^ 40 * 2367958 * 2
def baseEnd_2367958 : Nat := 810600415772901058089977

theorem tailTrace_2367958 : CollatzResearch.WordTrace tailWord_2367958 prefixEnd_2367958 810600415772901058089977 := by
  unfold tailWord_2367958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397907722206253492149033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57577682370200037249589685 5397907722206253492149033)
  ·
    refine ⟨4048430791654690119111775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5397907722206253492149033 4048430791654690119111775)
    ·
      refine ⟨6072646187482035178667663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048430791654690119111775 6072646187482035178667663)
      ·
        refine ⟨9108969281223052768001495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072646187482035178667663 9108969281223052768001495)
        ·
          refine ⟨13663453921834579152002243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108969281223052768001495 13663453921834579152002243)
          ·
            refine ⟨20495180882751868728003365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13663453921834579152002243 20495180882751868728003365)
            ·
              refine ⟨3842846415515975386500631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20495180882751868728003365 3842846415515975386500631)
              ·
                refine ⟨5764269623273963079750947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842846415515975386500631 5764269623273963079750947)
                ·
                  refine ⟨8646404434910944619626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764269623273963079750947 8646404434910944619626421)
                  ·
                    refine ⟨810600415772901058089977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8646404434910944619626421 810600415772901058089977)
                    ·
                      rfl

theorem cell22_2367958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2367958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367958 prefixEnd_2367958 := by exact prefixLift 2367958
  have htrace : WordTrace (prefixWord ++ tailWord_2367958) baseStart_2367958 baseEnd_2367958 := by
    simpa [prefixWord, tailWord_2367958, baseEnd_2367958] using wordTrace_append hprefix tailTrace_2367958
  have hstable : (prefixWord ++ tailWord_2367958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367958).length < 2 ^ (prefixWord ++ tailWord_2367958).sum := by decide
  have hdescent : baseEnd_2367958 < baseStart_2367958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367999 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 7]
def baseStart_2367999 : Nat := 118140960795 + 2367999 * 2 ^ 59
def prefixEnd_2367999 : Nat := 4983230072969 + 3 ^ 40 * 2367999 * 2
def baseEnd_2367999 : Nat := 270204816970263539271617

theorem tailTrace_2367999 : CollatzResearch.WordTrace tailWord_2367999 prefixEnd_2367999 270204816970263539271617 := by
  unfold tailWord_2367999
  simp only [CollatzResearch.WordTrace]
  refine ⟨86368018948151519876627051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57578679298767679917751367 86368018948151519876627051)
  ·
    refine ⟨129552028422227279814940577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86368018948151519876627051 129552028422227279814940577)
    ·
      refine ⟨97164021316670459861205433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129552028422227279814940577 97164021316670459861205433)
      ·
        refine ⟨72873015987502844895904075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97164021316670459861205433 72873015987502844895904075)
        ·
          refine ⟨109309523981254267343856113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72873015987502844895904075 109309523981254267343856113)
          ·
            refine ⟨81982142985940700507892085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109309523981254267343856113 81982142985940700507892085)
            ·
              refine ⟨7685825904931940672614883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81982142985940700507892085 7685825904931940672614883)
              ·
                refine ⟨11528738857397911008922325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685825904931940672614883 11528738857397911008922325)
                ·
                  refine ⟨270204816970263539271617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11528738857397911008922325 270204816970263539271617)
                  ·
                    rfl

theorem cell22_2367999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_2367999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2367999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2367999 prefixEnd_2367999 := by exact prefixLift 2367999
  have htrace : WordTrace (prefixWord ++ tailWord_2367999) baseStart_2367999 baseEnd_2367999 := by
    simpa [prefixWord, tailWord_2367999, baseEnd_2367999] using wordTrace_append hprefix tailTrace_2367999
  have hstable : (prefixWord ++ tailWord_2367999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367999).length < 2 ^ (prefixWord ++ tailWord_2367999).sum := by decide
  have hdescent : baseEnd_2367999 < baseStart_2367999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368003 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 1, 3]
def baseStart_2368003 : Nat := 118140960795 + 2368003 * 2 ^ 59
def prefixEnd_2368003 : Nat := 4983230072969 + 3 ^ 40 * 2368003 * 2
def baseEnd_2368003 : Nat := 810615820192535940714839

theorem tailTrace_2368003 : CollatzResearch.WordTrace tailWord_2368003 prefixEnd_2368003 810615820192535940714839 := by
  unfold tailWord_2368003
  simp only [CollatzResearch.WordTrace]
  refine ⟨86368164840137028559772663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57578776560091352373181775 86368164840137028559772663)
  ·
    refine ⟨129552247260205542839658995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86368164840137028559772663 129552247260205542839658995)
    ·
      refine ⟨194328370890308314259488493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129552247260205542839658995 194328370890308314259488493)
      ·
        refine ⟨72873139083865617847308185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194328370890308314259488493 72873139083865617847308185)
        ·
          refine ⟨54654854312899213385481139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72873139083865617847308185 54654854312899213385481139)
          ·
            refine ⟨81982281469348820078221709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54654854312899213385481139 81982281469348820078221709)
            ·
              refine ⟨30743355551005807529333141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81982281469348820078221709 30743355551005807529333141)
              ·
                refine ⟨1441094791453397227937491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30743355551005807529333141 1441094791453397227937491)
                ·
                  refine ⟨2161642187180095841906237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441094791453397227937491 2161642187180095841906237)
                  ·
                    refine ⟨810615820192535940714839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161642187180095841906237 810615820192535940714839)
                    ·
                      rfl

theorem cell22_2368003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 3].length) (baseStart_2368003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368003 prefixEnd_2368003 := by exact prefixLift 2368003
  have htrace : WordTrace (prefixWord ++ tailWord_2368003) baseStart_2368003 baseEnd_2368003 := by
    simpa [prefixWord, tailWord_2368003, baseEnd_2368003] using wordTrace_append hprefix tailTrace_2368003
  have hstable : (prefixWord ++ tailWord_2368003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368003).length < 2 ^ (prefixWord ++ tailWord_2368003).sum := by decide
  have hdescent : baseEnd_2368003 < baseStart_2368003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368020 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2368020 : Nat := 118140960795 + 2368020 * 2 ^ 59
def prefixEnd_2368020 : Nat := 4983230072969 + 3 ^ 40 * 2368020 * 2
def baseEnd_2368020 : Nat := 810621639639953563039787

theorem tailTrace_2368020 : CollatzResearch.WordTrace tailWord_2368020 prefixEnd_2368020 810621639639953563039787 := by
  unfold tailWord_2368020
  simp only [CollatzResearch.WordTrace]
  refine ⟨43184392440537720231570757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57579189920716960308761009 43184392440537720231570757)
  ·
    refine ⟨8097073582600822543419517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43184392440537720231570757 8097073582600822543419517)
    ·
      refine ⟨3036402593475308453782319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8097073582600822543419517 3036402593475308453782319)
      ·
        refine ⟨4554603890212962680673479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036402593475308453782319 4554603890212962680673479)
        ·
          refine ⟨6831905835319444021010219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554603890212962680673479 6831905835319444021010219)
          ·
            refine ⟨10247858752979166031515329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831905835319444021010219 10247858752979166031515329)
            ·
              refine ⟨7685894064734374523636497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10247858752979166031515329 7685894064734374523636497)
              ·
                refine ⟨5764420548550780892727373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7685894064734374523636497 5764420548550780892727373)
                ·
                  refine ⟨2161657705706542834772765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5764420548550780892727373 2161657705706542834772765)
                  ·
                    refine ⟨810621639639953563039787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161657705706542834772765 810621639639953563039787)
                    ·
                      rfl

theorem cell22_2368020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2368020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368020 prefixEnd_2368020 := by exact prefixLift 2368020
  have htrace : WordTrace (prefixWord ++ tailWord_2368020) baseStart_2368020 baseEnd_2368020 := by
    simpa [prefixWord, tailWord_2368020, baseEnd_2368020] using wordTrace_append hprefix tailTrace_2368020
  have hstable : (prefixWord ++ tailWord_2368020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368020).length < 2 ^ (prefixWord ++ tailWord_2368020).sum := by decide
  have hdescent : baseEnd_2368020 < baseStart_2368020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368044 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_2368044 : Nat := 118140960795 + 2368044 * 2 ^ 59
def prefixEnd_2368044 : Nat := 4983230072969 + 3 ^ 40 * 2368044 * 2
def baseEnd_2368044 : Nat := 270209951776808500146571

theorem tailTrace_2368044 : CollatzResearch.WordTrace tailWord_2368044 prefixEnd_2368044 270209951776808500146571 := by
  unfold tailWord_2368044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43184830116494246281007593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57579773488658995041343457 43184830116494246281007593)
  ·
    refine ⟨32388622587370684710755695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43184830116494246281007593 32388622587370684710755695)
    ·
      refine ⟨48582933881056027066133543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32388622587370684710755695 48582933881056027066133543)
      ·
        refine ⟨72874400821584040599200315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48582933881056027066133543 72874400821584040599200315)
        ·
          refine ⟨109311601232376060898800473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72874400821584040599200315 109311601232376060898800473)
          ·
            refine ⟨81983700924282045674100355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109311601232376060898800473 81983700924282045674100355)
            ·
              refine ⟨122975551386423068511150533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81983700924282045674100355 122975551386423068511150533)
              ·
                refine ⟨23057915884954325345840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122975551386423068511150533 23057915884954325345840725)
                ·
                  refine ⟨270209951776808500146571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23057915884954325345840725 270209951776808500146571)
                  ·
                    rfl

theorem cell22_2368044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_2368044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368044 prefixEnd_2368044 := by exact prefixLift 2368044
  have htrace : WordTrace (prefixWord ++ tailWord_2368044) baseStart_2368044 baseEnd_2368044 := by
    simpa [prefixWord, tailWord_2368044, baseEnd_2368044] using wordTrace_append hprefix tailTrace_2368044
  have hstable : (prefixWord ++ tailWord_2368044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368044).length < 2 ^ (prefixWord ++ tailWord_2368044).sum := by decide
  have hdescent : baseEnd_2368044 < baseStart_2368044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368054 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2368054 : Nat := 118140960795 + 2368054 * 2 ^ 59
def prefixEnd_2368054 : Nat := 4983230072969 + 3 ^ 40 * 2368054 * 2
def baseEnd_2368054 : Nat := 810633278534788807689683

theorem tailTrace_2368054 : CollatzResearch.WordTrace tailWord_2368054 prefixEnd_2368054 810633278534788807689683 := by
  unfold tailWord_2368054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5398126560184516516867451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57580016641968176179919477 5398126560184516516867451)
  ·
    refine ⟨8097189840276774775301177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5398126560184516516867451 8097189840276774775301177)
    ·
      refine ⟨6072892380207581081475883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8097189840276774775301177 6072892380207581081475883)
      ·
        refine ⟨9109338570311371622213825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072892380207581081475883 9109338570311371622213825)
        ·
          refine ⟨6832003927733528716660369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9109338570311371622213825 6832003927733528716660369)
          ·
            refine ⟨5124002945800146537495277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832003927733528716660369 5124002945800146537495277)
            ·
              refine ⟨1921501104675054951560729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5124002945800146537495277 1921501104675054951560729)
              ·
                refine ⟨1441125828506291213670547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921501104675054951560729 1441125828506291213670547)
                ·
                  refine ⟨2161688742759436820505821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441125828506291213670547 2161688742759436820505821)
                  ·
                    refine ⟨810633278534788807689683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161688742759436820505821 810633278534788807689683)
                    ·
                      rfl

theorem cell22_2368054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2368054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368054 prefixEnd_2368054 := by exact prefixLift 2368054
  have htrace : WordTrace (prefixWord ++ tailWord_2368054) baseStart_2368054 baseEnd_2368054 := by
    simpa [prefixWord, tailWord_2368054, baseEnd_2368054] using wordTrace_append hprefix tailTrace_2368054
  have hstable : (prefixWord ++ tailWord_2368054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368054).length < 2 ^ (prefixWord ++ tailWord_2368054).sum := by decide
  have hdescent : baseEnd_2368054 < baseStart_2368054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368076 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_2368076 : Nat := 118140960795 + 2368076 * 2 ^ 59
def prefixEnd_2368076 : Nat := 4983230072969 + 3 ^ 40 * 2368076 * 2
def baseEnd_2368076 : Nat := 810640809584388083639615

theorem tailTrace_2368076 : CollatzResearch.WordTrace tailWord_2368076 prefixEnd_2368076 810640809584388083639615 := by
  unfold tailWord_2368076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43185413684436281013590041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57580551579248374684786721 43185413684436281013590041)
  ·
    refine ⟨32389060263327210760192531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43185413684436281013590041 32389060263327210760192531)
    ·
      refine ⟨48583590394990816140288797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32389060263327210760192531 48583590394990816140288797)
      ·
        refine ⟨18218846398121556052608299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48583590394990816140288797 18218846398121556052608299)
        ·
          refine ⟨27328269597182334078912449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18218846398121556052608299 27328269597182334078912449)
          ·
            refine ⟨20496202197886750559184337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27328269597182334078912449 20496202197886750559184337)
            ·
              refine ⟨15372151648415062919388253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20496202197886750559184337 15372151648415062919388253)
              ·
                refine ⟨5764556868155648594770595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15372151648415062919388253 5764556868155648594770595)
                ·
                  refine ⟨8646835302233472892155893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764556868155648594770595 8646835302233472892155893)
                  ·
                    refine ⟨810640809584388083639615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8646835302233472892155893 810640809584388083639615)
                    ·
                      rfl

theorem cell22_2368076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_2368076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368076 prefixEnd_2368076 := by exact prefixLift 2368076
  have htrace : WordTrace (prefixWord ++ tailWord_2368076) baseStart_2368076 baseEnd_2368076 := by
    simpa [prefixWord, tailWord_2368076, baseEnd_2368076] using wordTrace_append hprefix tailTrace_2368076
  have hstable : (prefixWord ++ tailWord_2368076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368076).length < 2 ^ (prefixWord ++ tailWord_2368076).sum := by decide
  have hdescent : baseEnd_2368076 < baseStart_2368076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368110 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2368110 : Nat := 118140960795 + 2368110 * 2 ^ 59
def prefixEnd_2368110 : Nat := 4983230072969 + 3 ^ 40 * 2368110 * 2
def baseEnd_2368110 : Nat := 810652448479223328289511

theorem tailTrace_2368110 : CollatzResearch.WordTrace tailWord_2368110 prefixEnd_2368110 810652448479223328289511 := by
  unfold tailWord_2368110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796508431343673229239723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57581378300499590555945189 10796508431343673229239723)
  ·
    refine ⟨16194762647015509843859585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10796508431343673229239723 16194762647015509843859585)
    ·
      refine ⟨12146071985261632382894689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16194762647015509843859585 12146071985261632382894689)
      ·
        refine ⟨9109553988946224287171017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12146071985261632382894689 9109553988946224287171017)
        ·
          refine ⟨6832165491709668215378263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9109553988946224287171017 6832165491709668215378263)
          ·
            refine ⟨10248248237564502323067395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832165491709668215378263 10248248237564502323067395)
            ·
              refine ⟨15372372356346753484601093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10248248237564502323067395 15372372356346753484601093)
              ·
                refine ⟨2882319816815016278362705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15372372356346753484601093 2882319816815016278362705)
                ·
                  refine ⟨2161739862611262208772029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2882319816815016278362705 2161739862611262208772029)
                  ·
                    refine ⟨810652448479223328289511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161739862611262208772029 810652448479223328289511)
                    ·
                      rfl

theorem cell22_2368110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2368110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368110 prefixEnd_2368110 := by exact prefixLift 2368110
  have htrace : WordTrace (prefixWord ++ tailWord_2368110) baseStart_2368110 baseEnd_2368110 := by
    simpa [prefixWord, tailWord_2368110, baseEnd_2368110] using wordTrace_append hprefix tailTrace_2368110
  have hstable : (prefixWord ++ tailWord_2368110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368110).length < 2 ^ (prefixWord ++ tailWord_2368110).sum := by decide
  have hdescent : baseEnd_2368110 < baseStart_2368110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368112 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_2368112 : Nat := 118140960795 + 2368112 * 2 ^ 59
def prefixEnd_2368112 : Nat := 4983230072969 + 3 ^ 40 * 2368112 * 2
def baseEnd_2368112 : Nat := 270217711040031996579835

theorem tailTrace_2368112 : CollatzResearch.WordTrace tailWord_2368112 prefixEnd_2368112 270217711040031996579835 := by
  unfold tailWord_2368112
  simp only [CollatzResearch.WordTrace]
  refine ⟨43186070198371070087745295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57581426931161426783660393 43186070198371070087745295)
  ·
    refine ⟨64779105297556605131617943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43186070198371070087745295 64779105297556605131617943)
    ·
      refine ⟨97168657946334907697426915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64779105297556605131617943 97168657946334907697426915)
      ·
        refine ⟨145752986919502361546140373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97168657946334907697426915 145752986919502361546140373)
        ·
          refine ⟨3416085630925836598737665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 145752986919502361546140373 3416085630925836598737665)
          ·
            refine ⟨2562064223194377449053249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416085630925836598737665 2562064223194377449053249)
            ·
              refine ⟨1921548167395783086789937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562064223194377449053249 1921548167395783086789937)
              ·
                refine ⟨1441161125546837315092453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921548167395783086789937 1441161125546837315092453)
                ·
                  refine ⟨270217711040031996579835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441161125546837315092453 270217711040031996579835)
                  ·
                    rfl

theorem cell22_2368112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_2368112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368112 prefixEnd_2368112 := by exact prefixLift 2368112
  have htrace : WordTrace (prefixWord ++ tailWord_2368112) baseStart_2368112 baseEnd_2368112 := by
    simpa [prefixWord, tailWord_2368112, baseEnd_2368112] using wordTrace_append hprefix tailTrace_2368112
  have hstable : (prefixWord ++ tailWord_2368112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368112).length < 2 ^ (prefixWord ++ tailWord_2368112).sum := by decide
  have hdescent : baseEnd_2368112 < baseStart_2368112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368151 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 7]
def baseStart_2368151 : Nat := 118140960795 + 2368151 * 2 ^ 59
def prefixEnd_2368151 : Nat := 4983230072969 + 3 ^ 40 * 2368151 * 2
def baseEnd_2368151 : Nat := 270222161205704296004795

theorem tailTrace_2368151 : CollatzResearch.WordTrace tailWord_2368151 prefixEnd_2368151 270222161205704296004795 := by
  unfold tailWord_2368151
  simp only [CollatzResearch.WordTrace]
  refine ⟨86373562843600849836160307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57582375229067233224106871 86373562843600849836160307)
  ·
    refine ⟨129560344265401274754240461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86373562843600849836160307 129560344265401274754240461)
    ·
      refine ⟨48585129099525478032840173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129560344265401274754240461 48585129099525478032840173)
      ·
        refine ⟨18219423412322054262315065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48585129099525478032840173 18219423412322054262315065)
        ·
          refine ⟨13664567559241540696736299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18219423412322054262315065 13664567559241540696736299)
          ·
            refine ⟨20496851338862311045104449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13664567559241540696736299 20496851338862311045104449)
            ·
              refine ⟨15372638504146733283828337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20496851338862311045104449 15372638504146733283828337)
              ·
                refine ⟨11529478878110049962871253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15372638504146733283828337 11529478878110049962871253)
                ·
                  refine ⟨270222161205704296004795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11529478878110049962871253 270222161205704296004795)
                  ·
                    rfl

theorem cell22_2368151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_2368151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368151 prefixEnd_2368151 := by exact prefixLift 2368151
  have htrace : WordTrace (prefixWord ++ tailWord_2368151) baseStart_2368151 baseEnd_2368151 := by
    simpa [prefixWord, tailWord_2368151, baseEnd_2368151] using wordTrace_append hprefix tailTrace_2368151
  have hstable : (prefixWord ++ tailWord_2368151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368151).length < 2 ^ (prefixWord ++ tailWord_2368151).sum := by decide
  have hdescent : baseEnd_2368151 < baseStart_2368151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368260 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2368260 : Nat := 118140960795 + 2368260 * 2 ^ 59
def prefixEnd_2368260 : Nat := 4983230072969 + 3 ^ 40 * 2368260 * 2
def baseEnd_2368260 : Nat := 810703796544672937039051

theorem tailTrace_2368260 : CollatzResearch.WordTrace tailWord_2368260 prefixEnd_2368260 810703796544672937039051 := by
  unfold tailWord_2368260
  simp only [CollatzResearch.WordTrace]
  refine ⟨43188769200102980725939117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57585025600137307634585489 43188769200102980725939117)
  ·
    refine ⟨16195788450038617772227169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43188769200102980725939117 16195788450038617772227169)
    ·
      refine ⟨12146841337528963329170377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16195788450038617772227169 12146841337528963329170377)
      ·
        refine ⟨9110131003146722496877783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12146841337528963329170377 9110131003146722496877783)
        ·
          refine ⟨13665196504720083745316675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9110131003146722496877783 13665196504720083745316675)
          ·
            refine ⟨20497794757080125617975013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13665196504720083745316675 20497794757080125617975013)
            ·
              refine ⟨3843336516952523553370315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20497794757080125617975013 3843336516952523553370315)
              ·
                refine ⟨5765004775428785330055473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3843336516952523553370315 5765004775428785330055473)
                ·
                  refine ⟨4323753581571588997541605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5765004775428785330055473 4323753581571588997541605)
                  ·
                    refine ⟨810703796544672937039051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4323753581571588997541605 810703796544672937039051)
                    ·
                      rfl

theorem cell22_2368260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2368260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368260 prefixEnd_2368260 := by exact prefixLift 2368260
  have htrace : WordTrace (prefixWord ++ tailWord_2368260) baseStart_2368260 baseEnd_2368260 := by
    simpa [prefixWord, tailWord_2368260, baseEnd_2368260] using wordTrace_append hprefix tailTrace_2368260
  have hstable : (prefixWord ++ tailWord_2368260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368260).length < 2 ^ (prefixWord ++ tailWord_2368260).sum := by decide
  have hdescent : baseEnd_2368260 < baseStart_2368260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368288 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_2368288 : Nat := 118140960795 + 2368288 * 2 ^ 59
def prefixEnd_2368288 : Nat := 4983230072969 + 3 ^ 40 * 2368288 * 2
def baseEnd_2368288 : Nat := 810713381516890197338965

theorem tailTrace_2368288 : CollatzResearch.WordTrace tailWord_2368288 prefixEnd_2368288 810713381516890197338965 := by
  unfold tailWord_2368288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43189279822052261116948759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57585706429403014822598345 43189279822052261116948759)
  ·
    refine ⟨64783919733078391675423139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43189279822052261116948759 64783919733078391675423139)
    ·
      refine ⟨97175879599617587513134709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64783919733078391675423139 97175879599617587513134709)
      ·
        refine ⟨9110238712464148829356379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97175879599617587513134709 9110238712464148829356379)
        ·
          refine ⟨13665358068696223244034569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9110238712464148829356379 13665358068696223244034569)
          ·
            refine ⟨10249018551522167433025927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13665358068696223244034569 10249018551522167433025927)
            ·
              refine ⟨15373527827283251149538891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249018551522167433025927 15373527827283251149538891)
              ·
                refine ⟨23060291740924876724308337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15373527827283251149538891 23060291740924876724308337)
                ·
                  refine ⟨17295218805693657543231253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23060291740924876724308337 17295218805693657543231253)
                  ·
                    refine ⟨810713381516890197338965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17295218805693657543231253 810713381516890197338965)
                    ·
                      rfl

theorem cell22_2368288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_2368288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368288 prefixEnd_2368288 := by exact prefixLift 2368288
  have htrace : WordTrace (prefixWord ++ tailWord_2368288) baseStart_2368288 baseEnd_2368288 := by
    simpa [prefixWord, tailWord_2368288, baseEnd_2368288] using wordTrace_append hprefix tailTrace_2368288
  have hstable : (prefixWord ++ tailWord_2368288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368288).length < 2 ^ (prefixWord ++ tailWord_2368288).sum := by decide
  have hdescent : baseEnd_2368288 < baseStart_2368288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368292 : List Nat := [2, 3, 1, 3, 4, 1, 1, 7]
def baseStart_2368292 : Nat := 118140960795 + 2368292 * 2 ^ 59
def prefixEnd_2368292 : Nat := 4983230072969 + 3 ^ 40 * 2368292 * 2
def baseEnd_2368292 : Nat := 90079416755403946693217

theorem tailTrace_2368292 : CollatzResearch.WordTrace tailWord_2368292 prefixEnd_2368292 90079416755403946693217 := by
  unfold tailWord_2368292
  simp only [CollatzResearch.WordTrace]
  refine ⟨43189352768045015458521565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57585803690726687278028753 43189352768045015458521565)
  ·
    refine ⟨16196007288016880796945587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43189352768045015458521565 16196007288016880796945587)
    ·
      refine ⟨24294010932025321195418381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16196007288016880796945587 24294010932025321195418381)
      ·
        refine ⟨9110254099509495448281893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24294010932025321195418381 9110254099509495448281893)
        ·
          refine ⟨1708172643658030396552855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9110254099509495448281893 1708172643658030396552855)
          ·
            refine ⟨2562258965487045594829283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708172643658030396552855 2562258965487045594829283)
            ·
              refine ⟨3843388448230568392243925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562258965487045594829283 3843388448230568392243925)
              ·
                refine ⟨90079416755403946693217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3843388448230568392243925 90079416755403946693217)
                ·
                  rfl

theorem cell22_2368292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_2368292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368292 prefixEnd_2368292 := by exact prefixLift 2368292
  have htrace : WordTrace (prefixWord ++ tailWord_2368292) baseStart_2368292 baseEnd_2368292 := by
    simpa [prefixWord, tailWord_2368292, baseEnd_2368292] using wordTrace_append hprefix tailTrace_2368292
  have hstable : (prefixWord ++ tailWord_2368292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368292).length < 2 ^ (prefixWord ++ tailWord_2368292).sum := by decide
  have hdescent : baseEnd_2368292 < baseStart_2368292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368337 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 5]
def baseStart_2368337 : Nat := 118140960795 + 2368337 * 2 ^ 59
def prefixEnd_2368337 : Nat := 4983230072969 + 3 ^ 40 * 2368337 * 2
def baseEnd_2368337 : Nat := 270243385072756800954605

theorem tailTrace_2368337 : CollatzResearch.WordTrace tailWord_2368337 prefixEnd_2368337 270243385072756800954605 := by
  unfold tailWord_2368337
  simp only [CollatzResearch.WordTrace]
  refine ⟨86380346820927003602431265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57586897880618002401620843 86380346820927003602431265)
  ·
    refine ⟨64785260115695252701823449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86380346820927003602431265 64785260115695252701823449)
    ·
      refine ⟨48588945086771439526367587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64785260115695252701823449 48588945086771439526367587)
      ·
        refine ⟨72883417630157159289551381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48588945086771439526367587 72883417630157159289551381)
        ·
          refine ⟨3416410201413616841697721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72883417630157159289551381 3416410201413616841697721)
          ·
            refine ⟨2562307651060212631273291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416410201413616841697721 2562307651060212631273291)
            ·
              refine ⟨3843461476590318946909937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562307651060212631273291 3843461476590318946909937)
              ·
                refine ⟨2882596107442739210182453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3843461476590318946909937 2882596107442739210182453)
                ·
                  refine ⟨270243385072756800954605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2882596107442739210182453 270243385072756800954605)
                  ·
                    rfl

theorem cell22_2368337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_2368337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368337 prefixEnd_2368337 := by exact prefixLift 2368337
  have htrace : WordTrace (prefixWord ++ tailWord_2368337) baseStart_2368337 baseEnd_2368337 := by
    simpa [prefixWord, tailWord_2368337, baseEnd_2368337] using wordTrace_append hprefix tailTrace_2368337
  have hstable : (prefixWord ++ tailWord_2368337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368337).length < 2 ^ (prefixWord ++ tailWord_2368337).sum := by decide
  have hdescent : baseEnd_2368337 < baseStart_2368337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368354 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2368354 : Nat := 118140960795 + 2368354 * 2 ^ 59
def prefixEnd_2368354 : Nat := 4983230072969 + 3 ^ 40 * 2368354 * 2
def baseEnd_2368354 : Nat := 270245324888562675062921

theorem tailTrace_2368354 : CollatzResearch.WordTrace tailWord_2368354 prefixEnd_2368354 270245324888562675062921 := by
  unfold tailWord_2368354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21595241715466353876450029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57587311241243610337200077 21595241715466353876450029)
  ·
    refine ⟨8098215643299882703668761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21595241715466353876450029 8098215643299882703668761)
    ·
      refine ⟨6073661732474912027751571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8098215643299882703668761 6073661732474912027751571)
      ·
        refine ⟨9110492598712368041627357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073661732474912027751571 9110492598712368041627357)
        ·
          refine ⟨3416434724517138015610259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9110492598712368041627357 3416434724517138015610259)
          ·
            refine ⟨5124652086775707023415389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416434724517138015610259 5124652086775707023415389)
            ·
              refine ⟨1921744532540890133780771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5124652086775707023415389 1921744532540890133780771)
              ·
                refine ⟨2882616798811335200671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921744532540890133780771 2882616798811335200671157)
                ·
                  refine ⟨270245324888562675062921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2882616798811335200671157 270245324888562675062921)
                  ·
                    rfl

theorem cell22_2368354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2368354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368354 prefixEnd_2368354 := by exact prefixLift 2368354
  have htrace : WordTrace (prefixWord ++ tailWord_2368354) baseStart_2368354 baseEnd_2368354 := by
    simpa [prefixWord, tailWord_2368354, baseEnd_2368354] using wordTrace_append hprefix tailTrace_2368354
  have hstable : (prefixWord ++ tailWord_2368354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368354).length < 2 ^ (prefixWord ++ tailWord_2368354).sum := by decide
  have hdescent : baseEnd_2368354 < baseStart_2368354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368393 : List Nat := [1, 2, 1, 1, 5, 2, 10]
def baseStart_2368393 : Nat := 118140960795 + 2368393 * 2 ^ 59
def prefixEnd_2368393 : Nat := 4983230072969 + 3 ^ 40 * 2368393 * 2
def baseEnd_2368393 : Nat := 30027752783803886054209

theorem tailTrace_2368393 : CollatzResearch.WordTrace tailWord_2368393 prefixEnd_2368393 30027752783803886054209 := by
  unfold tailWord_2368393
  simp only [CollatzResearch.WordTrace]
  refine ⟨86382389308724125166469833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57588259539149416777646555 86382389308724125166469833)
  ·
    refine ⟨64786791981543093874852375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86382389308724125166469833 64786791981543093874852375)
    ·
      refine ⟨97180187972314640812278563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64786791981543093874852375 97180187972314640812278563)
      ·
        refine ⟨145770281958471961218417845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97180187972314640812278563 145770281958471961218417845)
        ·
          refine ⟨13665963933606746364226673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145770281958471961218417845 13665963933606746364226673)
          ·
            refine ⟨10249472950205059773170005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13665963933606746364226673 10249472950205059773170005)
            ·
              refine ⟨30027752783803886054209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10249472950205059773170005 30027752783803886054209)
              ·
                rfl

theorem cell22_2368393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 10].length) (baseStart_2368393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368393 prefixEnd_2368393 := by exact prefixLift 2368393
  have htrace : WordTrace (prefixWord ++ tailWord_2368393) baseStart_2368393 baseEnd_2368393 := by
    simpa [prefixWord, tailWord_2368393, baseEnd_2368393] using wordTrace_append hprefix tailTrace_2368393
  have hstable : (prefixWord ++ tailWord_2368393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368393).length < 2 ^ (prefixWord ++ tailWord_2368393).sum := by decide
  have hdescent : baseEnd_2368393 < baseStart_2368393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368425 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_2368425 : Nat := 118140960795 + 2368425 * 2 ^ 59
def prefixEnd_2368425 : Nat := 4983230072969 + 3 ^ 40 * 2368425 * 2
def baseEnd_2368425 : Nat := 810760279416667506663545

theorem tailTrace_2368425 : CollatzResearch.WordTrace tailWord_2368425 prefixEnd_2368425 810760279416667506663545 := by
  unfold tailWord_2368425
  simp only [CollatzResearch.WordTrace]
  refine ⟨86383556444608194631634729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57589037629738796421089819 86383556444608194631634729)
  ·
    refine ⟨64787667333456145973726047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86383556444608194631634729 64787667333456145973726047)
    ·
      refine ⟨97181501000184218960589071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64787667333456145973726047 97181501000184218960589071)
      ·
        refine ⟨145772251500276328440883607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97181501000184218960589071 145772251500276328440883607)
        ·
          refine ⟨218658377250414492661325411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145772251500276328440883607 218658377250414492661325411)
          ·
            refine ⟨327987565875621738991988117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218658377250414492661325411 327987565875621738991988117)
            ·
              refine ⟨15374417150419769015249443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 327987565875621738991988117 15374417150419769015249443)
              ·
                refine ⟨23061625725629653522874165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15374417150419769015249443 23061625725629653522874165)
                ·
                  refine ⟨2162027411777780017769453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23061625725629653522874165 2162027411777780017769453)
                  ·
                    refine ⟨810760279416667506663545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162027411777780017769453 810760279416667506663545)
                    ·
                      rfl

theorem cell22_2368425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_2368425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368425 prefixEnd_2368425 := by exact prefixLift 2368425
  have htrace : WordTrace (prefixWord ++ tailWord_2368425) baseStart_2368425 baseEnd_2368425 := by
    simpa [prefixWord, tailWord_2368425, baseEnd_2368425] using wordTrace_append hprefix tailTrace_2368425
  have hstable : (prefixWord ++ tailWord_2368425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368425).length < 2 ^ (prefixWord ++ tailWord_2368425).sum := by decide
  have hdescent : baseEnd_2368425 < baseStart_2368425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368455 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 5]
def baseStart_2368455 : Nat := 118140960795 + 2368455 * 2 ^ 59
def prefixEnd_2368455 : Nat := 4983230072969 + 3 ^ 40 * 2368455 * 2
def baseEnd_2368455 : Nat := 270256849676585809471151

theorem tailTrace_2368455 : CollatzResearch.WordTrace tailWord_2368455 prefixEnd_2368455 270256849676585809471151 := by
  unfold tailWord_2368455
  simp only [CollatzResearch.WordTrace]
  refine ⟨86384650634499509755226819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57589767089666339836817879 86384650634499509755226819)
  ·
    refine ⟨129576975951749264632840229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86384650634499509755226819 129576975951749264632840229)
    ·
      refine ⟨24295682990952987118657543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129576975951749264632840229 24295682990952987118657543)
      ·
        refine ⟨36443524486429480677986315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24295682990952987118657543 36443524486429480677986315)
        ·
          refine ⟨54665286729644221016979473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36443524486429480677986315 54665286729644221016979473)
          ·
            refine ⟨40998965047233165762734605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54665286729644221016979473 40998965047233165762734605)
            ·
              refine ⟨15374611892712437161025477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40998965047233165762734605 15374611892712437161025477)
              ·
                refine ⟨2882739729883581967692277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15374611892712437161025477 2882739729883581967692277)
                ·
                  refine ⟨270256849676585809471151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2882739729883581967692277 270256849676585809471151)
                  ·
                    rfl

theorem cell22_2368455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 5].length) (baseStart_2368455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368455 prefixEnd_2368455 := by exact prefixLift 2368455
  have htrace : WordTrace (prefixWord ++ tailWord_2368455) baseStart_2368455 baseEnd_2368455 := by
    simpa [prefixWord, tailWord_2368455, baseEnd_2368455] using wordTrace_append hprefix tailTrace_2368455
  have hstable : (prefixWord ++ tailWord_2368455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368455).length < 2 ^ (prefixWord ++ tailWord_2368455).sum := by decide
  have hdescent : baseEnd_2368455 < baseStart_2368455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368459 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 1, 3]
def baseStart_2368459 : Nat := 118140960795 + 2368459 * 2 ^ 59
def prefixEnd_2368459 : Nat := 4983230072969 + 3 ^ 40 * 2368459 * 2
def baseEnd_2368459 : Nat := 810771918311502751313441

theorem tailTrace_2368459 : CollatzResearch.WordTrace tailWord_2368459 prefixEnd_2368459 810771918311502751313441 := by
  unfold tailWord_2368459
  simp only [CollatzResearch.WordTrace]
  refine ⟨86384796526485018438372431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57589864350990012292248287 86384796526485018438372431)
  ·
    refine ⟨129577194789727527657558647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86384796526485018438372431 129577194789727527657558647)
    ·
      refine ⟨194365792184591291486337971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129577194789727527657558647 194365792184591291486337971)
      ·
        refine ⟨291548688276886937229506957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194365792184591291486337971 291548688276886937229506957)
        ·
          refine ⟨109330758103832601461065109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291548688276886937229506957 109330758103832601461065109)
          ·
            refine ⟨5124879286117153193487427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109330758103832601461065109 5124879286117153193487427)
            ·
              refine ⟨7687318929175729790231141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124879286117153193487427 7687318929175729790231141)
              ·
                refine ⟨1441372299220449335668339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7687318929175729790231141 1441372299220449335668339)
                ·
                  refine ⟨2162058448830674003502509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441372299220449335668339 2162058448830674003502509)
                  ·
                    refine ⟨810771918311502751313441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162058448830674003502509 810771918311502751313441)
                    ·
                      rfl

theorem cell22_2368459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 3].length) (baseStart_2368459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368459 prefixEnd_2368459 := by exact prefixLift 2368459
  have htrace : WordTrace (prefixWord ++ tailWord_2368459) baseStart_2368459 baseEnd_2368459 := by
    simpa [prefixWord, tailWord_2368459, baseEnd_2368459] using wordTrace_append hprefix tailTrace_2368459
  have hstable : (prefixWord ++ tailWord_2368459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368459).length < 2 ^ (prefixWord ++ tailWord_2368459).sum := by decide
  have hdescent : baseEnd_2368459 < baseStart_2368459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368517 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 4]
def baseStart_2368517 : Nat := 118140960795 + 2368517 * 2 ^ 59
def prefixEnd_2368517 : Nat := 4983230072969 + 3 ^ 40 * 2368517 * 2
def baseEnd_2368517 : Nat := 270263924298936644454421

theorem tailTrace_2368517 : CollatzResearch.WordTrace tailWord_2368517 prefixEnd_2368517 270263924298936644454421 := by
  unfold tailWord_2368517
  simp only [CollatzResearch.WordTrace]
  refine ⟨86386911960274894343983805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57591274640183262895989203 86386911960274894343983805)
  ·
    refine ⟨32395091985103085378993927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86386911960274894343983805 32395091985103085378993927)
    ·
      refine ⟨48592637977654628068490891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32395091985103085378993927 48592637977654628068490891)
      ·
        refine ⟨72888956966481942102736337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48592637977654628068490891 72888956966481942102736337)
        ·
          refine ⟨54666717724861456577052253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72888956966481942102736337 54666717724861456577052253)
          ·
            refine ⟨20500019146823046216394595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54666717724861456577052253 20500019146823046216394595)
            ·
              refine ⟨30750028720234569324591893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20500019146823046216394595 30750028720234569324591893)
              ·
                refine ⟨1441407596260995437090245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30750028720234569324591893 1441407596260995437090245)
                ·
                  refine ⟨270263924298936644454421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441407596260995437090245 270263924298936644454421)
                  ·
                    rfl

theorem cell22_2368517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_2368517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368517 prefixEnd_2368517 := by exact prefixLift 2368517
  have htrace : WordTrace (prefixWord ++ tailWord_2368517) baseStart_2368517 baseEnd_2368517 := by
    simpa [prefixWord, tailWord_2368517, baseEnd_2368517] using wordTrace_append hprefix tailTrace_2368517
  have hstable : (prefixWord ++ tailWord_2368517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368517).length < 2 ^ (prefixWord ++ tailWord_2368517).sum := by decide
  have hdescent : baseEnd_2368517 < baseStart_2368517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368551 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 4]
def baseStart_2368551 : Nat := 118140960795 + 2368551 * 2 ^ 59
def prefixEnd_2368551 : Nat := 4983230072969 + 3 ^ 40 * 2368551 * 2
def baseEnd_2368551 : Nat := 270267803930548392671053

theorem tailTrace_2368551 : CollatzResearch.WordTrace tailWord_2368551 prefixEnd_2368551 270267803930548392671053 := by
  unfold tailWord_2368551
  simp only [CollatzResearch.WordTrace]
  refine ⟨86388152042151718150721507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57592101361434478767147671 86388152042151718150721507)
  ·
    refine ⟨129582228063227577226082261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86388152042151718150721507 129582228063227577226082261)
    ·
      refine ⟨3037083470231896341236303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 129582228063227577226082261 3037083470231896341236303)
      ·
        refine ⟨4555625205347844511854455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037083470231896341236303 4555625205347844511854455)
        ·
          refine ⟨6833437808021766767781683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555625205347844511854455 6833437808021766767781683)
          ·
            refine ⟨10250156712032650151672525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833437808021766767781683 10250156712032650151672525)
            ·
              refine ⟨3843808767012243806877197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10250156712032650151672525 3843808767012243806877197)
              ·
                refine ⟨1441428287629591427578949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3843808767012243806877197 1441428287629591427578949)
                ·
                  refine ⟨270267803930548392671053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441428287629591427578949 270267803930548392671053)
                  ·
                    rfl

theorem cell22_2368551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 4].length) (baseStart_2368551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368551 prefixEnd_2368551 := by exact prefixLift 2368551
  have htrace : WordTrace (prefixWord ++ tailWord_2368551) baseStart_2368551 baseEnd_2368551 := by
    simpa [prefixWord, tailWord_2368551, baseEnd_2368551] using wordTrace_append hprefix tailTrace_2368551
  have hstable : (prefixWord ++ tailWord_2368551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368551).length < 2 ^ (prefixWord ++ tailWord_2368551).sum := by decide
  have hdescent : baseEnd_2368551 < baseStart_2368551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368564 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2368564 : Nat := 118140960795 + 2368564 * 2 ^ 59
def prefixEnd_2368564 : Nat := 4983230072969 + 3 ^ 40 * 2368564 * 2
def baseEnd_2368564 : Nat := 810807861957317477438119

theorem tailTrace_2368564 : CollatzResearch.WordTrace tailWord_2368564 prefixEnd_2368564 810807861957317477438119 := by
  unfold tailWord_2368564
  simp only [CollatzResearch.WordTrace]
  refine ⟨43194313095552310685472373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57592417460736414247296497 43194313095552310685472373)
  ·
    refine ⟨4049466852708029126763035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43194313095552310685472373 4049466852708029126763035)
    ·
      refine ⟨6074200279062043690144553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049466852708029126763035 6074200279062043690144553)
      ·
        refine ⟨4555650209296532767608415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6074200279062043690144553 4555650209296532767608415)
        ·
          refine ⟨6833475313944799151412623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555650209296532767608415 6833475313944799151412623)
          ·
            refine ⟨10250212970917198727118935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833475313944799151412623 10250212970917198727118935)
            ·
              refine ⟨15375319456375798090678403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10250212970917198727118935 15375319456375798090678403)
              ·
                refine ⟨23062979184563697136017605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15375319456375798090678403 23062979184563697136017605)
                ·
                  refine ⟨4324308597105693213003301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23062979184563697136017605 4324308597105693213003301)
                  ·
                    refine ⟨810807861957317477438119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324308597105693213003301 810807861957317477438119)
                    ·
                      rfl

theorem cell22_2368564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2368564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368564 prefixEnd_2368564 := by exact prefixLift 2368564
  have htrace : WordTrace (prefixWord ++ tailWord_2368564) baseStart_2368564 baseEnd_2368564 := by
    simpa [prefixWord, tailWord_2368564, baseEnd_2368564] using wordTrace_append hprefix tailTrace_2368564
  have hstable : (prefixWord ++ tailWord_2368564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368564).length < 2 ^ (prefixWord ++ tailWord_2368564).sum := by decide
  have hdescent : baseEnd_2368564 < baseStart_2368564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368575 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_2368575 : Nat := 118140960795 + 2368575 * 2 ^ 59
def prefixEnd_2368575 : Nat := 4983230072969 + 3 ^ 40 * 2368575 * 2
def baseEnd_2368575 : Nat := 810811627482117115413085

theorem tailTrace_2368575 : CollatzResearch.WordTrace tailWord_2368575 prefixEnd_2368575 810811627482117115413085 := by
  unfold tailWord_2368575
  simp only [CollatzResearch.WordTrace]
  refine ⟨86389027394064770249595179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57592684929376513499730119 86389027394064770249595179)
  ·
    refine ⟨129583541091097155374392769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86389027394064770249595179 129583541091097155374392769)
    ·
      refine ⟨97187655818322866530794577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129583541091097155374392769 97187655818322866530794577)
      ·
        refine ⟨72890741863742149898095933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97187655818322866530794577 72890741863742149898095933)
        ·
          refine ⟨27334028198903306211785975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72890741863742149898095933 27334028198903306211785975)
          ·
            refine ⟨41001042298354959317678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27334028198903306211785975 41001042298354959317678963)
            ·
              refine ⟨61501563447532438976518445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41001042298354959317678963 61501563447532438976518445)
              ·
                refine ⟨23063086292824664616194417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61501563447532438976518445 23063086292824664616194417)
                ·
                  refine ⟨17297314719618498462145813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23063086292824664616194417 17297314719618498462145813)
                  ·
                    refine ⟨810811627482117115413085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17297314719618498462145813 810811627482117115413085)
                    ·
                      rfl

theorem cell22_2368575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_2368575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368575 prefixEnd_2368575 := by exact prefixLift 2368575
  have htrace : WordTrace (prefixWord ++ tailWord_2368575) baseStart_2368575 baseEnd_2368575 := by
    simpa [prefixWord, tailWord_2368575, baseEnd_2368575] using wordTrace_append hprefix tailTrace_2368575
  have hstable : (prefixWord ++ tailWord_2368575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368575).length < 2 ^ (prefixWord ++ tailWord_2368575).sum := by decide
  have hdescent : baseEnd_2368575 < baseStart_2368575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368598 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2368598 : Nat := 118140960795 + 2368598 * 2 ^ 59
def prefixEnd_2368598 : Nat := 4983230072969 + 3 ^ 40 * 2368598 * 2
def baseEnd_2368598 : Nat := 810819500852152722088015

theorem tailTrace_2368598 : CollatzResearch.WordTrace tailWord_2368598 prefixEnd_2368598 810819500852152722088015 := by
  unfold tailWord_2368598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399366642061340323605153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57593244181987630118454965 5399366642061340323605153)
  ·
    refine ⟨4049524981546005242703865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5399366642061340323605153 4049524981546005242703865)
    ·
      refine ⟨3037143736159503932027899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4049524981546005242703865 3037143736159503932027899)
      ·
        refine ⟨4555715604239255898041849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037143736159503932027899 4555715604239255898041849)
        ·
          refine ⟨3416786703179441923531387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4555715604239255898041849 3416786703179441923531387)
          ·
            refine ⟨5125180054769162885297081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416786703179441923531387 5125180054769162885297081)
            ·
              refine ⟨3843885041076872163972811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5125180054769162885297081 3843885041076872163972811)
              ·
                refine ⟨5765827561615308245959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3843885041076872163972811 5765827561615308245959217)
                ·
                  refine ⟨4324370671211481184469413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5765827561615308245959217 4324370671211481184469413)
                  ·
                    refine ⟨810819500852152722088015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324370671211481184469413 810819500852152722088015)
                    ·
                      rfl

theorem cell22_2368598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2368598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368598 prefixEnd_2368598 := by exact prefixLift 2368598
  have htrace : WordTrace (prefixWord ++ tailWord_2368598) baseStart_2368598 baseEnd_2368598 := by
    simpa [prefixWord, tailWord_2368598, baseEnd_2368598] using wordTrace_append hprefix tailTrace_2368598
  have hstable : (prefixWord ++ tailWord_2368598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368598).length < 2 ^ (prefixWord ++ tailWord_2368598).sum := by decide
  have hdescent : baseEnd_2368598 < baseStart_2368598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368635 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 10]
def baseStart_2368635 : Nat := 118140960795 + 2368635 * 2 ^ 59
def prefixEnd_2368635 : Nat := 4983230072969 + 3 ^ 40 * 2368635 * 2
def baseEnd_2368635 : Nat := 270277388902765652970967

theorem tailTrace_2368635 : CollatzResearch.WordTrace tailWord_2368635 prefixEnd_2368635 270277388902765652970967 := by
  unfold tailWord_2368635
  simp only [CollatzResearch.WordTrace]
  refine ⟨86391215773847400496779359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57594143849231600331186239 86391215773847400496779359)
  ·
    refine ⟨129586823660771100745169039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86391215773847400496779359 129586823660771100745169039)
    ·
      refine ⟨194380235491156651117753559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129586823660771100745169039 194380235491156651117753559)
      ·
        refine ⟨291570353236734976676630339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194380235491156651117753559 291570353236734976676630339)
        ·
          refine ⟨437355529855102465014945509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291570353236734976676630339 437355529855102465014945509)
          ·
            refine ⟨82004161847831712190302283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437355529855102465014945509 82004161847831712190302283)
            ·
              refine ⟨123006242771747568285453425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82004161847831712190302283 123006242771747568285453425)
              ·
                refine ⟨92254682078810676214090069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123006242771747568285453425 92254682078810676214090069)
                ·
                  refine ⟨270277388902765652970967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92254682078810676214090069 270277388902765652970967)
                  ·
                    rfl

theorem cell22_2368635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_2368635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368635 prefixEnd_2368635 := by exact prefixLift 2368635
  have htrace : WordTrace (prefixWord ++ tailWord_2368635) baseStart_2368635 baseEnd_2368635 := by
    simpa [prefixWord, tailWord_2368635, baseEnd_2368635] using wordTrace_append hprefix tailTrace_2368635
  have hstable : (prefixWord ++ tailWord_2368635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368635).length < 2 ^ (prefixWord ++ tailWord_2368635).sum := by decide
  have hdescent : baseEnd_2368635 < baseStart_2368635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368637 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2368637 : Nat := 118140960795 + 2368637 * 2 ^ 59
def prefixEnd_2368637 : Nat := 4983230072969 + 3 ^ 40 * 2368637 * 2
def baseEnd_2368637 : Nat := 810832851349169620362895

theorem tailTrace_2368637 : CollatzResearch.WordTrace tailWord_2368637 prefixEnd_2368637 810832851349169620362895 := by
  unfold tailWord_2368637
  simp only [CollatzResearch.WordTrace]
  refine ⟨86391288719840154838352165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57594192479893436558901443 86391288719840154838352165)
  ·
    refine ⟨16198366634970029032191031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86391288719840154838352165 16198366634970029032191031)
    ·
      refine ⟨24297549952455043548286547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16198366634970029032191031 24297549952455043548286547)
      ·
        refine ⟨36446324928682565322429821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24297549952455043548286547 36446324928682565322429821)
        ·
          refine ⟨13667371848255961995911183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36446324928682565322429821 13667371848255961995911183)
          ·
            refine ⟨20501057772383942993866775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13667371848255961995911183 20501057772383942993866775)
            ·
              refine ⟨30751586658575914490800163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20501057772383942993866775 30751586658575914490800163)
              ·
                refine ⟨46127379987863871736200245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30751586658575914490800163 46127379987863871736200245)
                ·
                  refine ⟨4324441873862237975268773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46127379987863871736200245 4324441873862237975268773)
                  ·
                    refine ⟨810832851349169620362895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324441873862237975268773 810832851349169620362895)
                    ·
                      rfl

theorem cell22_2368637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2368637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368637 prefixEnd_2368637 := by exact prefixLift 2368637
  have htrace : WordTrace (prefixWord ++ tailWord_2368637) baseStart_2368637 baseEnd_2368637 := by
    simpa [prefixWord, tailWord_2368637, baseEnd_2368637] using wordTrace_append hprefix tailTrace_2368637
  have hstable : (prefixWord ++ tailWord_2368637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368637).length < 2 ^ (prefixWord ++ tailWord_2368637).sum := by decide
  have hdescent : baseEnd_2368637 < baseStart_2368637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368654 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2368654 : Nat := 118140960795 + 2368654 * 2 ^ 59
def prefixEnd_2368654 : Nat := 4983230072969 + 3 ^ 40 * 2368654 * 2
def baseEnd_2368654 : Nat := 810838670796587242687843

theorem tailTrace_2368654 : CollatzResearch.WordTrace tailWord_2368654 prefixEnd_2368654 810838670796587242687843 := by
  unfold tailWord_2368654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10798988595097320842715127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57594605840519044494480677 10798988595097320842715127)
  ·
    refine ⟨16198482892645981264072691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10798988595097320842715127 16198482892645981264072691)
    ·
      refine ⟨24297724338968971896109037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16198482892645981264072691 24297724338968971896109037)
      ·
        refine ⟨9111646627113364461040889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24297724338968971896109037 9111646627113364461040889)
        ·
          refine ⟨6833734970335023345780667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9111646627113364461040889 6833734970335023345780667)
          ·
            refine ⟨10250602455502535018671001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833734970335023345780667 10250602455502535018671001)
            ·
              refine ⟨7687951841626901264003251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10250602455502535018671001 7687951841626901264003251)
              ·
                refine ⟨11531927762440351896004877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687951841626901264003251 11531927762440351896004877)
                ·
                  refine ⟨4324472910915131961001829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11531927762440351896004877 4324472910915131961001829)
                  ·
                    refine ⟨810838670796587242687843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324472910915131961001829 810838670796587242687843)
                    ·
                      rfl

theorem cell22_2368654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2368654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368654 prefixEnd_2368654 := by exact prefixLift 2368654
  have htrace : WordTrace (prefixWord ++ tailWord_2368654) baseStart_2368654 baseEnd_2368654 := by
    simpa [prefixWord, tailWord_2368654, baseEnd_2368654] using wordTrace_append hprefix tailTrace_2368654
  have hstable : (prefixWord ++ tailWord_2368654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368654).length < 2 ^ (prefixWord ++ tailWord_2368654).sum := by decide
  have hdescent : baseEnd_2368654 < baseStart_2368654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368671 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 1, 4]
def baseStart_2368671 : Nat := 118140960795 + 2368671 * 2 ^ 59
def prefixEnd_2368671 : Nat := 4983230072969 + 3 ^ 40 * 2368671 * 2
def baseEnd_2368671 : Nat := 810844490244004865012791

theorem tailTrace_2368671 : CollatzResearch.WordTrace tailWord_2368671 prefixEnd_2368671 810844490244004865012791 := by
  unfold tailWord_2368671
  simp only [CollatzResearch.WordTrace]
  refine ⟨86392528801716978645089867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57595019201144652430059911 86392528801716978645089867)
  ·
    refine ⟨129588793202575467967634801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86392528801716978645089867 129588793202575467967634801)
    ·
      refine ⟨97191594901931600975726101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129588793202575467967634801 97191594901931600975726101)
      ·
        refine ⟨4555856011028043795737161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97191594901931600975726101 4555856011028043795737161)
        ·
          refine ⟨3416892008271032846802871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4555856011028043795737161 3416892008271032846802871)
          ·
            refine ⟨5125338012406549270204307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416892008271032846802871 5125338012406549270204307)
            ·
              refine ⟨7688007018609823905306461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125338012406549270204307 7688007018609823905306461)
              ·
                refine ⟨2883002631978683964489923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7688007018609823905306461 2883002631978683964489923)
                ·
                  refine ⟨4324503947968025946734885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883002631978683964489923 4324503947968025946734885)
                  ·
                    refine ⟨810844490244004865012791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324503947968025946734885 810844490244004865012791)
                    ·
                      rfl

theorem cell22_2368671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_2368671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368671 prefixEnd_2368671 := by exact prefixLift 2368671
  have htrace : WordTrace (prefixWord ++ tailWord_2368671) baseStart_2368671 baseEnd_2368671 := by
    simpa [prefixWord, tailWord_2368671, baseEnd_2368671] using wordTrace_append hprefix tailTrace_2368671
  have hstable : (prefixWord ++ tailWord_2368671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368671).length < 2 ^ (prefixWord ++ tailWord_2368671).sum := by decide
  have hdescent : baseEnd_2368671 < baseStart_2368671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368684 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_2368684 : Nat := 118140960795 + 2368684 * 2 ^ 59
def prefixEnd_2368684 : Nat := 4983230072969 + 3 ^ 40 * 2368684 * 2
def baseEnd_2368684 : Nat := 810848940409677164437751

theorem tailTrace_2368684 : CollatzResearch.WordTrace tailWord_2368684 prefixEnd_2368684 810848940409677164437751 := by
  unfold tailWord_2368684
  simp only [CollatzResearch.WordTrace]
  refine ⟨43196501475334940932656553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57595335300446587910208737 43196501475334940932656553)
  ·
    refine ⟨32397376106501205699492415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43196501475334940932656553 32397376106501205699492415)
    ·
      refine ⟨48596064159751808549238623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32397376106501205699492415 48596064159751808549238623)
      ·
        refine ⟨72894096239627712823857935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48596064159751808549238623 72894096239627712823857935)
        ·
          refine ⟨109341144359441569235786903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72894096239627712823857935 109341144359441569235786903)
          ·
            refine ⟨164011716539162353853680355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109341144359441569235786903 164011716539162353853680355)
            ·
              refine ⟨246017574808743530780520533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164011716539162353853680355 246017574808743530780520533)
              ·
                refine ⟨2883018454789963251334225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 246017574808743530780520533 2883018454789963251334225)
                ·
                  refine ⟨2162263841092472438500669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2883018454789963251334225 2162263841092472438500669)
                  ·
                    refine ⟨810848940409677164437751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162263841092472438500669 810848940409677164437751)
                    ·
                      rfl

theorem cell22_2368684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_2368684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368684 prefixEnd_2368684 := by exact prefixLift 2368684
  have htrace : WordTrace (prefixWord ++ tailWord_2368684) baseStart_2368684 baseEnd_2368684 := by
    simpa [prefixWord, tailWord_2368684, baseEnd_2368684] using wordTrace_append hprefix tailTrace_2368684
  have hstable : (prefixWord ++ tailWord_2368684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368684).length < 2 ^ (prefixWord ++ tailWord_2368684).sum := by decide
  have hdescent : baseEnd_2368684 < baseStart_2368684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368714 : List Nat := [3, 1, 2, 1, 3, 2, 4, 6]
def baseStart_2368714 : Nat := 118140960795 + 2368714 * 2 ^ 59
def prefixEnd_2368714 : Nat := 4983230072969 + 3 ^ 40 * 2368714 * 2
def baseEnd_2368714 : Nat := 90095467780307454020851

theorem tailTrace_2368714 : CollatzResearch.WordTrace tailWord_2368714 prefixEnd_2368714 90095467780307454020851 := by
  unfold tailWord_2368714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21598524285140299247226299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57596064760374131325936797 21598524285140299247226299)
  ·
    refine ⟨32397786427710448870839449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21598524285140299247226299 32397786427710448870839449)
    ·
      refine ⟨24298339820782836653129587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32397786427710448870839449 24298339820782836653129587)
      ·
        refine ⟨36447509731174254979694381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24298339820782836653129587 36447509731174254979694381)
        ·
          refine ⟨13667816149190345617385393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36447509731174254979694381 13667816149190345617385393)
          ·
            refine ⟨10250862111892759213039045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13667816149190345617385393 10250862111892759213039045)
            ·
              refine ⟨1922036645979892352444821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10250862111892759213039045 1922036645979892352444821)
              ·
                refine ⟨90095467780307454020851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1922036645979892352444821 90095467780307454020851)
                ·
                  rfl

theorem cell22_2368714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_2368714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368714 prefixEnd_2368714 := by exact prefixLift 2368714
  have htrace : WordTrace (prefixWord ++ tailWord_2368714) baseStart_2368714 baseEnd_2368714 := by
    simpa [prefixWord, tailWord_2368714, baseEnd_2368714] using wordTrace_append hprefix tailTrace_2368714
  have hstable : (prefixWord ++ tailWord_2368714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368714).length < 2 ^ (prefixWord ++ tailWord_2368714).sum := by decide
  have hdescent : baseEnd_2368714 < baseStart_2368714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368746 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2368746 : Nat := 118140960795 + 2368746 * 2 ^ 59
def prefixEnd_2368746 : Nat := 4983230072969 + 3 ^ 40 * 2368746 * 2
def baseEnd_2368746 : Nat := 810870164276729669387561

theorem tailTrace_2368746 : CollatzResearch.WordTrace tailWord_2368746 prefixEnd_2368746 810870164276729669387561 := by
  unfold tailWord_2368746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21598816069111316613517523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57596842850963510969380061 21598816069111316613517523)
  ·
    refine ⟨32398224103666974920276285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21598816069111316613517523 32398224103666974920276285)
    ·
      refine ⟨12149334038875115595103607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32398224103666974920276285 12149334038875115595103607)
      ·
        refine ⟨18224001058312673392655411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12149334038875115595103607 18224001058312673392655411)
        ·
          refine ⟨27336001587469010088983117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18224001058312673392655411 27336001587469010088983117)
          ·
            refine ⟨10251000595300878783368669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27336001587469010088983117 10251000595300878783368669)
            ·
              refine ⟨3844125223237829543763251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10251000595300878783368669 3844125223237829543763251)
              ·
                refine ⟨5766187834856744315644877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844125223237829543763251 5766187834856744315644877)
                ·
                  refine ⟨2162320438071279118366829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5766187834856744315644877 2162320438071279118366829)
                  ·
                    refine ⟨810870164276729669387561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162320438071279118366829 810870164276729669387561)
                    ·
                      rfl

theorem cell22_2368746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2368746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368746 prefixEnd_2368746 := by exact prefixLift 2368746
  have htrace : WordTrace (prefixWord ++ tailWord_2368746) baseStart_2368746 baseEnd_2368746 := by
    simpa [prefixWord, tailWord_2368746, baseEnd_2368746] using wordTrace_append hprefix tailTrace_2368746
  have hstable : (prefixWord ++ tailWord_2368746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368746).length < 2 ^ (prefixWord ++ tailWord_2368746).sum := by decide
  have hdescent : baseEnd_2368746 < baseStart_2368746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368797 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2368797 : Nat := 118140960795 + 2368797 * 2 ^ 59
def prefixEnd_2368797 : Nat := 4983230072969 + 3 ^ 40 * 2368797 * 2
def baseEnd_2368797 : Nat := 810887622618982536362405

theorem tailTrace_2368797 : CollatzResearch.WordTrace tailWord_2368797 prefixEnd_2368797 810887622618982536362405 := by
  unfold tailWord_2368797
  simp only [CollatzResearch.WordTrace]
  refine ⟨86397124399260502164176645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57598082932840334776117763 86397124399260502164176645)
  ·
    refine ⟨16199460824861344155783121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86397124399260502164176645 16199460824861344155783121)
    ·
      refine ⟨12149595618646008116837341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16199460824861344155783121 12149595618646008116837341)
      ·
        refine ⟨4556098356992253043814003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12149595618646008116837341 4556098356992253043814003)
        ·
          refine ⟨6834147535488379565721005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556098356992253043814003 6834147535488379565721005)
          ·
            refine ⟨2562805325808142337145377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6834147535488379565721005 2562805325808142337145377)
            ·
              refine ⟨1922103994356106752859033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562805325808142337145377 1922103994356106752859033)
              ·
                refine ⟨1441577995767080064644275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922103994356106752859033 1441577995767080064644275)
                ·
                  refine ⟨2162366993650620096966413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441577995767080064644275 2162366993650620096966413)
                  ·
                    refine ⟨810887622618982536362405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162366993650620096966413 810887622618982536362405)
                    ·
                      rfl

theorem cell22_2368797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2368797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368797 prefixEnd_2368797 := by exact prefixLift 2368797
  have htrace : WordTrace (prefixWord ++ tailWord_2368797) baseStart_2368797 baseEnd_2368797 := by
    simpa [prefixWord, tailWord_2368797, baseEnd_2368797] using wordTrace_append hprefix tailTrace_2368797
  have hstable : (prefixWord ++ tailWord_2368797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368797).length < 2 ^ (prefixWord ++ tailWord_2368797).sum := by decide
  have hdescent : baseEnd_2368797 < baseStart_2368797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368804 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_2368804 : Nat := 118140960795 + 2368804 * 2 ^ 59
def prefixEnd_2368804 : Nat := 4983230072969 + 3 ^ 40 * 2368804 * 2
def baseEnd_2368804 : Nat := 270296672954012283812461

theorem tailTrace_2368804 : CollatzResearch.WordTrace tailWord_2368804 prefixEnd_2368804 270296672954012283812461 := by
  unfold tailWord_2368804
  simp only [CollatzResearch.WordTrace]
  refine ⟨43198689855117571179840733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57598253140156761573120977 43198689855117571179840733)
  ·
    refine ⟨16199508695669089192440275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43198689855117571179840733 16199508695669089192440275)
    ·
      refine ⟨24299263043503633788660413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16199508695669089192440275 24299263043503633788660413)
      ·
        refine ⟨9112223641313862670747655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24299263043503633788660413 9112223641313862670747655)
        ·
          refine ⟨13668335461970794006121483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9112223641313862670747655 13668335461970794006121483)
          ·
            refine ⟨20502503192956191009182225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13668335461970794006121483 20502503192956191009182225)
            ·
              refine ⟨15376877394717143256886669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20502503192956191009182225 15376877394717143256886669)
              ·
                refine ⟨5766329023018928721332501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15376877394717143256886669 5766329023018928721332501)
                ·
                  refine ⟨270296672954012283812461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5766329023018928721332501 270296672954012283812461)
                  ·
                    rfl

theorem cell22_2368804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_2368804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368804 prefixEnd_2368804 := by exact prefixLift 2368804
  have htrace : WordTrace (prefixWord ++ tailWord_2368804) baseStart_2368804 baseEnd_2368804 := by
    simpa [prefixWord, tailWord_2368804, baseEnd_2368804] using wordTrace_append hprefix tailTrace_2368804
  have hstable : (prefixWord ++ tailWord_2368804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368804).length < 2 ^ (prefixWord ++ tailWord_2368804).sum := by decide
  have hdescent : baseEnd_2368804 < baseStart_2368804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368819 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_2368819 : Nat := 118140960795 + 2368819 * 2 ^ 59
def prefixEnd_2368819 : Nat := 4983230072969 + 3 ^ 40 * 2368819 * 2
def baseEnd_2368819 : Nat := 810895153668581812312337

theorem tailTrace_2368819 : CollatzResearch.WordTrace tailWord_2368819 prefixEnd_2368819 810895153668581812312337 := by
  unfold tailWord_2368819
  simp only [CollatzResearch.WordTrace]
  refine ⟨86397926805180799921477511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57598617870120533280985007 86397926805180799921477511)
  ·
    refine ⟨129596890207771199882216267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86397926805180799921477511 129596890207771199882216267)
    ·
      refine ⟨194395335311656799823324401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129596890207771199882216267 194395335311656799823324401)
      ·
        refine ⟨145796501483742599867493301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194395335311656799823324401 145796501483742599867493301)
        ·
          refine ⟨13668422014100868737577497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145796501483742599867493301 13668422014100868737577497)
          ·
            refine ⟨10251316510575651553183123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13668422014100868737577497 10251316510575651553183123)
            ·
              refine ⟨15376974765863477329774685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251316510575651553183123 15376974765863477329774685)
              ·
                refine ⟨5766365537198803998665507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15376974765863477329774685 5766365537198803998665507)
                ·
                  refine ⟨8649548305798205997998261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766365537198803998665507 8649548305798205997998261)
                  ·
                    refine ⟨810895153668581812312337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8649548305798205997998261 810895153668581812312337)
                    ·
                      rfl

theorem cell22_2368819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_2368819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368819 prefixEnd_2368819 := by exact prefixLift 2368819
  have htrace : WordTrace (prefixWord ++ tailWord_2368819) baseStart_2368819 baseEnd_2368819 := by
    simpa [prefixWord, tailWord_2368819, baseEnd_2368819] using wordTrace_append hprefix tailTrace_2368819
  have hstable : (prefixWord ++ tailWord_2368819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368819).length < 2 ^ (prefixWord ++ tailWord_2368819).sum := by decide
  have hdescent : baseEnd_2368819 < baseStart_2368819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368853 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2368853 : Nat := 118140960795 + 2368853 * 2 ^ 59
def prefixEnd_2368853 : Nat := 4983230072969 + 3 ^ 40 * 2368853 * 2
def baseEnd_2368853 : Nat := 810906792563417056962233

theorem tailTrace_2368853 : CollatzResearch.WordTrace tailWord_2368853 prefixEnd_2368853 810906792563417056962233 := by
  unfold tailWord_2368853
  simp only [CollatzResearch.WordTrace]
  refine ⟨86399166887057623728215213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57599444591371749152143475 86399166887057623728215213)
  ·
    refine ⟨32399687582646608898080705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86399166887057623728215213 32399687582646608898080705)
    ·
      refine ⟨24299765686984956673560529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32399687582646608898080705 24299765686984956673560529)
      ·
        refine ⟨18224824265238717505170397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24299765686984956673560529 18224824265238717505170397)
        ·
          refine ⟨6834309099464519064438899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18224824265238717505170397 6834309099464519064438899)
          ·
            refine ⟨10251463649196778596658349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834309099464519064438899 10251463649196778596658349)
            ·
              refine ⟨3844298868448791973746881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10251463649196778596658349 3844298868448791973746881)
              ·
                refine ⟨2883224151336593980310161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844298868448791973746881 2883224151336593980310161)
                ·
                  refine ⟨2162418113502445485232621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2883224151336593980310161 2162418113502445485232621)
                  ·
                    refine ⟨810906792563417056962233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162418113502445485232621 810906792563417056962233)
                    ·
                      rfl

theorem cell22_2368853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2368853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368853 prefixEnd_2368853 := by exact prefixLift 2368853
  have htrace : WordTrace (prefixWord ++ tailWord_2368853) baseStart_2368853 baseEnd_2368853 := by
    simpa [prefixWord, tailWord_2368853, baseEnd_2368853] using wordTrace_append hprefix tailTrace_2368853
  have hstable : (prefixWord ++ tailWord_2368853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368853).length < 2 ^ (prefixWord ++ tailWord_2368853).sum := by decide
  have hdescent : baseEnd_2368853 < baseStart_2368853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368881 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2368881 : Nat := 118140960795 + 2368881 * 2 ^ 59
def prefixEnd_2368881 : Nat := 4983230072969 + 3 ^ 40 * 2368881 * 2
def baseEnd_2368881 : Nat := 810916377535634317262147

theorem tailTrace_2368881 : CollatzResearch.WordTrace tailWord_2368881 prefixEnd_2368881 810916377535634317262147 := by
  unfold tailWord_2368881
  simp only [CollatzResearch.WordTrace]
  refine ⟨86400188130956184510234497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57600125420637456340156331 86400188130956184510234497)
  ·
    refine ⟨64800141098217138382675873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86400188130956184510234497 64800141098217138382675873)
    ·
      refine ⟨48600105823662853787006905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64800141098217138382675873 48600105823662853787006905)
      ·
        refine ⟨36450079367747140340255179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48600105823662853787006905 36450079367747140340255179)
        ·
          refine ⟨54675119051620710510382769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36450079367747140340255179 54675119051620710510382769)
          ·
            refine ⟨41006339288715532882787077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54675119051620710510382769 41006339288715532882787077)
            ·
              refine ⟨7688688616634162415522577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41006339288715532882787077 7688688616634162415522577)
              ·
                refine ⟨5766516462475621811641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7688688616634162415522577 5766516462475621811641933)
                ·
                  refine ⟨2162443673428358179365725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5766516462475621811641933 2162443673428358179365725)
                  ·
                    refine ⟨810916377535634317262147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162443673428358179365725 810916377535634317262147)
                    ·
                      rfl

theorem cell22_2368881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2368881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368881 prefixEnd_2368881 := by exact prefixLift 2368881
  have htrace : WordTrace (prefixWord ++ tailWord_2368881) baseStart_2368881 baseEnd_2368881 := by
    simpa [prefixWord, tailWord_2368881, baseEnd_2368881] using wordTrace_append hprefix tailTrace_2368881
  have hstable : (prefixWord ++ tailWord_2368881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368881).length < 2 ^ (prefixWord ++ tailWord_2368881).sum := by decide
  have hdescent : baseEnd_2368881 < baseStart_2368881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368969 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_2368969 : Nat := 118140960795 + 2368969 * 2 ^ 59
def prefixEnd_2368969 : Nat := 4983230072969 + 3 ^ 40 * 2368969 * 2
def baseEnd_2368969 : Nat := 810946501734031421061877

theorem tailTrace_2368969 : CollatzResearch.WordTrace tailWord_2368969 prefixEnd_2368969 810946501734031421061877 := by
  unfold tailWord_2368969
  simp only [CollatzResearch.WordTrace]
  refine ⟨86403397754637375539437961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57602265169758250359625307 86403397754637375539437961)
  ·
    refine ⟨64802548315978031654578471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86403397754637375539437961 64802548315978031654578471)
    ·
      refine ⟨97203822473967047481867707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64802548315978031654578471 97203822473967047481867707)
      ·
        refine ⟨145805733710950571222801561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97203822473967047481867707 145805733710950571222801561)
        ·
          refine ⟨109354300283212928417101171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145805733710950571222801561 109354300283212928417101171)
          ·
            refine ⟨164031450424819392625651757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109354300283212928417101171 164031450424819392625651757)
            ·
              refine ⟨61511793909307272234619409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164031450424819392625651757 61511793909307272234619409)
              ·
                refine ⟨46133845431980454175964557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61511793909307272234619409 46133845431980454175964557)
                ·
                  refine ⟨17300192036992670315986709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46133845431980454175964557 17300192036992670315986709)
                  ·
                    refine ⟨810946501734031421061877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17300192036992670315986709 810946501734031421061877)
                    ·
                      rfl

theorem cell22_2368969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_2368969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368969 prefixEnd_2368969 := by exact prefixLift 2368969
  have htrace : WordTrace (prefixWord ++ tailWord_2368969) baseStart_2368969 baseEnd_2368969 := by
    simpa [prefixWord, tailWord_2368969, baseEnd_2368969] using wordTrace_append hprefix tailTrace_2368969
  have hstable : (prefixWord ++ tailWord_2368969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368969).length < 2 ^ (prefixWord ++ tailWord_2368969).sum := by decide
  have hdescent : baseEnd_2368969 < baseStart_2368969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368971 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 4, 3]
def baseStart_2368971 : Nat := 118140960795 + 2368971 * 2 ^ 59
def prefixEnd_2368971 : Nat := 4983230072969 + 3 ^ 40 * 2368971 * 2
def baseEnd_2368971 : Nat := 810947186374904082511871

theorem tailTrace_2368971 : CollatzResearch.WordTrace tailWord_2368971 prefixEnd_2368971 810947186374904082511871 := by
  unfold tailWord_2368971
  simp only [CollatzResearch.WordTrace]
  refine ⟨86403470700630129881010767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57602313800420086587340511 86403470700630129881010767)
  ·
    refine ⟨129605206050945194821516151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86403470700630129881010767 129605206050945194821516151)
    ·
      refine ⟨194407809076417792232274227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129605206050945194821516151 194407809076417792232274227)
      ·
        refine ⟨291611713614626688348411341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194407809076417792232274227 291611713614626688348411341)
        ·
          refine ⟨109354392605485008130654253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291611713614626688348411341 109354392605485008130654253)
          ·
            refine ⟨41007897227056878048995345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109354392605485008130654253 41007897227056878048995345)
            ·
              refine ⟨30755922920292658536746509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41007897227056878048995345 30755922920292658536746509)
              ·
                refine ⟨11533471095109746951279941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30755922920292658536746509 11533471095109746951279941)
                ·
                  refine ⟨2162525830333077553364989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11533471095109746951279941 2162525830333077553364989)
                  ·
                    refine ⟨810947186374904082511871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162525830333077553364989 810947186374904082511871)
                    ·
                      rfl

theorem cell22_2368971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3].length) (baseStart_2368971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2368971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2368971 prefixEnd_2368971 := by exact prefixLift 2368971
  have htrace : WordTrace (prefixWord ++ tailWord_2368971) baseStart_2368971 baseEnd_2368971 := by
    simpa [prefixWord, tailWord_2368971, baseEnd_2368971] using wordTrace_append hprefix tailTrace_2368971
  have hstable : (prefixWord ++ tailWord_2368971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368971).length < 2 ^ (prefixWord ++ tailWord_2368971).sum := by decide
  have hdescent : baseEnd_2368971 < baseStart_2368971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369022 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2369022 : Nat := 118140960795 + 2369022 * 2 ^ 59
def prefixEnd_2369022 : Nat := 4983230072969 + 3 ^ 40 * 2369022 * 2
def baseEnd_2369022 : Nat := 810964644717156949486715

theorem tailTrace_2369022 : CollatzResearch.WordTrace tailWord_2369022 prefixEnd_2369022 810964644717156949486715 := by
  unfold tailWord_2369022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800666352930670698889665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57603553882296910394078213 10800666352930670698889665)
  ·
    refine ⟨8100499764698003024167249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10800666352930670698889665 8100499764698003024167249)
    ·
      refine ⟨6075374823523502268125437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8100499764698003024167249 6075374823523502268125437)
      ·
        refine ⟨2278265558821313350547039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6075374823523502268125437 2278265558821313350547039)
        ·
          refine ⟨3417398338231970025820559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278265558821313350547039 3417398338231970025820559)
          ·
            refine ⟨5126097507347955038730839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417398338231970025820559 5126097507347955038730839)
            ·
              refine ⟨7689146261021932558096259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126097507347955038730839 7689146261021932558096259)
              ·
                refine ⟨11533719391532898837144389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689146261021932558096259 11533719391532898837144389)
                ·
                  refine ⟨2162572385912418531964573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11533719391532898837144389 2162572385912418531964573)
                  ·
                    refine ⟨810964644717156949486715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162572385912418531964573 810964644717156949486715)
                    ·
                      rfl

theorem cell22_2369022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2369022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369022 prefixEnd_2369022 := by exact prefixLift 2369022
  have htrace : WordTrace (prefixWord ++ tailWord_2369022) baseStart_2369022 baseEnd_2369022 := by
    simpa [prefixWord, tailWord_2369022, baseEnd_2369022] using wordTrace_append hprefix tailTrace_2369022
  have hstable : (prefixWord ++ tailWord_2369022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369022).length < 2 ^ (prefixWord ++ tailWord_2369022).sum := by decide
  have hdescent : baseEnd_2369022 < baseStart_2369022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369033 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_2369033 : Nat := 118140960795 + 2369033 * 2 ^ 59
def prefixEnd_2369033 : Nat := 4983230072969 + 3 ^ 40 * 2369033 * 2
def baseEnd_2369033 : Nat := 810968410241956587461681

theorem tailTrace_2369033 : CollatzResearch.WordTrace tailWord_2369033 prefixEnd_2369033 810968410241956587461681 := by
  unfold tailWord_2369033
  simp only [CollatzResearch.WordTrace]
  refine ⟨86405732026405514469767753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57603821350937009646511835 86405732026405514469767753)
  ·
    refine ⟨64804299019804135852325815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86405732026405514469767753 64804299019804135852325815)
    ·
      refine ⟨97206448529706203778488723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64804299019804135852325815 97206448529706203778488723)
      ·
        refine ⟨145809672794559305667733085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97206448529706203778488723 145809672794559305667733085)
        ·
          refine ⟨54678627297959739625399907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145809672794559305667733085 54678627297959739625399907)
          ·
            refine ⟨82017940946939609438099861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54678627297959739625399907 82017940946939609438099861)
            ·
              refine ⟨3844590981887794192410931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82017940946939609438099861 3844590981887794192410931)
              ·
                refine ⟨5766886472831691288616397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844590981887794192410931 5766886472831691288616397)
                ·
                  refine ⟨2162582427311884233231149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5766886472831691288616397 2162582427311884233231149)
                  ·
                    refine ⟨810968410241956587461681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162582427311884233231149 810968410241956587461681)
                    ·
                      rfl

theorem cell22_2369033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_2369033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369033 prefixEnd_2369033 := by exact prefixLift 2369033
  have htrace : WordTrace (prefixWord ++ tailWord_2369033) baseStart_2369033 baseEnd_2369033 := by
    simpa [prefixWord, tailWord_2369033, baseEnd_2369033] using wordTrace_append hprefix tailTrace_2369033
  have hstable : (prefixWord ++ tailWord_2369033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369033).length < 2 ^ (prefixWord ++ tailWord_2369033).sum := by decide
  have hdescent : baseEnd_2369033 < baseStart_2369033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369084 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_2369084 : Nat := 118140960795 + 2369084 * 2 ^ 59
def prefixEnd_2369084 : Nat := 4983230072969 + 3 ^ 40 * 2369084 * 2
def baseEnd_2369084 : Nat := 810985868584209454436525

theorem tailTrace_2369084 : CollatzResearch.WordTrace tailWord_2369084 prefixEnd_2369084 810985868584209454436525 := by
  unfold tailWord_2369084
  simp only [CollatzResearch.WordTrace]
  refine ⟨43203796074610375089937153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57605061432813833453249537 43203796074610375089937153)
  ·
    refine ⟨32402847055957781317452865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43203796074610375089937153 32402847055957781317452865)
    ·
      refine ⟨24302135291968335988089649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32402847055957781317452865 24302135291968335988089649)
      ·
        refine ⟨18226601468976251991067237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24302135291968335988089649 18226601468976251991067237)
        ·
          refine ⟨3417487775433047248325107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18226601468976251991067237 3417487775433047248325107)
          ·
            refine ⟨5126231663149570872487661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417487775433047248325107 5126231663149570872487661)
            ·
              refine ⟨1922336873681089077182873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5126231663149570872487661 1922336873681089077182873)
              ·
                refine ⟨1441752655260816807887155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922336873681089077182873 1441752655260816807887155)
                ·
                  refine ⟨2162628982891225211830733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441752655260816807887155 2162628982891225211830733)
                  ·
                    refine ⟨810985868584209454436525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162628982891225211830733 810985868584209454436525)
                    ·
                      rfl

theorem cell22_2369084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_2369084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369084 prefixEnd_2369084 := by exact prefixLift 2369084
  have htrace : WordTrace (prefixWord ++ tailWord_2369084) baseStart_2369084 baseEnd_2369084 := by
    simpa [prefixWord, tailWord_2369084, baseEnd_2369084] using wordTrace_append hprefix tailTrace_2369084
  have hstable : (prefixWord ++ tailWord_2369084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369084).length < 2 ^ (prefixWord ++ tailWord_2369084).sum := by decide
  have hdescent : baseEnd_2369084 < baseStart_2369084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369123 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_2369123 : Nat := 118140960795 + 2369123 * 2 ^ 59
def prefixEnd_2369123 : Nat := 4983230072969 + 3 ^ 40 * 2369123 * 2
def baseEnd_2369123 : Nat := 810999219081226352711405

theorem tailTrace_2369123 : CollatzResearch.WordTrace tailWord_2369123 prefixEnd_2369123 810999219081226352711405 := by
  unfold tailWord_2369123
  simp only [CollatzResearch.WordTrace]
  refine ⟨86409014596079459840544023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57606009730719639893696015 86409014596079459840544023)
  ·
    refine ⟨129613521894119189760816035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86409014596079459840544023 129613521894119189760816035)
    ·
      refine ⟨194420282841178784641224053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129613521894119189760816035 194420282841178784641224053)
      ·
        refine ⟨18226901516360511060114755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194420282841178784641224053 18226901516360511060114755)
        ·
          refine ⟨27340352274540766590172133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18226901516360511060114755 27340352274540766590172133)
          ·
            refine ⟨5126316051476393735657275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27340352274540766590172133 5126316051476393735657275)
            ·
              refine ⟨7689474077214590603485913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126316051476393735657275 7689474077214590603485913)
              ·
                refine ⟨5767105557910942952614435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7689474077214590603485913 5767105557910942952614435)
                ·
                  refine ⟨8650658336866414428921653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767105557910942952614435 8650658336866414428921653)
                  ·
                    refine ⟨810999219081226352711405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8650658336866414428921653 810999219081226352711405)
                    ·
                      rfl

theorem cell22_2369123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_2369123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369123 prefixEnd_2369123 := by exact prefixLift 2369123
  have htrace : WordTrace (prefixWord ++ tailWord_2369123) baseStart_2369123 baseEnd_2369123 := by
    simpa [prefixWord, tailWord_2369123, baseEnd_2369123] using wordTrace_append hprefix tailTrace_2369123
  have hstable : (prefixWord ++ tailWord_2369123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369123).length < 2 ^ (prefixWord ++ tailWord_2369123).sum := by decide
  have hdescent : baseEnd_2369123 < baseStart_2369123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369136 : List Nat := [2, 1, 1, 1, 6, 11]
def baseStart_2369136 : Nat := 118140960795 + 2369136 * 2 ^ 59
def prefixEnd_2369136 : Nat := 4983230072969 + 3 ^ 40 * 2369136 * 2
def baseEnd_2369136 : Nat := 10012390978356773483165

theorem tailTrace_2369136 : CollatzResearch.WordTrace tailWord_2369136 prefixEnd_2369136 10012390978356773483165 := by
  unfold tailWord_2369136
  simp only [CollatzResearch.WordTrace]
  refine ⟨43204744372516181530383631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57606325830021575373844841 43204744372516181530383631)
  ·
    refine ⟨64807116558774272295575447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43204744372516181530383631 64807116558774272295575447)
    ·
      refine ⟨97210674838161408443363171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64807116558774272295575447 97210674838161408443363171)
      ·
        refine ⟨145816012257242112665044757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97210674838161408443363171 145816012257242112665044757)
        ·
          refine ⟨6835125574558224031173973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145816012257242112665044757 6835125574558224031173973)
          ·
            refine ⟨10012390978356773483165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6835125574558224031173973 10012390978356773483165)
            ·
              rfl

theorem cell22_2369136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 11].length) (baseStart_2369136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369136 prefixEnd_2369136 := by exact prefixLift 2369136
  have htrace : WordTrace (prefixWord ++ tailWord_2369136) baseStart_2369136 baseEnd_2369136 := by
    simpa [prefixWord, tailWord_2369136, baseEnd_2369136] using wordTrace_append hprefix tailTrace_2369136
  have hstable : (prefixWord ++ tailWord_2369136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369136).length < 2 ^ (prefixWord ++ tailWord_2369136).sum := by decide
  have hdescent : baseEnd_2369136 < baseStart_2369136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369142 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2369142 : Nat := 118140960795 + 2369142 * 2 ^ 59
def prefixEnd_2369142 : Nat := 4983230072969 + 3 ^ 40 * 2369142 * 2
def baseEnd_2369142 : Nat := 270335241056505545495449

theorem tailTrace_2369142 : CollatzResearch.WordTrace tailWord_2369142 prefixEnd_2369142 270335241056505545495449 := by
  unfold tailWord_2369142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5400606723938164130342855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57606471722007084056990453 5400606723938164130342855)
  ·
    refine ⟨8100910085907246195514283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5400606723938164130342855 8100910085907246195514283)
    ·
      refine ⟨12151365128860869293271425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8100910085907246195514283 12151365128860869293271425)
      ·
        refine ⟨9113523846645651969953569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12151365128860869293271425 9113523846645651969953569)
        ·
          refine ⟨6835142884984238977465177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9113523846645651969953569 6835142884984238977465177)
          ·
            refine ⟨5126357163738179233098883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6835142884984238977465177 5126357163738179233098883)
            ·
              refine ⟨7689535745607268849648325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126357163738179233098883 7689535745607268849648325)
              ·
                refine ⟨1441787952301362909309061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7689535745607268849648325 1441787952301362909309061)
                ·
                  refine ⟨270335241056505545495449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441787952301362909309061 270335241056505545495449)
                  ·
                    rfl

theorem cell22_2369142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2369142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369142 prefixEnd_2369142 := by exact prefixLift 2369142
  have htrace : WordTrace (prefixWord ++ tailWord_2369142) baseStart_2369142 baseEnd_2369142 := by
    simpa [prefixWord, tailWord_2369142, baseEnd_2369142] using wordTrace_append hprefix tailTrace_2369142
  have hstable : (prefixWord ++ tailWord_2369142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369142).length < 2 ^ (prefixWord ++ tailWord_2369142).sum := by decide
  have hdescent : baseEnd_2369142 < baseStart_2369142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369153 : List Nat := [1, 2, 4, 2, 1, 2, 3, 7]
def baseStart_2369153 : Nat := 118140960795 + 2369153 * 2 ^ 59
def prefixEnd_2369153 : Nat := 4983230072969 + 3 ^ 40 * 2369153 * 2
def baseEnd_2369153 : Nat := 90112165410479586051257

theorem tailTrace_2369153 : CollatzResearch.WordTrace tailWord_2369153 prefixEnd_2369153 90112165410479586051257 := by
  unfold tailWord_2369153
  simp only [CollatzResearch.WordTrace]
  refine ⟨86410108785970774964136113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57606739190647183309424075 86410108785970774964136113)
  ·
    refine ⟨64807581589478081223102085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86410108785970774964136113 64807581589478081223102085)
    ·
      refine ⟨12151421548027140229331641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64807581589478081223102085 12151421548027140229331641)
      ·
        refine ⟨9113566161020355171998731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12151421548027140229331641 9113566161020355171998731)
        ·
          refine ⟨13670349241530532757998097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113566161020355171998731 13670349241530532757998097)
          ·
            refine ⟨10252761931147899568498573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13670349241530532757998097 10252761931147899568498573)
            ·
              refine ⟨3844785724180462338186965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10252761931147899568498573 3844785724180462338186965)
              ·
                refine ⟨90112165410479586051257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3844785724180462338186965 90112165410479586051257)
                ·
                  rfl

theorem cell22_2369153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 7].length) (baseStart_2369153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369153 prefixEnd_2369153 := by exact prefixLift 2369153
  have htrace : WordTrace (prefixWord ++ tailWord_2369153) baseStart_2369153 baseEnd_2369153 := by
    simpa [prefixWord, tailWord_2369153, baseEnd_2369153] using wordTrace_append hprefix tailTrace_2369153
  have hstable : (prefixWord ++ tailWord_2369153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369153).length < 2 ^ (prefixWord ++ tailWord_2369153).sum := by decide
  have hdescent : baseEnd_2369153 < baseStart_2369153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369202 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_2369202 : Nat := 118140960795 + 2369202 * 2 ^ 59
def prefixEnd_2369202 : Nat := 4983230072969 + 3 ^ 40 * 2369202 * 2
def baseEnd_2369202 : Nat := 811026262395696479986163

theorem tailTrace_2369202 : CollatzResearch.WordTrace tailWord_2369202 prefixEnd_2369202 811026262395696479986163 := by
  unfold tailWord_2369202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21602973990698314083167465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57607930641862170888446573 21602973990698314083167465)
  ·
    refine ⟨16202230493023735562375599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21602973990698314083167465 16202230493023735562375599)
    ·
      refine ⟨24303345739535603343563399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16202230493023735562375599 24303345739535603343563399)
      ·
        refine ⟨36455018609303405015345099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24303345739535603343563399 36455018609303405015345099)
        ·
          refine ⟨54682527913955107523017649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36455018609303405015345099 54682527913955107523017649)
          ·
            refine ⟨41011895935466330642263237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54682527913955107523017649 41011895935466330642263237)
            ·
              refine ⟨7689730487899936995424357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41011895935466330642263237 7689730487899936995424357)
              ·
                refine ⟨1441824466481238186642067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7689730487899936995424357 1441824466481238186642067)
                ·
                  refine ⟨2162736699721857279963101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441824466481238186642067 2162736699721857279963101)
                  ·
                    refine ⟨811026262395696479986163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162736699721857279963101 811026262395696479986163)
                    ·
                      rfl

theorem cell22_2369202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_2369202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369202 prefixEnd_2369202 := by exact prefixLift 2369202
  have htrace : WordTrace (prefixWord ++ tailWord_2369202) baseStart_2369202 baseEnd_2369202 := by
    simpa [prefixWord, tailWord_2369202, baseEnd_2369202] using wordTrace_append hprefix tailTrace_2369202
  have hstable : (prefixWord ++ tailWord_2369202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369202).length < 2 ^ (prefixWord ++ tailWord_2369202).sum := by decide
  have hdescent : baseEnd_2369202 < baseStart_2369202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369213 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2369213 : Nat := 118140960795 + 2369213 * 2 ^ 59
def prefixEnd_2369213 : Nat := 4983230072969 + 3 ^ 40 * 2369213 * 2
def baseEnd_2369213 : Nat := 811030027920496117961129

theorem tailTrace_2369213 : CollatzResearch.WordTrace tailWord_2369213 prefixEnd_2369213 811030027920496117961129 := by
  unfold tailWord_2369213
  simp only [CollatzResearch.WordTrace]
  refine ⟨86412297165753405211320293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57608198110502270140880195 86412297165753405211320293)
  ·
    refine ⟨16202305718578763477122555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86412297165753405211320293 16202305718578763477122555)
    ·
      refine ⟨24303458577868145215683833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16202305718578763477122555 24303458577868145215683833)
      ·
        refine ⟨18227593933401108911762875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24303458577868145215683833 18227593933401108911762875)
        ·
          refine ⟨27341390900101663367644313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18227593933401108911762875 27341390900101663367644313)
          ·
            refine ⟨20506043175076247525733235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27341390900101663367644313 20506043175076247525733235)
            ·
              refine ⟨30759064762614371288599853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20506043175076247525733235 30759064762614371288599853)
              ·
                refine ⟨11534649285980389233224945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30759064762614371288599853 11534649285980389233224945)
                ·
                  refine ⟨8650986964485291924918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11534649285980389233224945 8650986964485291924918709)
                  ·
                    refine ⟨811030027920496117961129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8650986964485291924918709 811030027920496117961129)
                    ·
                      rfl

theorem cell22_2369213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2369213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369213 prefixEnd_2369213 := by exact prefixLift 2369213
  have htrace : WordTrace (prefixWord ++ tailWord_2369213) baseStart_2369213 baseEnd_2369213 := by
    simpa [prefixWord, tailWord_2369213, baseEnd_2369213] using wordTrace_append hprefix tailTrace_2369213
  have hstable : (prefixWord ++ tailWord_2369213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369213).length < 2 ^ (prefixWord ++ tailWord_2369213).sum := by decide
  have hdescent : baseEnd_2369213 < baseStart_2369213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369215 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 5]
def baseStart_2369215 : Nat := 118140960795 + 2369215 * 2 ^ 59
def prefixEnd_2369215 : Nat := 4983230072969 + 3 ^ 40 * 2369215 * 2
def baseEnd_2369215 : Nat := 270343570853789593137041

theorem tailTrace_2369215 : CollatzResearch.WordTrace tailWord_2369215 prefixEnd_2369215 270343570853789593137041 := by
  unfold tailWord_2369215
  simp only [CollatzResearch.WordTrace]
  refine ⟨86412370111746159552893099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57608246741164106368595399 86412370111746159552893099)
  ·
    refine ⟨129618555167619239329339649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86412370111746159552893099 129618555167619239329339649)
    ·
      refine ⟨97213916375714429497004737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129618555167619239329339649 97213916375714429497004737)
      ·
        refine ⟨72910437281785822122753553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97213916375714429497004737 72910437281785822122753553)
        ·
          refine ⟨54682827961339366592065165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72910437281785822122753553 54682827961339366592065165)
          ·
            refine ⟨20506060485502262472024437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54682827961339366592065165 20506060485502262472024437)
            ·
              refine ⟨1922443170515837106752291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20506060485502262472024437 1922443170515837106752291)
              ·
                refine ⟨2883664755773755660128437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922443170515837106752291 2883664755773755660128437)
                ·
                  refine ⟨270343570853789593137041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2883664755773755660128437 270343570853789593137041)
                  ·
                    rfl

theorem cell22_2369215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 5].length) (baseStart_2369215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369215 prefixEnd_2369215 := by exact prefixLift 2369215
  have htrace : WordTrace (prefixWord ++ tailWord_2369215) baseStart_2369215 baseEnd_2369215 := by
    simpa [prefixWord, tailWord_2369215, baseEnd_2369215] using wordTrace_append hprefix tailTrace_2369215
  have hstable : (prefixWord ++ tailWord_2369215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369215).length < 2 ^ (prefixWord ++ tailWord_2369215).sum := by decide
  have hdescent : baseEnd_2369215 < baseStart_2369215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369236 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2369236 : Nat := 118140960795 + 2369236 * 2 ^ 59
def prefixEnd_2369236 : Nat := 4983230072969 + 3 ^ 40 * 2369236 * 2
def baseEnd_2369236 : Nat := 811037901290531724636059

theorem tailTrace_2369236 : CollatzResearch.WordTrace tailWord_2369236 prefixEnd_2369236 811037901290531724636059 := by
  unfold tailWord_2369236
  simp only [CollatzResearch.WordTrace]
  refine ⟨43206568022335040069703781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57608757363113386759605041 43206568022335040069703781)
  ·
    refine ⟨8101231504187820013069459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43206568022335040069703781 8101231504187820013069459)
    ·
      refine ⟨12151847256281730019604189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101231504187820013069459 12151847256281730019604189)
      ·
        refine ⟨4556942721105648757351571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12151847256281730019604189 4556942721105648757351571)
        ·
          refine ⟨6835414081658473136027357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556942721105648757351571 6835414081658473136027357)
          ·
            refine ⟨2563280280621927426010259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6835414081658473136027357 2563280280621927426010259)
            ·
              refine ⟨3844920420932891139015389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563280280621927426010259 3844920420932891139015389)
              ·
                refine ⟨1441845157849834177130771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3844920420932891139015389 1441845157849834177130771)
                ·
                  refine ⟨2162767736774751265696157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441845157849834177130771 2162767736774751265696157)
                  ·
                    refine ⟨811037901290531724636059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162767736774751265696157 811037901290531724636059)
                    ·
                      rfl

theorem cell22_2369236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2369236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369236 prefixEnd_2369236 := by exact prefixLift 2369236
  have htrace : WordTrace (prefixWord ++ tailWord_2369236) baseStart_2369236 baseEnd_2369236 := by
    simpa [prefixWord, tailWord_2369236, baseEnd_2369236] using wordTrace_append hprefix tailTrace_2369236
  have hstable : (prefixWord ++ tailWord_2369236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369236).length < 2 ^ (prefixWord ++ tailWord_2369236).sum := by decide
  have hdescent : baseEnd_2369236 < baseStart_2369236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369260 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 4]
def baseStart_2369260 : Nat := 118140960795 + 2369260 * 2 ^ 59
def prefixEnd_2369260 : Nat := 4983230072969 + 3 ^ 40 * 2369260 * 2
def baseEnd_2369260 : Nat := 270348705660334554011995

theorem tailTrace_2369260 : CollatzResearch.WordTrace tailWord_2369260 prefixEnd_2369260 270348705660334554011995 := by
  unfold tailWord_2369260
  simp only [CollatzResearch.WordTrace]
  refine ⟨43207005698291566119140617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57609340931055421492187489 43207005698291566119140617)
  ·
    refine ⟨32405254273718674589355463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43207005698291566119140617 32405254273718674589355463)
    ·
      refine ⟨48607881410578011884033195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32405254273718674589355463 48607881410578011884033195)
      ·
        refine ⟨72911822115867017826049793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48607881410578011884033195 72911822115867017826049793)
        ·
          refine ⟨54683866586900263369537345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72911822115867017826049793 54683866586900263369537345)
          ·
            refine ⟨41012899940175197527153009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54683866586900263369537345 41012899940175197527153009)
            ·
              refine ⟨30759674955131398145364757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41012899940175197527153009 30759674955131398145364757)
              ·
                refine ⟨1441859763521784288063973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30759674955131398145364757 1441859763521784288063973)
                ·
                  refine ⟨270348705660334554011995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441859763521784288063973 270348705660334554011995)
                  ·
                    rfl

theorem cell22_2369260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_2369260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369260 prefixEnd_2369260 := by exact prefixLift 2369260
  have htrace : WordTrace (prefixWord ++ tailWord_2369260) baseStart_2369260 baseEnd_2369260 := by
    simpa [prefixWord, tailWord_2369260, baseEnd_2369260] using wordTrace_append hprefix tailTrace_2369260
  have hstable : (prefixWord ++ tailWord_2369260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369260).length < 2 ^ (prefixWord ++ tailWord_2369260).sum := by decide
  have hdescent : baseEnd_2369260 < baseStart_2369260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369288 : List Nat := [2, 1, 3, 2, 2, 1, 1, 10]
def baseStart_2369288 : Nat := 118140960795 + 2369288 * 2 ^ 59
def prefixEnd_2369288 : Nat := 4983230072969 + 3 ^ 40 * 2369288 * 2
def baseEnd_2369288 : Nat := 90117300217024546926211

theorem tailTrace_2369288 : CollatzResearch.WordTrace tailWord_2369288 prefixEnd_2369288 90117300217024546926211 := by
  unfold tailWord_2369288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43207516320240846510150259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57610021760321128680200345 43207516320240846510150259)
  ·
    refine ⟨64811274480361269765225389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43207516320240846510150259 64811274480361269765225389)
    ·
      refine ⟨24304227930135476161959521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64811274480361269765225389 24304227930135476161959521)
      ·
        refine ⟨18228170947601607121469641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24304227930135476161959521 18228170947601607121469641)
        ·
          refine ⟨13671128210701205341102231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18228170947601607121469641 13671128210701205341102231)
          ·
            refine ⟨20506692316051808011653347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13671128210701205341102231 20506692316051808011653347)
            ·
              refine ⟨30760038474077712017480021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20506692316051808011653347 30760038474077712017480021)
              ·
                refine ⟨90117300217024546926211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30760038474077712017480021 90117300217024546926211)
                ·
                  rfl

theorem cell22_2369288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_2369288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369288 prefixEnd_2369288 := by exact prefixLift 2369288
  have htrace : WordTrace (prefixWord ++ tailWord_2369288) baseStart_2369288 baseEnd_2369288 := by
    simpa [prefixWord, tailWord_2369288, baseEnd_2369288] using wordTrace_append hprefix tailTrace_2369288
  have hstable : (prefixWord ++ tailWord_2369288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369288).length < 2 ^ (prefixWord ++ tailWord_2369288).sum := by decide
  have hdescent : baseEnd_2369288 < baseStart_2369288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369290 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2369290 : Nat := 118140960795 + 2369290 * 2 ^ 59
def prefixEnd_2369290 : Nat := 4983230072969 + 3 ^ 40 * 2369290 * 2
def baseEnd_2369290 : Nat := 811056386594093583785893

theorem tailTrace_2369290 : CollatzResearch.WordTrace tailWord_2369290 prefixEnd_2369290 811056386594093583785893 := by
  unfold tailWord_2369290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21603776396618611840468331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57610070390982964907915549 21603776396618611840468331)
  ·
    refine ⟨32405664594927917760702497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21603776396618611840468331 32405664594927917760702497)
    ·
      refine ⟨24304248446195938320526873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32405664594927917760702497 24304248446195938320526873)
      ·
        refine ⟨18228186334646953740395155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24304248446195938320526873 18228186334646953740395155)
        ·
          refine ⟨27342279501970430610592733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18228186334646953740395155 27342279501970430610592733)
          ·
            refine ⟨10253354813238911478972275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27342279501970430610592733 10253354813238911478972275)
            ·
              refine ⟨15380032219858367218458413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10253354813238911478972275 15380032219858367218458413)
              ·
                refine ⟨5767512082446887706921905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15380032219858367218458413 5767512082446887706921905)
                ·
                  refine ⟨4325634061835165780191429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5767512082446887706921905 4325634061835165780191429)
                  ·
                    refine ⟨811056386594093583785893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325634061835165780191429 811056386594093583785893)
                    ·
                      rfl

theorem cell22_2369290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2369290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369290 prefixEnd_2369290 := by exact prefixLift 2369290
  have htrace : WordTrace (prefixWord ++ tailWord_2369290) baseStart_2369290 baseEnd_2369290 := by
    simpa [prefixWord, tailWord_2369290, baseEnd_2369290] using wordTrace_append hprefix tailTrace_2369290
  have hstable : (prefixWord ++ tailWord_2369290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369290).length < 2 ^ (prefixWord ++ tailWord_2369290).sum := by decide
  have hdescent : baseEnd_2369290 < baseStart_2369290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369354 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_2369354 : Nat := 118140960795 + 2369354 * 2 ^ 59
def prefixEnd_2369354 : Nat := 4983230072969 + 3 ^ 40 * 2369354 * 2
def baseEnd_2369354 : Nat := 811078295102018750185697

theorem tailTrace_2369354 : CollatzResearch.WordTrace tailWord_2369354 prefixEnd_2369354 811078295102018750185697 := by
  unfold tailWord_2369354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604359964560646573050779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57611626572161724194802077 21604359964560646573050779)
  ·
    refine ⟨32406539946840969859576169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21604359964560646573050779 32406539946840969859576169)
    ·
      refine ⟨24304904960130727394682127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32406539946840969859576169 24304904960130727394682127)
      ·
        refine ⟨36457357440196091092023191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24304904960130727394682127 36457357440196091092023191)
        ·
          refine ⟨54686036160294136638034787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36457357440196091092023191 54686036160294136638034787)
          ·
            refine ⟨82029054240441204957052181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54686036160294136638034787 82029054240441204957052181)
            ·
              refine ⟨3845111917520681482361821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82029054240441204957052181 3845111917520681482361821)
              ·
                refine ⟨1441916969070255555885683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845111917520681482361821 1441916969070255555885683)
                ·
                  refine ⟨2162875453605383333828525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441916969070255555885683 2162875453605383333828525)
                  ·
                    refine ⟨811078295102018750185697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162875453605383333828525 811078295102018750185697)
                    ·
                      rfl

theorem cell22_2369354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_2369354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369354 prefixEnd_2369354 := by exact prefixLift 2369354
  have htrace : WordTrace (prefixWord ++ tailWord_2369354) baseStart_2369354 baseEnd_2369354 := by
    simpa [prefixWord, tailWord_2369354, baseEnd_2369354] using wordTrace_append hprefix tailTrace_2369354
  have hstable : (prefixWord ++ tailWord_2369354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369354).length < 2 ^ (prefixWord ++ tailWord_2369354).sum := by decide
  have hdescent : baseEnd_2369354 < baseStart_2369354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369365 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2369365 : Nat := 118140960795 + 2369365 * 2 ^ 59
def prefixEnd_2369365 : Nat := 4983230072969 + 3 ^ 40 * 2369365 * 2
def baseEnd_2369365 : Nat := 811082060626818388160663

theorem tailTrace_2369365 : CollatzResearch.WordTrace tailWord_2369365 prefixEnd_2369365 811082060626818388160663 := by
  unfold tailWord_2369365
  simp only [CollatzResearch.WordTrace]
  refine ⟨86417841061202735170853549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57611894040801823447235699 86417841061202735170853549)
  ·
    refine ⟨32406690397951025689070081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86417841061202735170853549 32406690397951025689070081)
    ·
      refine ⟨24305017798463269266802561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32406690397951025689070081 24305017798463269266802561)
      ·
        refine ⟨18228763348847451950101921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24305017798463269266802561 18228763348847451950101921)
        ·
          refine ⟨13671572511635588962576441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18228763348847451950101921 13671572511635588962576441)
          ·
            refine ⟨10253679383726691721932331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13671572511635588962576441 10253679383726691721932331)
            ·
              refine ⟨15380519075590037582898497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10253679383726691721932331 15380519075590037582898497)
              ·
                refine ⟨11535389306692528187173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15380519075590037582898497 11535389306692528187173873)
                ·
                  refine ⟨8651541980019396140380405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11535389306692528187173873 8651541980019396140380405)
                  ·
                    refine ⟨811082060626818388160663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8651541980019396140380405 811082060626818388160663)
                    ·
                      rfl

theorem cell22_2369365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2369365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369365 prefixEnd_2369365 := by exact prefixLift 2369365
  have htrace : WordTrace (prefixWord ++ tailWord_2369365) baseStart_2369365 baseEnd_2369365 := by
    simpa [prefixWord, tailWord_2369365, baseEnd_2369365] using wordTrace_append hprefix tailTrace_2369365
  have hstable : (prefixWord ++ tailWord_2369365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369365).length < 2 ^ (prefixWord ++ tailWord_2369365).sum := by decide
  have hdescent : baseEnd_2369365 < baseStart_2369365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369425 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2369425 : Nat := 118140960795 + 2369425 * 2 ^ 59
def prefixEnd_2369425 : Nat := 4983230072969 + 3 ^ 40 * 2369425 * 2
def baseEnd_2369425 : Nat := 811102599852998231660479

theorem tailTrace_2369425 : CollatzResearch.WordTrace tailWord_2369425 prefixEnd_2369425 811102599852998231660479 := by
  unfold tailWord_2369425
  simp only [CollatzResearch.WordTrace]
  refine ⟨86420029440985365418037729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57613352960656910278691819 86420029440985365418037729)
  ·
    refine ⟨64815022080739024063528297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86420029440985365418037729 64815022080739024063528297)
    ·
      refine ⟨48611266560554268047646223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64815022080739024063528297 48611266560554268047646223)
      ·
        refine ⟨72916899840831402071469335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48611266560554268047646223 72916899840831402071469335)
        ·
          refine ⟨109375349761247103107204003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72916899840831402071469335 109375349761247103107204003)
          ·
            refine ⟨164063024641870654660806005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109375349761247103107204003 164063024641870654660806005)
            ·
              refine ⟨15380908560175373874450563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164063024641870654660806005 15380908560175373874450563)
              ·
                refine ⟨23071362840263060811675845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15380908560175373874450563 23071362840263060811675845)
                ·
                  refine ⟨4325880532549323902189221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23071362840263060811675845 4325880532549323902189221)
                  ·
                    refine ⟨811102599852998231660479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325880532549323902189221 811102599852998231660479)
                    ·
                      rfl

theorem cell22_2369425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2369425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369425 prefixEnd_2369425 := by exact prefixLift 2369425
  have htrace : WordTrace (prefixWord ++ tailWord_2369425) baseStart_2369425 baseEnd_2369425 := by
    simpa [prefixWord, tailWord_2369425, baseEnd_2369425] using wordTrace_append hprefix tailTrace_2369425
  have hstable : (prefixWord ++ tailWord_2369425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369425).length < 2 ^ (prefixWord ++ tailWord_2369425).sum := by decide
  have hdescent : baseEnd_2369425 < baseStart_2369425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369429 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 4]
def baseStart_2369429 : Nat := 118140960795 + 2369429 * 2 ^ 59
def prefixEnd_2369429 : Nat := 4983230072969 + 3 ^ 40 * 2369429 * 2
def baseEnd_2369429 : Nat := 270367989711581184853489

theorem tailTrace_2369429 : CollatzResearch.WordTrace tailWord_2369429 prefixEnd_2369429 270367989711581184853489 := by
  unfold tailWord_2369429
  simp only [CollatzResearch.WordTrace]
  refine ⟨86420175332970874101183341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57613450221980582734122227 86420175332970874101183341)
  ·
    refine ⟨32407565749864077787943753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86420175332970874101183341 32407565749864077787943753)
    ·
      refine ⟨24305674312398058340957815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32407565749864077787943753 24305674312398058340957815)
      ·
        refine ⟨36458511468597087511436723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24305674312398058340957815 36458511468597087511436723)
        ·
          refine ⟨54687767202895631267155085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36458511468597087511436723 54687767202895631267155085)
          ·
            refine ⟨20507912701085861725183157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54687767202895631267155085 20507912701085861725183157)
            ·
              refine ⟨1922616815726799536735921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20507912701085861725183157 1922616815726799536735921)
              ·
                refine ⟨1441962611795099652551941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922616815726799536735921 1441962611795099652551941)
                ·
                  refine ⟨270367989711581184853489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441962611795099652551941 270367989711581184853489)
                  ·
                    rfl

theorem cell22_2369429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_2369429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369429 prefixEnd_2369429 := by exact prefixLift 2369429
  have htrace : WordTrace (prefixWord ++ tailWord_2369429) baseStart_2369429 baseEnd_2369429 := by
    simpa [prefixWord, tailWord_2369429, baseEnd_2369429] using wordTrace_append hprefix tailTrace_2369429
  have hstable : (prefixWord ++ tailWord_2369429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369429).length < 2 ^ (prefixWord ++ tailWord_2369429).sum := by decide
  have hdescent : baseEnd_2369429 < baseStart_2369429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369444 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_2369444 : Nat := 118140960795 + 2369444 * 2 ^ 59
def prefixEnd_2369444 : Nat := 4983230072969 + 3 ^ 40 * 2369444 * 2
def baseEnd_2369444 : Nat := 811109103941288515435421

theorem tailTrace_2369444 : CollatzResearch.WordTrace tailWord_2369444 prefixEnd_2369444 811109103941288515435421 := by
  unfold tailWord_2369444
  simp only [CollatzResearch.WordTrace]
  refine ⟨43210361213958265831489693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57613814951944354441986257 43210361213958265831489693)
  ·
    refine ⟨16203885455234349686808635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43210361213958265831489693 16203885455234349686808635)
    ·
      refine ⟨24305828182851524530212953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16203885455234349686808635 24305828182851524530212953)
      ·
        refine ⟨18229371137138643397659715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24305828182851524530212953 18229371137138643397659715)
        ·
          refine ⟨27344056705707965096489573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18229371137138643397659715 27344056705707965096489573)
          ·
            refine ⟨5127010632320243455591795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27344056705707965096489573 5127010632320243455591795)
            ·
              refine ⟨7690515948480365183387693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127010632320243455591795 7690515948480365183387693)
              ·
                refine ⟨2883943480680136943770385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7690515948480365183387693 2883943480680136943770385)
                ·
                  refine ⟨2162957610510102707827789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2883943480680136943770385 2162957610510102707827789)
                  ·
                    refine ⟨811109103941288515435421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162957610510102707827789 811109103941288515435421)
                    ·
                      rfl

theorem cell22_2369444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_2369444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369444 prefixEnd_2369444 := by exact prefixLift 2369444
  have htrace : WordTrace (prefixWord ++ tailWord_2369444) baseStart_2369444 baseEnd_2369444 := by
    simpa [prefixWord, tailWord_2369444, baseEnd_2369444] using wordTrace_append hprefix tailTrace_2369444
  have hstable : (prefixWord ++ tailWord_2369444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369444).length < 2 ^ (prefixWord ++ tailWord_2369444).sum := by decide
  have hdescent : baseEnd_2369444 < baseStart_2369444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369448 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2369448 : Nat := 118140960795 + 2369448 * 2 ^ 59
def prefixEnd_2369448 : Nat := 4983230072969 + 3 ^ 40 * 2369448 * 2
def baseEnd_2369448 : Nat := 811110473223033838335409

theorem tailTrace_2369448 : CollatzResearch.WordTrace tailWord_2369448 prefixEnd_2369448 811110473223033838335409 := by
  unfold tailWord_2369448
  simp only [CollatzResearch.WordTrace]
  refine ⟨43210434159951020173062499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57613912213268026897416665 43210434159951020173062499)
  ·
    refine ⟨64815651239926530259593749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43210434159951020173062499 64815651239926530259593749)
    ·
      refine ⟨3038233651871556105918457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64815651239926530259593749 3038233651871556105918457)
      ·
        refine ⟨2278675238903667079438843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3038233651871556105918457 2278675238903667079438843)
        ·
          refine ⟨3418012858355500619158265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278675238903667079438843 3418012858355500619158265)
          ·
            refine ⟨2563509643766625464368699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3418012858355500619158265 2563509643766625464368699)
            ·
              refine ⟨3845264465649938196553049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563509643766625464368699 3845264465649938196553049)
              ·
                refine ⟨2883948349237453647414787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3845264465649938196553049 2883948349237453647414787)
                ·
                  refine ⟨4325922523856180471122181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883948349237453647414787 4325922523856180471122181)
                  ·
                    refine ⟨811110473223033838335409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325922523856180471122181 811110473223033838335409)
                    ·
                      rfl

theorem cell22_2369448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2369448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369448 prefixEnd_2369448 := by exact prefixLift 2369448
  have htrace : WordTrace (prefixWord ++ tailWord_2369448) baseStart_2369448 baseEnd_2369448 := by
    simpa [prefixWord, tailWord_2369448, baseEnd_2369448] using wordTrace_append hprefix tailTrace_2369448
  have hstable : (prefixWord ++ tailWord_2369448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369448).length < 2 ^ (prefixWord ++ tailWord_2369448).sum := by decide
  have hdescent : baseEnd_2369448 < baseStart_2369448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369534 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2369534 : Nat := 118140960795 + 2369534 * 2 ^ 59
def prefixEnd_2369534 : Nat := 4983230072969 + 3 ^ 40 * 2369534 * 2
def baseEnd_2369534 : Nat := 811139912780558280685145

theorem tailTrace_2369534 : CollatzResearch.WordTrace tailWord_2369534 prefixEnd_2369534 811139912780558280685145 := by
  unfold tailWord_2369534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803000624698809629219457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57616003331726984689170437 10803000624698809629219457)
  ·
    refine ⟨8102250468524107221914593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803000624698809629219457 8102250468524107221914593)
    ·
      refine ⟨6076687851393080416435945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8102250468524107221914593 6076687851393080416435945)
      ·
        refine ⟨4557515888544810312326959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076687851393080416435945 4557515888544810312326959)
        ·
          refine ⟨6836273832817215468490439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557515888544810312326959 6836273832817215468490439)
          ·
            refine ⟨10254410749225823202735659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836273832817215468490439 10254410749225823202735659)
            ·
              refine ⟨15381616123838734804103489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10254410749225823202735659 15381616123838734804103489)
              ·
                refine ⟨11536212092879051103077617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15381616123838734804103489 11536212092879051103077617)
                ·
                  refine ⟨8652159069659288327308213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11536212092879051103077617 8652159069659288327308213)
                  ·
                    refine ⟨811139912780558280685145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8652159069659288327308213 811139912780558280685145)
                    ·
                      rfl

theorem cell22_2369534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2369534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369534 prefixEnd_2369534 := by exact prefixLift 2369534
  have htrace : WordTrace (prefixWord ++ tailWord_2369534) baseStart_2369534 baseEnd_2369534 := by
    simpa [prefixWord, tailWord_2369534, baseEnd_2369534] using wordTrace_append hprefix tailTrace_2369534
  have hstable : (prefixWord ++ tailWord_2369534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369534).length < 2 ^ (prefixWord ++ tailWord_2369534).sum := by decide
  have hdescent : baseEnd_2369534 < baseStart_2369534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369545 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_2369545 : Nat := 118140960795 + 2369545 * 2 ^ 59
def prefixEnd_2369545 : Nat := 4983230072969 + 3 ^ 40 * 2369545 * 2
def baseEnd_2369545 : Nat := 811143678305357918660111

theorem tailTrace_2369545 : CollatzResearch.WordTrace tailWord_2369545 prefixEnd_2369545 811143678305357918660111 := by
  unfold tailWord_2369545
  simp only [CollatzResearch.WordTrace]
  refine ⟨86424406200550625912406089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57616270800367083941604059 86424406200550625912406089)
  ·
    refine ⟨64818304650412969434304567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86424406200550625912406089 64818304650412969434304567)
    ·
      refine ⟨97227456975619454151456851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64818304650412969434304567 97227456975619454151456851)
      ·
        refine ⟨145841185463429181227185277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97227456975619454151456851 145841185463429181227185277)
        ·
          refine ⟨54690444548785942960194479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145841185463429181227185277 54690444548785942960194479)
          ·
            refine ⟨82035666823178914440291719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54690444548785942960194479 82035666823178914440291719)
            ·
              refine ⟨123053500234768371660437579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82035666823178914440291719 123053500234768371660437579)
              ·
                refine ⟨184580250352152557490656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123053500234768371660437579 184580250352152557490656369)
                ·
                  refine ⟨138435187764114418117992277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184580250352152557490656369 138435187764114418117992277)
                  ·
                    refine ⟨811143678305357918660111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138435187764114418117992277 811143678305357918660111)
                    ·
                      rfl

theorem cell22_2369545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_2369545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369545 prefixEnd_2369545 := by exact prefixLift 2369545
  have htrace : WordTrace (prefixWord ++ tailWord_2369545) baseStart_2369545 baseEnd_2369545 := by
    simpa [prefixWord, tailWord_2369545, baseEnd_2369545] using wordTrace_append hprefix tailTrace_2369545
  have hstable : (prefixWord ++ tailWord_2369545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369545).length < 2 ^ (prefixWord ++ tailWord_2369545).sum := by decide
  have hdescent : baseEnd_2369545 < baseStart_2369545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369547 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 6]
def baseStart_2369547 : Nat := 118140960795 + 2369547 * 2 ^ 59
def prefixEnd_2369547 : Nat := 4983230072969 + 3 ^ 40 * 2369547 * 2
def baseEnd_2369547 : Nat := 270381454315410193370035

theorem tailTrace_2369547 : CollatzResearch.WordTrace tailWord_2369547 prefixEnd_2369547 270381454315410193370035 := by
  unfold tailWord_2369547
  simp only [CollatzResearch.WordTrace]
  refine ⟨86424479146543380253978895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57616319431028920169319263 86424479146543380253978895)
  ·
    refine ⟨129636718719815070380968343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86424479146543380253978895 129636718719815070380968343)
    ·
      refine ⟨194455078079722605571452515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129636718719815070380968343 194455078079722605571452515)
      ·
        refine ⟨291682617119583908357178773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194455078079722605571452515 291682617119583908357178773)
        ·
          refine ⟨13672622677480495704242755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 291682617119583908357178773 13672622677480495704242755)
          ·
            refine ⟨20508934016220743556364133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13672622677480495704242755 20508934016220743556364133)
            ·
              refine ⟨3845425128041389416818275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20508934016220743556364133 3845425128041389416818275)
              ·
                refine ⟨5768137692062084125227413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845425128041389416818275 5768137692062084125227413)
                ·
                  refine ⟨270381454315410193370035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5768137692062084125227413 270381454315410193370035)
                  ·
                    rfl

theorem cell22_2369547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 6].length) (baseStart_2369547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369547 prefixEnd_2369547 := by exact prefixLift 2369547
  have htrace : WordTrace (prefixWord ++ tailWord_2369547) baseStart_2369547 baseEnd_2369547 := by
    simpa [prefixWord, tailWord_2369547, baseEnd_2369547] using wordTrace_append hprefix tailTrace_2369547
  have hstable : (prefixWord ++ tailWord_2369547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369547).length < 2 ^ (prefixWord ++ tailWord_2369547).sum := by decide
  have hdescent : baseEnd_2369547 < baseStart_2369547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369598 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_2369598 : Nat := 118140960795 + 2369598 * 2 ^ 59
def prefixEnd_2369598 : Nat := 4983230072969 + 3 ^ 40 * 2369598 * 2
def baseEnd_2369598 : Nat := 270387273762827815694983

theorem tailTrace_2369598 : CollatzResearch.WordTrace tailWord_2369598 prefixEnd_2369598 270387273762827815694983 := by
  unfold tailWord_2369598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803292408669826995510681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57617559512905743976056965 10803292408669826995510681)
  ·
    refine ⟨8102469306502370246633011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803292408669826995510681 8102469306502370246633011)
    ·
      refine ⟨12153703959753555369949517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8102469306502370246633011 12153703959753555369949517)
      ·
        refine ⟨4557638984907583263731069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12153703959753555369949517 4557638984907583263731069)
        ·
          refine ⟨1709114619340343723899151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4557638984907583263731069 1709114619340343723899151)
          ·
            refine ⟨2563671929010515585848727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709114619340343723899151 2563671929010515585848727)
            ·
              refine ⟨3845507893515773378773091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563671929010515585848727 3845507893515773378773091)
              ·
                refine ⟨5768261840273660068159637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845507893515773378773091 5768261840273660068159637)
                ·
                  refine ⟨270387273762827815694983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5768261840273660068159637 270387273762827815694983)
                  ·
                    rfl

theorem cell22_2369598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_2369598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369598 prefixEnd_2369598 := by exact prefixLift 2369598
  have htrace : WordTrace (prefixWord ++ tailWord_2369598) baseStart_2369598 baseEnd_2369598 := by
    simpa [prefixWord, tailWord_2369598, baseEnd_2369598] using wordTrace_append hprefix tailTrace_2369598
  have hstable : (prefixWord ++ tailWord_2369598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369598).length < 2 ^ (prefixWord ++ tailWord_2369598).sum := by decide
  have hdescent : baseEnd_2369598 < baseStart_2369598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369641 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 1, 3]
def baseStart_2369641 : Nat := 118140960795 + 2369641 * 2 ^ 59
def prefixEnd_2369641 : Nat := 4983230072969 + 3 ^ 40 * 2369641 * 2
def baseEnd_2369641 : Nat := 811176541067245668259817

theorem tailTrace_2369641 : CollatzResearch.WordTrace tailWord_2369641 prefixEnd_2369641 811176541067245668259817 := by
  unfold tailWord_2369641
  simp only [CollatzResearch.WordTrace]
  refine ⟨86427907608202834307900777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57618605072135222871933851 86427907608202834307900777)
  ·
    refine ⟨64820930706152125730925583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86427907608202834307900777 64820930706152125730925583)
    ·
      refine ⟨97231396059228188596388375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64820930706152125730925583 97231396059228188596388375)
      ·
        refine ⟨145847094088842282894582563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97231396059228188596388375 145847094088842282894582563)
        ·
          refine ⟨218770641133263424341873845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145847094088842282894582563 218770641133263424341873845)
          ·
            refine ⟨20509747606243446032050673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218770641133263424341873845 20509747606243446032050673)
            ·
              refine ⟨15382310704682584524038005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20509747606243446032050673 15382310704682584524038005)
              ·
                refine ⟨1442091628563992299128563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15382310704682584524038005 1442091628563992299128563)
                ·
                  refine ⟨2163137442845988448692845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442091628563992299128563 2163137442845988448692845)
                  ·
                    refine ⟨811176541067245668259817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163137442845988448692845 811176541067245668259817)
                    ·
                      rfl

theorem cell22_2369641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_2369641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369641 prefixEnd_2369641 := by exact prefixLift 2369641
  have htrace : WordTrace (prefixWord ++ tailWord_2369641) baseStart_2369641 baseEnd_2369641 := by
    simpa [prefixWord, tailWord_2369641, baseEnd_2369641] using wordTrace_append hprefix tailTrace_2369641
  have hstable : (prefixWord ++ tailWord_2369641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369641).length < 2 ^ (prefixWord ++ tailWord_2369641).sum := by decide
  have hdescent : baseEnd_2369641 < baseStart_2369641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369669 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_2369669 : Nat := 118140960795 + 2369669 * 2 ^ 59
def prefixEnd_2369669 : Nat := 4983230072969 + 3 ^ 40 * 2369669 * 2
def baseEnd_2369669 : Nat := 811186126039462928559731

theorem tailTrace_2369669 : CollatzResearch.WordTrace tailWord_2369669 prefixEnd_2369669 811186126039462928559731 := by
  unfold tailWord_2369669
  simp only [CollatzResearch.WordTrace]
  refine ⟨86428928852101395089920061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57619285901400930059946707 86428928852101395089920061)
  ·
    refine ⟨32410848319538023158720023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86428928852101395089920061 32410848319538023158720023)
    ·
      refine ⟨48616272479307034738080035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32410848319538023158720023 48616272479307034738080035)
      ·
        refine ⟨72924408718960552107120053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48616272479307034738080035 72924408718960552107120053)
        ·
          refine ⟨6836663317402551760042505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72924408718960552107120053 6836663317402551760042505)
          ·
            refine ⟨5127497488051913820031879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6836663317402551760042505 5127497488051913820031879)
            ·
              refine ⟨7691246232077870730047819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127497488051913820031879 7691246232077870730047819)
              ·
                refine ⟨11536869348116806095071729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7691246232077870730047819 11536869348116806095071729)
                ·
                  refine ⟨8652652011087604571303797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11536869348116806095071729 8652652011087604571303797)
                  ·
                    refine ⟨811186126039462928559731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8652652011087604571303797 811186126039462928559731)
                    ·
                      rfl

theorem cell22_2369669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_2369669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369669 prefixEnd_2369669 := by exact prefixLift 2369669
  have htrace : WordTrace (prefixWord ++ tailWord_2369669) baseStart_2369669 baseEnd_2369669 := by
    simpa [prefixWord, tailWord_2369669, baseEnd_2369669] using wordTrace_append hprefix tailTrace_2369669
  have hstable : (prefixWord ++ tailWord_2369669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369669).length < 2 ^ (prefixWord ++ tailWord_2369669).sum := by decide
  have hdescent : baseEnd_2369669 < baseStart_2369669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369712 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_2369712 : Nat := 118140960795 + 2369712 * 2 ^ 59
def prefixEnd_2369712 : Nat := 4983230072969 + 3 ^ 40 * 2369712 * 2
def baseEnd_2369712 : Nat := 811200845818225149734599

theorem tailTrace_2369712 : CollatzResearch.WordTrace tailWord_2369712 prefixEnd_2369712 811200845818225149734599 := by
  unfold tailWord_2369712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43215248595472806716867695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57620331460630408955823593 43215248595472806716867695)
  ·
    refine ⟨64822872893209210075301543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43215248595472806716867695 64822872893209210075301543)
    ·
      refine ⟨97234309339813815112952315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64822872893209210075301543 97234309339813815112952315)
      ·
        refine ⟨145851464009720722669428473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97234309339813815112952315 145851464009720722669428473)
        ·
          refine ⟨109388598007290542002071355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145851464009720722669428473 109388598007290542002071355)
          ·
            refine ⟨164082897010935813003107033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109388598007290542002071355 164082897010935813003107033)
            ·
              refine ⟨123062172758201859752330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164082897010935813003107033 123062172758201859752330275)
              ·
                refine ⟨184593259137302789628495413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123062172758201859752330275 184593259137302789628495413)
                ·
                  refine ⟨17305618044122136527671445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184593259137302789628495413 17305618044122136527671445)
                  ·
                    refine ⟨811200845818225149734599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17305618044122136527671445 811200845818225149734599)
                    ·
                      rfl

theorem cell22_2369712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_2369712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369712 prefixEnd_2369712 := by exact prefixLift 2369712
  have htrace : WordTrace (prefixWord ++ tailWord_2369712) baseStart_2369712 baseEnd_2369712 := by
    simpa [prefixWord, tailWord_2369712, baseEnd_2369712] using wordTrace_append hprefix tailTrace_2369712
  have hstable : (prefixWord ++ tailWord_2369712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369712).length < 2 ^ (prefixWord ++ tailWord_2369712).sum := by decide
  have hdescent : baseEnd_2369712 < baseStart_2369712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369727 : List Nat := [1, 1, 2, 2, 2, 2, 1, 11]
def baseStart_2369727 : Nat := 118140960795 + 2369727 * 2 ^ 59
def prefixEnd_2369727 : Nat := 4983230072969 + 3 ^ 40 * 2369727 * 2
def baseEnd_2369727 : Nat := 90133997847196678956617

theorem tailTrace_2369727 : CollatzResearch.WordTrace tailWord_2369727 prefixEnd_2369727 90133997847196678956617 := by
  unfold tailWord_2369727
  simp only [CollatzResearch.WordTrace]
  refine ⟨86431044285891270995531435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57620696190594180663687623 86431044285891270995531435)
  ·
    refine ⟨129646566428836906493297153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86431044285891270995531435 129646566428836906493297153)
    ·
      refine ⟨97234924821627679869972865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129646566428836906493297153 97234924821627679869972865)
      ·
        refine ⟨72926193616220759902479649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97234924821627679869972865 72926193616220759902479649)
        ·
          refine ⟨54694645212165569926859737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72926193616220759902479649 54694645212165569926859737)
          ·
            refine ⟨41020983909124177445144803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54694645212165569926859737 41020983909124177445144803)
            ·
              refine ⟨61531475863686266167717205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41020983909124177445144803 61531475863686266167717205)
              ·
                refine ⟨90133997847196678956617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61531475863686266167717205 90133997847196678956617)
                ·
                  rfl

theorem cell22_2369727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 11].length) (baseStart_2369727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369727 prefixEnd_2369727 := by exact prefixLift 2369727
  have htrace : WordTrace (prefixWord ++ tailWord_2369727) baseStart_2369727 baseEnd_2369727 := by
    simpa [prefixWord, tailWord_2369727, baseEnd_2369727] using wordTrace_append hprefix tailTrace_2369727
  have hstable : (prefixWord ++ tailWord_2369727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369727).length < 2 ^ (prefixWord ++ tailWord_2369727).sum := by decide
  have hdescent : baseEnd_2369727 < baseStart_2369727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369750 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2369750 : Nat := 118140960795 + 2369750 * 2 ^ 59
def prefixEnd_2369750 : Nat := 4983230072969 + 3 ^ 40 * 2369750 * 2
def baseEnd_2369750 : Nat := 270404617998268572428161

theorem tailTrace_2369750 : CollatzResearch.WordTrace tailWord_2369750 prefixEnd_2369750 270404617998268572428161 := by
  unfold tailWord_2369750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401992697800496620226169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57621255443205297282412469 5401992697800496620226169)
  ·
    refine ⟨4051494523350372465169627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5401992697800496620226169 4051494523350372465169627)
    ·
      refine ⟨6077241785025558697754441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051494523350372465169627 6077241785025558697754441)
      ·
        refine ⟨4557931338769169023315831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6077241785025558697754441 4557931338769169023315831)
        ·
          refine ⟨6836897008153753534973747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557931338769169023315831 6836897008153753534973747)
          ·
            refine ⟨10255345512230630302460621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836897008153753534973747 10255345512230630302460621)
            ·
              refine ⟨3845754567086486363422733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10255345512230630302460621 3845754567086486363422733)
              ·
                refine ⟨1442157962657432386283525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845754567086486363422733 1442157962657432386283525)
                ·
                  refine ⟨270404617998268572428161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442157962657432386283525 270404617998268572428161)
                  ·
                    rfl

theorem cell22_2369750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2369750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369750 prefixEnd_2369750 := by exact prefixLift 2369750
  have htrace : WordTrace (prefixWord ++ tailWord_2369750) baseStart_2369750 baseEnd_2369750 := by
    simpa [prefixWord, tailWord_2369750, baseEnd_2369750] using wordTrace_append hprefix tailTrace_2369750
  have hstable : (prefixWord ++ tailWord_2369750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369750).length < 2 ^ (prefixWord ++ tailWord_2369750).sum := by decide
  have hdescent : baseEnd_2369750 < baseStart_2369750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369763 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 2, 4]
def baseStart_2369763 : Nat := 118140960795 + 2369763 * 2 ^ 59
def prefixEnd_2369763 : Nat := 4983230072969 + 3 ^ 40 * 2369763 * 2
def baseEnd_2369763 : Nat := 811218304160478016709443

theorem tailTrace_2369763 : CollatzResearch.WordTrace tailWord_2369763 prefixEnd_2369763 811218304160478016709443 := by
  unfold tailWord_2369763
  simp only [CollatzResearch.WordTrace]
  refine ⟨86432357313760849143841943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57621571542507232762561295 86432357313760849143841943)
  ·
    refine ⟨129648535970641273715762915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86432357313760849143841943 129648535970641273715762915)
    ·
      refine ⟨194472803955961910573644373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129648535970641273715762915 194472803955961910573644373)
      ·
        refine ⟨2278978171358928639534895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 194472803955961910573644373 2278978171358928639534895)
        ·
          refine ⟨3418467257038392959302343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278978171358928639534895 3418467257038392959302343)
          ·
            refine ⟨5127700885557589438953515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418467257038392959302343 5127700885557589438953515)
            ·
              refine ⟨7691551328336384158430273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127700885557589438953515 7691551328336384158430273)
              ·
                refine ⟨5768663496252288118822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691551328336384158430273 5768663496252288118822705)
                ·
                  refine ⟨4326497622189216089117029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768663496252288118822705 4326497622189216089117029)
                  ·
                    refine ⟨811218304160478016709443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4326497622189216089117029 811218304160478016709443)
                    ·
                      rfl

theorem cell22_2369763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4].length) (baseStart_2369763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369763 prefixEnd_2369763 := by exact prefixLift 2369763
  have htrace : WordTrace (prefixWord ++ tailWord_2369763) baseStart_2369763 baseEnd_2369763 := by
    simpa [prefixWord, tailWord_2369763, baseEnd_2369763] using wordTrace_append hprefix tailTrace_2369763
  have hstable : (prefixWord ++ tailWord_2369763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369763).length < 2 ^ (prefixWord ++ tailWord_2369763).sum := by decide
  have hdescent : baseEnd_2369763 < baseStart_2369763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369774 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2369774 : Nat := 118140960795 + 2369774 * 2 ^ 59
def prefixEnd_2369774 : Nat := 4983230072969 + 3 ^ 40 * 2369774 * 2
def baseEnd_2369774 : Nat := 811222069685277654684409

theorem tailTrace_2369774 : CollatzResearch.WordTrace tailWord_2369774 prefixEnd_2369774 811222069685277654684409 := by
  unfold tailWord_2369774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10804094814590124752811547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57621839011147332014994917 10804094814590124752811547)
  ·
    refine ⟨16206142221885187129217321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10804094814590124752811547 16206142221885187129217321)
    ·
      refine ⟨12154606666413890346912991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16206142221885187129217321 12154606666413890346912991)
      ·
        refine ⟨18231909999620835520369487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154606666413890346912991 18231909999620835520369487)
        ·
          refine ⟨27347864999431253280554231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18231909999620835520369487 27347864999431253280554231)
          ·
            refine ⟨41021797499146879920831347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27347864999431253280554231 41021797499146879920831347)
            ·
              refine ⟨61532696248720319881247021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41021797499146879920831347 61532696248720319881247021)
              ·
                refine ⟨23074761093270119955467633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61532696248720319881247021 23074761093270119955467633)
                ·
                  refine ⟨17306070819952589966600725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23074761093270119955467633 17306070819952589966600725)
                  ·
                    refine ⟨811222069685277654684409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17306070819952589966600725 811222069685277654684409)
                    ·
                      rfl

theorem cell22_2369774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2369774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369774 prefixEnd_2369774 := by exact prefixLift 2369774
  have htrace : WordTrace (prefixWord ++ tailWord_2369774) baseStart_2369774 baseEnd_2369774 := by
    simpa [prefixWord, tailWord_2369774, baseEnd_2369774] using wordTrace_append hprefix tailTrace_2369774
  have hstable : (prefixWord ++ tailWord_2369774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369774).length < 2 ^ (prefixWord ++ tailWord_2369774).sum := by decide
  have hdescent : baseEnd_2369774 < baseStart_2369774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369868 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_2369868 : Nat := 118140960795 + 2369868 * 2 ^ 59
def prefixEnd_2369868 : Nat := 4983230072969 + 3 ^ 40 * 2369868 * 2
def baseEnd_2369868 : Nat := 270418082602097580944707

theorem tailTrace_2369868 : CollatzResearch.WordTrace tailWord_2369868 prefixEnd_2369868 270418082602097580944707 := by
  unfold tailWord_2369868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43218093489190226038207129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57624124652253634717609505 43218093489190226038207129)
  ·
    refine ⟨32413570116892669528655347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43218093489190226038207129 32413570116892669528655347)
    ·
      refine ⟨48620355175339004292983021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32413570116892669528655347 48620355175339004292983021)
      ·
        refine ⟨18232633190752126609868633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48620355175339004292983021 18232633190752126609868633)
        ·
          refine ⟨13674474893064094957401475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18232633190752126609868633 13674474893064094957401475)
          ·
            refine ⟨20511712339596142436102213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13674474893064094957401475 20511712339596142436102213)
            ·
              refine ⟨3845946063674276706769165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20511712339596142436102213 3845946063674276706769165)
              ·
                refine ⟨1442229773877853765038437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845946063674276706769165 1442229773877853765038437)
                ·
                  refine ⟨270418082602097580944707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442229773877853765038437 270418082602097580944707)
                  ·
                    rfl

theorem cell22_2369868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_2369868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369868 prefixEnd_2369868 := by exact prefixLift 2369868
  have htrace : WordTrace (prefixWord ++ tailWord_2369868) baseStart_2369868 baseEnd_2369868 := by
    simpa [prefixWord, tailWord_2369868, baseEnd_2369868] using wordTrace_append hprefix tailTrace_2369868
  have hstable : (prefixWord ++ tailWord_2369868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369868).length < 2 ^ (prefixWord ++ tailWord_2369868).sum := by decide
  have hdescent : baseEnd_2369868 < baseStart_2369868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369879 : List Nat := [1, 1, 3, 2, 3, 1, 11]
def baseStart_2369879 : Nat := 118140960795 + 2369879 * 2 ^ 59
def prefixEnd_2369879 : Nat := 4983230072969 + 3 ^ 40 * 2369879 * 2
def baseEnd_2369879 : Nat := 30046593086336754844781

theorem tailTrace_2369879 : CollatzResearch.WordTrace tailWord_2369879 prefixEnd_2369879 30046593086336754844781 := by
  unfold tailWord_2369879
  simp only [CollatzResearch.WordTrace]
  refine ⟨86436588181340600955064691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57624392120893733970043127 86436588181340600955064691)
  ·
    refine ⟨129654882272010901432597037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86436588181340600955064691 129654882272010901432597037)
    ·
      refine ⟨48620580852004088037223889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129654882272010901432597037 48620580852004088037223889)
      ·
        refine ⟨36465435639003066027917917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48620580852004088037223889 36465435639003066027917917)
        ·
          refine ⟨13674538364626149760469219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36465435639003066027917917 13674538364626149760469219)
          ·
            refine ⟨20511807546939224640703829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13674538364626149760469219 20511807546939224640703829)
            ·
              refine ⟨30046593086336754844781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20511807546939224640703829 30046593086336754844781)
              ·
                rfl

theorem cell22_2369879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 11].length) (baseStart_2369879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369879 prefixEnd_2369879 := by exact prefixLift 2369879
  have htrace : WordTrace (prefixWord ++ tailWord_2369879) baseStart_2369879 baseEnd_2369879 := by
    simpa [prefixWord, tailWord_2369879, baseEnd_2369879] using wordTrace_append hprefix tailTrace_2369879
  have hstable : (prefixWord ++ tailWord_2369879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369879).length < 2 ^ (prefixWord ++ tailWord_2369879).sum := by decide
  have hdescent : baseEnd_2369879 < baseStart_2369879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369900 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_2369900 : Nat := 118140960795 + 2369900 * 2 ^ 59
def prefixEnd_2369900 : Nat := 4983230072969 + 3 ^ 40 * 2369900 * 2
def baseEnd_2369900 : Nat := 811265202060255326034023

theorem tailTrace_2369900 : CollatzResearch.WordTrace tailWord_2369900 prefixEnd_2369900 811265202060255326034023 := by
  unfold tailWord_2369900
  simp only [CollatzResearch.WordTrace]
  refine ⟨43218677057132260770789577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57624902742843014361052769 43218677057132260770789577)
  ·
    refine ⟨32414007792849195578092183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43218677057132260770789577 32414007792849195578092183)
    ·
      refine ⟨48621011689273793367138275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32414007792849195578092183 48621011689273793367138275)
      ·
        refine ⟨72931517533910690050707413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48621011689273793367138275 72931517533910690050707413)
        ·
          refine ⟨1709332442201031798063455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 72931517533910690050707413 1709332442201031798063455)
          ·
            refine ⟨2563998663301547697095183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709332442201031798063455 2563998663301547697095183)
            ·
              refine ⟨3845997994952321545642775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563998663301547697095183 3845997994952321545642775)
              ·
                refine ⟨5768996992428482318464163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845997994952321545642775 5768996992428482318464163)
                ·
                  refine ⟨8653495488642723477696245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768996992428482318464163 8653495488642723477696245)
                  ·
                    refine ⟨811265202060255326034023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8653495488642723477696245 811265202060255326034023)
                    ·
                      rfl

theorem cell22_2369900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_2369900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369900 prefixEnd_2369900 := by exact prefixLift 2369900
  have htrace : WordTrace (prefixWord ++ tailWord_2369900) baseStart_2369900 baseEnd_2369900 := by
    simpa [prefixWord, tailWord_2369900, baseEnd_2369900] using wordTrace_append hprefix tailTrace_2369900
  have hstable : (prefixWord ++ tailWord_2369900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369900).length < 2 ^ (prefixWord ++ tailWord_2369900).sum := by decide
  have hdescent : baseEnd_2369900 < baseStart_2369900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369911 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 5, 3]
def baseStart_2369911 : Nat := 118140960795 + 2369911 * 2 ^ 59
def prefixEnd_2369911 : Nat := 4983230072969 + 3 ^ 40 * 2369911 * 2
def baseEnd_2369911 : Nat := 811268967585054964008989

theorem tailTrace_2369911 : CollatzResearch.WordTrace tailWord_2369911 prefixEnd_2369911 811268967585054964008989 := by
  unfold tailWord_2369911
  simp only [CollatzResearch.WordTrace]
  refine ⟨86437755317224670420229587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57625170211483113613486391 86437755317224670420229587)
  ·
    refine ⟨129656632975837005630344381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86437755317224670420229587 129656632975837005630344381)
    ·
      refine ⟨48621237365938877111379143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129656632975837005630344381 48621237365938877111379143)
      ·
        refine ⟨72931856048908315667068715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48621237365938877111379143 72931856048908315667068715)
        ·
          refine ⟨109397784073362473500603073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72931856048908315667068715 109397784073362473500603073)
          ·
            refine ⟨82048338055021855125452305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109397784073362473500603073 82048338055021855125452305)
            ·
              refine ⟨61536253541266391344089229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82048338055021855125452305 61536253541266391344089229)
              ·
                refine ⟨23076095077974896754033461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61536253541266391344089229 23076095077974896754033461)
                ·
                  refine ⟨2163383913560146570690637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23076095077974896754033461 2163383913560146570690637)
                  ·
                    refine ⟨811268967585054964008989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163383913560146570690637 811268967585054964008989)
                    ·
                      rfl

theorem cell22_2369911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_2369911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369911 prefixEnd_2369911 := by exact prefixLift 2369911
  have htrace : WordTrace (prefixWord ++ tailWord_2369911) baseStart_2369911 baseEnd_2369911 := by
    simpa [prefixWord, tailWord_2369911, baseEnd_2369911] using wordTrace_append hprefix tailTrace_2369911
  have hstable : (prefixWord ++ tailWord_2369911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369911).length < 2 ^ (prefixWord ++ tailWord_2369911).sum := by decide
  have hdescent : baseEnd_2369911 < baseStart_2369911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369930 : List Nat := [3, 1, 2, 5, 2, 1, 8]
def baseStart_2369930 : Nat := 118140960795 + 2369930 * 2 ^ 59
def prefixEnd_2369930 : Nat := 4983230072969 + 3 ^ 40 * 2369930 * 2
def baseEnd_2369930 : Nat := 30047239691605379547553

theorem tailTrace_2369930 : CollatzResearch.WordTrace tailWord_2369930 prefixEnd_2369930 30047239691605379547553 := by
  unfold tailWord_2369930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21609612076038959166292811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57625632202770557776780829 21609612076038959166292811)
  ·
    refine ⟨32414418114058438749439217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21609612076038959166292811 32414418114058438749439217)
    ·
      refine ⟨24310813585543829062079413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32414418114058438749439217 24310813585543829062079413)
      ·
        refine ⟨2279138773644733974569945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24310813585543829062079413 2279138773644733974569945)
        ·
          refine ⟨1709354080233550480927459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2279138773644733974569945 1709354080233550480927459)
          ·
            refine ⟨2564031120350325721391189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709354080233550480927459 2564031120350325721391189)
            ·
              refine ⟨30047239691605379547553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2564031120350325721391189 30047239691605379547553)
              ·
                rfl

theorem cell22_2369930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 8].length) (baseStart_2369930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369930 prefixEnd_2369930 := by exact prefixLift 2369930
  have htrace : WordTrace (prefixWord ++ tailWord_2369930) baseStart_2369930 baseEnd_2369930 := by
    simpa [prefixWord, tailWord_2369930, baseEnd_2369930] using wordTrace_append hprefix tailTrace_2369930
  have hstable : (prefixWord ++ tailWord_2369930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369930).length < 2 ^ (prefixWord ++ tailWord_2369930).sum := by decide
  have hdescent : baseEnd_2369930 < baseStart_2369930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369941 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 5]
def baseStart_2369941 : Nat := 118140960795 + 2369941 * 2 ^ 59
def prefixEnd_2369941 : Nat := 4983230072969 + 3 ^ 40 * 2369941 * 2
def baseEnd_2369941 : Nat := 270426412399381628586299

theorem tailTrace_2369941 : CollatzResearch.WordTrace tailWord_2369941 prefixEnd_2369941 270426412399381628586299 := by
  unfold tailWord_2369941
  simp only [CollatzResearch.WordTrace]
  refine ⟨86438849507115985543821677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57625899671410657029214451 86438849507115985543821677)
  ·
    refine ⟨32414568565168494578933129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86438849507115985543821677 32414568565168494578933129)
    ·
      refine ⟨24310926423876370934199847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32414568565168494578933129 24310926423876370934199847)
      ·
        refine ⟨36466389635814556401299771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24310926423876370934199847 36466389635814556401299771)
        ·
          refine ⟨54699584453721834601949657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36466389635814556401299771 54699584453721834601949657)
          ·
            refine ⟨41024688340291375951462243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54699584453721834601949657 41024688340291375951462243)
            ·
              refine ⟨61537032510437063927193365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41024688340291375951462243 61537032510437063927193365)
              ·
                refine ⟨2884548398926737371587189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61537032510437063927193365 2884548398926737371587189)
                ·
                  refine ⟨270426412399381628586299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2884548398926737371587189 270426412399381628586299)
                  ·
                    rfl

theorem cell22_2369941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_2369941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369941 prefixEnd_2369941 := by exact prefixLift 2369941
  have htrace : WordTrace (prefixWord ++ tailWord_2369941) baseStart_2369941 baseEnd_2369941 := by
    simpa [prefixWord, tailWord_2369941, baseEnd_2369941] using wordTrace_append hprefix tailTrace_2369941
  have hstable : (prefixWord ++ tailWord_2369941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369941).length < 2 ^ (prefixWord ++ tailWord_2369941).sum := by decide
  have hdescent : baseEnd_2369941 < baseStart_2369941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369956 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_2369956 : Nat := 118140960795 + 2369956 * 2 ^ 59
def prefixEnd_2369956 : Nat := 4983230072969 + 3 ^ 40 * 2369956 * 2
def baseEnd_2369956 : Nat := 811284372004689846633851

theorem tailTrace_2369956 : CollatzResearch.WordTrace tailWord_2369956 prefixEnd_2369956 811284372004689846633851 := by
  unfold tailWord_2369956
  simp only [CollatzResearch.WordTrace]
  refine ⟨43219698301030821552808861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57626264401374428737078481 43219698301030821552808861)
  ·
    refine ⟨16207386862886558082303323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43219698301030821552808861 16207386862886558082303323)
    ·
      refine ⟨24311080294329837123454985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16207386862886558082303323 24311080294329837123454985)
      ·
        refine ⟨18233310220747377842591239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24311080294329837123454985 18233310220747377842591239)
        ·
          refine ⟨27349965331121066763886859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18233310220747377842591239 27349965331121066763886859)
          ·
            refine ⟨41024947996681600145830289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27349965331121066763886859 41024947996681600145830289)
            ·
              refine ⟨30768710997511200109372717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41024947996681600145830289 30768710997511200109372717)
              ·
                refine ⟨11538266624066700041014769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30768710997511200109372717 11538266624066700041014769)
                ·
                  refine ⟨8653699968050025030761077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11538266624066700041014769 8653699968050025030761077)
                  ·
                    refine ⟨811284372004689846633851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8653699968050025030761077 811284372004689846633851)
                    ·
                      rfl

theorem cell22_2369956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_2369956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369956 prefixEnd_2369956 := by exact prefixLift 2369956
  have htrace : WordTrace (prefixWord ++ tailWord_2369956) baseStart_2369956 baseEnd_2369956 := by
    simpa [prefixWord, tailWord_2369956, baseEnd_2369956] using wordTrace_append hprefix tailTrace_2369956
  have hstable : (prefixWord ++ tailWord_2369956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369956).length < 2 ^ (prefixWord ++ tailWord_2369956).sum := by decide
  have hdescent : baseEnd_2369956 < baseStart_2369956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369996 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_2369996 : Nat := 118140960795 + 2369996 * 2 ^ 59
def prefixEnd_2369996 : Nat := 4983230072969 + 3 ^ 40 * 2369996 * 2
def baseEnd_2369996 : Nat := 811298064822143075633729

theorem tailTrace_2369996 : CollatzResearch.WordTrace tailWord_2369996 prefixEnd_2369996 811298064822143075633729 := by
  unfold tailWord_2369996
  simp only [CollatzResearch.WordTrace]
  refine ⟨43220427760958364968536921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57627237014611153291382561 43220427760958364968536921)
  ·
    refine ⟨32415320820718773726402691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43220427760958364968536921 32415320820718773726402691)
    ·
      refine ⟨48622981231078160589604037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32415320820718773726402691 48622981231078160589604037)
      ·
        refine ⟨9116808980827155110550757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48622981231078160589604037 9116808980827155110550757)
        ·
          refine ⟨1709401683905091583228267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9116808980827155110550757 1709401683905091583228267)
          ·
            refine ⟨2564102525857637374842401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709401683905091583228267 2564102525857637374842401)
            ·
              refine ⟨1923076894393228031131801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564102525857637374842401 1923076894393228031131801)
              ·
                refine ⟨1442307670794921023348851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923076894393228031131801 1442307670794921023348851)
                ·
                  refine ⟨2163461506192381535023277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442307670794921023348851 2163461506192381535023277)
                  ·
                    refine ⟨811298064822143075633729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163461506192381535023277 811298064822143075633729)
                    ·
                      rfl

theorem cell22_2369996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_2369996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2369996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2369996 prefixEnd_2369996 := by exact prefixLift 2369996
  have htrace : WordTrace (prefixWord ++ tailWord_2369996) baseStart_2369996 baseEnd_2369996 := by
    simpa [prefixWord, tailWord_2369996, baseEnd_2369996] using wordTrace_append hprefix tailTrace_2369996
  have hstable : (prefixWord ++ tailWord_2369996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369996).length < 2 ^ (prefixWord ++ tailWord_2369996).sum := by decide
  have hdescent : baseEnd_2369996 < baseStart_2369996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370016 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_2370016 : Nat := 118140960795 + 2370016 * 2 ^ 59
def prefixEnd_2370016 : Nat := 4983230072969 + 3 ^ 40 * 2370016 * 2
def baseEnd_2370016 : Nat := 811304911230869690133667

theorem tailTrace_2370016 : CollatzResearch.WordTrace tailWord_2370016 prefixEnd_2370016 811304911230869690133667 := by
  unfold tailWord_2370016
  simp only [CollatzResearch.WordTrace]
  refine ⟨43220792490922136676400951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57627723321229515568534601 43220792490922136676400951)
  ·
    refine ⟨64831188736383205014601427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43220792490922136676400951 64831188736383205014601427)
    ·
      refine ⟨97246783104574807521902141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64831188736383205014601427 97246783104574807521902141)
      ·
        refine ⟨36467543664215552820713303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97246783104574807521902141 36467543664215552820713303)
        ·
          refine ⟨54701315496323329231069955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36467543664215552820713303 54701315496323329231069955)
          ·
            refine ⟨82051973244484993846604933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54701315496323329231069955 82051973244484993846604933)
            ·
              refine ⟨15384744983340936346238425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82051973244484993846604933 15384744983340936346238425)
              ·
                refine ⟨11538558737505702259678819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15384744983340936346238425 11538558737505702259678819)
                ·
                  refine ⟨17307838106258553389518229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11538558737505702259678819 17307838106258553389518229)
                  ·
                    refine ⟨811304911230869690133667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17307838106258553389518229 811304911230869690133667)
                    ·
                      rfl

theorem cell22_2370016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_2370016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370016 prefixEnd_2370016 := by exact prefixLift 2370016
  have htrace : WordTrace (prefixWord ++ tailWord_2370016) baseStart_2370016 baseEnd_2370016 := by
    simpa [prefixWord, tailWord_2370016, baseEnd_2370016] using wordTrace_append hprefix tailTrace_2370016
  have hstable : (prefixWord ++ tailWord_2370016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370016).length < 2 ^ (prefixWord ++ tailWord_2370016).sum := by decide
  have hdescent : baseEnd_2370016 < baseStart_2370016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370052 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2370052 : Nat := 118140960795 + 2370052 * 2 ^ 59
def prefixEnd_2370052 : Nat := 4983230072969 + 3 ^ 40 * 2370052 * 2
def baseEnd_2370052 : Nat := 811317234766577596233557

theorem tailTrace_2370052 : CollatzResearch.WordTrace tailWord_2370052 prefixEnd_2370052 811317234766577596233557 := by
  unfold tailWord_2370052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43221449004856925750556205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57628598673142567667408273 43221449004856925750556205)
  ·
    refine ⟨16208043376821347156458577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43221449004856925750556205 16208043376821347156458577)
    ·
      refine ⟨12156032532616010367343933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16208043376821347156458577 12156032532616010367343933)
      ·
        refine ⟨4558512199731003887753975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12156032532616010367343933 4558512199731003887753975)
        ·
          refine ⟨6837768299596505831630963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558512199731003887753975 6837768299596505831630963)
          ·
            refine ⟨10256652449394758747446445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6837768299596505831630963 10256652449394758747446445)
            ·
              refine ⟨3846244668523034530292417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10256652449394758747446445 3846244668523034530292417)
              ·
                refine ⟨2884683501392275897719313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3846244668523034530292417 2884683501392275897719313)
                ·
                  refine ⟨2163512626044206923289485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2884683501392275897719313 2163512626044206923289485)
                  ·
                    refine ⟨811317234766577596233557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163512626044206923289485 811317234766577596233557)
                    ·
                      rfl

theorem cell22_2370052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2370052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370052 prefixEnd_2370052 := by exact prefixLift 2370052
  have htrace : WordTrace (prefixWord ++ tailWord_2370052) baseStart_2370052 baseEnd_2370052 := by
    simpa [prefixWord, tailWord_2370052, baseEnd_2370052] using wordTrace_append hprefix tailTrace_2370052
  have hstable : (prefixWord ++ tailWord_2370052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370052).length < 2 ^ (prefixWord ++ tailWord_2370052).sum := by decide
  have hdescent : baseEnd_2370052 < baseStart_2370052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370054 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2370054 : Nat := 118140960795 + 2370054 * 2 ^ 59
def prefixEnd_2370054 : Nat := 4983230072969 + 3 ^ 40 * 2370054 * 2
def baseEnd_2370054 : Nat := 270439306469150085894517

theorem tailTrace_2370054 : CollatzResearch.WordTrace tailWord_2370054 prefixEnd_2370054 270439306469150085894517 := by
  unfold tailWord_2370054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701342842365831432583913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57628647303804403895123477 2701342842365831432583913)
  ·
    refine ⟨2026007131774373574437935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2701342842365831432583913 2026007131774373574437935)
    ·
      refine ⟨3039010697661560361656903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026007131774373574437935 3039010697661560361656903)
      ·
        refine ⟨4558516046492340542485355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039010697661560361656903 4558516046492340542485355)
        ·
          refine ⟨6837774069738510813728033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558516046492340542485355 6837774069738510813728033)
          ·
            refine ⟨5128330552303883110296025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6837774069738510813728033 5128330552303883110296025)
            ·
              refine ⟨3846247914227912332722019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5128330552303883110296025 3846247914227912332722019)
              ·
                refine ⟨5769371871341868499083029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846247914227912332722019 5769371871341868499083029)
                ·
                  refine ⟨270439306469150085894517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5769371871341868499083029 270439306469150085894517)
                  ·
                    rfl

theorem cell22_2370054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2370054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370054 prefixEnd_2370054 := by exact prefixLift 2370054
  have htrace : WordTrace (prefixWord ++ tailWord_2370054) baseStart_2370054 baseEnd_2370054 := by
    simpa [prefixWord, tailWord_2370054, baseEnd_2370054] using wordTrace_append hprefix tailTrace_2370054
  have hstable : (prefixWord ++ tailWord_2370054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370054).length < 2 ^ (prefixWord ++ tailWord_2370054).sum := by decide
  have hdescent : baseEnd_2370054 < baseStart_2370054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370063 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 3, 3]
def baseStart_2370063 : Nat := 118140960795 + 2370063 * 2 ^ 59
def prefixEnd_2370063 : Nat := 4983230072969 + 3 ^ 40 * 2370063 * 2
def baseEnd_2370063 : Nat := 811321000291377234208523

theorem tailTrace_2370063 : CollatzResearch.WordTrace tailWord_2370063 prefixEnd_2370063 811321000291377234208523 := by
  unfold tailWord_2370063
  simp only [CollatzResearch.WordTrace]
  refine ⟨86443299212674000379762843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57628866141782666919841895 86443299212674000379762843)
  ·
    refine ⟨129664948819011000569644265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86443299212674000379762843 129664948819011000569644265)
    ·
      refine ⟨97248711614258250427233199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129664948819011000569644265 97248711614258250427233199)
      ·
        refine ⟨145873067421387375640849799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97248711614258250427233199 145873067421387375640849799)
        ·
          refine ⟨218809601132081063461274699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145873067421387375640849799 218809601132081063461274699)
          ·
            refine ⟨328214401698121595191912049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218809601132081063461274699 328214401698121595191912049)
            ·
              refine ⟨246160801273591196393934037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328214401698121595191912049 246160801273591196393934037)
              ·
                refine ⟨5769393779849793665482829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 246160801273591196393934037 5769393779849793665482829)
                ·
                  refine ⟨2163522667443672624556061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5769393779849793665482829 2163522667443672624556061)
                  ·
                    refine ⟨811321000291377234208523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163522667443672624556061 811321000291377234208523)
                    ·
                      rfl

theorem cell22_2370063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_2370063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370063 prefixEnd_2370063 := by exact prefixLift 2370063
  have htrace : WordTrace (prefixWord ++ tailWord_2370063) baseStart_2370063 baseEnd_2370063 := by
    simpa [prefixWord, tailWord_2370063, baseEnd_2370063] using wordTrace_append hprefix tailTrace_2370063
  have hstable : (prefixWord ++ tailWord_2370063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370063).length < 2 ^ (prefixWord ++ tailWord_2370063).sum := by decide
  have hdescent : baseEnd_2370063 < baseStart_2370063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370091 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_2370091 : Nat := 118140960795 + 2370091 * 2 ^ 59
def prefixEnd_2370091 : Nat := 4983230072969 + 3 ^ 40 * 2370091 * 2
def baseEnd_2370091 : Nat := 811330585263594494508437

theorem tailTrace_2370091 : CollatzResearch.WordTrace tailWord_2370091 prefixEnd_2370091 811330585263594494508437 := by
  unfold tailWord_2370091
  simp only [CollatzResearch.WordTrace]
  refine ⟨86444320456572561161782127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57629546971048374107854751 86444320456572561161782127)
  ·
    refine ⟨129666480684858841742673191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86444320456572561161782127 129666480684858841742673191)
    ·
      refine ⟨194499721027288262614009787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129666480684858841742673191 194499721027288262614009787)
      ·
        refine ⟨291749581540932393921014681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194499721027288262614009787 291749581540932393921014681)
        ·
          refine ⟨218812186155699295440761011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291749581540932393921014681 218812186155699295440761011)
          ·
            refine ⟨328218279233548943161141517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218812186155699295440761011 328218279233548943161141517)
            ·
              refine ⟨123081854712580853685428069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328218279233548943161141517 123081854712580853685428069)
              ·
                refine ⟨23077847758608910066017763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123081854712580853685428069 23077847758608910066017763)
                ·
                  refine ⟨34616771637913365099026645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23077847758608910066017763 34616771637913365099026645)
                  ·
                    refine ⟨811330585263594494508437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34616771637913365099026645 811330585263594494508437)
                    ·
                      rfl

theorem cell22_2370091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_2370091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370091 prefixEnd_2370091 := by exact prefixLift 2370091
  have htrace : WordTrace (prefixWord ++ tailWord_2370091) baseStart_2370091 baseEnd_2370091 := by
    simpa [prefixWord, tailWord_2370091, baseEnd_2370091] using wordTrace_append hprefix tailTrace_2370091
  have hstable : (prefixWord ++ tailWord_2370091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370091).length < 2 ^ (prefixWord ++ tailWord_2370091).sum := by decide
  have hdescent : baseEnd_2370091 < baseStart_2370091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370097 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 1, 3]
def baseStart_2370097 : Nat := 118140960795 + 2370097 * 2 ^ 59
def prefixEnd_2370097 : Nat := 4983230072969 + 3 ^ 40 * 2370097 * 2
def baseEnd_2370097 : Nat := 811332639186212478858419

theorem tailTrace_2370097 : CollatzResearch.WordTrace tailWord_2370097 prefixEnd_2370097 811332639186212478858419 := by
  unfold tailWord_2370097
  simp only [CollatzResearch.WordTrace]
  refine ⟨86444539294550824186500545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57629692863033882791000363 86444539294550824186500545)
  ·
    refine ⟨64833404470913118139875409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86444539294550824186500545 64833404470913118139875409)
    ·
      refine ⟨48625053353184838604906557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64833404470913118139875409 48625053353184838604906557)
      ·
        refine ⟨18234395007444314476839959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48625053353184838604906557 18234395007444314476839959)
        ·
          refine ⟨27351592511166471715259939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18234395007444314476839959 27351592511166471715259939)
          ·
            refine ⟨41027388766749707572889909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27351592511166471715259939 41027388766749707572889909)
            ·
              refine ⟨3846317696882785084958429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41027388766749707572889909 3846317696882785084958429)
              ·
                refine ⟨1442369136331044406859411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3846317696882785084958429 1442369136331044406859411)
                ·
                  refine ⟨2163553704496566610289117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442369136331044406859411 2163553704496566610289117)
                  ·
                    refine ⟨811332639186212478858419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163553704496566610289117 811332639186212478858419)
                    ·
                      rfl

theorem cell22_2370097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_2370097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370097 prefixEnd_2370097 := by exact prefixLift 2370097
  have htrace : WordTrace (prefixWord ++ tailWord_2370097) baseStart_2370097 baseEnd_2370097 := by
    simpa [prefixWord, tailWord_2370097, baseEnd_2370097] using wordTrace_append hprefix tailTrace_2370097
  have hstable : (prefixWord ++ tailWord_2370097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370097).length < 2 ^ (prefixWord ++ tailWord_2370097).sum := by decide
  have hdescent : baseEnd_2370097 < baseStart_2370097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370172 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_2370172 : Nat := 118140960795 + 2370172 * 2 ^ 59
def prefixEnd_2370172 : Nat := 4983230072969 + 3 ^ 40 * 2370172 * 2
def baseEnd_2370172 : Nat := 270452771072979094411063

theorem tailTrace_2370172 : CollatzResearch.WordTrace tailWord_2370172 prefixEnd_2370172 270452771072979094411063 := by
  unfold tailWord_2370172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43223637384639555997740385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57631516512852741330320513 43223637384639555997740385)
  ·
    refine ⟨32417728038479666998305289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43223637384639555997740385 32417728038479666998305289)
    ·
      refine ⟨24313296028859750248728967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32417728038479666998305289 24313296028859750248728967)
      ·
        refine ⟨36469944043289625373093451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24313296028859750248728967 36469944043289625373093451)
        ·
          refine ⟨54704916064934438059640177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36469944043289625373093451 54704916064934438059640177)
          ·
            refine ⟨41028687048700828544730133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54704916064934438059640177 41028687048700828544730133)
            ·
              refine ⟨1923219705407851338034225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41028687048700828544730133 1923219705407851338034225)
              ·
                refine ⟨1442414779055888503525669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923219705407851338034225 1442414779055888503525669)
                ·
                  refine ⟨270452771072979094411063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442414779055888503525669 270452771072979094411063)
                  ·
                    rfl

theorem cell22_2370172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_2370172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370172 prefixEnd_2370172 := by exact prefixLift 2370172
  have htrace : WordTrace (prefixWord ++ tailWord_2370172) baseStart_2370172 baseEnd_2370172 := by
    simpa [prefixWord, tailWord_2370172, baseEnd_2370172] using wordTrace_append hprefix tailTrace_2370172
  have hstable : (prefixWord ++ tailWord_2370172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370172).length < 2 ^ (prefixWord ++ tailWord_2370172).sum := by decide
  have hdescent : baseEnd_2370172 < baseStart_2370172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370200 : List Nat := [2, 1, 2, 4, 1, 1, 5, 6]
def baseStart_2370200 : Nat := 118140960795 + 2370200 * 2 ^ 59
def prefixEnd_2370200 : Nat := 4983230072969 + 3 ^ 40 * 2370200 * 2
def baseEnd_2370200 : Nat := 90151988687906060392567

theorem tailTrace_2370200 : CollatzResearch.WordTrace tailWord_2370200 prefixEnd_2370200 90151988687906060392567 := by
  unfold tailWord_2370200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43224148006588836388750027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57632197342118448518333369 43224148006588836388750027)
  ·
    refine ⟨64836222009883254583125041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43224148006588836388750027 64836222009883254583125041)
    ·
      refine ⟨48627166507412440937343781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64836222009883254583125041 48627166507412440937343781)
      ·
        refine ⟨9117593720139832675751959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48627166507412440937343781 9117593720139832675751959)
        ·
          refine ⟨13676390580209749013627939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117593720139832675751959 13676390580209749013627939)
          ·
            refine ⟨20514585870314623520441909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13676390580209749013627939 20514585870314623520441909)
            ·
              refine ⟨1923242425341995955041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20514585870314623520441909 1923242425341995955041429)
              ·
                refine ⟨90151988687906060392567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1923242425341995955041429 90151988687906060392567)
                ·
                  rfl

theorem cell22_2370200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_2370200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370200 prefixEnd_2370200 := by exact prefixLift 2370200
  have htrace : WordTrace (prefixWord ++ tailWord_2370200) baseStart_2370200 baseEnd_2370200 := by
    simpa [prefixWord, tailWord_2370200, baseEnd_2370200] using wordTrace_append hprefix tailTrace_2370200
  have hstable : (prefixWord ++ tailWord_2370200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370200).length < 2 ^ (prefixWord ++ tailWord_2370200).sum := by decide
  have hdescent : baseEnd_2370200 < baseStart_2370200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370202 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_2370202 : Nat := 118140960795 + 2370202 * 2 ^ 59
def prefixEnd_2370202 : Nat := 4983230072969 + 3 ^ 40 * 2370202 * 2
def baseEnd_2370202 : Nat := 811368582832027204983097

theorem tailTrace_2370202 : CollatzResearch.WordTrace tailWord_2370202 prefixEnd_2370202 811368582832027204983097 := by
  unfold tailWord_2370202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21612092239792606779768215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57632245972780284746048573 21612092239792606779768215)
  ·
    refine ⟨32418138359688910169652323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21612092239792606779768215 32418138359688910169652323)
    ·
      refine ⟨48627207539533365254478485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32418138359688910169652323 48627207539533365254478485)
      ·
        refine ⟨2279400353415626496303679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48627207539533365254478485 2279400353415626496303679)
        ·
          refine ⟨3419100530123439744455519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279400353415626496303679 3419100530123439744455519)
          ·
            refine ⟨5128650795185159616683279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419100530123439744455519 5128650795185159616683279)
            ·
              refine ⟨7692976192777739425024919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128650795185159616683279 7692976192777739425024919)
              ·
                refine ⟨11539464289166609137537379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692976192777739425024919 11539464289166609137537379)
                ·
                  refine ⟨17309196433749913706306069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11539464289166609137537379 17309196433749913706306069)
                  ·
                    refine ⟨811368582832027204983097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17309196433749913706306069 811368582832027204983097)
                    ·
                      rfl

theorem cell22_2370202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_2370202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370202 prefixEnd_2370202 := by exact prefixLift 2370202
  have htrace : WordTrace (prefixWord ++ tailWord_2370202) baseStart_2370202 baseEnd_2370202 := by
    simpa [prefixWord, tailWord_2370202, baseEnd_2370202] using wordTrace_append hprefix tailTrace_2370202
  have hstable : (prefixWord ++ tailWord_2370202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370202).length < 2 ^ (prefixWord ++ tailWord_2370202).sum := by decide
  have hdescent : baseEnd_2370202 < baseStart_2370202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370305 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2370305 : Nat := 118140960795 + 2370305 * 2 ^ 59
def prefixEnd_2370305 : Nat := 4983230072969 + 3 ^ 40 * 2370305 * 2
def baseEnd_2370305 : Nat := 811403841836969269657781

theorem tailTrace_2370305 : CollatzResearch.WordTrace tailWord_2370305 prefixEnd_2370305 811403841836969269657781 := by
  unfold tailWord_2370305
  simp only [CollatzResearch.WordTrace]
  refine ⟨86452125677797275710072369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57634750451864850473381579 86452125677797275710072369)
  ·
    refine ⟨64839094258347956782554277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86452125677797275710072369 64839094258347956782554277)
    ·
      refine ⟨12157330173440241896728927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64839094258347956782554277 12157330173440241896728927)
      ·
        refine ⟨18235995260160362845093391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12157330173440241896728927 18235995260160362845093391)
        ·
          refine ⟨27353992890240544267640087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18235995260160362845093391 27353992890240544267640087)
          ·
            refine ⟨41030989335360816401460131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27353992890240544267640087 41030989335360816401460131)
            ·
              refine ⟨61546484003041224602190197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41030989335360816401460131 61546484003041224602190197)
              ·
                refine ⟨5769982875285114806455331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61546484003041224602190197 5769982875285114806455331)
                ·
                  refine ⟨8654974312927672209682997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5769982875285114806455331 8654974312927672209682997)
                  ·
                    refine ⟨811403841836969269657781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8654974312927672209682997 811403841836969269657781)
                    ·
                      rfl

theorem cell22_2370305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2370305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370305 prefixEnd_2370305 := by exact prefixLift 2370305
  have htrace : WordTrace (prefixWord ++ tailWord_2370305) baseStart_2370305 baseEnd_2370305 := by
    simpa [prefixWord, tailWord_2370305, baseEnd_2370305] using wordTrace_append hprefix tailTrace_2370305
  have hstable : (prefixWord ++ tailWord_2370305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370305).length < 2 ^ (prefixWord ++ tailWord_2370305).sum := by decide
  have hdescent : baseEnd_2370305 < baseStart_2370305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370367 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 5, 3]
def baseStart_2370367 : Nat := 118140960795 + 2370367 * 2 ^ 59
def prefixEnd_2370367 : Nat := 4983230072969 + 3 ^ 40 * 2370367 * 2
def baseEnd_2370367 : Nat := 811425065704021774607591

theorem tailTrace_2370367 : CollatzResearch.WordTrace tailWord_2370367 prefixEnd_2370367 811425065704021774607591 := by
  unfold tailWord_2370367
  simp only [CollatzResearch.WordTrace]
  refine ⟨86454387003572660298829355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57636258002381773532552903 86454387003572660298829355)
  ·
    refine ⟨129681580505358990448244033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86454387003572660298829355 129681580505358990448244033)
    ·
      refine ⟨97261185379019242836183025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129681580505358990448244033 97261185379019242836183025)
      ·
        refine ⟨72945889034264432127137269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97261185379019242836183025 72945889034264432127137269)
        ·
          refine ⟨6838677096962290511919119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72945889034264432127137269 6838677096962290511919119)
          ·
            refine ⟨10258015645443435767878679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838677096962290511919119 10258015645443435767878679)
            ·
              refine ⟨15387023468165153651818019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10258015645443435767878679 15387023468165153651818019)
              ·
                refine ⟨23080535202247730477727029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15387023468165153651818019 23080535202247730477727029)
                ·
                  refine ⟨2163800175210724732286909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23080535202247730477727029 2163800175210724732286909)
                  ·
                    refine ⟨811425065704021774607591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163800175210724732286909 811425065704021774607591)
                    ·
                      rfl

theorem cell22_2370367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_2370367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370367 prefixEnd_2370367 := by exact prefixLift 2370367
  have htrace : WordTrace (prefixWord ++ tailWord_2370367) baseStart_2370367 baseEnd_2370367 := by
    simpa [prefixWord, tailWord_2370367, baseEnd_2370367] using wordTrace_append hprefix tailTrace_2370367
  have hstable : (prefixWord ++ tailWord_2370367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370367).length < 2 ^ (prefixWord ++ tailWord_2370367).sum := by decide
  have hdescent : baseEnd_2370367 < baseStart_2370367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370384 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 1, 3]
def baseStart_2370384 : Nat := 118140960795 + 2370384 * 2 ^ 59
def prefixEnd_2370384 : Nat := 4983230072969 + 3 ^ 40 * 2370384 * 2
def baseEnd_2370384 : Nat := 811430885151439396932539

theorem tailTrace_2370384 : CollatzResearch.WordTrace tailWord_2370384 prefixEnd_2370384 811430885151439396932539 := by
  unfold tailWord_2370384
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227503522255536101099103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57636671363007381468132137 43227503522255536101099103)
  ·
    refine ⟨64841255283383304151648655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43227503522255536101099103 64841255283383304151648655)
    ·
      refine ⟨97261882925074956227472983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64841255283383304151648655 97261882925074956227472983)
      ·
        refine ⟨145892824387612434341209475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97261882925074956227472983 145892824387612434341209475)
        ·
          refine ⟨218839236581418651511814213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145892824387612434341209475 218839236581418651511814213)
          ·
            refine ⟨41032356859015997158465165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218839236581418651511814213 41032356859015997158465165)
            ·
              refine ⟨15387133822130998934424437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41032356859015997158465165 15387133822130998934424437)
              ·
                refine ⟨1442543795824781150102291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15387133822130998934424437 1442543795824781150102291)
                ·
                  refine ⟨2163815693737171725153437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442543795824781150102291 2163815693737171725153437)
                  ·
                    refine ⟨811430885151439396932539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163815693737171725153437 811430885151439396932539)
                    ·
                      rfl

theorem cell22_2370384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_2370384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370384 prefixEnd_2370384 := by exact prefixLift 2370384
  have htrace : WordTrace (prefixWord ++ tailWord_2370384) baseStart_2370384 baseEnd_2370384 := by
    simpa [prefixWord, tailWord_2370384, baseEnd_2370384] using wordTrace_append hprefix tailTrace_2370384
  have hstable : (prefixWord ++ tailWord_2370384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370384).length < 2 ^ (prefixWord ++ tailWord_2370384).sum := by decide
  have hdescent : baseEnd_2370384 < baseStart_2370384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370427 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 1, 4]
def baseStart_2370427 : Nat := 118140960795 + 2370427 * 2 ^ 59
def prefixEnd_2370427 : Nat := 4983230072969 + 3 ^ 40 * 2370427 * 2
def baseEnd_2370427 : Nat := 811445604930201618107407

theorem tailTrace_2370427 : CollatzResearch.WordTrace tailWord_2370427 prefixEnd_2370427 811445604930201618107407 := by
  unfold tailWord_2370427
  simp only [CollatzResearch.WordTrace]
  refine ⟨86456575383355290546013535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57637716922236860364009023 86456575383355290546013535)
  ·
    refine ⟨129684863075032935819020303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86456575383355290546013535 129684863075032935819020303)
    ·
      refine ⟨194527294612549403728530455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129684863075032935819020303 194527294612549403728530455)
      ·
        refine ⟨291790941918824105592795683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194527294612549403728530455 291790941918824105592795683)
        ·
          refine ⟨437686412878236158389193525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291790941918824105592795683 437686412878236158389193525)
          ·
            refine ⟨41033101207334639848986893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 437686412878236158389193525 41033101207334639848986893)
            ·
              refine ⟨15387412952750489943370085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41033101207334639848986893 15387412952750489943370085)
              ·
                refine ⟨2885139928640716864381891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15387412952750489943370085 2885139928640716864381891)
                ·
                  refine ⟨4327709892961075296572837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885139928640716864381891 4327709892961075296572837)
                  ·
                    refine ⟨811445604930201618107407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327709892961075296572837 811445604930201618107407)
                    ·
                      rfl

theorem cell22_2370427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 4].length) (baseStart_2370427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370427 prefixEnd_2370427 := by exact prefixLift 2370427
  have htrace : WordTrace (prefixWord ++ tailWord_2370427) baseStart_2370427 baseEnd_2370427 := by
    simpa [prefixWord, tailWord_2370427, baseEnd_2370427] using wordTrace_append hprefix tailTrace_2370427
  have hstable : (prefixWord ++ tailWord_2370427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370427).length < 2 ^ (prefixWord ++ tailWord_2370427).sum := by decide
  have hdescent : baseEnd_2370427 < baseStart_2370427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370489 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_2370489 : Nat := 118140960795 + 2370489 * 2 ^ 59
def prefixEnd_2370489 : Nat := 4983230072969 + 3 ^ 40 * 2370489 * 2
def baseEnd_2370489 : Nat := 811466828797254123057217

theorem tailTrace_2370489 : CollatzResearch.WordTrace tailWord_2370489 prefixEnd_2370489 811466828797254123057217 := by
  unfold tailWord_2370489
  simp only [CollatzResearch.WordTrace]
  refine ⟨86458836709130675134770521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57639224472753783423180347 86458836709130675134770521)
  ·
    refine ⟨64844127531848006351077891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86458836709130675134770521 64844127531848006351077891)
    ·
      refine ⟨97266191297772009526616837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64844127531848006351077891 97266191297772009526616837)
      ·
        refine ⟨18237410868332251786240657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97266191297772009526616837 18237410868332251786240657)
        ·
          refine ⟨13678058151249188839680493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18237410868332251786240657 13678058151249188839680493)
          ·
            refine ⟨5129271806718445814880185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13678058151249188839680493 5129271806718445814880185)
            ·
              refine ⟨3846953855038834361160139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129271806718445814880185 3846953855038834361160139)
              ·
                refine ⟨5770430782558251541740209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846953855038834361160139 5770430782558251541740209)
                ·
                  refine ⟨4327823086918688656305157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770430782558251541740209 4327823086918688656305157)
                  ·
                    refine ⟨811466828797254123057217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327823086918688656305157 811466828797254123057217)
                    ·
                      rfl

theorem cell22_2370489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_2370489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370489 prefixEnd_2370489 := by exact prefixLift 2370489
  have htrace : WordTrace (prefixWord ++ tailWord_2370489) baseStart_2370489 baseEnd_2370489 := by
    simpa [prefixWord, tailWord_2370489, baseEnd_2370489] using wordTrace_append hprefix tailTrace_2370489
  have hstable : (prefixWord ++ tailWord_2370489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370489).length < 2 ^ (prefixWord ++ tailWord_2370489).sum := by decide
  have hdescent : baseEnd_2370489 < baseStart_2370489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370594 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_2370594 : Nat := 118140960795 + 2370594 * 2 ^ 59
def prefixEnd_2370594 : Nat := 4983230072969 + 3 ^ 40 * 2370594 * 2
def baseEnd_2370594 : Nat := 270500924147689616393965

theorem tailTrace_2370594 : CollatzResearch.WordTrace tailWord_2370594 prefixEnd_2370594 270500924147689616393965 := by
  unfold tailWord_2370594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21615666593437569516835709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57641777582500185378228557 21615666593437569516835709)
  ·
    refine ⟨8105874972539088568813391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21615666593437569516835709 8105874972539088568813391)
    ·
      refine ⟨12158812458808632853220087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105874972539088568813391 12158812458808632853220087)
      ·
        refine ⟨18238218688212949279830131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158812458808632853220087 18238218688212949279830131)
        ·
          refine ⟨27357328032319423919745197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18238218688212949279830131 27357328032319423919745197)
          ·
            refine ⟨10258998012119783969904449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27357328032319423919745197 10258998012119783969904449)
            ·
              refine ⟨7694248509089837977428337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10258998012119783969904449 7694248509089837977428337)
              ·
                refine ⟨5770686381817378483071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7694248509089837977428337 5770686381817378483071253)
                ·
                  refine ⟨270500924147689616393965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5770686381817378483071253 270500924147689616393965)
                  ·
                    rfl

theorem cell22_2370594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_2370594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370594 prefixEnd_2370594 := by exact prefixLift 2370594
  have htrace : WordTrace (prefixWord ++ tailWord_2370594) baseStart_2370594 baseEnd_2370594 := by
    simpa [prefixWord, tailWord_2370594, baseEnd_2370594] using wordTrace_append hprefix tailTrace_2370594
  have hstable : (prefixWord ++ tailWord_2370594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370594).length < 2 ^ (prefixWord ++ tailWord_2370594).sum := by decide
  have hdescent : baseEnd_2370594 < baseStart_2370594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370596 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_2370596 : Nat := 118140960795 + 2370596 * 2 ^ 59
def prefixEnd_2370596 : Nat := 4983230072969 + 3 ^ 40 * 2370596 * 2
def baseEnd_2370596 : Nat := 811503457083941510631889

theorem tailTrace_2370596 : CollatzResearch.WordTrace tailWord_2370596 prefixEnd_2370596 811503457083941510631889 := by
  unfold tailWord_2370596
  simp only [CollatzResearch.WordTrace]
  refine ⟨43231369659871516204457821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57641826213162021605943761 43231369659871516204457821)
  ·
    refine ⟨16211763622451818576671683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43231369659871516204457821 16211763622451818576671683)
    ·
      refine ⟨24317645433677727865007525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16211763622451818576671683 24317645433677727865007525)
      ·
        refine ⟨4559558518814573974688911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24317645433677727865007525 4559558518814573974688911)
        ·
          refine ⟨6839337778221860962033367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559558518814573974688911 6839337778221860962033367)
          ·
            refine ⟨10259006667332791443050051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6839337778221860962033367 10259006667332791443050051)
            ·
              refine ⟨15388510000999187164575077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10259006667332791443050051 15388510000999187164575077)
              ·
                refine ⟨2885345625187347593357827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15388510000999187164575077 2885345625187347593357827)
                ·
                  refine ⟨4328018437781021390036741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885345625187347593357827 4328018437781021390036741)
                  ·
                    refine ⟨811503457083941510631889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328018437781021390036741 811503457083941510631889)
                    ·
                      rfl

theorem cell22_2370596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_2370596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370596 prefixEnd_2370596 := by exact prefixLift 2370596
  have htrace : WordTrace (prefixWord ++ tailWord_2370596) baseStart_2370596 baseEnd_2370596 := by
    simpa [prefixWord, tailWord_2370596, baseEnd_2370596] using wordTrace_append hprefix tailTrace_2370596
  have hstable : (prefixWord ++ tailWord_2370596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370596).length < 2 ^ (prefixWord ++ tailWord_2370596).sum := by decide
  have hdescent : baseEnd_2370596 < baseStart_2370596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370609 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2370609 : Nat := 118140960795 + 2370609 * 2 ^ 59
def prefixEnd_2370609 : Nat := 4983230072969 + 3 ^ 40 * 2370609 * 2
def baseEnd_2370609 : Nat := 811507907249613810056849

theorem tailTrace_2370609 : CollatzResearch.WordTrace tailWord_2370609 prefixEnd_2370609 811507907249613810056849 := by
  unfold tailWord_2370609
  simp only [CollatzResearch.WordTrace]
  refine ⟨86463213468695935629138881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57642142312463957086092587 86463213468695935629138881)
  ·
    refine ⟨64847410101521951721854161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86463213468695935629138881 64847410101521951721854161)
    ·
      refine ⟨48635557576141463791390621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64847410101521951721854161 48635557576141463791390621)
      ·
        refine ⟨18238334091053048921771483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48635557576141463791390621 18238334091053048921771483)
        ·
          refine ⟨27357501136579573382657225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18238334091053048921771483 27357501136579573382657225)
          ·
            refine ⟨20518125852434680036992919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27357501136579573382657225 20518125852434680036992919)
            ·
              refine ⟨30777188778652020055489379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20518125852434680036992919 30777188778652020055489379)
              ·
                refine ⟨46165783167978030083234069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30777188778652020055489379 46165783167978030083234069)
                ·
                  refine ⟨2164021085998970160151597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46165783167978030083234069 2164021085998970160151597)
                  ·
                    refine ⟨811507907249613810056849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164021085998970160151597 811507907249613810056849)
                    ·
                      rfl

theorem cell22_2370609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2370609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370609 prefixEnd_2370609 := by exact prefixLift 2370609
  have htrace : WordTrace (prefixWord ++ tailWord_2370609) baseStart_2370609 baseEnd_2370609 := by
    simpa [prefixWord, tailWord_2370609, baseEnd_2370609] using wordTrace_append hprefix tailTrace_2370609
  have hstable : (prefixWord ++ tailWord_2370609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370609).length < 2 ^ (prefixWord ++ tailWord_2370609).sum := by decide
  have hdescent : baseEnd_2370609 < baseStart_2370609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370624 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_2370624 : Nat := 118140960795 + 2370624 * 2 ^ 59
def prefixEnd_2370624 : Nat := 4983230072969 + 3 ^ 40 * 2370624 * 2
def baseEnd_2370624 : Nat := 811513042056158770931803

theorem tailTrace_2370624 : CollatzResearch.WordTrace tailWord_2370624 prefixEnd_2370624 811513042056158770931803 := by
  unfold tailWord_2370624
  simp only [CollatzResearch.WordTrace]
  refine ⟨43231880281820796595467463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57642507042427728793956617 43231880281820796595467463)
  ·
    refine ⟨64847820422731194893201195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43231880281820796595467463 64847820422731194893201195)
    ·
      refine ⟨97271730634096792339801793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64847820422731194893201195 97271730634096792339801793)
      ·
        refine ⟨72953797975572594254851345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97271730634096792339801793 72953797975572594254851345)
        ·
          refine ⟨54715348481679445691138509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72953797975572594254851345 54715348481679445691138509)
          ·
            refine ⟨20518255680629792134176941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54715348481679445691138509 20518255680629792134176941)
            ·
              refine ⟨7694345880236172050316353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20518255680629792134176941 7694345880236172050316353)
              ·
                refine ⟨5770759410177129037737265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7694345880236172050316353 5770759410177129037737265)
                ·
                  refine ⟨4328069557632846778302949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770759410177129037737265 4328069557632846778302949)
                  ·
                    refine ⟨811513042056158770931803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328069557632846778302949 811513042056158770931803)
                    ·
                      rfl

theorem cell22_2370624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_2370624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370624 prefixEnd_2370624 := by exact prefixLift 2370624
  have htrace : WordTrace (prefixWord ++ tailWord_2370624) baseStart_2370624 baseEnd_2370624 := by
    simpa [prefixWord, tailWord_2370624, baseEnd_2370624] using wordTrace_append hprefix tailTrace_2370624
  have hstable : (prefixWord ++ tailWord_2370624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370624).length < 2 ^ (prefixWord ++ tailWord_2370624).sum := by decide
  have hdescent : baseEnd_2370624 < baseStart_2370624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370658 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2370658 : Nat := 118140960795 + 2370658 * 2 ^ 59
def prefixEnd_2370658 : Nat := 4983230072969 + 3 ^ 40 * 2370658 * 2
def baseEnd_2370658 : Nat := 811524680950994015581699

theorem tailTrace_2370658 : CollatzResearch.WordTrace tailWord_2370658 prefixEnd_2370658 811524680950994015581699 := by
  unfold tailWord_2370658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616250161379604249418157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57643333763678944665115085 21616250161379604249418157)
  ·
    refine ⟨8106093810517351593531809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21616250161379604249418157 8106093810517351593531809)
    ·
      refine ⟨6079570357888013695148857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8106093810517351593531809 6079570357888013695148857)
      ·
        refine ⟨4559677768416010271361643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6079570357888013695148857 4559677768416010271361643)
        ·
          refine ⟨6839516652624015407042465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559677768416010271361643 6839516652624015407042465)
          ·
            refine ⟨5129637489468011555281849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6839516652624015407042465 5129637489468011555281849)
            ·
              refine ⟨3847228117101008666461387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129637489468011555281849 3847228117101008666461387)
              ·
                refine ⟨5770842175651512999692081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847228117101008666461387 5770842175651512999692081)
                ·
                  refine ⟨4328131631738634749769061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5770842175651512999692081 4328131631738634749769061)
                  ·
                    refine ⟨811524680950994015581699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328131631738634749769061 811524680950994015581699)
                    ·
                      rfl

theorem cell22_2370658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2370658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370658 prefixEnd_2370658 := by exact prefixLift 2370658
  have htrace : WordTrace (prefixWord ++ tailWord_2370658) baseStart_2370658 baseEnd_2370658 := by
    simpa [prefixWord, tailWord_2370658, baseEnd_2370658] using wordTrace_append hprefix tailTrace_2370658
  have hstable : (prefixWord ++ tailWord_2370658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370658).length < 2 ^ (prefixWord ++ tailWord_2370658).sum := by decide
  have hdescent : baseEnd_2370658 < baseStart_2370658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370722 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2370722 : Nat := 118140960795 + 2370722 * 2 ^ 59
def prefixEnd_2370722 : Nat := 4983230072969 + 3 ^ 40 * 2370722 * 2
def baseEnd_2370722 : Nat := 811546589458919181981503

theorem tailTrace_2370722 : CollatzResearch.WordTrace tailWord_2370722 prefixEnd_2370722 811546589458919181981503 := by
  unfold tailWord_2370722
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616833729321638982000605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57644889944857703952001613 21616833729321638982000605)
  ·
    refine ⟨8106312648495614618250227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21616833729321638982000605 8106312648495614618250227)
    ·
      refine ⟨12159468972743421927375341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8106312648495614618250227 12159468972743421927375341)
      ·
        refine ⟨4559800864778783222765753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12159468972743421927375341 4559800864778783222765753)
        ·
          refine ⟨3419850648584087417074315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559800864778783222765753 3419850648584087417074315)
          ·
            refine ⟨5129775972876131125611473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419850648584087417074315 5129775972876131125611473)
            ·
              refine ⟨3847331979657098344208605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129775972876131125611473 3847331979657098344208605)
              ·
                refine ⟨1442749492371411879078227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3847331979657098344208605 1442749492371411879078227)
                ·
                  refine ⟨2164124238557117818617341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442749492371411879078227 2164124238557117818617341)
                  ·
                    refine ⟨811546589458919181981503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164124238557117818617341 811546589458919181981503)
                    ·
                      rfl

theorem cell22_2370722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2370722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370722 prefixEnd_2370722 := by exact prefixLift 2370722
  have htrace : WordTrace (prefixWord ++ tailWord_2370722) baseStart_2370722 baseEnd_2370722 := by
    simpa [prefixWord, tailWord_2370722, baseEnd_2370722] using wordTrace_append hprefix tailTrace_2370722
  have hstable : (prefixWord ++ tailWord_2370722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370722).length < 2 ^ (prefixWord ++ tailWord_2370722).sum := by decide
  have hdescent : baseEnd_2370722 < baseStart_2370722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370812 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_2370812 : Nat := 118140960795 + 2370812 * 2 ^ 59
def prefixEnd_2370812 : Nat := 4983230072969 + 3 ^ 40 * 2370812 * 2
def baseEnd_2370812 : Nat := 811577398298188947231227

theorem tailTrace_2370812 : CollatzResearch.WordTrace tailWord_2370812 prefixEnd_2370812 811577398298188947231227 := by
  unfold tailWord_2370812
  simp only [CollatzResearch.WordTrace]
  refine ⟨43235308743480250649389345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57647078324640334199185793 43235308743480250649389345)
  ·
    refine ⟨32426481557610187987042009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43235308743480250649389345 32426481557610187987042009)
    ·
      refine ⟨24319861168207640990281507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32426481557610187987042009 24319861168207640990281507)
      ·
        refine ⟨36479791752311461485422261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24319861168207640990281507 36479791752311461485422261)
        ·
          refine ⟨3419980476779199514258337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36479791752311461485422261 3419980476779199514258337)
          ·
            refine ⟨2564985357584399635693753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419980476779199514258337 2564985357584399635693753)
            ·
              refine ⟨1923739018188299726770315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564985357584399635693753 1923739018188299726770315)
              ·
                refine ⟨2885608527282449590155473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923739018188299726770315 2885608527282449590155473)
                ·
                  refine ⟨2164206395461837192616605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2885608527282449590155473 2164206395461837192616605)
                  ·
                    refine ⟨811577398298188947231227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164206395461837192616605 811577398298188947231227)
                    ·
                      rfl

theorem cell22_2370812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_2370812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370812 prefixEnd_2370812 := by exact prefixLift 2370812
  have htrace : WordTrace (prefixWord ++ tailWord_2370812) baseStart_2370812 baseEnd_2370812 := by
    simpa [prefixWord, tailWord_2370812, baseEnd_2370812] using wordTrace_append hprefix tailTrace_2370812
  have hstable : (prefixWord ++ tailWord_2370812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370812).length < 2 ^ (prefixWord ++ tailWord_2370812).sum := by decide
  have hdescent : baseEnd_2370812 < baseStart_2370812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370853 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 5]
def baseStart_2370853 : Nat := 118140960795 + 2370853 * 2 ^ 59
def prefixEnd_2370853 : Nat := 4983230072969 + 3 ^ 40 * 2370853 * 2
def baseEnd_2370853 : Nat := 270530477812026168985367

theorem tailTrace_2370853 : CollatzResearch.WordTrace tailWord_2370853 prefixEnd_2370853 270530477812026168985367 := by
  unfold tailWord_2370853
  simp only [CollatzResearch.WordTrace]
  refine ⟨86472112879811965301021213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57648075253207976867347475 86472112879811965301021213)
  ·
    refine ⟨32427042329929486987882955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86472112879811965301021213 32427042329929486987882955)
    ·
      refine ⟨48640563494894230481824433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32427042329929486987882955 48640563494894230481824433)
      ·
        refine ⟨36480422621170672861368325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48640563494894230481824433 36480422621170672861368325)
        ·
          refine ⟨6840079241469501161506561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36480422621170672861368325 6840079241469501161506561)
          ·
            refine ⟨5130059431102125871129921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6840079241469501161506561 5130059431102125871129921)
            ·
              refine ⟨3847544573326594403347441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5130059431102125871129921 3847544573326594403347441)
              ·
                refine ⟨2885658429994945802510581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847544573326594403347441 2885658429994945802510581)
                ·
                  refine ⟨270530477812026168985367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2885658429994945802510581 270530477812026168985367)
                  ·
                    rfl

theorem cell22_2370853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_2370853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370853 prefixEnd_2370853 := by exact prefixLift 2370853
  have htrace : WordTrace (prefixWord ++ tailWord_2370853) baseStart_2370853 baseEnd_2370853 := by
    simpa [prefixWord, tailWord_2370853, baseEnd_2370853] using wordTrace_append hprefix tailTrace_2370853
  have hstable : (prefixWord ++ tailWord_2370853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370853).length < 2 ^ (prefixWord ++ tailWord_2370853).sum := by decide
  have hdescent : baseEnd_2370853 < baseStart_2370853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370868 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2370868 : Nat := 118140960795 + 2370868 * 2 ^ 59
def prefixEnd_2370868 : Nat := 4983230072969 + 3 ^ 40 * 2370868 * 2
def baseEnd_2370868 : Nat := 811596568242623467831055

theorem tailTrace_2370868 : CollatzResearch.WordTrace tailWord_2370868 prefixEnd_2370868 811596568242623467831055 := by
  unfold tailWord_2370868
  simp only [CollatzResearch.WordTrace]
  refine ⟨43236329987378811431408629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57648439983171748575211505 43236329987378811431408629)
  ·
    refine ⟨4053405936316763571694559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43236329987378811431408629 4053405936316763571694559)
    ·
      refine ⟨6080108904475145357541839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4053405936316763571694559 6080108904475145357541839)
      ·
        refine ⟨9120163356712718036312759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6080108904475145357541839 9120163356712718036312759)
        ·
          refine ⟨13680245035069077054469139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9120163356712718036312759 13680245035069077054469139)
          ·
            refine ⟨20520367552603615581703709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13680245035069077054469139 20520367552603615581703709)
            ·
              refine ⟨7695137832226355843138891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20520367552603615581703709 7695137832226355843138891)
              ·
                refine ⟨11542706748339533764708337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695137832226355843138891 11542706748339533764708337)
                ·
                  refine ⟨8657030061254650323531253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11542706748339533764708337 8657030061254650323531253)
                  ·
                    refine ⟨811596568242623467831055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8657030061254650323531253 811596568242623467831055)
                    ·
                      rfl

theorem cell22_2370868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2370868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370868 prefixEnd_2370868 := by exact prefixLift 2370868
  have htrace : WordTrace (prefixWord ++ tailWord_2370868) baseStart_2370868 baseEnd_2370868 := by
    simpa [prefixWord, tailWord_2370868, baseEnd_2370868] using wordTrace_append hprefix tailTrace_2370868
  have hstable : (prefixWord ++ tailWord_2370868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370868).length < 2 ^ (prefixWord ++ tailWord_2370868).sum := by decide
  have hdescent : baseEnd_2370868 < baseStart_2370868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370896 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_2370896 : Nat := 118140960795 + 2370896 * 2 ^ 59
def prefixEnd_2370896 : Nat := 4983230072969 + 3 ^ 40 * 2370896 * 2
def baseEnd_2370896 : Nat := 811606153214840728130969

theorem tailTrace_2370896 : CollatzResearch.WordTrace tailWord_2370896 prefixEnd_2370896 811606153214840728130969 := by
  unfold tailWord_2370896
  simp only [CollatzResearch.WordTrace]
  refine ⟨43236840609328091822418271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57649120812437455763224361 43236840609328091822418271)
  ·
    refine ⟨64855260913992137733627407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43236840609328091822418271 64855260913992137733627407)
    ·
      refine ⟨97282891370988206600441111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64855260913992137733627407 97282891370988206600441111)
      ·
        refine ⟨145924337056482309900661667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97282891370988206600441111 145924337056482309900661667)
        ·
          refine ⟨218886505584723464850992501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145924337056482309900661667 218886505584723464850992501)
          ·
            refine ⟨20520609898567824829780547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218886505584723464850992501 20520609898567824829780547)
            ·
              refine ⟨30780914847851737244670821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20520609898567824829780547 30780914847851737244670821)
              ·
                refine ⟨5771421533972200733375779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30780914847851737244670821 5771421533972200733375779)
                ·
                  refine ⟨8657132300958301100063669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5771421533972200733375779 8657132300958301100063669)
                  ·
                    refine ⟨811606153214840728130969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8657132300958301100063669 811606153214840728130969)
                    ·
                      rfl

theorem cell22_2370896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_2370896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370896 prefixEnd_2370896 := by exact prefixLift 2370896
  have htrace : WordTrace (prefixWord ++ tailWord_2370896) baseStart_2370896 baseEnd_2370896 := by
    simpa [prefixWord, tailWord_2370896, baseEnd_2370896] using wordTrace_append hprefix tailTrace_2370896
  have hstable : (prefixWord ++ tailWord_2370896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370896).length < 2 ^ (prefixWord ++ tailWord_2370896).sum := by decide
  have hdescent : baseEnd_2370896 < baseStart_2370896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370911 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_2370911 : Nat := 118140960795 + 2370911 * 2 ^ 59
def prefixEnd_2370911 : Nat := 4983230072969 + 3 ^ 40 * 2370911 * 2
def baseEnd_2370911 : Nat := 811611288021385689005923

theorem tailTrace_2370911 : CollatzResearch.WordTrace tailWord_2370911 prefixEnd_2370911 811611288021385689005923 := by
  unfold tailWord_2370911
  simp only [CollatzResearch.WordTrace]
  refine ⟨86474228313601841206632587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57649485542401227471088391 86474228313601841206632587)
  ·
    refine ⟨129711342470402761809948881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86474228313601841206632587 129711342470402761809948881)
    ·
      refine ⟨97283506852802071357461661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129711342470402761809948881 97283506852802071357461661)
      ·
        refine ⟨36481315069800776759048123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97283506852802071357461661 36481315069800776759048123)
        ·
          refine ⟨54721972604701165138572185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36481315069800776759048123 54721972604701165138572185)
          ·
            refine ⟨41041479453525873853929139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54721972604701165138572185 41041479453525873853929139)
            ·
              refine ⟨61562219180288810780893709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41041479453525873853929139 61562219180288810780893709)
              ·
                refine ⟨23085832192608304042835141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61562219180288810780893709 23085832192608304042835141)
                ·
                  refine ⟨4328593536114057008031589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23085832192608304042835141 4328593536114057008031589)
                  ·
                    refine ⟨811611288021385689005923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328593536114057008031589 811611288021385689005923)
                    ·
                      rfl

theorem cell22_2370911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_2370911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370911 prefixEnd_2370911 := by exact prefixLift 2370911
  have htrace : WordTrace (prefixWord ++ tailWord_2370911) baseStart_2370911 baseEnd_2370911 := by
    simpa [prefixWord, tailWord_2370911, baseEnd_2370911] using wordTrace_append hprefix tailTrace_2370911
  have hstable : (prefixWord ++ tailWord_2370911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370911).length < 2 ^ (prefixWord ++ tailWord_2370911).sum := by decide
  have hdescent : baseEnd_2370911 < baseStart_2370911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370941 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2370941 : Nat := 118140960795 + 2370941 * 2 ^ 59
def prefixEnd_2370941 : Nat := 4983230072969 + 3 ^ 40 * 2370941 * 2
def baseEnd_2370941 : Nat := 811621557634475610755831

theorem tailTrace_2370941 : CollatzResearch.WordTrace tailWord_2370941 prefixEnd_2370941 811621557634475610755831 := by
  unfold tailWord_2370941
  simp only [CollatzResearch.WordTrace]
  refine ⟨86475322503493156330224677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57650215002328770886816451 86475322503493156330224677)
  ·
    refine ⟨16214122969404966811917127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86475322503493156330224677 16214122969404966811917127)
    ·
      refine ⟨24321184454107450217875691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214122969404966811917127 24321184454107450217875691)
      ·
        refine ⟨36481776681161175326813537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321184454107450217875691 36481776681161175326813537)
        ·
          refine ⟨27361332510870881495110153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36481776681161175326813537 27361332510870881495110153)
          ·
            refine ⟨20520999383153161121332615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27361332510870881495110153 20520999383153161121332615)
            ·
              refine ⟨30781499074729741681998923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20520999383153161121332615 30781499074729741681998923)
              ·
                refine ⟨46172248612094612522998385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30781499074729741681998923 46172248612094612522998385)
                ·
                  refine ⟨34629186459070959392248789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46172248612094612522998385 34629186459070959392248789)
                  ·
                    refine ⟨811621557634475610755831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34629186459070959392248789 811621557634475610755831)
                    ·
                      rfl

theorem cell22_2370941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2370941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370941 prefixEnd_2370941 := by exact prefixLift 2370941
  have htrace : WordTrace (prefixWord ++ tailWord_2370941) baseStart_2370941 baseEnd_2370941 := by
    simpa [prefixWord, tailWord_2370941, baseEnd_2370941] using wordTrace_append hprefix tailTrace_2370941
  have hstable : (prefixWord ++ tailWord_2370941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370941).length < 2 ^ (prefixWord ++ tailWord_2370941).sum := by decide
  have hdescent : baseEnd_2370941 < baseStart_2370941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370962 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2370962 : Nat := 118140960795 + 2370962 * 2 ^ 59
def prefixEnd_2370962 : Nat := 4983230072969 + 3 ^ 40 * 2370962 * 2
def baseEnd_2370962 : Nat := 811628746363638555980767

theorem tailTrace_2370962 : CollatzResearch.WordTrace tailWord_2370962 prefixEnd_2370962 811628746363638555980767 := by
  unfold tailWord_2370962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21619022109104269229184785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57650725624278051277826093 21619022109104269229184785)
  ·
    refine ⟨16214266581828201921888589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21619022109104269229184785 16214266581828201921888589)
    ·
      refine ⟨6080349968185575720708221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16214266581828201921888589 6080349968185575720708221)
      ·
        refine ⟨2280131238069590895265583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6080349968185575720708221 2280131238069590895265583)
        ·
          refine ⟨3420196857104386342898375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280131238069590895265583 3420196857104386342898375)
          ·
            refine ⟨5130295285656579514347563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420196857104386342898375 5130295285656579514347563)
            ·
              refine ⟨7695442928484869271521345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130295285656579514347563 7695442928484869271521345)
              ·
                refine ⟨5771582196363651953641009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7695442928484869271521345 5771582196363651953641009)
                ·
                  refine ⟨4328686647272738965230757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5771582196363651953641009 4328686647272738965230757)
                  ·
                    refine ⟨811628746363638555980767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328686647272738965230757 811628746363638555980767)
                    ·
                      rfl

theorem cell22_2370962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2370962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370962 prefixEnd_2370962 := by exact prefixLift 2370962
  have htrace : WordTrace (prefixWord ++ tailWord_2370962) baseStart_2370962 baseEnd_2370962 := by
    simpa [prefixWord, tailWord_2370962, baseEnd_2370962] using wordTrace_append hprefix tailTrace_2370962
  have hstable : (prefixWord ++ tailWord_2370962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370962).length < 2 ^ (prefixWord ++ tailWord_2370962).sum := by decide
  have hdescent : baseEnd_2370962 < baseStart_2370962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370975 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 3, 3]
def baseStart_2370975 : Nat := 118140960795 + 2370975 * 2 ^ 59
def prefixEnd_2370975 : Nat := 4983230072969 + 3 ^ 40 * 2370975 * 2
def baseEnd_2370975 : Nat := 811633196529310855405727

theorem tailTrace_2370975 : CollatzResearch.WordTrace tailWord_2370975 prefixEnd_2370975 811633196529310855405727 := by
  unfold tailWord_2370975
  simp only [CollatzResearch.WordTrace]
  refine ⟨86476562585369980136962379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57651041723579986757974919 86476562585369980136962379)
  ·
    refine ⟨129714843878054970205443569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86476562585369980136962379 129714843878054970205443569)
    ·
      refine ⟨97286132908541227654082677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129714843878054970205443569 97286132908541227654082677)
      ·
        refine ⟨9120574960175740092570251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97286132908541227654082677 9120574960175740092570251)
        ·
          refine ⟨13680862440263610138855377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9120574960175740092570251 13680862440263610138855377)
          ·
            refine ⟨10260646830197707604141533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13680862440263610138855377 10260646830197707604141533)
            ·
              refine ⟨3847742561324140351553075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10260646830197707604141533 3847742561324140351553075)
              ·
                refine ⟨5771613841986210527329613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847742561324140351553075 5771613841986210527329613)
                ·
                  refine ⟨2164355190744828947748605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5771613841986210527329613 2164355190744828947748605)
                  ·
                    refine ⟨811633196529310855405727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2164355190744828947748605 811633196529310855405727)
                    ·
                      rfl

theorem cell22_2370975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_2370975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2370975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2370975 prefixEnd_2370975 := by exact prefixLift 2370975
  have htrace : WordTrace (prefixWord ++ tailWord_2370975) baseStart_2370975 baseEnd_2370975 := by
    simpa [prefixWord, tailWord_2370975, baseEnd_2370975] using wordTrace_append hprefix tailTrace_2370975
  have hstable : (prefixWord ++ tailWord_2370975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370975).length < 2 ^ (prefixWord ++ tailWord_2370975).sum := by decide
  have hdescent : baseEnd_2370975 < baseStart_2370975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371050 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_2371050 : Nat := 118140960795 + 2371050 * 2 ^ 59
def prefixEnd_2371050 : Nat := 4983230072969 + 3 ^ 40 * 2371050 * 2
def baseEnd_2371050 : Nat := 270552956854011886593499

theorem tailTrace_2371050 : CollatzResearch.WordTrace tailWord_2371050 prefixEnd_2371050 270552956854011886593499 := by
  unfold tailWord_2371050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21619824515024566986485651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57652865373398845297295069 21619824515024566986485651)
  ·
    refine ⟨32429736772536850479728477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21619824515024566986485651 32429736772536850479728477)
    ·
      refine ⟨12161151289701318929898179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32429736772536850479728477 12161151289701318929898179)
      ·
        refine ⟨18241726934551978394847269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161151289701318929898179 18241726934551978394847269)
        ·
          refine ⟨3420323800228495949033863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18241726934551978394847269 3420323800228495949033863)
          ·
            refine ⟨5130485700342743923550795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420323800228495949033863 5130485700342743923550795)
            ·
              refine ⟨7695728550514115885326193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130485700342743923550795 7695728550514115885326193)
              ·
                refine ⟨5771796412885586913994645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7695728550514115885326193 5771796412885586913994645)
                ·
                  refine ⟨270552956854011886593499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5771796412885586913994645 270552956854011886593499)
                  ·
                    rfl

theorem cell22_2371050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_2371050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371050 prefixEnd_2371050 := by exact prefixLift 2371050
  have htrace : WordTrace (prefixWord ++ tailWord_2371050) baseStart_2371050 baseEnd_2371050 := by
    simpa [prefixWord, tailWord_2371050, baseEnd_2371050] using wordTrace_append hprefix tailTrace_2371050
  have hstable : (prefixWord ++ tailWord_2371050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371050).length < 2 ^ (prefixWord ++ tailWord_2371050).sum := by decide
  have hdescent : baseEnd_2371050 < baseStart_2371050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371063 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_2371063 : Nat := 118140960795 + 2371063 * 2 ^ 59
def prefixEnd_2371063 : Nat := 4983230072969 + 3 ^ 40 * 2371063 * 2
def baseEnd_2371063 : Nat := 811663320727707959205457

theorem tailTrace_2371063 : CollatzResearch.WordTrace tailWord_2371063 prefixEnd_2371063 811663320727707959205457 := by
  unfold tailWord_2371063
  simp only [CollatzResearch.WordTrace]
  refine ⟨86479772209051171166165843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57653181472700780777443895 86479772209051171166165843)
  ·
    refine ⟨129719658313576756749248765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86479772209051171166165843 129719658313576756749248765)
    ·
      refine ⟨48644871867591283780968287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129719658313576756749248765 48644871867591283780968287)
      ·
        refine ⟨72967307801386925671452431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48644871867591283780968287 72967307801386925671452431)
        ·
          refine ⟨109450961702080388507178647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72967307801386925671452431 109450961702080388507178647)
          ·
            refine ⟨164176442553120582760767971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109450961702080388507178647 164176442553120582760767971)
            ·
              refine ⟨246264663829680874141151957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164176442553120582760767971 246264663829680874141151957)
              ·
                refine ⟨5771828058508145487683249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 246264663829680874141151957 5771828058508145487683249)
                ·
                  refine ⟨4328871043881109115762437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5771828058508145487683249 4328871043881109115762437)
                  ·
                    refine ⟨811663320727707959205457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328871043881109115762437 811663320727707959205457)
                    ·
                      rfl

theorem cell22_2371063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_2371063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2371063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2371063 prefixEnd_2371063 := by exact prefixLift 2371063
  have htrace : WordTrace (prefixWord ++ tailWord_2371063) baseStart_2371063 baseEnd_2371063 := by
    simpa [prefixWord, tailWord_2371063, baseEnd_2371063] using wordTrace_append hprefix tailTrace_2371063
  have hstable : (prefixWord ++ tailWord_2371063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371063).length < 2 ^ (prefixWord ++ tailWord_2371063).sum := by decide
  have hdescent : baseEnd_2371063 < baseStart_2371063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
