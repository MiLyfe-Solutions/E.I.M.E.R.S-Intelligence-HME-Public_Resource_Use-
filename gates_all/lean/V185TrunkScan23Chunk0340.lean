import V185TrunkScan23Chunk0339

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2009715 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 1, 4]
def baseStart_2009715 : Nat := 118140960795 + 2009715 * 2 ^ 59
def prefixEnd_2009715 : Nat := 4983230072969 + 3 ^ 40 * 2009715 * 2
def baseEnd_2009715 : Nat := 343983257850236571506665

theorem tailTrace_2009715 : CollatzResearch.WordTrace tailWord_2009715 prefixEnd_2009715 343983257850236571506665 := by
  unfold tailWord_2009715
  simp only [CollatzResearch.WordTrace]
  refine ⟨73300327914153261841014599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48866885276102174560676399 73300327914153261841014599)
  ·
    refine ⟨109950491871229892761521899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73300327914153261841014599 109950491871229892761521899)
    ·
      refine ⟨164925737806844839142282849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109950491871229892761521899 164925737806844839142282849)
      ·
        refine ⟨123694303355133629356712137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164925737806844839142282849 123694303355133629356712137)
        ·
          refine ⟨92770727516350222017534103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123694303355133629356712137 92770727516350222017534103)
          ·
            refine ⟨139156091274525333026301155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92770727516350222017534103 139156091274525333026301155)
            ·
              refine ⟨208734136911787999539451733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139156091274525333026301155 208734136911787999539451733)
              ·
                refine ⟨1223051583467507809801475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 208734136911787999539451733 1223051583467507809801475)
                ·
                  refine ⟨1834577375201261714702213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223051583467507809801475 1834577375201261714702213)
                  ·
                    refine ⟨343983257850236571506665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834577375201261714702213 343983257850236571506665)
                    ·
                      rfl

theorem cell23_2009715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 4].length) (baseStart_2009715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009715 prefixEnd_2009715 := by exact prefixLift 2009715
  have htrace : WordTrace (prefixWord ++ tailWord_2009715) baseStart_2009715 baseEnd_2009715 := by
    simpa [prefixWord, tailWord_2009715, baseEnd_2009715] using wordTrace_append hprefix tailTrace_2009715
  have hstable : (prefixWord ++ tailWord_2009715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009715).length < 2 ^ (prefixWord ++ tailWord_2009715).sum := by decide
  have hdescent : baseEnd_2009715 < baseStart_2009715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009731 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_2009731 : Nat := 118140960795 + 2009731 * 2 ^ 59
def prefixEnd_2009731 : Nat := 4983230072969 + 3 ^ 40 * 2009731 * 2
def baseEnd_2009731 : Nat := 1031957989241181651919921

theorem tailTrace_2009731 : CollatzResearch.WordTrace tailWord_2009731 prefixEnd_2009731 1031957989241181651919921 := by
  unfold tailWord_2009731
  simp only [CollatzResearch.WordTrace]
  refine ⟨73300911482095296573597047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48867274321396864382398031 73300911482095296573597047)
  ·
    refine ⟨109951367223142944860395571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73300911482095296573597047 109951367223142944860395571)
    ·
      refine ⟨164927050834714417290593357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109951367223142944860395571 164927050834714417290593357)
      ·
        refine ⟨61847644063017906483972509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164927050834714417290593357 61847644063017906483972509)
        ·
          refine ⟨23192866523631714931489691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61847644063017906483972509 23192866523631714931489691)
          ·
            refine ⟨34789299785447572397234537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23192866523631714931489691 34789299785447572397234537)
            ·
              refine ⟨26091974839085679297925903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34789299785447572397234537 26091974839085679297925903)
              ·
                refine ⟨39137962258628518946888855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26091974839085679297925903 39137962258628518946888855)
                ·
                  refine ⟨58706943387942778420333283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39137962258628518946888855 58706943387942778420333283)
                  ·
                    refine ⟨88060415081914167630499925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58706943387942778420333283 88060415081914167630499925)
                    ·
                      refine ⟨1031957989241181651919921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88060415081914167630499925 1031957989241181651919921)
                      ·
                        rfl

theorem cell23_2009731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_2009731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009731 prefixEnd_2009731 := by exact prefixLift 2009731
  have htrace : WordTrace (prefixWord ++ tailWord_2009731) baseStart_2009731 baseEnd_2009731 := by
    simpa [prefixWord, tailWord_2009731, baseEnd_2009731] using wordTrace_append hprefix tailTrace_2009731
  have hstable : (prefixWord ++ tailWord_2009731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009731).length < 2 ^ (prefixWord ++ tailWord_2009731).sum := by decide
  have hdescent : baseEnd_2009731 < baseStart_2009731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009732 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_2009732 : Nat := 118140960795 + 2009732 * 2 ^ 59
def prefixEnd_2009732 : Nat := 4983230072969 + 3 ^ 40 * 2009732 * 2
def baseEnd_2009732 : Nat := 343986167573945382669139

theorem tailTrace_2009732 : CollatzResearch.WordTrace tailWord_2009732 prefixEnd_2009732 343986167573945382669139 := by
  unfold tailWord_2009732
  simp only [CollatzResearch.WordTrace]
  refine ⟨36650473977545836872191725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48867298636727782496255633 36650473977545836872191725)
  ·
    refine ⟨13743927741579688827071897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36650473977545836872191725 13743927741579688827071897)
    ·
      refine ⟨10307945806184766620303923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13743927741579688827071897 10307945806184766620303923)
      ·
        refine ⟨15461918709277149930455885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10307945806184766620303923 15461918709277149930455885)
        ·
          refine ⟨5798219515978931223920957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15461918709277149930455885 5798219515978931223920957)
          ·
            refine ⟨2174332318492099208970359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5798219515978931223920957 2174332318492099208970359)
            ·
              refine ⟨3261498477738148813455539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174332318492099208970359 3261498477738148813455539)
              ·
                refine ⟨4892247716607223220183309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261498477738148813455539 4892247716607223220183309)
                ·
                  refine ⟨1834592893727708707568741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4892247716607223220183309 1834592893727708707568741)
                  ·
                    refine ⟨343986167573945382669139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834592893727708707568741 343986167573945382669139)
                    ·
                      rfl

theorem cell23_2009732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_2009732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009732 prefixEnd_2009732 := by exact prefixLift 2009732
  have htrace : WordTrace (prefixWord ++ tailWord_2009732) baseStart_2009732 baseEnd_2009732 := by
    simpa [prefixWord, tailWord_2009732, baseEnd_2009732] using wordTrace_append hprefix tailTrace_2009732
  have hstable : (prefixWord ++ tailWord_2009732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009732).length < 2 ^ (prefixWord ++ tailWord_2009732).sum := by decide
  have hdescent : baseEnd_2009732 < baseStart_2009732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009788 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_2009788 : Nat := 118140960795 + 2009788 * 2 ^ 59
def prefixEnd_2009788 : Nat := 4983230072969 + 3 ^ 40 * 2009788 * 2
def baseEnd_2009788 : Nat := 343995752546162642969053

theorem tailTrace_2009788 : CollatzResearch.WordTrace tailWord_2009788 prefixEnd_2009788 343995752546162642969053 := by
  unfold tailWord_2009788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36651495221444397654211009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48868660295259196872281345 36651495221444397654211009)
  ·
    refine ⟨27488621416083298240658257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36651495221444397654211009 27488621416083298240658257)
    ·
      refine ⟨20616466062062473680493693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27488621416083298240658257 20616466062062473680493693)
      ·
        refine ⟨7731174773273427630185135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20616466062062473680493693 7731174773273427630185135)
        ·
          refine ⟨11596762159910141445277703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731174773273427630185135 11596762159910141445277703)
          ·
            refine ⟨17395143239865212167916555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11596762159910141445277703 17395143239865212167916555)
            ·
              refine ⟨26092714859797818251874833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395143239865212167916555 26092714859797818251874833)
              ·
                refine ⟨19569536144848363688906125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26092714859797818251874833 19569536144848363688906125)
                ·
                  refine ⟨7338576054318136383339797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19569536144848363688906125 7338576054318136383339797)
                  ·
                    refine ⟨343995752546162642969053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7338576054318136383339797 343995752546162642969053)
                    ·
                      rfl

theorem cell23_2009788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_2009788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009788 prefixEnd_2009788 := by exact prefixLift 2009788
  have htrace : WordTrace (prefixWord ++ tailWord_2009788) baseStart_2009788 baseEnd_2009788 := by
    simpa [prefixWord, tailWord_2009788, baseEnd_2009788] using wordTrace_append hprefix tailTrace_2009788
  have hstable : (prefixWord ++ tailWord_2009788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009788).length < 2 ^ (prefixWord ++ tailWord_2009788).sum := by decide
  have hdescent : baseEnd_2009788 < baseStart_2009788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009789 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_2009789 : Nat := 118140960795 + 2009789 * 2 ^ 59
def prefixEnd_2009789 : Nat := 4983230072969 + 3 ^ 40 * 2009789 * 2
def baseEnd_2009789 : Nat := 1031987771119142424994655

theorem tailTrace_2009789 : CollatzResearch.WordTrace tailWord_2009789 prefixEnd_2009789 1031987771119142424994655 := by
  unfold tailWord_2009789
  simp only [CollatzResearch.WordTrace]
  refine ⟨73303026915885172479208421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48868684610590114986138947 73303026915885172479208421)
  ·
    refine ⟨13744317546728469839851579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73303026915885172479208421 13744317546728469839851579)
    ·
      refine ⟨20616476320092704759777369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13744317546728469839851579 20616476320092704759777369)
      ·
        refine ⟨15462357240069528569833027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20616476320092704759777369 15462357240069528569833027)
        ·
          refine ⟨23193535860104292854749541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462357240069528569833027 23193535860104292854749541)
          ·
            refine ⟨4348787973769554910265539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23193535860104292854749541 4348787973769554910265539)
            ·
              refine ⟨6523181960654332365398309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348787973769554910265539 6523181960654332365398309)
              ·
                refine ⟨1223096617622687318512183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6523181960654332365398309 1223096617622687318512183)
                ·
                  refine ⟨1834644926434030977768275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223096617622687318512183 1834644926434030977768275)
                  ·
                    refine ⟨2751967389651046466652413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834644926434030977768275 2751967389651046466652413)
                    ·
                      refine ⟨1031987771119142424994655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751967389651046466652413 1031987771119142424994655)
                      ·
                        rfl

theorem cell23_2009789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_2009789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009789 prefixEnd_2009789 := by exact prefixLift 2009789
  have htrace : WordTrace (prefixWord ++ tailWord_2009789) baseStart_2009789 baseEnd_2009789 := by
    simpa [prefixWord, tailWord_2009789, baseEnd_2009789] using wordTrace_append hprefix tailTrace_2009789
  have hstable : (prefixWord ++ tailWord_2009789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009789).length < 2 ^ (prefixWord ++ tailWord_2009789).sum := by decide
  have hdescent : baseEnd_2009789 < baseStart_2009789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009815 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_2009815 : Nat := 118140960795 + 2009815 * 2 ^ 59
def prefixEnd_2009815 : Nat := 4983230072969 + 3 ^ 40 * 2009815 * 2
def baseEnd_2009815 : Nat := 1032001121616159323269535

theorem tailTrace_2009815 : CollatzResearch.WordTrace tailWord_2009815 prefixEnd_2009815 1032001121616159323269535 := by
  unfold tailWord_2009815
  simp only [CollatzResearch.WordTrace]
  refine ⟨73303975213790978919654899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48869316809193985946436599 73303975213790978919654899)
  ·
    refine ⟨109955962820686468379482349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73303975213790978919654899 109955962820686468379482349)
    ·
      refine ⟨41233486057757425642305881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109955962820686468379482349 41233486057757425642305881)
      ·
        refine ⟨30925114543318069231729411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41233486057757425642305881 30925114543318069231729411)
        ·
          refine ⟨46387671814977103847594117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30925114543318069231729411 46387671814977103847594117)
          ·
            refine ⟨8697688465308206971423897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46387671814977103847594117 8697688465308206971423897)
            ·
              refine ⟨6523266348981155228567923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697688465308206971423897 6523266348981155228567923)
              ·
                refine ⟨9784899523471732842851885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523266348981155228567923 9784899523471732842851885)
                ·
                  refine ⟨3669337321301899816069457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9784899523471732842851885 3669337321301899816069457)
                  ·
                    refine ⟨2752002990976424862052093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3669337321301899816069457 2752002990976424862052093)
                    ·
                      refine ⟨1032001121616159323269535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752002990976424862052093 1032001121616159323269535)
                      ·
                        rfl

theorem cell23_2009815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_2009815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009815 prefixEnd_2009815 := by exact prefixLift 2009815
  have htrace : WordTrace (prefixWord ++ tailWord_2009815) baseStart_2009815 baseEnd_2009815 := by
    simpa [prefixWord, tailWord_2009815, baseEnd_2009815] using wordTrace_append hprefix tailTrace_2009815
  have hstable : (prefixWord ++ tailWord_2009815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009815).length < 2 ^ (prefixWord ++ tailWord_2009815).sum := by decide
  have hdescent : baseEnd_2009815 < baseStart_2009815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009825 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2009825 : Nat := 118140960795 + 2009825 * 2 ^ 59
def prefixEnd_2009825 : Nat := 4983230072969 + 3 ^ 40 * 2009825 * 2
def baseEnd_2009825 : Nat := 1032006256422704284144489

theorem tailTrace_2009825 : CollatzResearch.WordTrace tailWord_2009825 prefixEnd_2009825 1032006256422704284144489 := by
  unfold tailWord_2009825
  simp only [CollatzResearch.WordTrace]
  refine ⟨73304339943754750627518929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48869559962503167085012619 73304339943754750627518929)
  ·
    refine ⟨54978254957816062970639197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73304339943754750627518929 54978254957816062970639197)
    ·
      refine ⟨20616845609181023613989699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54978254957816062970639197 20616845609181023613989699)
      ·
        refine ⟨30925268413771535420984549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20616845609181023613989699 30925268413771535420984549)
        ·
          refine ⟨5798487827582162891434603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30925268413771535420984549 5798487827582162891434603)
          ·
            refine ⟨8697731741373244337151905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798487827582162891434603 8697731741373244337151905)
            ·
              refine ⟨6523298806029933252863929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697731741373244337151905 6523298806029933252863929)
              ·
                refine ⟨4892474104522449939647947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523298806029933252863929 4892474104522449939647947)
                ·
                  refine ⟨7338711156783674909471921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892474104522449939647947 7338711156783674909471921)
                  ·
                    refine ⟨5504033367587756182103941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7338711156783674909471921 5504033367587756182103941)
                    ·
                      refine ⟨1032006256422704284144489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5504033367587756182103941 1032006256422704284144489)
                      ·
                        rfl

theorem cell23_2009825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2009825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009825 prefixEnd_2009825 := by exact prefixLift 2009825
  have htrace : WordTrace (prefixWord ++ tailWord_2009825) baseStart_2009825 baseEnd_2009825 := by
    simpa [prefixWord, tailWord_2009825, baseEnd_2009825] using wordTrace_append hprefix tailTrace_2009825
  have hstable : (prefixWord ++ tailWord_2009825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009825).length < 2 ^ (prefixWord ++ tailWord_2009825).sum := by decide
  have hdescent : baseEnd_2009825 < baseStart_2009825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009829 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2009829 : Nat := 118140960795 + 2009829 * 2 ^ 59
def prefixEnd_2009829 : Nat := 4983230072969 + 3 ^ 40 * 2009829 * 2
def baseEnd_2009829 : Nat := 1032008310345322268494471

theorem tailTrace_2009829 : CollatzResearch.WordTrace tailWord_2009829 prefixEnd_2009829 1032008310345322268494471 := by
  unfold tailWord_2009829
  simp only [CollatzResearch.WordTrace]
  refine ⟨73304485835740259310664541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48869657223826839540443027 73304485835740259310664541)
  ·
    refine ⟨27489182188402597241499203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73304485835740259310664541 27489182188402597241499203)
    ·
      refine ⟨41233773282603895862248805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27489182188402597241499203 41233773282603895862248805)
      ·
        refine ⟨7731332490488230474171651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41233773282603895862248805 7731332490488230474171651)
        ·
          refine ⟨11596998735732345711257477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731332490488230474171651 11596998735732345711257477)
          ·
            refine ⟨2174437262949814820860777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11596998735732345711257477 2174437262949814820860777)
            ·
              refine ⟨1630827947212361115645583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174437262949814820860777 1630827947212361115645583)
              ·
                refine ⟨2446241920818541673468375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630827947212361115645583 2446241920818541673468375)
                ·
                  refine ⟨3669362881227812510202563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446241920818541673468375 3669362881227812510202563)
                  ·
                    refine ⟨5504044321841718765303845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3669362881227812510202563 5504044321841718765303845)
                    ·
                      refine ⟨1032008310345322268494471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5504044321841718765303845 1032008310345322268494471)
                      ·
                        rfl

theorem cell23_2009829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2009829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009829 prefixEnd_2009829 := by exact prefixLift 2009829
  have htrace : WordTrace (prefixWord ++ tailWord_2009829) baseStart_2009829 baseEnd_2009829 := by
    simpa [prefixWord, tailWord_2009829, baseEnd_2009829] using wordTrace_append hprefix tailTrace_2009829
  have hstable : (prefixWord ++ tailWord_2009829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009829).length < 2 ^ (prefixWord ++ tailWord_2009829).sum := by decide
  have hdescent : baseEnd_2009829 < baseStart_2009829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009846 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_2009846 : Nat := 118140960795 + 2009846 * 2 ^ 59
def prefixEnd_2009846 : Nat := 4983230072969 + 3 ^ 40 * 2009846 * 2
def baseEnd_2009846 : Nat := 1032017039516448701981893

theorem tailTrace_2009846 : CollatzResearch.WordTrace tailWord_2009846 prefixEnd_2009846 1032017039516448701981893 := by
  unfold tailWord_2009846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581569117292416950877087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48870070584452447476022261 4581569117292416950877087)
  ·
    refine ⟨6872353675938625426315631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581569117292416950877087 6872353675938625426315631)
    ·
      refine ⟨10308530513907938139473447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872353675938625426315631 10308530513907938139473447)
      ·
        refine ⟨15462795770861907209210171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308530513907938139473447 15462795770861907209210171)
        ·
          refine ⟨23194193656292860813815257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462795770861907209210171 23194193656292860813815257)
          ·
            refine ⟨17395645242219645610361443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23194193656292860813815257 17395645242219645610361443)
            ·
              refine ⟨26093467863329468415542165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395645242219645610361443 26093467863329468415542165)
              ·
                refine ⟨1223131306093568831978539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26093467863329468415542165 1223131306093568831978539)
                ·
                  refine ⟨1834696959140353247967809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223131306093568831978539 1834696959140353247967809)
                  ·
                    refine ⟨1376022719355264935975857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1834696959140353247967809 1376022719355264935975857)
                    ·
                      refine ⟨1032017039516448701981893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376022719355264935975857 1032017039516448701981893)
                      ·
                        rfl

theorem cell23_2009846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_2009846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009846 prefixEnd_2009846 := by exact prefixLift 2009846
  have htrace : WordTrace (prefixWord ++ tailWord_2009846) baseStart_2009846 baseEnd_2009846 := by
    simpa [prefixWord, tailWord_2009846, baseEnd_2009846] using wordTrace_append hprefix tailTrace_2009846
  have hstable : (prefixWord ++ tailWord_2009846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009846).length < 2 ^ (prefixWord ++ tailWord_2009846).sum := by decide
  have hdescent : baseEnd_2009846 < baseStart_2009846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009905 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_2009905 : Nat := 118140960795 + 2009905 * 2 ^ 59
def prefixEnd_2009905 : Nat := 4983230072969 + 3 ^ 40 * 2009905 * 2
def baseEnd_2009905 : Nat := 1032047334875063971144121

theorem tailTrace_2009905 : CollatzResearch.WordTrace tailWord_2009905 prefixEnd_2009905 1032047334875063971144121 := by
  unfold tailWord_2009905
  simp only [CollatzResearch.WordTrace]
  refine ⟨73307257783464924290431169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48871505188976616193620779 73307257783464924290431169)
  ·
    refine ⟨54980443337598693217823377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73307257783464924290431169 54980443337598693217823377)
    ·
      refine ⟨41235332503199019913367533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54980443337598693217823377 41235332503199019913367533)
      ·
        refine ⟨15463249688699632467512825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41235332503199019913367533 15463249688699632467512825)
        ·
          refine ⟨11597437266524724350634619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15463249688699632467512825 11597437266524724350634619)
          ·
            refine ⟨17396155899787086525951929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11597437266524724350634619 17396155899787086525951929)
            ·
              refine ⟨13047116924840314894463947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17396155899787086525951929 13047116924840314894463947)
              ·
                refine ⟨19570675387260472341695921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13047116924840314894463947 19570675387260472341695921)
                ·
                  refine ⟨14678006540445354256271941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19570675387260472341695921 14678006540445354256271941)
                  ·
                    refine ⟨2752126226333503923050989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14678006540445354256271941 2752126226333503923050989)
                    ·
                      refine ⟨1032047334875063971144121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752126226333503923050989 1032047334875063971144121)
                      ·
                        rfl

theorem cell23_2009905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_2009905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009905 prefixEnd_2009905 := by exact prefixLift 2009905
  have htrace : WordTrace (prefixWord ++ tailWord_2009905) baseStart_2009905 baseEnd_2009905 := by
    simpa [prefixWord, tailWord_2009905, baseEnd_2009905] using wordTrace_append hprefix tailTrace_2009905
  have hstable : (prefixWord ++ tailWord_2009905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009905).length < 2 ^ (prefixWord ++ tailWord_2009905).sum := by decide
  have hdescent : baseEnd_2009905 < baseStart_2009905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009959 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 5]
def baseStart_2009959 : Nat := 118140960795 + 2009959 * 2 ^ 59
def prefixEnd_2009959 : Nat := 4983230072969 + 3 ^ 40 * 2009959 * 2
def baseEnd_2009959 : Nat := 114675006981156306652097

theorem tailTrace_2009959 : CollatzResearch.WordTrace tailWord_2009959 prefixEnd_2009959 114675006981156306652097 := by
  unfold tailWord_2009959
  simp only [CollatzResearch.WordTrace]
  refine ⟨73309227325269291512896931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48872818216846194341931287 73309227325269291512896931)
  ·
    refine ⟨109963840987903937269345397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73309227325269291512896931 109963840987903937269345397)
    ·
      refine ⟨10309110092615994119001131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109963840987903937269345397 10309110092615994119001131)
      ·
        refine ⟨15463665138923991178501697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10309110092615994119001131 15463665138923991178501697)
        ·
          refine ⟨11597748854192993383876273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15463665138923991178501697 11597748854192993383876273)
          ·
            refine ⟨8698311640644745037907205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11597748854192993383876273 8698311640644745037907205)
            ·
              refine ⟨1630933432620889694607601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8698311640644745037907205 1630933432620889694607601)
              ·
                refine ⟨1223200074465667270955701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630933432620889694607601 1223200074465667270955701)
                ·
                  refine ⟨114675006981156306652097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1223200074465667270955701 114675006981156306652097)
                  ·
                    rfl

theorem cell23_2009959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 5].length) (baseStart_2009959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009959 prefixEnd_2009959 := by exact prefixLift 2009959
  have htrace : WordTrace (prefixWord ++ tailWord_2009959) baseStart_2009959 baseEnd_2009959 := by
    simpa [prefixWord, tailWord_2009959, baseEnd_2009959] using wordTrace_append hprefix tailTrace_2009959
  have hstable : (prefixWord ++ tailWord_2009959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009959).length < 2 ^ (prefixWord ++ tailWord_2009959).sum := by decide
  have hdescent : baseEnd_2009959 < baseStart_2009959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009975 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_2009975 : Nat := 118140960795 + 2009975 * 2 ^ 59
def prefixEnd_2009975 : Nat := 4983230072969 + 3 ^ 40 * 2009975 * 2
def baseEnd_2009975 : Nat := 1032083278520878697268799

theorem tailTrace_2009975 : CollatzResearch.WordTrace tailWord_2009975 prefixEnd_2009975 1032083278520878697268799 := by
  unfold tailWord_2009975
  simp only [CollatzResearch.WordTrace]
  refine ⟨73309810893211326245479379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48873207262140884163652919 73309810893211326245479379)
  ·
    refine ⟨109964716339816989368219069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73309810893211326245479379 109964716339816989368219069)
    ·
      refine ⟨41236768627431371013082151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109964716339816989368219069 41236768627431371013082151)
      ·
        refine ⟨61855152941147056519623227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41236768627431371013082151 61855152941147056519623227)
        ·
          refine ⟨92782729411720584779434841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61855152941147056519623227 92782729411720584779434841)
          ·
            refine ⟨69587047058790438584576131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92782729411720584779434841 69587047058790438584576131)
            ·
              refine ⟨104380570588185657876864197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69587047058790438584576131 104380570588185657876864197)
              ·
                refine ⟨19571356985284810851912037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104380570588185657876864197 19571356985284810851912037)
                ·
                  refine ⟨3669629434740902034733507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19571356985284810851912037 3669629434740902034733507)
                  ·
                    refine ⟨5504444152111353052100261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3669629434740902034733507 5504444152111353052100261)
                    ·
                      refine ⟨1032083278520878697268799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5504444152111353052100261 1032083278520878697268799)
                      ·
                        rfl

theorem cell23_2009975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_2009975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009975 prefixEnd_2009975 := by exact prefixLift 2009975
  have htrace : WordTrace (prefixWord ++ tailWord_2009975) baseStart_2009975 baseEnd_2009975 := by
    simpa [prefixWord, tailWord_2009975, baseEnd_2009975] using wordTrace_append hprefix tailTrace_2009975
  have hstable : (prefixWord ++ tailWord_2009975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009975).length < 2 ^ (prefixWord ++ tailWord_2009975).sum := by decide
  have hdescent : baseEnd_2009975 < baseStart_2009975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009992 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2009992 : Nat := 118140960795 + 2009992 * 2 ^ 59
def prefixEnd_2009992 : Nat := 4983230072969 + 3 ^ 40 * 2009992 * 2
def baseEnd_2009992 : Nat := 1032092007692005130756221

theorem tailTrace_2009992 : CollatzResearch.WordTrace tailWord_2009992 prefixEnd_2009992 1032092007692005130756221 := by
  unfold tailWord_2009992
  simp only [CollatzResearch.WordTrace]
  refine ⟨36655215467074869074424115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48873620622766492099232153 36655215467074869074424115)
  ·
    refine ⟨54982823200612303611636173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36655215467074869074424115 54982823200612303611636173)
    ·
      refine ⟨20618558700229613854363565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54982823200612303611636173 20618558700229613854363565)
      ·
        refine ⟨7731959512586105195386337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20618558700229613854363565 7731959512586105195386337)
        ·
          refine ⟨5798969634439578896539753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7731959512586105195386337 5798969634439578896539753)
          ·
            refine ⟨4349227225829684172404815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5798969634439578896539753 4349227225829684172404815)
            ·
              refine ⟨6523840838744526258607223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349227225829684172404815 6523840838744526258607223)
              ·
                refine ⟨9785761258116789387910835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523840838744526258607223 9785761258116789387910835)
                ·
                  refine ⟨14678641887175184081866253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9785761258116789387910835 14678641887175184081866253)
                  ·
                    refine ⟨5504490707690694030699845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14678641887175184081866253 5504490707690694030699845)
                    ·
                      refine ⟨1032092007692005130756221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5504490707690694030699845 1032092007692005130756221)
                      ·
                        rfl

theorem cell23_2009992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2009992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009992 prefixEnd_2009992 := by exact prefixLift 2009992
  have htrace : WordTrace (prefixWord ++ tailWord_2009992) baseStart_2009992 baseEnd_2009992 := by
    simpa [prefixWord, tailWord_2009992, baseEnd_2009992] using wordTrace_append hprefix tailTrace_2009992
  have hstable : (prefixWord ++ tailWord_2009992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009992).length < 2 ^ (prefixWord ++ tailWord_2009992).sum := by decide
  have hdescent : baseEnd_2009992 < baseStart_2009992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010005 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2010005 : Nat := 118140960795 + 2010005 * 2 ^ 59
def prefixEnd_2010005 : Nat := 4983230072969 + 3 ^ 40 * 2010005 * 2
def baseEnd_2010005 : Nat := 1032098682940513579893661

theorem tailTrace_2010005 : CollatzResearch.WordTrace tailWord_2010005 prefixEnd_2010005 1032098682940513579893661 := by
  unfold tailWord_2010005
  simp only [CollatzResearch.WordTrace]
  refine ⟨73310905083102641369071469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48873936722068427579380979 73310905083102641369071469)
  ·
    refine ⟨27491589406163490513401801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73310905083102641369071469 27491589406163490513401801)
    ·
      refine ⟨20618692054622617885051351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27491589406163490513401801 20618692054622617885051351)
      ·
        refine ⟨30928038081933926827577027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618692054622617885051351 30928038081933926827577027)
        ·
          refine ⟨46392057122900890241365541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30928038081933926827577027 46392057122900890241365541)
          ·
            refine ⟨8698510710543916920256039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46392057122900890241365541 8698510710543916920256039)
            ·
              refine ⟨13047766065815875380384059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698510710543916920256039 13047766065815875380384059)
              ·
                refine ⟨19571649098723813070576089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13047766065815875380384059 19571649098723813070576089)
                ·
                  refine ⟨14678736824042859802932067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19571649098723813070576089 14678736824042859802932067)
                  ·
                    refine ⟨22018105236064289704398101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14678736824042859802932067 22018105236064289704398101)
                    ·
                      refine ⟨1032098682940513579893661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22018105236064289704398101 1032098682940513579893661)
                      ·
                        rfl

theorem cell23_2010005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2010005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010005 prefixEnd_2010005 := by exact prefixLift 2010005
  have htrace : WordTrace (prefixWord ++ tailWord_2010005) baseStart_2010005 baseEnd_2010005 := by
    simpa [prefixWord, tailWord_2010005, baseEnd_2010005] using wordTrace_append hprefix tailTrace_2010005
  have hstable : (prefixWord ++ tailWord_2010005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010005).length < 2 ^ (prefixWord ++ tailWord_2010005).sum := by decide
  have hdescent : baseEnd_2010005 < baseStart_2010005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010019 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 1, 4]
def baseStart_2010019 : Nat := 118140960795 + 2010019 * 2 ^ 59
def prefixEnd_2010019 : Nat := 4983230072969 + 3 ^ 40 * 2010019 * 2
def baseEnd_2010019 : Nat := 344035290556558841706199

theorem tailTrace_2010019 : CollatzResearch.WordTrace tailWord_2010019 prefixEnd_2010019 344035290556558841706199 := by
  unfold tailWord_2010019
  simp only [CollatzResearch.WordTrace]
  refine ⟨73311415705051921760081111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48874277136701281173387407 73311415705051921760081111)
  ·
    refine ⟨109967123557577882640121667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73311415705051921760081111 109967123557577882640121667)
    ·
      refine ⟨164950685336366823960182501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109967123557577882640121667 164950685336366823960182501)
      ·
        refine ⟨30928253500568779492534219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164950685336366823960182501 30928253500568779492534219)
        ·
          refine ⟨46392380250853169238801329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30928253500568779492534219 46392380250853169238801329)
          ·
            refine ⟨34794285188139876929100997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46392380250853169238801329 34794285188139876929100997)
            ·
              refine ⟨6523928472776226924206437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34794285188139876929100997 6523928472776226924206437)
              ·
                refine ⟨1223236588645542548288707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6523928472776226924206437 1223236588645542548288707)
                ·
                  refine ⟨1834854882968313822433061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223236588645542548288707 1834854882968313822433061)
                  ·
                    refine ⟨344035290556558841706199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834854882968313822433061 344035290556558841706199)
                    ·
                      rfl

theorem cell23_2010019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 4].length) (baseStart_2010019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010019 prefixEnd_2010019 := by exact prefixLift 2010019
  have htrace : WordTrace (prefixWord ++ tailWord_2010019) baseStart_2010019 baseEnd_2010019 := by
    simpa [prefixWord, tailWord_2010019, baseEnd_2010019] using wordTrace_append hprefix tailTrace_2010019
  have hstable : (prefixWord ++ tailWord_2010019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010019).length < 2 ^ (prefixWord ++ tailWord_2010019).sum := by decide
  have hdescent : baseEnd_2010019 < baseStart_2010019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010036 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2010036 : Nat := 118140960795 + 2010036 * 2 ^ 59
def prefixEnd_2010036 : Nat := 4983230072969 + 3 ^ 40 * 2010036 * 2
def baseEnd_2010036 : Nat := 344038200280267652868673

theorem tailTrace_2010036 : CollatzResearch.WordTrace tailWord_2010036 prefixEnd_2010036 344038200280267652868673 := by
  unfold tailWord_2010036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656017872995166831724981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48874690497326889108966641 36656017872995166831724981)
  ·
    refine ⟨3436501675593296890474217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36656017872995166831724981 3436501675593296890474217)
    ·
      refine ⟨2577376256694972667855663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3436501675593296890474217 2577376256694972667855663)
      ·
        refine ⟨3866064385042459001783495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577376256694972667855663 3866064385042459001783495)
        ·
          refine ⟨5799096577563688502675243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866064385042459001783495 5799096577563688502675243)
          ·
            refine ⟨8698644866345532754012865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799096577563688502675243 8698644866345532754012865)
            ·
              refine ⟨6523983649759149565509649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8698644866345532754012865 6523983649759149565509649)
              ·
                refine ⟨4892987737319362174132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523983649759149565509649 4892987737319362174132237)
                ·
                  refine ⟨1834870401494760815299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4892987737319362174132237 1834870401494760815299589)
                  ·
                    refine ⟨344038200280267652868673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834870401494760815299589 344038200280267652868673)
                    ·
                      rfl

theorem cell23_2010036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2010036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010036 prefixEnd_2010036 := by exact prefixLift 2010036
  have htrace : WordTrace (prefixWord ++ tailWord_2010036) baseStart_2010036 baseEnd_2010036 := by
    simpa [prefixWord, tailWord_2010036, baseEnd_2010036] using wordTrace_append hprefix tailTrace_2010036
  have hstable : (prefixWord ++ tailWord_2010036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010036).length < 2 ^ (prefixWord ++ tailWord_2010036).sum := by decide
  have hdescent : baseEnd_2010036 < baseStart_2010036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010070 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2010070 : Nat := 118140960795 + 2010070 * 2 ^ 59
def prefixEnd_2010070 : Nat := 4983230072969 + 3 ^ 40 * 2010070 * 2
def baseEnd_2010070 : Nat := 344044019727685275193621

theorem tailTrace_2010070 : CollatzResearch.WordTrace tailWord_2010070 prefixEnd_2010070 344044019727685275193621 := by
  unfold tailWord_2010070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582079739241697341886729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48875517218578104980125109 4582079739241697341886729)
  ·
    refine ⟨3436559804431273006415047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4582079739241697341886729 3436559804431273006415047)
    ·
      refine ⟨5154839706646909509622571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3436559804431273006415047 5154839706646909509622571)
      ·
        refine ⟨7732259559970364264433857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154839706646909509622571 7732259559970364264433857)
        ·
          refine ⟨5799194669977773198325393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7732259559970364264433857 5799194669977773198325393)
          ·
            refine ⟨4349396002483329898744045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799194669977773198325393 4349396002483329898744045)
            ·
              refine ⟨1631023500931248712029017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4349396002483329898744045 1631023500931248712029017)
              ·
                refine ⟨1223267625698436534021763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631023500931248712029017 1223267625698436534021763)
                ·
                  refine ⟨1834901438547654801032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223267625698436534021763 1834901438547654801032645)
                  ·
                    refine ⟨344044019727685275193621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834901438547654801032645 344044019727685275193621)
                    ·
                      rfl

theorem cell23_2010070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2010070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010070 prefixEnd_2010070 := by exact prefixLift 2010070
  have htrace : WordTrace (prefixWord ++ tailWord_2010070) baseStart_2010070 baseEnd_2010070 := by
    simpa [prefixWord, tailWord_2010070, baseEnd_2010070] using wordTrace_append hprefix tailTrace_2010070
  have hstable : (prefixWord ++ tailWord_2010070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010070).length < 2 ^ (prefixWord ++ tailWord_2010070).sum := by decide
  have hdescent : baseEnd_2010070 < baseStart_2010070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010105 : List Nat := [1, 2, 1, 3, 1, 3, 1, 11]
def baseStart_2010105 : Nat := 118140960795 + 2010105 * 2 ^ 59
def prefixEnd_2010105 : Nat := 4983230072969 + 3 ^ 40 * 2010105 * 2
def baseEnd_2010105 : Nat := 38227778926146784764563

theorem tailTrace_2010105 : CollatzResearch.WordTrace tailWord_2010105 prefixEnd_2010105 38227778926146784764563 := by
  unfold tailWord_2010105
  simp only [CollatzResearch.WordTrace]
  refine ⟨73314552382740358447711769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48876368255160238965141179 73314552382740358447711769)
  ·
    refine ⟨54985914287055268835783827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73314552382740358447711769 54985914287055268835783827)
    ·
      refine ⟨82478871430582903253675741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54985914287055268835783827 82478871430582903253675741)
      ·
        refine ⟨30929576786468588720128403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82478871430582903253675741 30929576786468588720128403)
        ·
          refine ⟨46394365179702883080192605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30929576786468588720128403 46394365179702883080192605)
          ·
            refine ⟨17397886942388581155072227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46394365179702883080192605 17397886942388581155072227)
            ·
              refine ⟨26096830413582871732608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17397886942388581155072227 26096830413582871732608341)
              ·
                refine ⟨38227778926146784764563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26096830413582871732608341 38227778926146784764563)
                ·
                  rfl

theorem cell23_2010105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 11].length) (baseStart_2010105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010105 prefixEnd_2010105 := by exact prefixLift 2010105
  have htrace : WordTrace (prefixWord ++ tailWord_2010105) baseStart_2010105 baseEnd_2010105 := by
    simpa [prefixWord, tailWord_2010105, baseEnd_2010105] using wordTrace_append hprefix tailTrace_2010105
  have hstable : (prefixWord ++ tailWord_2010105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010105).length < 2 ^ (prefixWord ++ tailWord_2010105).sum := by decide
  have hdescent : baseEnd_2010105 < baseStart_2010105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010126 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2010126 : Nat := 118140960795 + 2010126 * 2 ^ 59
def prefixEnd_2010126 : Nat := 4983230072969 + 3 ^ 40 * 2010126 * 2
def baseEnd_2010126 : Nat := 344053604699902535493535

theorem tailTrace_2010126 : CollatzResearch.WordTrace tailWord_2010126 prefixEnd_2010126 344053604699902535493535 := by
  unfold tailWord_2010126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164414789458034879278279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48876878877109519356150821 9164414789458034879278279)
  ·
    refine ⟨13746622184187052318917419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9164414789458034879278279 13746622184187052318917419)
    ·
      refine ⟨20619933276280578478376129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746622184187052318917419 20619933276280578478376129)
      ·
        refine ⟨15464949957210433858782097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20619933276280578478376129 15464949957210433858782097)
        ·
          refine ⟨11598712467907825394086573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15464949957210433858782097 11598712467907825394086573)
          ·
            refine ⟨4349517175465434522782465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11598712467907825394086573 4349517175465434522782465)
            ·
              refine ⟨3262137881599075892086849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349517175465434522782465 3262137881599075892086849)
              ·
                refine ⟨2446603411199306919065137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262137881599075892086849 2446603411199306919065137)
                ·
                  refine ⟨1834952558399480189298853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2446603411199306919065137 1834952558399480189298853)
                  ·
                    refine ⟨344053604699902535493535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834952558399480189298853 344053604699902535493535)
                    ·
                      rfl

theorem cell23_2010126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2010126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010126 prefixEnd_2010126 := by exact prefixLift 2010126
  have htrace : WordTrace (prefixWord ++ tailWord_2010126) baseStart_2010126 baseEnd_2010126 := by
    simpa [prefixWord, tailWord_2010126, baseEnd_2010126] using wordTrace_append hprefix tailTrace_2010126
  have hstable : (prefixWord ++ tailWord_2010126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010126).length < 2 ^ (prefixWord ++ tailWord_2010126).sum := by decide
  have hdescent : baseEnd_2010126 < baseStart_2010126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010149 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_2010149 : Nat := 118140960795 + 2010149 * 2 ^ 59
def prefixEnd_2010149 : Nat := 4983230072969 + 3 ^ 40 * 2010149 * 2
def baseEnd_2010149 : Nat := 1032172624154761016492999

theorem tailTrace_2010149 : CollatzResearch.WordTrace tailWord_2010149 prefixEnd_2010149 1032172624154761016492999 := by
  unfold tailWord_2010149
  simp only [CollatzResearch.WordTrace]
  refine ⟨73316157194580953962313501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48877438129720635974875667 73316157194580953962313501)
  ·
    refine ⟨27493558947967857735867563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73316157194580953962313501 27493558947967857735867563)
    ·
      refine ⟨41240338421951786603801345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27493558947967857735867563 41240338421951786603801345)
      ·
        refine ⟨30930253816463839952851009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41240338421951786603801345 30930253816463839952851009)
        ·
          refine ⟨23197690362347879964638257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30930253816463839952851009 23197690362347879964638257)
          ·
            refine ⟨17398267771760909973478693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23197690362347879964638257 17398267771760909973478693)
            ·
              refine ⟨3262175207205170620027255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17398267771760909973478693 3262175207205170620027255)
              ·
                refine ⟨4893262810807755930040883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262175207205170620027255 4893262810807755930040883)
                ·
                  refine ⟨7339894216211633895061325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893262810807755930040883 7339894216211633895061325)
                  ·
                    refine ⟨2752460331079362710647997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7339894216211633895061325 2752460331079362710647997)
                    ·
                      refine ⟨1032172624154761016492999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752460331079362710647997 1032172624154761016492999)
                      ·
                        rfl

theorem cell23_2010149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_2010149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010149 prefixEnd_2010149 := by exact prefixLift 2010149
  have htrace : WordTrace (prefixWord ++ tailWord_2010149) baseStart_2010149 baseEnd_2010149 := by
    simpa [prefixWord, tailWord_2010149, baseEnd_2010149] using wordTrace_append hprefix tailTrace_2010149
  have hstable : (prefixWord ++ tailWord_2010149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010149).length < 2 ^ (prefixWord ++ tailWord_2010149).sum := by decide
  have hdescent : baseEnd_2010149 < baseStart_2010149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010162 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2010162 : Nat := 118140960795 + 2010162 * 2 ^ 59
def prefixEnd_2010162 : Nat := 4983230072969 + 3 ^ 40 * 2010162 * 2
def baseEnd_2010162 : Nat := 1032179299403269465630439

theorem tailTrace_2010162 : CollatzResearch.WordTrace tailWord_2010162 prefixEnd_2010162 1032179299403269465630439 := by
  unfold tailWord_2010162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329157835883464295634185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48877754229022571455024493 18329157835883464295634185)
  ·
    refine ⟨13746868376912598221725639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18329157835883464295634185 13746868376912598221725639)
    ·
      refine ⟨20620302565368897332588459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746868376912598221725639 20620302565368897332588459)
      ·
        refine ⟨30930453848053345998882689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20620302565368897332588459 30930453848053345998882689)
        ·
          refine ⟨23197840386040009499162017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30930453848053345998882689 23197840386040009499162017)
          ·
            refine ⟨17398380289530007124371513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23197840386040009499162017 17398380289530007124371513)
            ·
              refine ⟨13048785217147505343278635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17398380289530007124371513 13048785217147505343278635)
              ·
                refine ⟨19573177825721258014917953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13048785217147505343278635 19573177825721258014917953)
                ·
                  refine ⟨14679883369290943511188465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19573177825721258014917953 14679883369290943511188465)
                  ·
                    refine ⟨11009912526968207633391349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14679883369290943511188465 11009912526968207633391349)
                    ·
                      refine ⟨1032179299403269465630439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11009912526968207633391349 1032179299403269465630439)
                      ·
                        rfl

theorem cell23_2010162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2010162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010162 prefixEnd_2010162 := by exact prefixLift 2010162
  have htrace : WordTrace (prefixWord ++ tailWord_2010162) baseStart_2010162 baseEnd_2010162 := by
    simpa [prefixWord, tailWord_2010162, baseEnd_2010162] using wordTrace_append hprefix tailTrace_2010162
  have hstable : (prefixWord ++ tailWord_2010162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010162).length < 2 ^ (prefixWord ++ tailWord_2010162).sum := by decide
  have hdescent : baseEnd_2010162 < baseStart_2010162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010166 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2010166 : Nat := 118140960795 + 2010166 * 2 ^ 59
def prefixEnd_2010166 : Nat := 4983230072969 + 3 ^ 40 * 2010166 * 2
def baseEnd_2010166 : Nat := 1032181353325887449980421

theorem tailTrace_2010166 : CollatzResearch.WordTrace tailWord_2010166 prefixEnd_2010166 1032181353325887449980421 := by
  unfold tailWord_2010166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582298577219960366605147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48877851490346243910454901 4582298577219960366605147)
  ·
    refine ⟨6873447865829940549907721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4582298577219960366605147 6873447865829940549907721)
    ·
      refine ⟨5155085899372455412430791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6873447865829940549907721 5155085899372455412430791)
      ·
        refine ⟨7732628849058683118646187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5155085899372455412430791 7732628849058683118646187)
        ·
          refine ⟨11598943273588024677969281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732628849058683118646187 11598943273588024677969281)
          ·
            refine ⟨8699207455191018508476961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11598943273588024677969281 8699207455191018508476961)
            ·
              refine ⟨6524405591393263881357721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8699207455191018508476961 6524405591393263881357721)
              ·
                refine ⟨4893304193544947911018291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524405591393263881357721 4893304193544947911018291)
                ·
                  refine ⟨7339956290317421866527437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893304193544947911018291 7339956290317421866527437)
                  ·
                    refine ⟨2752483608869033199947789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7339956290317421866527437 2752483608869033199947789)
                    ·
                      refine ⟨1032181353325887449980421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752483608869033199947789 1032181353325887449980421)
                      ·
                        rfl

theorem cell23_2010166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2010166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010166 prefixEnd_2010166 := by exact prefixLift 2010166
  have htrace : WordTrace (prefixWord ++ tailWord_2010166) baseStart_2010166 baseEnd_2010166 := by
    simpa [prefixWord, tailWord_2010166, baseEnd_2010166] using wordTrace_append hprefix tailTrace_2010166
  have hstable : (prefixWord ++ tailWord_2010166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010166).length < 2 ^ (prefixWord ++ tailWord_2010166).sum := by decide
  have hdescent : baseEnd_2010166 < baseStart_2010166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010176 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2]
def baseStart_2010176 : Nat := 118140960795 + 2010176 * 2 ^ 59
def prefixEnd_2010176 : Nat := 4983230072969 + 3 ^ 40 * 2010176 * 2
def baseEnd_2010176 : Nat := 1032186488132432410855375

theorem tailTrace_2010176 : CollatzResearch.WordTrace tailWord_2010176 prefixEnd_2010176 1032186488132432410855375 := by
  unfold tailWord_2010176
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658570982741568786773191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48878094643655425049030921 36658570982741568786773191)
  ·
    refine ⟨54987856474112353180159787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36658570982741568786773191 54987856474112353180159787)
    ·
      refine ⟨82481784711168529770239681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54987856474112353180159787 82481784711168529770239681)
      ·
        refine ⟨61861338533376397327679761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82481784711168529770239681 61861338533376397327679761)
        ·
          refine ⟨46396003900032297995759821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61861338533376397327679761 46396003900032297995759821)
          ·
            refine ⟨17398501462512111748409933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46396003900032297995759821 17398501462512111748409933)
            ·
              refine ⟨6524438048442041905653725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17398501462512111748409933 6524438048442041905653725)
              ·
                refine ⟨2446664268165765714620147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6524438048442041905653725 2446664268165765714620147)
                ·
                  refine ⟨3669996402248648571930221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446664268165765714620147 3669996402248648571930221)
                  ·
                    refine ⟨1376248650843243214473833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3669996402248648571930221 1376248650843243214473833)
                    ·
                      refine ⟨1032186488132432410855375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376248650843243214473833 1032186488132432410855375)
                      ·
                        rfl

theorem cell23_2010176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_2010176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010176 prefixEnd_2010176 := by exact prefixLift 2010176
  have htrace : WordTrace (prefixWord ++ tailWord_2010176) baseStart_2010176 baseEnd_2010176 := by
    simpa [prefixWord, tailWord_2010176, baseEnd_2010176] using wordTrace_append hprefix tailTrace_2010176
  have hstable : (prefixWord ++ tailWord_2010176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010176).length < 2 ^ (prefixWord ++ tailWord_2010176).sum := by decide
  have hdescent : baseEnd_2010176 < baseStart_2010176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010183 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_2010183 : Nat := 118140960795 + 2010183 * 2 ^ 59
def prefixEnd_2010183 : Nat := 4983230072969 + 3 ^ 40 * 2010183 * 2
def baseEnd_2010183 : Nat := 1032190082497013883467843

theorem tailTrace_2010183 : CollatzResearch.WordTrace tailWord_2010183 prefixEnd_2010183 1032190082497013883467843 := by
  unfold tailWord_2010183
  simp only [CollatzResearch.WordTrace]
  refine ⟨73317397276457777769051203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48878264850971851846034135 73317397276457777769051203)
  ·
    refine ⟨109976095914686666653576805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73317397276457777769051203 109976095914686666653576805)
    ·
      refine ⟨20620517984003749997545651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109976095914686666653576805 20620517984003749997545651)
      ·
        refine ⟨30930776976005624996318477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20620517984003749997545651 30930776976005624996318477)
        ·
          refine ⟨11599041366002109373619429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30930776976005624996318477 11599041366002109373619429)
          ·
            refine ⟨2174820256125395507553643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11599041366002109373619429 2174820256125395507553643)
            ·
              refine ⟨3262230384188093261330465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174820256125395507553643 3262230384188093261330465)
              ·
                refine ⟨2446672788141069945997849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262230384188093261330465 2446672788141069945997849)
                ·
                  refine ⟨1835004591105802459498387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2446672788141069945997849 1835004591105802459498387)
                  ·
                    refine ⟨2752506886658703689247581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835004591105802459498387 2752506886658703689247581)
                    ·
                      refine ⟨1032190082497013883467843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752506886658703689247581 1032190082497013883467843)
                      ·
                        rfl

theorem cell23_2010183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_2010183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010183 prefixEnd_2010183 := by exact prefixLift 2010183
  have htrace : WordTrace (prefixWord ++ tailWord_2010183) baseStart_2010183 baseEnd_2010183 := by
    simpa [prefixWord, tailWord_2010183, baseEnd_2010183] using wordTrace_append hprefix tailTrace_2010183
  have hstable : (prefixWord ++ tailWord_2010183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010183).length < 2 ^ (prefixWord ++ tailWord_2010183).sum := by decide
  have hdescent : baseEnd_2010183 < baseStart_2010183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010192 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_2010192 : Nat := 118140960795 + 2010192 * 2 ^ 59
def prefixEnd_2010192 : Nat := 4983230072969 + 3 ^ 40 * 2010192 * 2
def baseEnd_2010192 : Nat := 1032194703822904348255301

theorem tailTrace_2010192 : CollatzResearch.WordTrace tailWord_2010192 prefixEnd_2010192 1032194703822904348255301 := by
  unfold tailWord_2010192
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658862766712586153064415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48878483688950114870752553 36658862766712586153064415)
  ·
    refine ⟨54988294150068879229596623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36658862766712586153064415 54988294150068879229596623)
    ·
      refine ⟨82482441225103318844394935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54988294150068879229596623 82482441225103318844394935)
      ·
        refine ⟨123723661837654978266592403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82482441225103318844394935 123723661837654978266592403)
        ·
          refine ⟨185585492756482467399888605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123723661837654978266592403 185585492756482467399888605)
          ·
            refine ⟨69594559783680925274958227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185585492756482467399888605 69594559783680925274958227)
            ·
              refine ⟨104391839675521387912437341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69594559783680925274958227 104391839675521387912437341)
              ·
                refine ⟨39146939878320520467164003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104391839675521387912437341 39146939878320520467164003)
                ·
                  refine ⟨58720409817480780700746005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39146939878320520467164003 58720409817480780700746005)
                  ·
                    refine ⟨2752519210194411595347469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58720409817480780700746005 2752519210194411595347469)
                    ·
                      refine ⟨1032194703822904348255301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752519210194411595347469 1032194703822904348255301)
                      ·
                        rfl

theorem cell23_2010192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_2010192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010192 prefixEnd_2010192 := by exact prefixLift 2010192
  have htrace : WordTrace (prefixWord ++ tailWord_2010192) baseStart_2010192 baseEnd_2010192 := by
    simpa [prefixWord, tailWord_2010192, baseEnd_2010192] using wordTrace_append hprefix tailTrace_2010192
  have hstable : (prefixWord ++ tailWord_2010192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010192).length < 2 ^ (prefixWord ++ tailWord_2010192).sum := by decide
  have hdescent : baseEnd_2010192 < baseStart_2010192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010202 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2010202 : Nat := 118140960795 + 2010202 * 2 ^ 59
def prefixEnd_2010202 : Nat := 4983230072969 + 3 ^ 40 * 2010202 * 2
def baseEnd_2010202 : Nat := 1032199838629449309130255

theorem tailTrace_2010202 : CollatzResearch.WordTrace tailWord_2010202 prefixEnd_2010202 1032199838629449309130255 := by
  unfold tailWord_2010202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329522565847236003498215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48878726842259296009328573 18329522565847236003498215)
  ·
    refine ⟨27494283848770854005247323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18329522565847236003498215 27494283848770854005247323)
    ·
      refine ⟨41241425773156281007870985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27494283848770854005247323 41241425773156281007870985)
      ·
        refine ⟨30931069329867210755903239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41241425773156281007870985 30931069329867210755903239)
        ·
          refine ⟨46396603994800816133854859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30931069329867210755903239 46396603994800816133854859)
          ·
            refine ⟨69594905992201224200782289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46396603994800816133854859 69594905992201224200782289)
            ·
              refine ⟨52196179494150918150586717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69594905992201224200782289 52196179494150918150586717)
              ·
                refine ⟨19573567310306594306470019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52196179494150918150586717 19573567310306594306470019)
                ·
                  refine ⟨29360350965459891459705029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19573567310306594306470019 29360350965459891459705029)
                  ·
                    refine ⟨5505065806023729648694693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29360350965459891459705029 5505065806023729648694693)
                    ·
                      refine ⟨1032199838629449309130255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5505065806023729648694693 1032199838629449309130255)
                      ·
                        rfl

theorem cell23_2010202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2010202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010202 prefixEnd_2010202 := by exact prefixLift 2010202
  have htrace : WordTrace (prefixWord ++ tailWord_2010202) baseStart_2010202 baseEnd_2010202 := by
    simpa [prefixWord, tailWord_2010202, baseEnd_2010202] using wordTrace_append hprefix tailTrace_2010202
  have hstable : (prefixWord ++ tailWord_2010202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010202).length < 2 ^ (prefixWord ++ tailWord_2010202).sum := by decide
  have hdescent : baseEnd_2010202 < baseStart_2010202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010210 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2010210 : Nat := 118140960795 + 2010210 * 2 ^ 59
def prefixEnd_2010210 : Nat := 4983230072969 + 3 ^ 40 * 2010210 * 2
def baseEnd_2010210 : Nat := 1032203946474685277830219

theorem tailTrace_2010210 : CollatzResearch.WordTrace tailWord_2010210 prefixEnd_2010210 1032203946474685277830219 := by
  unfold tailWord_2010210
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329595511839990345071021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48878921364906640920189389 18329595511839990345071021)
  ·
    refine ⟨6873598316939996379401633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18329595511839990345071021 6873598316939996379401633)
    ·
      refine ⟨5155198737704997284551225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6873598316939996379401633 5155198737704997284551225)
      ·
        refine ⟨3866399053278747963413419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5155198737704997284551225 3866399053278747963413419)
        ·
          refine ⟨5799598579918121945120129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866399053278747963413419 5799598579918121945120129)
          ·
            refine ⟨4349698934938591458840097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799598579918121945120129 4349698934938591458840097)
            ·
              refine ⟨3262274201203943594130073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349698934938591458840097 3262274201203943594130073)
              ·
                refine ⟨2446705650902957695597555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262274201203943594130073 2446705650902957695597555)
                ·
                  refine ⟨3670058476354436543396333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446705650902957695597555 3670058476354436543396333)
                  ·
                    refine ⟨1376271928632913703773625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670058476354436543396333 1376271928632913703773625)
                    ·
                      refine ⟨1032203946474685277830219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376271928632913703773625 1032203946474685277830219)
                      ·
                        rfl

theorem cell23_2010210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2010210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010210 prefixEnd_2010210 := by exact prefixLift 2010210
  have htrace : WordTrace (prefixWord ++ tailWord_2010210) baseStart_2010210 baseEnd_2010210 := by
    simpa [prefixWord, tailWord_2010210, baseEnd_2010210] using wordTrace_append hprefix tailTrace_2010210
  have hstable : (prefixWord ++ tailWord_2010210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010210).length < 2 ^ (prefixWord ++ tailWord_2010210).sum := by decide
  have hdescent : baseEnd_2010210 < baseStart_2010210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010276 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_2010276 : Nat := 118140960795 + 2010276 * 2 ^ 59
def prefixEnd_2010276 : Nat := 4983230072969 + 3 ^ 40 * 2010276 * 2
def baseEnd_2010276 : Nat := 344079278732627339868305

theorem tailTrace_2010276 : CollatzResearch.WordTrace tailWord_2010276 prefixEnd_2010276 344079278732627339868305 := by
  unfold tailWord_2010276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36660394632560427326093341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48880526176747236434791121 36660394632560427326093341)
  ·
    refine ⟨13747647987210160247285003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36660394632560427326093341 13747647987210160247285003)
    ·
      refine ⟨20621471980815240370927505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13747647987210160247285003 20621471980815240370927505)
      ·
        refine ⟨15466103985611430278195629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20621471980815240370927505 15466103985611430278195629)
        ·
          refine ⟨5799788994604286354323361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15466103985611430278195629 5799788994604286354323361)
          ·
            refine ⟨4349841745953214765742521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799788994604286354323361 4349841745953214765742521)
            ·
              refine ⟨3262381309464911074306891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349841745953214765742521 3262381309464911074306891)
              ·
                refine ⟨4893571964197366611460337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262381309464911074306891 4893571964197366611460337)
                ·
                  refine ⟨3670178973148024958595253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4893571964197366611460337 3670178973148024958595253)
                  ·
                    refine ⟨344079278732627339868305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670178973148024958595253 344079278732627339868305)
                    ·
                      rfl

theorem cell23_2010276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_2010276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010276 prefixEnd_2010276 := by exact prefixLift 2010276
  have htrace : WordTrace (prefixWord ++ tailWord_2010276) baseStart_2010276 baseEnd_2010276 := by
    simpa [prefixWord, tailWord_2010276, baseEnd_2010276] using wordTrace_append hprefix tailTrace_2010276
  have hstable : (prefixWord ++ tailWord_2010276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010276).length < 2 ^ (prefixWord ++ tailWord_2010276).sum := by decide
  have hdescent : baseEnd_2010276 < baseStart_2010276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010299 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3]
def baseStart_2010299 : Nat := 118140960795 + 2010299 * 2 ^ 59
def prefixEnd_2010299 : Nat := 4983230072969 + 3 ^ 40 * 2010299 * 2
def baseEnd_2010299 : Nat := 1032249646252935429617309

theorem tailTrace_2010299 : CollatzResearch.WordTrace tailWord_2010299 prefixEnd_2010299 1032249646252935429617309 := by
  unfold tailWord_2010299
  simp only [CollatzResearch.WordTrace]
  refine ⟨73321628144037529580273951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48881085429358353053515967 73321628144037529580273951)
  ·
    refine ⟨109982442216056294370410927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73321628144037529580273951 109982442216056294370410927)
    ·
      refine ⟨164973663324084441555616391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109982442216056294370410927 164973663324084441555616391)
      ·
        refine ⟨247460494986126662333424587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164973663324084441555616391 247460494986126662333424587)
        ·
          refine ⟨371190742479189993500136881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247460494986126662333424587 371190742479189993500136881)
          ·
            refine ⟨278393056859392495125102661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371190742479189993500136881 278393056859392495125102661)
            ·
              refine ⟨52198698161136092835956749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278393056859392495125102661 52198698161136092835956749)
              ·
                refine ⟨19574511810426034813483781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52198698161136092835956749 19574511810426034813483781)
                ·
                  refine ⟨3670220964454881527528209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19574511810426034813483781 3670220964454881527528209)
                  ·
                    refine ⟨2752665723341161145646157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3670220964454881527528209 2752665723341161145646157)
                    ·
                      refine ⟨1032249646252935429617309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752665723341161145646157 1032249646252935429617309)
                      ·
                        rfl

theorem cell23_2010299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3].length) (baseStart_2010299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010299 prefixEnd_2010299 := by exact prefixLift 2010299
  have htrace : WordTrace (prefixWord ++ tailWord_2010299) baseStart_2010299 baseEnd_2010299 := by
    simpa [prefixWord, tailWord_2010299, baseEnd_2010299] using wordTrace_append hprefix tailTrace_2010299
  have hstable : (prefixWord ++ tailWord_2010299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010299).length < 2 ^ (prefixWord ++ tailWord_2010299).sum := by decide
  have hdescent : baseEnd_2010299 < baseStart_2010299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010333 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2010333 : Nat := 118140960795 + 2010333 * 2 ^ 59
def prefixEnd_2010333 : Nat := 4983230072969 + 3 ^ 40 * 2010333 * 2
def baseEnd_2010333 : Nat := 1032267104595188296592153

theorem tailTrace_2010333 : CollatzResearch.WordTrace tailWord_2010333 prefixEnd_2010333 1032267104595188296592153 := by
  unfold tailWord_2010333
  simp only [CollatzResearch.WordTrace]
  refine ⟨73322868225914353387011653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48881912150609568924674435 73322868225914353387011653)
  ·
    refine ⟨13748037792358941260064685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73322868225914353387011653 13748037792358941260064685)
    ·
      refine ⟨5155514172134602972524257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13748037792358941260064685 5155514172134602972524257)
      ·
        refine ⟨3866635629100952229393193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5155514172134602972524257 3866635629100952229393193)
        ·
          refine ⟨2899976721825714172044895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3866635629100952229393193 2899976721825714172044895)
          ·
            refine ⟨4349965082738571258067343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899976721825714172044895 4349965082738571258067343)
            ·
              refine ⟨6524947624107856887101015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349965082738571258067343 6524947624107856887101015)
              ·
                refine ⟨9787421436161785330651523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524947624107856887101015 9787421436161785330651523)
                ·
                  refine ⟨14681132154242677995977285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787421436161785330651523 14681132154242677995977285)
                  ·
                    refine ⟨2752712278920502124245741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14681132154242677995977285 2752712278920502124245741)
                    ·
                      refine ⟨1032267104595188296592153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752712278920502124245741 1032267104595188296592153)
                      ·
                        rfl

theorem cell23_2010333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2010333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010333 prefixEnd_2010333 := by exact prefixLift 2010333
  have htrace : WordTrace (prefixWord ++ tailWord_2010333) baseStart_2010333 baseEnd_2010333 := by
    simpa [prefixWord, tailWord_2010333, baseEnd_2010333] using wordTrace_append hprefix tailTrace_2010333
  have hstable : (prefixWord ++ tailWord_2010333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010333).length < 2 ^ (prefixWord ++ tailWord_2010333).sum := by decide
  have hdescent : baseEnd_2010333 < baseStart_2010333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010370 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2010370 : Nat := 118140960795 + 2010370 * 2 ^ 59
def prefixEnd_2010370 : Nat := 4983230072969 + 3 ^ 40 * 2010370 * 2
def baseEnd_2010370 : Nat := 114698455931044961314387

theorem tailTrace_2010370 : CollatzResearch.WordTrace tailWord_2010370 prefixEnd_2010370 114698455931044961314387 := by
  unfold tailWord_2010370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331054431695077176527141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48882811817853539137405709 18331054431695077176527141)
  ·
    refine ⟨3437072705942826970598839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18331054431695077176527141 3437072705942826970598839)
    ·
      refine ⟨5155609058914240455898259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437072705942826970598839 5155609058914240455898259)
      ·
        refine ⟨7733413588371360683847389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5155609058914240455898259 7733413588371360683847389)
        ·
          refine ⟨2900030095639260256442771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7733413588371360683847389 2900030095639260256442771)
          ·
            refine ⟨4350045143458890384664157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900030095639260256442771 4350045143458890384664157)
            ·
              refine ⟨1631266928797083894249059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350045143458890384664157 1631266928797083894249059)
              ·
                refine ⟨2446900393195625841373589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631266928797083894249059 2446900393195625841373589)
                ·
                  refine ⟨114698455931044961314387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2446900393195625841373589 114698455931044961314387)
                  ·
                    rfl

theorem cell23_2010370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2010370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010370 prefixEnd_2010370 := by exact prefixLift 2010370
  have htrace : WordTrace (prefixWord ++ tailWord_2010370) baseStart_2010370 baseEnd_2010370 := by
    simpa [prefixWord, tailWord_2010370, baseEnd_2010370] using wordTrace_append hprefix tailTrace_2010370
  have hstable : (prefixWord ++ tailWord_2010370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010370).length < 2 ^ (prefixWord ++ tailWord_2010370).sum := by decide
  have hdescent : baseEnd_2010370 < baseStart_2010370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010389 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2010389 : Nat := 118140960795 + 2010389 * 2 ^ 59
def prefixEnd_2010389 : Nat := 4983230072969 + 3 ^ 40 * 2010389 * 2
def baseEnd_2010389 : Nat := 1032295859511840077491895

theorem tailTrace_2010389 : CollatzResearch.WordTrace tailWord_2010389 prefixEnd_2010389 1032295859511840077491895 := by
  unfold tailWord_2010389
  simp only [CollatzResearch.WordTrace]
  refine ⟨73324910713711474951050221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48883273809140983300700147 73324910713711474951050221)
  ·
    refine ⟨27496841517641803106643833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73324910713711474951050221 27496841517641803106643833)
    ·
      refine ⟨20622631138231352329982875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27496841517641803106643833 20622631138231352329982875)
      ·
        refine ⟨30933946707347028494974313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20622631138231352329982875 30933946707347028494974313)
        ·
          refine ⟨23200460030510271371230735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30933946707347028494974313 23200460030510271371230735)
          ·
            refine ⟨34800690045765407056846103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23200460030510271371230735 34800690045765407056846103)
            ·
              refine ⟨52201035068648110585269155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34800690045765407056846103 52201035068648110585269155)
              ·
                refine ⟨78301552602972165877903733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52201035068648110585269155 78301552602972165877903733)
                ·
                  refine ⟨7340770556528640551053475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78301552602972165877903733 7340770556528640551053475)
                  ·
                    refine ⟨11011155834792960826580213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7340770556528640551053475 11011155834792960826580213)
                    ·
                      refine ⟨1032295859511840077491895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11011155834792960826580213 1032295859511840077491895)
                      ·
                        rfl

theorem cell23_2010389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2010389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010389 prefixEnd_2010389 := by exact prefixLift 2010389
  have htrace : WordTrace (prefixWord ++ tailWord_2010389) baseStart_2010389 baseEnd_2010389 := by
    simpa [prefixWord, tailWord_2010389, baseEnd_2010389] using wordTrace_append hprefix tailTrace_2010389
  have hstable : (prefixWord ++ tailWord_2010389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010389).length < 2 ^ (prefixWord ++ tailWord_2010389).sum := by decide
  have hdescent : baseEnd_2010389 < baseStart_2010389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010396 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_2010396 : Nat := 118140960795 + 2010396 * 2 ^ 59
def prefixEnd_2010396 : Nat := 4983230072969 + 3 ^ 40 * 2010396 * 2
def baseEnd_2010396 : Nat := 344099817958807183368121

theorem tailTrace_2010396 : CollatzResearch.WordTrace tailWord_2010396 prefixEnd_2010396 344099817958807183368121 := by
  unfold tailWord_2010396
  simp only [CollatzResearch.WordTrace]
  refine ⟨36662583012343057573277521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48883444016457410097703361 36662583012343057573277521)
  ·
    refine ⟨27496937259257293179958141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36662583012343057573277521 27496937259257293179958141)
    ·
      refine ⟨10311351472221484942484303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27496937259257293179958141 10311351472221484942484303)
      ·
        refine ⟨15467027208332227413726455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311351472221484942484303 15467027208332227413726455)
        ·
          refine ⟨23200540812498341120589683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15467027208332227413726455 23200540812498341120589683)
          ·
            refine ⟨34800811218747511680884525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23200540812498341120589683 34800811218747511680884525)
            ·
              refine ⟨13050304207030316880331697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34800811218747511680884525 13050304207030316880331697)
              ·
                refine ⟨9787728155272737660248773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13050304207030316880331697 9787728155272737660248773)
                ·
                  refine ⟨1835199029113638311296645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9787728155272737660248773 1835199029113638311296645)
                  ·
                    refine ⟨344099817958807183368121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835199029113638311296645 344099817958807183368121)
                    ·
                      rfl

theorem cell23_2010396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_2010396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010396 prefixEnd_2010396 := by exact prefixLift 2010396
  have htrace : WordTrace (prefixWord ++ tailWord_2010396) baseStart_2010396 baseEnd_2010396 := by
    simpa [prefixWord, tailWord_2010396, baseEnd_2010396] using wordTrace_append hprefix tailTrace_2010396
  have hstable : (prefixWord ++ tailWord_2010396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010396).length < 2 ^ (prefixWord ++ tailWord_2010396).sum := by decide
  have hdescent : baseEnd_2010396 < baseStart_2010396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010397 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2010397 : Nat := 118140960795 + 2010397 * 2 ^ 59
def prefixEnd_2010397 : Nat := 4983230072969 + 3 ^ 40 * 2010397 * 2
def baseEnd_2010397 : Nat := 1032299967357076046191859

theorem tailTrace_2010397 : CollatzResearch.WordTrace tailWord_2010397 prefixEnd_2010397 1032299967357076046191859 := by
  unfold tailWord_2010397
  simp only [CollatzResearch.WordTrace]
  refine ⟨73325202497682492317341445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48883468331788328211560963 73325202497682492317341445)
  ·
    refine ⟨13748475468315467309501521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73325202497682492317341445 13748475468315467309501521)
    ·
      refine ⟨10311356601236600482126141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13748475468315467309501521 10311356601236600482126141)
      ·
        refine ⟨3866758725463725180797303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10311356601236600482126141 3866758725463725180797303)
        ·
          refine ⟨5800138088195587771195955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866758725463725180797303 5800138088195587771195955)
          ·
            refine ⟨8700207132293381656793933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800138088195587771195955 8700207132293381656793933)
            ·
              refine ⟨3262577674610018121297725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8700207132293381656793933 3262577674610018121297725)
              ·
                refine ⟨1223466627978756795486647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3262577674610018121297725 1223466627978756795486647)
                ·
                  refine ⟨1835199941968135193229971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223466627978756795486647 1835199941968135193229971)
                  ·
                    refine ⟨2752799912952202789844957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835199941968135193229971 2752799912952202789844957)
                    ·
                      refine ⟨1032299967357076046191859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752799912952202789844957 1032299967357076046191859)
                      ·
                        rfl

theorem cell23_2010397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2010397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010397 prefixEnd_2010397 := by exact prefixLift 2010397
  have htrace : WordTrace (prefixWord ++ tailWord_2010397) baseStart_2010397 baseEnd_2010397 := by
    simpa [prefixWord, tailWord_2010397, baseEnd_2010397] using wordTrace_append hprefix tailTrace_2010397
  have hstable : (prefixWord ++ tailWord_2010397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010397).length < 2 ^ (prefixWord ++ tailWord_2010397).sum := by decide
  have hdescent : baseEnd_2010397 < baseStart_2010397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010453 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2010453 : Nat := 118140960795 + 2010453 * 2 ^ 59
def prefixEnd_2010453 : Nat := 4983230072969 + 3 ^ 40 * 2010453 * 2
def baseEnd_2010453 : Nat := 1032328722273727827091601

theorem tailTrace_2010453 : CollatzResearch.WordTrace tailWord_2010453 prefixEnd_2010453 1032328722273727827091601 := by
  unfold tailWord_2010453
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327244985479613881380013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48884829990319742587586675 73327244985479613881380013)
  ·
    refine ⟨27497716869554855205517505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73327244985479613881380013 27497716869554855205517505)
    ·
      refine ⟨20623287652166141404138129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27497716869554855205517505 20623287652166141404138129)
      ·
        refine ⟨15467465739124606053103597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20623287652166141404138129 15467465739124606053103597)
        ·
          refine ⟨5800299652171727269913849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15467465739124606053103597 5800299652171727269913849)
          ·
            refine ⟨4350224739128795452435387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800299652171727269913849 4350224739128795452435387)
            ·
              refine ⟨6525337108693193178653081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350224739128795452435387 6525337108693193178653081)
              ·
                refine ⟨4894002831519894883989811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525337108693193178653081 4894002831519894883989811)
                ·
                  refine ⟨7341004247279842325984717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894002831519894883989811 7341004247279842325984717)
                  ·
                    refine ⟨2752876592729940872244269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7341004247279842325984717 2752876592729940872244269)
                    ·
                      refine ⟨1032328722273727827091601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2752876592729940872244269 1032328722273727827091601)
                      ·
                        rfl

theorem cell23_2010453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2010453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010453 prefixEnd_2010453 := by exact prefixLift 2010453
  have htrace : WordTrace (prefixWord ++ tailWord_2010453) baseStart_2010453 baseEnd_2010453 := by
    simpa [prefixWord, tailWord_2010453, baseEnd_2010453] using wordTrace_append hprefix tailTrace_2010453
  have hstable : (prefixWord ++ tailWord_2010453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010453).length < 2 ^ (prefixWord ++ tailWord_2010453).sum := by decide
  have hdescent : baseEnd_2010453 < baseStart_2010453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010471 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_2010471 : Nat := 118140960795 + 2010471 * 2 ^ 59
def prefixEnd_2010471 : Nat := 4983230072969 + 3 ^ 40 * 2010471 * 2
def baseEnd_2010471 : Nat := 1032337964925508756666519

theorem tailTrace_2010471 : CollatzResearch.WordTrace tailWord_2010471 prefixEnd_2010471 1032337964925508756666519 := by
  unfold tailWord_2010471
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327901499414402955535267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48885267666276268637023511 73327901499414402955535267)
  ·
    refine ⟨109991852249121604433302901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73327901499414402955535267 109991852249121604433302901)
    ·
      refine ⟨10311736148355150415622147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109991852249121604433302901 10311736148355150415622147)
      ·
        refine ⟨15467604222532725623433221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311736148355150415622147 15467604222532725623433221)
        ·
          refine ⟨2900175791724886054393729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15467604222532725623433221 2900175791724886054393729)
          ·
            refine ⟨2175131843793664540795297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2900175791724886054393729 2175131843793664540795297)
            ·
              refine ⟨1631348882845248405596473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175131843793664540795297 1631348882845248405596473)
              ·
                refine ⟨1223511662133936304197355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631348882845248405596473 1223511662133936304197355)
                ·
                  refine ⟨1835267493200904456296033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223511662133936304197355 1835267493200904456296033)
                  ·
                    refine ⟨1376450619900678342222025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1835267493200904456296033 1376450619900678342222025)
                    ·
                      refine ⟨1032337964925508756666519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376450619900678342222025 1032337964925508756666519)
                      ·
                        rfl

theorem cell23_2010471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_2010471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010471 prefixEnd_2010471 := by exact prefixLift 2010471
  have htrace : WordTrace (prefixWord ++ tailWord_2010471) baseStart_2010471 baseEnd_2010471 := by
    simpa [prefixWord, tailWord_2010471, baseEnd_2010471] using wordTrace_append hprefix tailTrace_2010471
  have hstable : (prefixWord ++ tailWord_2010471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010471).length < 2 ^ (prefixWord ++ tailWord_2010471).sum := by decide
  have hdescent : baseEnd_2010471 < baseStart_2010471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010476 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_2010476 : Nat := 118140960795 + 2010476 * 2 ^ 59
def prefixEnd_2010476 : Nat := 4983230072969 + 3 ^ 40 * 2010476 * 2
def baseEnd_2010476 : Nat := 1032340532328781237103995

theorem tailTrace_2010476 : CollatzResearch.WordTrace tailWord_2010476 prefixEnd_2010476 1032340532328781237103995 := by
  unfold tailWord_2010476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36664041932198144404733641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48885389242930859206311521 36664041932198144404733641)
  ·
    refine ⟨27498031449148608303550231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36664041932198144404733641 27498031449148608303550231)
    ·
      refine ⟨41247047173722912455325347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498031449148608303550231 41247047173722912455325347)
      ·
        refine ⟨61870570760584368682988021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41247047173722912455325347 61870570760584368682988021)
        ·
          refine ⟨5800366008804784564030127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61870570760584368682988021 5800366008804784564030127)
          ·
            refine ⟨8700549013207176846045191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800366008804784564030127 8700549013207176846045191)
            ·
              refine ⟨13050823519810765269067787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700549013207176846045191 13050823519810765269067787)
              ·
                refine ⟨19576235279716147903601681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050823519810765269067787 19576235279716147903601681)
                ·
                  refine ⟨14682176459787110927701261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19576235279716147903601681 14682176459787110927701261)
                  ·
                    refine ⟨5505816172420166597887973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14682176459787110927701261 5505816172420166597887973)
                    ·
                      refine ⟨1032340532328781237103995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5505816172420166597887973 1032340532328781237103995)
                      ·
                        rfl

theorem cell23_2010476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_2010476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010476 prefixEnd_2010476 := by exact prefixLift 2010476
  have htrace : WordTrace (prefixWord ++ tailWord_2010476) baseStart_2010476 baseEnd_2010476 := by
    simpa [prefixWord, tailWord_2010476, baseEnd_2010476] using wordTrace_append hprefix tailTrace_2010476
  have hstable : (prefixWord ++ tailWord_2010476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010476).length < 2 ^ (prefixWord ++ tailWord_2010476).sum := by decide
  have hdescent : baseEnd_2010476 < baseStart_2010476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010514 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2010514 : Nat := 118140960795 + 2010514 * 2 ^ 59
def prefixEnd_2010514 : Nat := 4983230072969 + 3 ^ 40 * 2010514 * 2
def baseEnd_2010514 : Nat := 1032360044593652088428821

theorem tailTrace_2010514 : CollatzResearch.WordTrace tailWord_2010514 prefixEnd_2010514 1032360044593652088428821 := by
  unfold tailWord_2010514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332367459564655324837649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48886313225505747532900397 18332367459564655324837649)
  ·
    refine ⟨13749275594673491493628237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18332367459564655324837649 13749275594673491493628237)
    ·
      refine ⟨5155978348002559310110589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13749275594673491493628237 5155978348002559310110589)
      ·
        refine ⟨1933491880500959741291471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5155978348002559310110589 1933491880500959741291471)
        ·
          refine ⟨2900237820751439611937207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933491880500959741291471 2900237820751439611937207)
          ·
            refine ⟨4350356731127159417905811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900237820751439611937207 4350356731127159417905811)
            ·
              refine ⟨6525535096690739126858717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350356731127159417905811 6525535096690739126858717)
              ·
                refine ⟨2447075661259027172572019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525535096690739126858717 2447075661259027172572019)
                ·
                  refine ⟨3670613491888540758858029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447075661259027172572019 3670613491888540758858029)
                  ·
                    refine ⟨1376480059458202784571761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670613491888540758858029 1376480059458202784571761)
                    ·
                      refine ⟨1032360044593652088428821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376480059458202784571761 1032360044593652088428821)
                      ·
                        rfl

theorem cell23_2010514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2010514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010514 prefixEnd_2010514 := by exact prefixLift 2010514
  have htrace : WordTrace (prefixWord ++ tailWord_2010514) baseStart_2010514 baseEnd_2010514 := by
    simpa [prefixWord, tailWord_2010514, baseEnd_2010514] using wordTrace_append hprefix tailTrace_2010514
  have hstable : (prefixWord ++ tailWord_2010514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010514).length < 2 ^ (prefixWord ++ tailWord_2010514).sum := by decide
  have hdescent : baseEnd_2010514 < baseStart_2010514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010527 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 2, 2, 2]
def baseStart_2010527 : Nat := 118140960795 + 2010527 * 2 ^ 59
def prefixEnd_2010527 : Nat := 4983230072969 + 3 ^ 40 * 2010527 * 2
def baseEnd_2010527 : Nat := 1032366719842160537566261

theorem tailTrace_2010527 : CollatzResearch.WordTrace tailWord_2010527 prefixEnd_2010527 1032366719842160537566261 := by
  unfold tailWord_2010527
  simp only [CollatzResearch.WordTrace]
  refine ⟨73329943987211524519573835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48886629324807683013049223 73329943987211524519573835)
  ·
    refine ⟨109994915980817286779360753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73329943987211524519573835 109994915980817286779360753)
    ·
      refine ⟨82496186985612965084520565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109994915980817286779360753 82496186985612965084520565)
      ·
        refine ⟨7734017529901215476673803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82496186985612965084520565 7734017529901215476673803)
        ·
          refine ⟨11601026294851823215010705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734017529901215476673803 11601026294851823215010705)
          ·
            refine ⟨8700769721138867411258029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11601026294851823215010705 8700769721138867411258029)
            ·
              refine ⟨3262788645427075279221761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8700769721138867411258029 3262788645427075279221761)
              ·
                refine ⟨2447091484070306459416321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3262788645427075279221761 2447091484070306459416321)
                ·
                  refine ⟨1835318613052729844562241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2447091484070306459416321 1835318613052729844562241)
                  ·
                    refine ⟨1376488959789547383421681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1835318613052729844562241 1376488959789547383421681)
                    ·
                      refine ⟨1032366719842160537566261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376488959789547383421681 1032366719842160537566261)
                      ·
                        rfl

theorem cell23_2010527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_2010527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010527 prefixEnd_2010527 := by exact prefixLift 2010527
  have htrace : WordTrace (prefixWord ++ tailWord_2010527) baseStart_2010527 baseEnd_2010527 := by
    simpa [prefixWord, tailWord_2010527, baseEnd_2010527] using wordTrace_append hprefix tailTrace_2010527
  have hstable : (prefixWord ++ tailWord_2010527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010527).length < 2 ^ (prefixWord ++ tailWord_2010527).sum := by decide
  have hdescent : baseEnd_2010527 < baseStart_2010527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010546 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2010546 : Nat := 118140960795 + 2010546 * 2 ^ 59
def prefixEnd_2010546 : Nat := 4983230072969 + 3 ^ 40 * 2010546 * 2
def baseEnd_2010546 : Nat := 344125491991531987742891

theorem tailTrace_2010546 : CollatzResearch.WordTrace tailWord_2010546 prefixEnd_2010546 344125491991531987742891 := by
  unfold tailWord_2010546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332659243535672691128873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48887091316095127176343661 18332659243535672691128873)
  ·
    refine ⟨13749494432651754518346655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18332659243535672691128873 13749494432651754518346655)
    ·
      refine ⟨20624241648977631777519983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13749494432651754518346655 20624241648977631777519983)
      ·
        refine ⟨30936362473466447666279975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20624241648977631777519983 30936362473466447666279975)
        ·
          refine ⟨46404543710199671499419963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30936362473466447666279975 46404543710199671499419963)
          ·
            refine ⟨69606815565299507249129945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46404543710199671499419963 69606815565299507249129945)
            ·
              refine ⟨52205111673974630436847459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69606815565299507249129945 52205111673974630436847459)
              ·
                refine ⟨78307667510961945655271189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52205111673974630436847459 78307667510961945655271189)
                ·
                  refine ⟨3670671914576341202590837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78307667510961945655271189 3670671914576341202590837)
                  ·
                    refine ⟨344125491991531987742891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670671914576341202590837 344125491991531987742891)
                    ·
                      rfl

theorem cell23_2010546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2010546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010546 prefixEnd_2010546 := by exact prefixLift 2010546
  have htrace : WordTrace (prefixWord ++ tailWord_2010546) baseStart_2010546 baseEnd_2010546 := by
    simpa [prefixWord, tailWord_2010546, baseEnd_2010546] using wordTrace_append hprefix tailTrace_2010546
  have hstable : (prefixWord ++ tailWord_2010546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010546).length < 2 ^ (prefixWord ++ tailWord_2010546).sum := by decide
  have hdescent : baseEnd_2010546 < baseStart_2010546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010580 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2010580 : Nat := 118140960795 + 2010580 * 2 ^ 59
def prefixEnd_2010580 : Nat := 4983230072969 + 3 ^ 40 * 2010580 * 2
def baseEnd_2010580 : Nat := 344131311438949610067839

theorem tailTrace_2010580 : CollatzResearch.WordTrace tailWord_2010580 prefixEnd_2010580 344131311438949610067839 := by
  unfold tailWord_2010580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665938528009757285626597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48887918037346343047502129 36665938528009757285626597)
  ·
    refine ⟨6874863474001829491054987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36665938528009757285626597 6874863474001829491054987)
    ·
      refine ⟨10312295211002744236582481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874863474001829491054987 10312295211002744236582481)
      ·
        refine ⟨7734221408252058177436861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312295211002744236582481 7734221408252058177436861)
        ·
          refine ⟨2900333028094521816538823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7734221408252058177436861 2900333028094521816538823)
          ·
            refine ⟨4350499542141782724808235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900333028094521816538823 4350499542141782724808235)
            ·
              refine ⟨6525749313212674087212353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350499542141782724808235 6525749313212674087212353)
              ·
                refine ⟨4894311984909505565409265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525749313212674087212353 4894311984909505565409265)
                ·
                  refine ⟨3670733988682129174056949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894311984909505565409265 3670733988682129174056949)
                  ·
                    refine ⟨344131311438949610067839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670733988682129174056949 344131311438949610067839)
                    ·
                      rfl

theorem cell23_2010580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2010580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010580 prefixEnd_2010580 := by exact prefixLift 2010580
  have htrace : WordTrace (prefixWord ++ tailWord_2010580) baseStart_2010580 baseEnd_2010580 := by
    simpa [prefixWord, tailWord_2010580, baseEnd_2010580] using wordTrace_append hprefix tailTrace_2010580
  have hstable : (prefixWord ++ tailWord_2010580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010580).length < 2 ^ (prefixWord ++ tailWord_2010580).sum := by decide
  have hdescent : baseEnd_2010580 < baseStart_2010580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010583 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_2010583 : Nat := 118140960795 + 2010583 * 2 ^ 59
def prefixEnd_2010583 : Nat := 4983230072969 + 3 ^ 40 * 2010583 * 2
def baseEnd_2010583 : Nat := 1032395474758812318466003

theorem tailTrace_2010583 : CollatzResearch.WordTrace tailWord_2010583 prefixEnd_2010583 1032395474758812318466003 := by
  unfold tailWord_2010583
  simp only [CollatzResearch.WordTrace]
  refine ⟨73331986475008646083612403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48887990983339097389074935 73331986475008646083612403)
  ·
    refine ⟨109997979712512969125418605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73331986475008646083612403 109997979712512969125418605)
    ·
      refine ⟨41249242392192363422031977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109997979712512969125418605 41249242392192363422031977)
      ·
        refine ⟨30936931794144272566523983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41249242392192363422031977 30936931794144272566523983)
        ·
          refine ⟨46405397691216408849785975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30936931794144272566523983 46405397691216408849785975)
          ·
            refine ⟨69608096536824613274678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46405397691216408849785975 69608096536824613274678963)
            ·
              refine ⟨104412144805236919912018445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69608096536824613274678963 104412144805236919912018445)
              ·
                refine ⟨39154554301963844967006917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104412144805236919912018445 39154554301963844967006917)
                ·
                  refine ⟨7341478931618220931313797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39154554301963844967006917 7341478931618220931313797)
                  ·
                    refine ⟨1376527299678416424621337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341478931618220931313797 1376527299678416424621337)
                    ·
                      refine ⟨1032395474758812318466003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376527299678416424621337 1032395474758812318466003)
                      ·
                        rfl

theorem cell23_2010583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_2010583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010583 prefixEnd_2010583 := by exact prefixLift 2010583
  have htrace : WordTrace (prefixWord ++ tailWord_2010583) baseStart_2010583 baseEnd_2010583 := by
    simpa [prefixWord, tailWord_2010583, baseEnd_2010583] using wordTrace_append hprefix tailTrace_2010583
  have hstable : (prefixWord ++ tailWord_2010583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010583).length < 2 ^ (prefixWord ++ tailWord_2010583).sum := by decide
  have hdescent : baseEnd_2010583 < baseStart_2010583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010596 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2010596 : Nat := 118140960795 + 2010596 * 2 ^ 59
def prefixEnd_2010596 : Nat := 4983230072969 + 3 ^ 40 * 2010596 * 2
def baseEnd_2010596 : Nat := 1032402150007320767603443

theorem tailTrace_2010596 : CollatzResearch.WordTrace tailWord_2010596 prefixEnd_2010596 1032402150007320767603443 := by
  unfold tailWord_2010596
  simp only [CollatzResearch.WordTrace]
  refine ⟨36666230311980774651917821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48888307082641032869223761 36666230311980774651917821)
  ·
    refine ⟨13749836366992790494469183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36666230311980774651917821 13749836366992790494469183)
    ·
      refine ⟨20624754550489185741703775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13749836366992790494469183 20624754550489185741703775)
      ·
        refine ⟨30937131825733778612555663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20624754550489185741703775 30937131825733778612555663)
        ·
          refine ⟨46405697738600667918833495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30937131825733778612555663 46405697738600667918833495)
          ·
            refine ⟨69608546607901001878250243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46405697738600667918833495 69608546607901001878250243)
            ·
              refine ⟨104412819911851502817375365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69608546607901001878250243 104412819911851502817375365)
              ·
                refine ⟨19577403733472156778257881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104412819911851502817375365 19577403733472156778257881)
                ·
                  refine ⟨14683052800104117583693411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19577403733472156778257881 14683052800104117583693411)
                  ·
                    refine ⟨22024579200156176375540117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14683052800104117583693411 22024579200156176375540117)
                    ·
                      refine ⟨1032402150007320767603443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22024579200156176375540117 1032402150007320767603443)
                      ·
                        rfl

theorem cell23_2010596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2010596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010596 prefixEnd_2010596 := by exact prefixLift 2010596
  have htrace : WordTrace (prefixWord ++ tailWord_2010596) baseStart_2010596 baseEnd_2010596 := by
    simpa [prefixWord, tailWord_2010596, baseEnd_2010596] using wordTrace_append hprefix tailTrace_2010596
  have hstable : (prefixWord ++ tailWord_2010596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010596).length < 2 ^ (prefixWord ++ tailWord_2010596).sum := by decide
  have hdescent : baseEnd_2010596 < baseStart_2010596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010650 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_2010650 : Nat := 118140960795 + 2010650 * 2 ^ 59
def prefixEnd_2010650 : Nat := 4983230072969 + 3 ^ 40 * 2010650 * 2
def baseEnd_2010650 : Nat := 1032429877962663556328195

theorem tailTrace_2010650 : CollatzResearch.WordTrace tailWord_2010650 prefixEnd_2010650 1032429877962663556328195 := by
  unfold tailWord_2010650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333607541441479131575351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48889620110510611017534269 18333607541441479131575351)
  ·
    refine ⟨27500411312162218697363027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333607541441479131575351 27500411312162218697363027)
    ·
      refine ⟨41250616968243328046044541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500411312162218697363027 41250616968243328046044541)
      ·
        refine ⟨15468981363091248017266703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41250616968243328046044541 15468981363091248017266703)
        ·
          refine ⟨23203472044636872025900055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15468981363091248017266703 23203472044636872025900055)
          ·
            refine ⟨34805208066955308038850083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23203472044636872025900055 34805208066955308038850083)
            ·
              refine ⟨52207812100432962058275125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34805208066955308038850083 52207812100432962058275125)
              ·
                refine ⟨4894482384415590192963293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52207812100432962058275125 4894482384415590192963293)
                ·
                  refine ⟨1835430894155846322361235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4894482384415590192963293 1835430894155846322361235)
                  ·
                    refine ⟨2753146341233769483541853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835430894155846322361235 2753146341233769483541853)
                    ·
                      refine ⟨1032429877962663556328195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2753146341233769483541853 1032429877962663556328195)
                      ·
                        rfl

theorem cell23_2010650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_2010650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010650 prefixEnd_2010650 := by exact prefixLift 2010650
  have htrace : WordTrace (prefixWord ++ tailWord_2010650) baseStart_2010650 baseEnd_2010650 := by
    simpa [prefixWord, tailWord_2010650, baseEnd_2010650] using wordTrace_append hprefix tailTrace_2010650
  have hstable : (prefixWord ++ tailWord_2010650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010650).length < 2 ^ (prefixWord ++ tailWord_2010650).sum := by decide
  have hdescent : baseEnd_2010650 < baseStart_2010650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010653 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2010653 : Nat := 118140960795 + 2010653 * 2 ^ 59
def prefixEnd_2010653 : Nat := 4983230072969 + 3 ^ 40 * 2010653 * 2
def baseEnd_2010653 : Nat := 344143806134875681530227

theorem tailTrace_2010653 : CollatzResearch.WordTrace tailWord_2010653 prefixEnd_2010653 344143806134875681530227 := by
  unfold tailWord_2010653
  simp only [CollatzResearch.WordTrace]
  refine ⟨73334539584755048038660613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48889693056503365359107075 73334539584755048038660613)
  ·
    refine ⟨13750226172141571507248865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73334539584755048038660613 13750226172141571507248865)
    ·
      refine ⟨10312669629106178630436649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13750226172141571507248865 10312669629106178630436649)
      ·
        refine ⟨7734502221829633972827487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312669629106178630436649 7734502221829633972827487)
        ·
          refine ⟨11601753332744450959241231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734502221829633972827487 11601753332744450959241231)
          ·
            refine ⟨17402629999116676438861847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601753332744450959241231 17402629999116676438861847)
            ·
              refine ⟨26103944998675014658292771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17402629999116676438861847 26103944998675014658292771)
              ·
                refine ⟨39155917498012521987439157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26103944998675014658292771 39155917498012521987439157)
                ·
                  refine ⟨3670867265438673936322421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39155917498012521987439157 3670867265438673936322421)
                  ·
                    refine ⟨344143806134875681530227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670867265438673936322421 344143806134875681530227)
                    ·
                      rfl

theorem cell23_2010653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2010653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010653 prefixEnd_2010653 := by exact prefixLift 2010653
  have htrace : WordTrace (prefixWord ++ tailWord_2010653) baseStart_2010653 baseEnd_2010653 := by
    simpa [prefixWord, tailWord_2010653, baseEnd_2010653] using wordTrace_append hprefix tailTrace_2010653
  have hstable : (prefixWord ++ tailWord_2010653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010653).length < 2 ^ (prefixWord ++ tailWord_2010653).sum := by decide
  have hdescent : baseEnd_2010653 < baseStart_2010653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010670 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2010670 : Nat := 118140960795 + 2010670 * 2 ^ 59
def prefixEnd_2010670 : Nat := 4983230072969 + 3 ^ 40 * 2010670 * 2
def baseEnd_2010670 : Nat := 344146715858584492692701

theorem tailTrace_2010670 : CollatzResearch.WordTrace tailWord_2010670 prefixEnd_2010670 344146715858584492692701 := by
  unfold tailWord_2010670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166894953211682492753683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48890106417128973294686309 9166894953211682492753683)
  ·
    refine ⟨13750342429817523739130525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9166894953211682492753683 13750342429817523739130525)
    ·
      refine ⟨5156378411181571402173947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13750342429817523739130525 5156378411181571402173947)
      ·
        refine ⟨7734567616772357103260921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156378411181571402173947 7734567616772357103260921)
        ·
          refine ⟨5800925712579267827445691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7734567616772357103260921 5800925712579267827445691)
          ·
            refine ⟨8701388568868901741168537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800925712579267827445691 8701388568868901741168537)
            ·
              refine ⟨6526041426651676305876403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8701388568868901741168537 6526041426651676305876403)
              ·
                refine ⟨9789062139977514458814605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526041426651676305876403 9789062139977514458814605)
                ·
                  refine ⟨3670898302491567922055477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9789062139977514458814605 3670898302491567922055477)
                  ·
                    refine ⟨344146715858584492692701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670898302491567922055477 344146715858584492692701)
                    ·
                      rfl

theorem cell23_2010670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2010670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010670 prefixEnd_2010670 := by exact prefixLift 2010670
  have htrace : WordTrace (prefixWord ++ tailWord_2010670) baseStart_2010670 baseEnd_2010670 := by
    simpa [prefixWord, tailWord_2010670, baseEnd_2010670] using wordTrace_append hprefix tailTrace_2010670
  have hstable : (prefixWord ++ tailWord_2010670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010670).length < 2 ^ (prefixWord ++ tailWord_2010670).sum := by decide
  have hdescent : baseEnd_2010670 < baseStart_2010670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010677 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_2010677 : Nat := 118140960795 + 2010677 * 2 ^ 59
def prefixEnd_2010677 : Nat := 4983230072969 + 3 ^ 40 * 2010677 * 2
def baseEnd_2010677 : Nat := 1032443741940334950690571

theorem tailTrace_2010677 : CollatzResearch.WordTrace tailWord_2010677 prefixEnd_2010677 1032443741940334950690571 := by
  unfold tailWord_2010677
  simp only [CollatzResearch.WordTrace]
  refine ⟨73335414936668100137534285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48890276624445400091689523 73335414936668100137534285)
  ·
    refine ⟨27500780601250537551575357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73335414936668100137534285 27500780601250537551575357)
    ·
      refine ⟨10312792725468951581840759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27500780601250537551575357 10312792725468951581840759)
      ·
        refine ⟨15469189088203427372761139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10312792725468951581840759 15469189088203427372761139)
        ·
          refine ⟨23203783632305141059141709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15469189088203427372761139 23203783632305141059141709)
          ·
            refine ⟨8701418862114427897178141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23203783632305141059141709 8701418862114427897178141)
            ·
              refine ⟨3263032073292910461441803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8701418862114427897178141 3263032073292910461441803)
              ·
                refine ⟨4894548109939365692162705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263032073292910461441803 4894548109939365692162705)
                ·
                  refine ⟨3670911082454524269122029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894548109939365692162705 3670911082454524269122029)
                  ·
                    refine ⟨1376591655920446600920761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670911082454524269122029 1376591655920446600920761)
                    ·
                      refine ⟨1032443741940334950690571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376591655920446600920761 1032443741940334950690571)
                      ·
                        rfl

theorem cell23_2010677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_2010677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010677 prefixEnd_2010677 := by exact prefixLift 2010677
  have htrace : WordTrace (prefixWord ++ tailWord_2010677) baseStart_2010677 baseEnd_2010677 := by
    simpa [prefixWord, tailWord_2010677, baseEnd_2010677] using wordTrace_append hprefix tailTrace_2010677
  have hstable : (prefixWord ++ tailWord_2010677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010677).length < 2 ^ (prefixWord ++ tailWord_2010677).sum := by decide
  have hdescent : baseEnd_2010677 < baseStart_2010677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010687 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 1, 5]
def baseStart_2010687 : Nat := 118140960795 + 2010687 * 2 ^ 59
def prefixEnd_2010687 : Nat := 4983230072969 + 3 ^ 40 * 2010687 * 2
def baseEnd_2010687 : Nat := 344149625582293303855175

theorem tailTrace_2010687 : CollatzResearch.WordTrace tailWord_2010687 prefixEnd_2010687 344149625582293303855175 := by
  unfold tailWord_2010687
  simp only [CollatzResearch.WordTrace]
  refine ⟨73335779666631871845398315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48890519777754581230265543 73335779666631871845398315)
  ·
    refine ⟨110003669499947807768097473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73335779666631871845398315 110003669499947807768097473)
    ·
      refine ⟨82502752124960855826073105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110003669499947807768097473 82502752124960855826073105)
      ·
        refine ⟨61877064093720641869554829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82502752124960855826073105 61877064093720641869554829)
        ·
          refine ⟨23203899035145240701083061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61877064093720641869554829 23203899035145240701083061)
          ·
            refine ⟨2175365534544866315726537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23203899035145240701083061 2175365534544866315726537)
            ·
              refine ⟨1631524150908649736794903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175365534544866315726537 1631524150908649736794903)
              ·
                refine ⟨2447286226362974605192355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631524150908649736794903 2447286226362974605192355)
                ·
                  refine ⟨3670929339544461907788533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447286226362974605192355 3670929339544461907788533)
                  ·
                    refine ⟨344149625582293303855175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3670929339544461907788533 344149625582293303855175)
                    ·
                      rfl

theorem cell23_2010687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_2010687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010687 prefixEnd_2010687 := by exact prefixLift 2010687
  have htrace : WordTrace (prefixWord ++ tailWord_2010687) baseStart_2010687 baseEnd_2010687 := by
    simpa [prefixWord, tailWord_2010687, baseEnd_2010687] using wordTrace_append hprefix tailTrace_2010687
  have hstable : (prefixWord ++ tailWord_2010687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010687).length < 2 ^ (prefixWord ++ tailWord_2010687).sum := by decide
  have hdescent : baseEnd_2010687 < baseStart_2010687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010693 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_2010693 : Nat := 118140960795 + 2010693 * 2 ^ 59
def prefixEnd_2010693 : Nat := 4983230072969 + 3 ^ 40 * 2010693 * 2
def baseEnd_2010693 : Nat := 1032451957630806888090497

theorem tailTrace_2010693 : CollatzResearch.WordTrace tailWord_2010693 prefixEnd_2010693 1032451957630806888090497 := by
  unfold tailWord_2010693
  simp only [CollatzResearch.WordTrace]
  refine ⟨73335998504610134870116733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48890665669740089913411155 73335998504610134870116733)
  ·
    refine ⟨27500999439228800576293775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73335998504610134870116733 27500999439228800576293775)
    ·
      refine ⟨41251499158843200864440663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500999439228800576293775 41251499158843200864440663)
      ·
        refine ⟨61877248738264801296660995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41251499158843200864440663 61877248738264801296660995)
        ·
          refine ⟨92815873107397201944991493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61877248738264801296660995 92815873107397201944991493)
          ·
            refine ⟨17402976207636975364685905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92815873107397201944991493 17402976207636975364685905)
            ·
              refine ⟨13052232155727731523514429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17402976207636975364685905 13052232155727731523514429)
              ·
                refine ⟨4894587058397899321317911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13052232155727731523514429 4894587058397899321317911)
                ·
                  refine ⟨7341880587596848981976867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894587058397899321317911 7341880587596848981976867)
                  ·
                    refine ⟨11012820881395273472965301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7341880587596848981976867 11012820881395273472965301)
                    ·
                      refine ⟨1032451957630806888090497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11012820881395273472965301 1032451957630806888090497)
                      ·
                        rfl

theorem cell23_2010693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_2010693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010693 prefixEnd_2010693 := by exact prefixLift 2010693
  have htrace : WordTrace (prefixWord ++ tailWord_2010693) baseStart_2010693 baseEnd_2010693 := by
    simpa [prefixWord, tailWord_2010693, baseEnd_2010693] using wordTrace_append hprefix tailTrace_2010693
  have hstable : (prefixWord ++ tailWord_2010693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010693).length < 2 ^ (prefixWord ++ tailWord_2010693).sum := by decide
  have hdescent : baseEnd_2010693 < baseStart_2010693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010700 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_2010700 : Nat := 118140960795 + 2010700 * 2 ^ 59
def prefixEnd_2010700 : Nat := 4983230072969 + 3 ^ 40 * 2010700 * 2
def baseEnd_2010700 : Nat := 344151850665129453567655

theorem tailTrace_2010700 : CollatzResearch.WordTrace tailWord_2010700 prefixEnd_2010700 344151850665129453567655 := by
  unfold tailWord_2010700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36668126907792387532810777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48890835877056516710414369 36668126907792387532810777)
  ·
    refine ⟨27501095180844290649608083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36668126907792387532810777 27501095180844290649608083)
    ·
      refine ⟨41251642771266435974412125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27501095180844290649608083 41251642771266435974412125)
      ·
        refine ⟨15469366039224913490404547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41251642771266435974412125 15469366039224913490404547)
        ·
          refine ⟨23204049058837370235606821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15469366039224913490404547 23204049058837370235606821)
          ·
            refine ⟨4350759198532006919176279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23204049058837370235606821 4350759198532006919176279)
            ·
              refine ⟨6526138797798010378764419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350759198532006919176279 6526138797798010378764419)
              ·
                refine ⟨9789208196697015568146629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526138797798010378764419 9789208196697015568146629)
                ·
                  refine ⟨1835476536880690419027493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9789208196697015568146629 1835476536880690419027493)
                  ·
                    refine ⟨344151850665129453567655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835476536880690419027493 344151850665129453567655)
                    ·
                      rfl

theorem cell23_2010700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_2010700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010700 prefixEnd_2010700 := by exact prefixLift 2010700
  have htrace : WordTrace (prefixWord ++ tailWord_2010700) baseStart_2010700 baseEnd_2010700 := by
    simpa [prefixWord, tailWord_2010700, baseEnd_2010700] using wordTrace_append hprefix tailTrace_2010700
  have hstable : (prefixWord ++ tailWord_2010700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010700).length < 2 ^ (prefixWord ++ tailWord_2010700).sum := by decide
  have hdescent : baseEnd_2010700 < baseStart_2010700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010730 : List Nat := [3, 1, 3, 2, 1, 2, 4, 7]
def baseStart_2010730 : Nat := 118140960795 + 2010730 * 2 ^ 59
def prefixEnd_2010730 : Nat := 4983230072969 + 3 ^ 40 * 2010730 * 2
def baseEnd_2010730 : Nat := 38239665052408268271401

theorem tailTrace_2010730 : CollatzResearch.WordTrace tailWord_2010730 prefixEnd_2010730 38239665052408268271401 := by
  unfold tailWord_2010730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18334337001369022547303411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48891565336984060126142429 18334337001369022547303411)
  ·
    refine ⟨27501505502053533820955117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18334337001369022547303411 27501505502053533820955117)
    ·
      refine ⟨10313064563270075182858169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27501505502053533820955117 10313064563270075182858169)
      ·
        refine ⟨7734798422452556387143627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10313064563270075182858169 7734798422452556387143627)
        ·
          refine ⟨11602197633678834580715441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734798422452556387143627 11602197633678834580715441)
          ·
            refine ⟨8701648225259125935536581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11602197633678834580715441 8701648225259125935536581)
            ·
              refine ⟨1631559042236086112913109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8701648225259125935536581 1631559042236086112913109)
              ·
                refine ⟨38239665052408268271401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1631559042236086112913109 38239665052408268271401)
                ·
                  rfl

theorem cell23_2010730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_2010730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010730 prefixEnd_2010730 := by exact prefixLift 2010730
  have htrace : WordTrace (prefixWord ++ tailWord_2010730) baseStart_2010730 baseEnd_2010730 := by
    simpa [prefixWord, tailWord_2010730, baseEnd_2010730] using wordTrace_append hprefix tailTrace_2010730
  have hstable : (prefixWord ++ tailWord_2010730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010730).length < 2 ^ (prefixWord ++ tailWord_2010730).sum := by decide
  have hdescent : baseEnd_2010730 < baseStart_2010730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010757 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_2010757 : Nat := 118140960795 + 2010757 * 2 ^ 59
def prefixEnd_2010757 : Nat := 4983230072969 + 3 ^ 40 * 2010757 * 2
def baseEnd_2010757 : Nat := 1032484820392694637690203

theorem tailTrace_2010757 : CollatzResearch.WordTrace tailWord_2010757 prefixEnd_2010757 1032484820392694637690203 := by
  unfold tailWord_2010757
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338332776378273800446525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48892221850918849200297683 73338332776378273800446525)
  ·
    refine ⟨27501874791141852675167447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73338332776378273800446525 27501874791141852675167447)
    ·
      refine ⟨41252812186712779012751171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27501874791141852675167447 41252812186712779012751171)
      ·
        refine ⟨61879218280069168519126757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41252812186712779012751171 61879218280069168519126757)
        ·
          refine ⟨11602353427512969097336267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61879218280069168519126757 11602353427512969097336267)
          ·
            refine ⟨17403530141269453646004401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602353427512969097336267 17403530141269453646004401)
            ·
              refine ⟨13052647605952090234503301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17403530141269453646004401 13052647605952090234503301)
              ·
                refine ⟨2447371426116016918969369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13052647605952090234503301 2447371426116016918969369)
                ·
                  refine ⟨1835528569587012689227027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2447371426116016918969369 1835528569587012689227027)
                  ·
                    refine ⟨2753292854380519033840541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835528569587012689227027 2753292854380519033840541)
                    ·
                      refine ⟨1032484820392694637690203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2753292854380519033840541 1032484820392694637690203)
                      ·
                        rfl

theorem cell23_2010757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_2010757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010757 prefixEnd_2010757 := by exact prefixLift 2010757
  have htrace : WordTrace (prefixWord ++ tailWord_2010757) baseStart_2010757 baseEnd_2010757 := by
    simpa [prefixWord, tailWord_2010757, baseEnd_2010757] using wordTrace_append hprefix tailTrace_2010757
  have hstable : (prefixWord ++ tailWord_2010757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010757).length < 2 ^ (prefixWord ++ tailWord_2010757).sum := by decide
  have hdescent : baseEnd_2010757 < baseStart_2010757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010763 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_2010763 : Nat := 118140960795 + 2010763 * 2 ^ 59
def prefixEnd_2010763 : Nat := 4983230072969 + 3 ^ 40 * 2010763 * 2
def baseEnd_2010763 : Nat := 1032487901276621614215175

theorem tailTrace_2010763 : CollatzResearch.WordTrace tailWord_2010763 prefixEnd_2010763 1032487901276621614215175 := by
  unfold tailWord_2010763
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338551614356536825164943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48892367742904357883443295 73338551614356536825164943)
  ·
    refine ⟨110007827421534805237747415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73338551614356536825164943 110007827421534805237747415)
    ·
      refine ⟨165011741132302207856621123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110007827421534805237747415 165011741132302207856621123)
      ·
        refine ⟨247517611698453311784931685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165011741132302207856621123 247517611698453311784931685)
        ·
          refine ⟨46409552193459995959674691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247517611698453311784931685 46409552193459995959674691)
          ·
            refine ⟨69614328290189993939512037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46409552193459995959674691 69614328290189993939512037)
            ·
              refine ⟨13052686554410623863658507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69614328290189993939512037 13052686554410623863658507)
              ·
                refine ⟨19579029831615935795487761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13052686554410623863658507 19579029831615935795487761)
                ·
                  refine ⟨14684272373711951846615821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19579029831615935795487761 14684272373711951846615821)
                  ·
                    refine ⟨5506602140141981942480933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14684272373711951846615821 5506602140141981942480933)
                    ·
                      refine ⟨1032487901276621614215175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5506602140141981942480933 1032487901276621614215175)
                      ·
                        rfl

theorem cell23_2010763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_2010763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010763 prefixEnd_2010763 := by exact prefixLift 2010763
  have htrace : WordTrace (prefixWord ++ tailWord_2010763) baseStart_2010763 baseEnd_2010763 := by
    simpa [prefixWord, tailWord_2010763, baseEnd_2010763] using wordTrace_append hprefix tailTrace_2010763
  have hstable : (prefixWord ++ tailWord_2010763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010763).length < 2 ^ (prefixWord ++ tailWord_2010763).sum := by decide
  have hdescent : baseEnd_2010763 < baseStart_2010763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010773 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2010773 : Nat := 118140960795 + 2010773 * 2 ^ 59
def prefixEnd_2010773 : Nat := 4983230072969 + 3 ^ 40 * 2010773 * 2
def baseEnd_2010773 : Nat := 344164345361055525030043

theorem tailTrace_2010773 : CollatzResearch.WordTrace tailWord_2010773 prefixEnd_2010773 344164345361055525030043 := by
  unfold tailWord_2010773
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338916344320308533028973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48892610896213539022019315 73338916344320308533028973)
  ·
    refine ⟨27502093629120115699885865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73338916344320308533028973 27502093629120115699885865)
    ·
      refine ⟨20626570221840086774914399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27502093629120115699885865 20626570221840086774914399)
      ·
        refine ⟨30939855332760130162371599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20626570221840086774914399 30939855332760130162371599)
        ·
          refine ⟨46409782999140195243557399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30939855332760130162371599 46409782999140195243557399)
          ·
            refine ⟨69614674498710292865336099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46409782999140195243557399 69614674498710292865336099)
            ·
              refine ⟨104422011748065439298004149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69614674498710292865336099 104422011748065439298004149)
              ·
                refine ⟨9789563601381134934187889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104422011748065439298004149 9789563601381134934187889)
                ·
                  refine ⟨7342172701035851200640917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9789563601381134934187889 7342172701035851200640917)
                  ·
                    refine ⟨344164345361055525030043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7342172701035851200640917 344164345361055525030043)
                    ·
                      rfl

theorem cell23_2010773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2010773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010773 prefixEnd_2010773 := by exact prefixLift 2010773
  have htrace : WordTrace (prefixWord ++ tailWord_2010773) baseStart_2010773 baseEnd_2010773 := by
    simpa [prefixWord, tailWord_2010773, baseEnd_2010773] using wordTrace_append hprefix tailTrace_2010773
  have hstable : (prefixWord ++ tailWord_2010773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010773).length < 2 ^ (prefixWord ++ tailWord_2010773).sum := by decide
  have hdescent : baseEnd_2010773 < baseStart_2010773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010784 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2]
def baseStart_2010784 : Nat := 118140960795 + 2010784 * 2 ^ 59
def prefixEnd_2010784 : Nat := 4983230072969 + 3 ^ 40 * 2010784 * 2
def baseEnd_2010784 : Nat := 1032498684370366032052579

theorem tailTrace_2010784 : CollatzResearch.WordTrace tailWord_2010784 prefixEnd_2010784 1032498684370366032052579 := by
  unfold tailWord_2010784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669658773640228705839703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48892878364853638274452937 36669658773640228705839703)
  ·
    refine ⟨55004488160460343058759555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36669658773640228705839703 55004488160460343058759555)
    ·
      refine ⟨82506732240690514588139333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55004488160460343058759555 82506732240690514588139333)
      ·
        refine ⟨15470012295129471485276125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82506732240690514588139333 15470012295129471485276125)
        ·
          refine ⟨5801254610673551806978547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15470012295129471485276125 5801254610673551806978547)
          ·
            refine ⟨8701881916010327710467821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801254610673551806978547 8701881916010327710467821)
            ·
              refine ⟨3263205718503872891425433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8701881916010327710467821 3263205718503872891425433)
              ·
                refine ⟨2447404288877904668569075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263205718503872891425433 2447404288877904668569075)
                ·
                  refine ⟨3671106433316857002853613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447404288877904668569075 3671106433316857002853613)
                  ·
                    refine ⟨1376664912493821376070105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671106433316857002853613 1376664912493821376070105)
                    ·
                      refine ⟨1032498684370366032052579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376664912493821376070105 1032498684370366032052579)
                      ·
                        rfl

theorem cell23_2010784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_2010784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010784 prefixEnd_2010784 := by exact prefixLift 2010784
  have htrace : WordTrace (prefixWord ++ tailWord_2010784) baseStart_2010784 baseEnd_2010784 := by
    simpa [prefixWord, tailWord_2010784, baseEnd_2010784] using wordTrace_append hprefix tailTrace_2010784
  have hstable : (prefixWord ++ tailWord_2010784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010784).length < 2 ^ (prefixWord ++ tailWord_2010784).sum := by decide
  have hdescent : baseEnd_2010784 < baseStart_2010784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010820 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 7]
def baseStart_2010820 : Nat := 118140960795 + 2010820 * 2 ^ 59
def prefixEnd_2010820 : Nat := 4983230072969 + 3 ^ 40 * 2010820 * 2
def baseEnd_2010820 : Nat := 114724129963769765689157

theorem tailTrace_2010820 : CollatzResearch.WordTrace tailWord_2010820 prefixEnd_2010820 114724129963769765689157 := by
  unfold tailWord_2010820
  simp only [CollatzResearch.WordTrace]
  refine ⟨36670315287575017779994957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48893753716766690373326609 36670315287575017779994957)
  ·
    refine ⟨13751368232840631667498109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36670315287575017779994957 13751368232840631667498109)
    ·
      refine ⟨5156763087315236875311791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13751368232840631667498109 5156763087315236875311791)
      ·
        refine ⟨7735144630972855312967687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156763087315236875311791 7735144630972855312967687)
        ·
          refine ⟨11602716946459282969451531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735144630972855312967687 11602716946459282969451531)
          ·
            refine ⟨17404075419688924454177297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602716946459282969451531 17404075419688924454177297)
            ·
              refine ⟨13053056564766693340632973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17404075419688924454177297 13053056564766693340632973)
              ·
                refine ⟨4894896211787510002737365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13053056564766693340632973 4894896211787510002737365)
                ·
                  refine ⟨114724129963769765689157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4894896211787510002737365 114724129963769765689157)
                  ·
                    rfl

theorem cell23_2010820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_2010820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010820 prefixEnd_2010820 := by exact prefixLift 2010820
  have htrace : WordTrace (prefixWord ++ tailWord_2010820) baseStart_2010820 baseEnd_2010820 := by
    simpa [prefixWord, tailWord_2010820, baseEnd_2010820] using wordTrace_append hprefix tailTrace_2010820
  have hstable : (prefixWord ++ tailWord_2010820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010820).length < 2 ^ (prefixWord ++ tailWord_2010820).sum := by decide
  have hdescent : baseEnd_2010820 < baseStart_2010820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010880 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_2010880 : Nat := 118140960795 + 2010880 * 2 ^ 59
def prefixEnd_2010880 : Nat := 4983230072969 + 3 ^ 40 * 2010880 * 2
def baseEnd_2010880 : Nat := 344182659504399218817379

theorem tailTrace_2010880 : CollatzResearch.WordTrace tailWord_2010880 prefixEnd_2010880 344182659504399218817379 := by
  unfold tailWord_2010880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36671409477466332903587047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48895212636621777204782729 36671409477466332903587047)
  ·
    refine ⟨55007114216199499355380571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36671409477466332903587047 55007114216199499355380571)
    ·
      refine ⟨82510671324299249033070857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55007114216199499355380571 82510671324299249033070857)
      ·
        refine ⟨61883003493224436774803143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82510671324299249033070857 61883003493224436774803143)
        ·
          refine ⟨92824505239836655162204715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61883003493224436774803143 92824505239836655162204715)
          ·
            refine ⟨139236757859754982743307073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92824505239836655162204715 139236757859754982743307073)
            ·
              refine ⟨104427568394816237057480305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139236757859754982743307073 104427568394816237057480305)
              ·
                refine ⟨78320676296112177793110229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104427568394816237057480305 78320676296112177793110229)
                ·
                  refine ⟨1835640850690129167026021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78320676296112177793110229 1835640850690129167026021)
                  ·
                    refine ⟨344182659504399218817379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835640850690129167026021 344182659504399218817379)
                    ·
                      rfl

theorem cell23_2010880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_2010880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010880 prefixEnd_2010880 := by exact prefixLift 2010880
  have htrace : WordTrace (prefixWord ++ tailWord_2010880) baseStart_2010880 baseEnd_2010880 := by
    simpa [prefixWord, tailWord_2010880, baseEnd_2010880] using wordTrace_append hprefix tailTrace_2010880
  have hstable : (prefixWord ++ tailWord_2010880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010880).length < 2 ^ (prefixWord ++ tailWord_2010880).sum := by decide
  have hdescent : baseEnd_2010880 < baseStart_2010880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010931 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 3, 4]
def baseStart_2010931 : Nat := 118140960795 + 2010931 * 2 ^ 59
def prefixEnd_2010931 : Nat := 4983230072969 + 3 ^ 40 * 2010931 * 2
def baseEnd_2010931 : Nat := 344191388675525652304801

theorem tailTrace_2010931 : CollatzResearch.WordTrace tailWord_2010931 prefixEnd_2010931 344191388675525652304801 := by
  unfold tailWord_2010931
  simp only [CollatzResearch.WordTrace]
  refine ⟨73344679077747901517280647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48896452718498601011520431 73344679077747901517280647)
  ·
    refine ⟨110017018616621852275920971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73344679077747901517280647 110017018616621852275920971)
    ·
      refine ⟨165025527924932778413881457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110017018616621852275920971 165025527924932778413881457)
      ·
        refine ⟨123769145943699583810411093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165025527924932778413881457 123769145943699583810411093)
        ·
          refine ⟨1450419679027729497778255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 123769145943699583810411093 1450419679027729497778255)
          ·
            refine ⟨2175629518541594246667383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450419679027729497778255 2175629518541594246667383)
            ·
              refine ⟨3263444277812391370001075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175629518541594246667383 3263444277812391370001075)
              ·
                refine ⟨4895166416718587055001613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263444277812391370001075 4895166416718587055001613)
                ·
                  refine ⟨1835687406269470145625605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4895166416718587055001613 1835687406269470145625605)
                  ·
                    refine ⟨344191388675525652304801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835687406269470145625605 344191388675525652304801)
                    ·
                      rfl

theorem cell23_2010931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 4].length) (baseStart_2010931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010931 prefixEnd_2010931 := by exact prefixLift 2010931
  have htrace : WordTrace (prefixWord ++ tailWord_2010931) baseStart_2010931 baseEnd_2010931 := by
    simpa [prefixWord, tailWord_2010931, baseEnd_2010931] using wordTrace_append hprefix tailTrace_2010931
  have hstable : (prefixWord ++ tailWord_2010931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010931).length < 2 ^ (prefixWord ++ tailWord_2010931).sum := by decide
  have hdescent : baseEnd_2010931 < baseStart_2010931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010988 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 1, 1, 3]
def baseStart_2010988 : Nat := 118140960795 + 2010988 * 2 ^ 59
def prefixEnd_2010988 : Nat := 4983230072969 + 3 ^ 40 * 2010988 * 2
def baseEnd_2010988 : Nat := 1032603434423883233901641

theorem tailTrace_2010988 : CollatzResearch.WordTrace tailWord_2010988 prefixEnd_2010988 1032603434423883233901641 := by
  unfold tailWord_2010988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36673379019270700126052809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48897838692360933501403745 36673379019270700126052809)
  ·
    refine ⟨27505034264453025094539607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36673379019270700126052809 27505034264453025094539607)
    ·
      refine ⟨41257551396679537641809411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27505034264453025094539607 41257551396679537641809411)
      ·
        refine ⟨61886327095019306462714117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41257551396679537641809411 61886327095019306462714117)
        ·
          refine ⟨11603686330316119961758897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61886327095019306462714117 11603686330316119961758897)
          ·
            refine ⟨8702764747737089971319173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11603686330316119961758897 8702764747737089971319173)
            ·
              refine ⟨1631768390200704369622345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8702764747737089971319173 1631768390200704369622345)
              ·
                refine ⟨1223826292650528277216759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631768390200704369622345 1223826292650528277216759)
                ·
                  refine ⟨1835739438975792415825139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223826292650528277216759 1835739438975792415825139)
                  ·
                    refine ⟨2753609158463688623737709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835739438975792415825139 2753609158463688623737709)
                    ·
                      refine ⟨1032603434423883233901641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2753609158463688623737709 1032603434423883233901641)
                      ·
                        rfl

theorem cell23_2010988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_2010988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010988 prefixEnd_2010988 := by exact prefixLift 2010988
  have htrace : WordTrace (prefixWord ++ tailWord_2010988) baseStart_2010988 baseEnd_2010988 := by
    simpa [prefixWord, tailWord_2010988, baseEnd_2010988] using wordTrace_append hprefix tailTrace_2010988
  have hstable : (prefixWord ++ tailWord_2010988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010988).length < 2 ^ (prefixWord ++ tailWord_2010988).sum := by decide
  have hdescent : baseEnd_2010988 < baseStart_2010988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2010997 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2010997 : Nat := 118140960795 + 2010997 * 2 ^ 59
def prefixEnd_2010997 : Nat := 4983230072969 + 3 ^ 40 * 2010997 * 2
def baseEnd_2010997 : Nat := 1032608055749773698689099

theorem tailTrace_2010997 : CollatzResearch.WordTrace tailWord_2010997 prefixEnd_2010997 1032608055749773698689099 := by
  unfold tailWord_2010997
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347086295508794789183245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48898057530339196526122163 73347086295508794789183245)
  ·
    refine ⟨27505157360815798045943717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73347086295508794789183245 27505157360815798045943717)
    ·
      refine ⟨5157217005152962133614447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27505157360815798045943717 5157217005152962133614447)
      ·
        refine ⟨7735825507729443200421671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157217005152962133614447 7735825507729443200421671)
        ·
          refine ⟨11603738261594164800632507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735825507729443200421671 11603738261594164800632507)
          ·
            refine ⟨17405607392391247200948761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603738261594164800632507 17405607392391247200948761)
            ·
              refine ⟨13054205544293435400711571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17405607392391247200948761 13054205544293435400711571)
              ·
                refine ⟨19581308316440153101067357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13054205544293435400711571 19581308316440153101067357)
                ·
                  refine ⟨7342990618665057412900259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19581308316440153101067357 7342990618665057412900259)
                  ·
                    refine ⟨11014485927997586119350389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342990618665057412900259 11014485927997586119350389)
                    ·
                      refine ⟨1032608055749773698689099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11014485927997586119350389 1032608055749773698689099)
                      ·
                        rfl

theorem cell23_2010997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2010997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2010997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2010997 prefixEnd_2010997 := by exact prefixLift 2010997
  have htrace : WordTrace (prefixWord ++ tailWord_2010997) baseStart_2010997 baseEnd_2010997 := by
    simpa [prefixWord, tailWord_2010997, baseEnd_2010997] using wordTrace_append hprefix tailTrace_2010997
  have hstable : (prefixWord ++ tailWord_2010997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2010997).length < 2 ^ (prefixWord ++ tailWord_2010997).sum := by decide
  have hdescent : baseEnd_2010997 < baseStart_2010997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2010997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011011 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 3, 2, 2]
def baseStart_2011011 : Nat := 118140960795 + 2011011 * 2 ^ 59
def prefixEnd_2011011 : Nat := 4983230072969 + 3 ^ 40 * 2011011 * 2
def baseEnd_2011011 : Nat := 1032615244478936643914035

theorem tailTrace_2011011 : CollatzResearch.WordTrace tailWord_2011011 prefixEnd_2011011 1032615244478936643914035 := by
  unfold tailWord_2011011
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347596917458075180192887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48898397944972050120128591 73347596917458075180192887)
  ·
    refine ⟨110021395376187112770289331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73347596917458075180192887 110021395376187112770289331)
    ·
      refine ⟨165032093064280669155433997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110021395376187112770289331 165032093064280669155433997)
      ·
        refine ⟨61887034899105250933287749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165032093064280669155433997 61887034899105250933287749)
        ·
          refine ⟨11603819043582234549991453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61887034899105250933287749 11603819043582234549991453)
          ·
            refine ⟨4351432141343337956246795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11603819043582234549991453 4351432141343337956246795)
            ·
              refine ⟨6527148212015006934370193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351432141343337956246795 6527148212015006934370193)
              ·
                refine ⟨4895361159011255200777645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527148212015006934370193 4895361159011255200777645)
                ·
                  refine ⟨1835760434629220700291617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4895361159011255200777645 1835760434629220700291617)
                  ·
                    refine ⟨1376820325971915525218713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1835760434629220700291617 1376820325971915525218713)
                    ·
                      refine ⟨1032615244478936643914035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376820325971915525218713 1032615244478936643914035)
                      ·
                        rfl

theorem cell23_2011011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_2011011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011011 prefixEnd_2011011 := by exact prefixLift 2011011
  have htrace : WordTrace (prefixWord ++ tailWord_2011011) baseStart_2011011 baseEnd_2011011 := by
    simpa [prefixWord, tailWord_2011011, baseEnd_2011011] using wordTrace_append hprefix tailTrace_2011011
  have hstable : (prefixWord ++ tailWord_2011011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011011).length < 2 ^ (prefixWord ++ tailWord_2011011).sum := by decide
  have hdescent : baseEnd_2011011 < baseStart_2011011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011017 : List Nat := [1, 2, 1, 1, 5, 1, 5, 7]
def baseStart_2011017 : Nat := 118140960795 + 2011017 * 2 ^ 59
def prefixEnd_2011017 : Nat := 4983230072969 + 3 ^ 40 * 2011017 * 2
def baseEnd_2011017 : Nat := 38245123161587541497741

theorem tailTrace_2011017 : CollatzResearch.WordTrace tailWord_2011017 prefixEnd_2011017 38245123161587541497741 := by
  unfold tailWord_2011017
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347815755436338204911305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48898543836957558803274203 73347815755436338204911305)
  ·
    refine ⟨55010861816577253653683479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73347815755436338204911305 55010861816577253653683479)
    ·
      refine ⟨82516292724865880480525219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55010861816577253653683479 82516292724865880480525219)
      ·
        refine ⟨123774439087298820720787829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82516292724865880480525219 123774439087298820720787829)
        ·
          refine ⟨11603853664434264442573859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123774439087298820720787829 11603853664434264442573859)
          ·
            refine ⟨17405780496651396663860789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603853664434264442573859 17405780496651396663860789)
            ·
              refine ⟨1631791921561068437236949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17405780496651396663860789 1631791921561068437236949)
              ·
                refine ⟨38245123161587541497741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1631791921561068437236949 38245123161587541497741)
                ·
                  rfl

theorem cell23_2011017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 7].length) (baseStart_2011017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011017 prefixEnd_2011017 := by exact prefixLift 2011017
  have htrace : WordTrace (prefixWord ++ tailWord_2011017) baseStart_2011017 baseEnd_2011017 := by
    simpa [prefixWord, tailWord_2011017, baseEnd_2011017] using wordTrace_append hprefix tailTrace_2011017
  have hstable : (prefixWord ++ tailWord_2011017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011017).length < 2 ^ (prefixWord ++ tailWord_2011017).sum := by decide
  have hdescent : baseEnd_2011017 < baseStart_2011017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011028 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2011028 : Nat := 118140960795 + 2011028 * 2 ^ 59
def prefixEnd_2011028 : Nat := 4983230072969 + 3 ^ 40 * 2011028 * 2
def baseEnd_2011028 : Nat := 1032623973650063077401457

theorem tailTrace_2011028 : CollatzResearch.WordTrace tailWord_2011028 prefixEnd_2011028 1032623973650063077401457 := by
  unfold tailWord_2011028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36674108479198243541780869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48898811305597658055707825 36674108479198243541780869)
  ·
    refine ⟨6876395339849670664083913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36674108479198243541780869 6876395339849670664083913)
    ·
      refine ⟨5157296504887252998062935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6876395339849670664083913 5157296504887252998062935)
      ·
        refine ⟨7735944757330879497094403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157296504887252998062935 7735944757330879497094403)
        ·
          refine ⟨11603917135996319245641605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735944757330879497094403 11603917135996319245641605)
          ·
            refine ⟨2175734462999309858557801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11603917135996319245641605 2175734462999309858557801)
            ·
              refine ⟨1631800847249482393918351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175734462999309858557801 1631800847249482393918351)
              ·
                refine ⟨2447701270874223590877527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631800847249482393918351 2447701270874223590877527)
                ·
                  refine ⟨3671551906311335386316291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447701270874223590877527 3671551906311335386316291)
                  ·
                    refine ⟨5507327859467003079474437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3671551906311335386316291 5507327859467003079474437)
                    ·
                      refine ⟨1032623973650063077401457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5507327859467003079474437 1032623973650063077401457)
                      ·
                        rfl

theorem cell23_2011028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2011028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011028 prefixEnd_2011028 := by exact prefixLift 2011028
  have htrace : WordTrace (prefixWord ++ tailWord_2011028) baseStart_2011028 baseEnd_2011028 := by
    simpa [prefixWord, tailWord_2011028, baseEnd_2011028] using wordTrace_append hprefix tailTrace_2011028
  have hstable : (prefixWord ++ tailWord_2011028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011028).length < 2 ^ (prefixWord ++ tailWord_2011028).sum := by decide
  have hdescent : baseEnd_2011028 < baseStart_2011028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011031 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_2011031 : Nat := 118140960795 + 2011031 * 2 ^ 59
def prefixEnd_2011031 : Nat := 4983230072969 + 3 ^ 40 * 2011031 * 2
def baseEnd_2011031 : Nat := 1032625514092026565663943

theorem tailTrace_2011031 : CollatzResearch.WordTrace tailWord_2011031 prefixEnd_2011031 1032625514092026565663943 := by
  unfold tailWord_2011031
  simp only [CollatzResearch.WordTrace]
  refine ⟨73348326377385618595920947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48898884251590412397280631 73348326377385618595920947)
  ·
    refine ⟨110022489566078427893881421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73348326377385618595920947 110022489566078427893881421)
    ·
      refine ⟨41258433587279410460205533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110022489566078427893881421 41258433587279410460205533)
      ·
        refine ⟨15471912595229778922577075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41258433587279410460205533 15471912595229778922577075)
        ·
          refine ⟨23207868892844668383865613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471912595229778922577075 23207868892844668383865613)
          ·
            refine ⟨8702950834816750643949605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23207868892844668383865613 8702950834816750643949605)
            ·
              refine ⟨1631803281528140745740551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8702950834816750643949605 1631803281528140745740551)
              ·
                refine ⟨2447704922292211118610827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631803281528140745740551 2447704922292211118610827)
                ·
                  refine ⟨3671557383438316677916241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447704922292211118610827 3671557383438316677916241)
                  ·
                    refine ⟨2753668037578737508437181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3671557383438316677916241 2753668037578737508437181)
                    ·
                      refine ⟨1032625514092026565663943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2753668037578737508437181 1032625514092026565663943)
                      ·
                        rfl

theorem cell23_2011031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_2011031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011031 prefixEnd_2011031 := by exact prefixLift 2011031
  have htrace : WordTrace (prefixWord ++ tailWord_2011031) baseStart_2011031 baseEnd_2011031 := by
    simpa [prefixWord, tailWord_2011031, baseEnd_2011031] using wordTrace_append hprefix tailTrace_2011031
  have hstable : (prefixWord ++ tailWord_2011031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011031).length < 2 ^ (prefixWord ++ tailWord_2011031).sum := by decide
  have hdescent : baseEnd_2011031 < baseStart_2011031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011038 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2011038 : Nat := 118140960795 + 2011038 * 2 ^ 59
def prefixEnd_2011038 : Nat := 4983230072969 + 3 ^ 40 * 2011038 * 2
def baseEnd_2011038 : Nat := 344209702818869346092137

theorem tailTrace_2011038 : CollatzResearch.WordTrace tailWord_2011038 prefixEnd_2011038 344209702818869346092137 := by
  unfold tailWord_2011038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168572711045032348928221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48899054458906839194283845 9168572711045032348928221)
  ·
    refine ⟨3438214766641887130848083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9168572711045032348928221 3438214766641887130848083)
    ·
      refine ⟨5157322149962830696272125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438214766641887130848083 5157322149962830696272125)
      ·
        refine ⟨1933995806236061511102047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5157322149962830696272125 1933995806236061511102047)
        ·
          refine ⟨2900993709354092266653071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933995806236061511102047 2900993709354092266653071)
          ·
            refine ⟨4351490564031138399979607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900993709354092266653071 4351490564031138399979607)
            ·
              refine ⟨6527235846046707599969411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351490564031138399979607 6527235846046707599969411)
              ·
                refine ⟨9790853769070061399954117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527235846046707599969411 9790853769070061399954117)
                ·
                  refine ⟨1835785081700636512491397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9790853769070061399954117 1835785081700636512491397)
                  ·
                    refine ⟨344209702818869346092137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835785081700636512491397 344209702818869346092137)
                    ·
                      rfl

theorem cell23_2011038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2011038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011038 prefixEnd_2011038 := by exact prefixLift 2011038
  have htrace : WordTrace (prefixWord ++ tailWord_2011038) baseStart_2011038 baseEnd_2011038 := by
    simpa [prefixWord, tailWord_2011038, baseEnd_2011038] using wordTrace_append hprefix tailTrace_2011038
  have hstable : (prefixWord ++ tailWord_2011038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011038).length < 2 ^ (prefixWord ++ tailWord_2011038).sum := by decide
  have hdescent : baseEnd_2011038 < baseStart_2011038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011061 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2011061 : Nat := 118140960795 + 2011061 * 2 ^ 59
def prefixEnd_2011061 : Nat := 4983230072969 + 3 ^ 40 * 2011061 * 2
def baseEnd_2011061 : Nat := 1032640918511661448288805

theorem tailTrace_2011061 : CollatzResearch.WordTrace tailWord_2011061 prefixEnd_2011061 1032640918511661448288805 := by
  unfold tailWord_2011061
  simp only [CollatzResearch.WordTrace]
  refine ⟨73349420567276933719513037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48899613711517955813008691 73349420567276933719513037)
  ·
    refine ⟨27506032712728850144817389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73349420567276933719513037 27506032712728850144817389)
    ·
      refine ⟨10314762267273318804306521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27506032712728850144817389 10314762267273318804306521)
      ·
        refine ⟨7736071700454989103229891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10314762267273318804306521 7736071700454989103229891)
        ·
          refine ⟨11604107550682483654844837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736071700454989103229891 11604107550682483654844837)
          ·
            refine ⟨2175770165752965685283407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11604107550682483654844837 2175770165752965685283407)
            ·
              refine ⟨3263655248629448527925111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175770165752965685283407 3263655248629448527925111)
              ·
                refine ⟨4895482872944172791887667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263655248629448527925111 4895482872944172791887667)
                ·
                  refine ⟨7343224309416259187831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895482872944172791887667 7343224309416259187831501)
                  ·
                    refine ⟨2753709116031097195436813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7343224309416259187831501 2753709116031097195436813)
                    ·
                      refine ⟨1032640918511661448288805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2753709116031097195436813 1032640918511661448288805)
                      ·
                        rfl

theorem cell23_2011061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2011061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011061 prefixEnd_2011061 := by exact prefixLift 2011061
  have htrace : WordTrace (prefixWord ++ tailWord_2011061) baseStart_2011061 baseEnd_2011061 := by
    simpa [prefixWord, tailWord_2011061, baseEnd_2011061] using wordTrace_append hprefix tailTrace_2011061
  have hstable : (prefixWord ++ tailWord_2011061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011061).length < 2 ^ (prefixWord ++ tailWord_2011061).sum := by decide
  have hdescent : baseEnd_2011061 < baseStart_2011061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011068 : List Nat := [2, 2, 2, 5, 2, 1, 2, 7]
def baseStart_2011068 : Nat := 118140960795 + 2011068 * 2 ^ 59
def prefixEnd_2011068 : Nat := 4983230072969 + 3 ^ 40 * 2011068 * 2
def baseEnd_2011068 : Nat := 38246093069490478551899

theorem tailTrace_2011068 : CollatzResearch.WordTrace tailWord_2011068 prefixEnd_2011068 38246093069490478551899 := by
  unfold tailWord_2011068
  simp only [CollatzResearch.WordTrace]
  refine ⟨36674837939125786957508929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48899783918834382610011905 36674837939125786957508929)
  ·
    refine ⟨27506128454344340218131697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36674837939125786957508929 27506128454344340218131697)
    ·
      refine ⟨20629596340758255163598773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27506128454344340218131697 20629596340758255163598773)
      ·
        refine ⟨1934024656946086421587385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20629596340758255163598773 1934024656946086421587385)
        ·
          refine ⟨1450518492709564816190539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934024656946086421587385 1450518492709564816190539)
          ·
            refine ⟨2175777739064347224285809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450518492709564816190539 2175777739064347224285809)
            ·
              refine ⟨1631833304298260418214357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175777739064347224285809 1631833304298260418214357)
              ·
                refine ⟨38246093069490478551899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1631833304298260418214357 38246093069490478551899)
                ·
                  rfl

theorem cell23_2011068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 7].length) (baseStart_2011068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011068 prefixEnd_2011068 := by exact prefixLift 2011068
  have htrace : WordTrace (prefixWord ++ tailWord_2011068) baseStart_2011068 baseEnd_2011068 := by
    simpa [prefixWord, tailWord_2011068, baseEnd_2011068] using wordTrace_append hprefix tailTrace_2011068
  have hstable : (prefixWord ++ tailWord_2011068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011068).length < 2 ^ (prefixWord ++ tailWord_2011068).sum := by decide
  have hdescent : baseEnd_2011068 < baseStart_2011068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011071 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 1, 3, 2]
def baseStart_2011071 : Nat := 118140960795 + 2011071 * 2 ^ 59
def prefixEnd_2011071 : Nat := 4983230072969 + 3 ^ 40 * 2011071 * 2
def baseEnd_2011071 : Nat := 1032646053318206409163759

theorem tailTrace_2011071 : CollatzResearch.WordTrace tailWord_2011071 prefixEnd_2011071 1032646053318206409163759 := by
  unfold tailWord_2011071
  simp only [CollatzResearch.WordTrace]
  refine ⟨73349785297240705427377067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48899856864827136951584711 73349785297240705427377067)
  ·
    refine ⟨110024677945861058141065601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73349785297240705427377067 110024677945861058141065601)
    ·
      refine ⟨82518508459395793605799201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110024677945861058141065601 82518508459395793605799201)
      ·
        refine ⟨61888881344546845204349401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82518508459395793605799201 61888881344546845204349401)
        ·
          refine ⟨46416661008410133903262051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61888881344546845204349401 46416661008410133903262051)
          ·
            refine ⟨69624991512615200854893077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46416661008410133903262051 69624991512615200854893077)
            ·
              refine ⟨3263671477153837540073113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69624991512615200854893077 3263671477153837540073113)
              ·
                refine ⟨2447753607865378155054835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263671477153837540073113 2447753607865378155054835)
                ·
                  refine ⟨3671630411798067232582253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447753607865378155054835 3671630411798067232582253)
                  ·
                    refine ⟨1376861404424275212218345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671630411798067232582253 1376861404424275212218345)
                    ·
                      refine ⟨1032646053318206409163759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376861404424275212218345 1032646053318206409163759)
                      ·
                        rfl

theorem cell23_2011071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_2011071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011071 prefixEnd_2011071 := by exact prefixLift 2011071
  have htrace : WordTrace (prefixWord ++ tailWord_2011071) baseStart_2011071 baseEnd_2011071 := by
    simpa [prefixWord, tailWord_2011071, baseEnd_2011071] using wordTrace_append hprefix tailTrace_2011071
  have hstable : (prefixWord ++ tailWord_2011071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011071).length < 2 ^ (prefixWord ++ tailWord_2011071).sum := by decide
  have hdescent : baseEnd_2011071 < baseStart_2011071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011087 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_2011087 : Nat := 118140960795 + 2011087 * 2 ^ 59
def prefixEnd_2011087 : Nat := 4983230072969 + 3 ^ 40 * 2011087 * 2
def baseEnd_2011087 : Nat := 1032654269008678346563685

theorem tailTrace_2011087 : CollatzResearch.WordTrace tailWord_2011087 prefixEnd_2011087 1032654269008678346563685 := by
  unfold tailWord_2011087
  simp only [CollatzResearch.WordTrace]
  refine ⟨73350368865182740159959515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48900245910121826773306343 73350368865182740159959515)
  ·
    refine ⟨110025553297774110239939273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73350368865182740159959515 110025553297774110239939273)
    ·
      refine ⟨82519164973330582679954455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110025553297774110239939273 82519164973330582679954455)
      ·
        refine ⟨123778747459995874019931683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82519164973330582679954455 123778747459995874019931683)
        ·
          refine ⟨185668121189993811029897525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123778747459995874019931683 185668121189993811029897525)
          ·
            refine ⟨17406386361561919784052893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185668121189993811029897525 17406386361561919784052893)
            ·
              refine ⟨6527394885585719919019835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17406386361561919784052893 6527394885585719919019835)
              ·
                refine ⟨9791092328378579878529753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527394885585719919019835 9791092328378579878529753)
                ·
                  refine ⟨7343319246283934908897315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9791092328378579878529753 7343319246283934908897315)
                  ·
                    refine ⟨11014978869425902363345973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7343319246283934908897315 11014978869425902363345973)
                    ·
                      refine ⟨1032654269008678346563685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11014978869425902363345973 1032654269008678346563685)
                      ·
                        rfl

theorem cell23_2011087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_2011087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011087 prefixEnd_2011087 := by exact prefixLift 2011087
  have htrace : WordTrace (prefixWord ++ tailWord_2011087) baseStart_2011087 baseEnd_2011087 := by
    simpa [prefixWord, tailWord_2011087, baseEnd_2011087] using wordTrace_append hprefix tailTrace_2011087
  have hstable : (prefixWord ++ tailWord_2011087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011087).length < 2 ^ (prefixWord ++ tailWord_2011087).sum := by decide
  have hdescent : baseEnd_2011087 < baseStart_2011087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011147 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_2011147 : Nat := 118140960795 + 2011147 * 2 ^ 59
def prefixEnd_2011147 : Nat := 4983230072969 + 3 ^ 40 * 2011147 * 2
def baseEnd_2011147 : Nat := 1032685077847948111813409

theorem tailTrace_2011147 : CollatzResearch.WordTrace tailWord_2011147 prefixEnd_2011147 1032685077847948111813409 := by
  unfold tailWord_2011147
  simp only [CollatzResearch.WordTrace]
  refine ⟨73352557244965370407143695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48901704829976913604762463 73352557244965370407143695)
  ·
    refine ⟨110028835867448055610715543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73352557244965370407143695 110028835867448055610715543)
    ·
      refine ⟨165043253801172083416073315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110028835867448055610715543 165043253801172083416073315)
      ·
        refine ⟨247564880701758125124109973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165043253801172083416073315 247564880701758125124109973)
        ·
          refine ⟨11604603782894912115192655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247564880701758125124109973 11604603782894912115192655)
          ·
            refine ⟨17406905674342368172788983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604603782894912115192655 17406905674342368172788983)
            ·
              refine ⟨26110358511513552259183475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406905674342368172788983 26110358511513552259183475)
              ·
                refine ⟨39165537767270328388775213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26110358511513552259183475 39165537767270328388775213)
                ·
                  refine ⟨14687076662726373145790705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39165537767270328388775213 14687076662726373145790705)
                  ·
                    refine ⟨11015307497044779859343029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14687076662726373145790705 11015307497044779859343029)
                    ·
                      refine ⟨1032685077847948111813409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11015307497044779859343029 1032685077847948111813409)
                      ·
                        rfl

theorem cell23_2011147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_2011147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011147 prefixEnd_2011147 := by exact prefixLift 2011147
  have htrace : WordTrace (prefixWord ++ tailWord_2011147) baseStart_2011147 baseEnd_2011147 := by
    simpa [prefixWord, tailWord_2011147, baseEnd_2011147] using wordTrace_append hprefix tailTrace_2011147
  have hstable : (prefixWord ++ tailWord_2011147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011147).length < 2 ^ (prefixWord ++ tailWord_2011147).sum := by decide
  have hdescent : baseEnd_2011147 < baseStart_2011147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011164 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2011164 : Nat := 118140960795 + 2011164 * 2 ^ 59
def prefixEnd_2011164 : Nat := 4983230072969 + 3 ^ 40 * 2011164 * 2
def baseEnd_2011164 : Nat := 1032693807019074545300831

theorem tailTrace_2011164 : CollatzResearch.WordTrace tailWord_2011164 prefixEnd_2011164 1032693807019074545300831 := by
  unfold tailWord_2011164
  simp only [CollatzResearch.WordTrace]
  refine ⟨36676588642951891155256273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48902118190602521540341697 36676588642951891155256273)
  ·
    refine ⟨27507441482213918366442205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36676588642951891155256273 27507441482213918366442205)
    ·
      refine ⟨10315290555830219387415827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27507441482213918366442205 10315290555830219387415827)
      ·
        refine ⟨15472935833745329081123741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315290555830219387415827 15472935833745329081123741)
        ·
          refine ⟨5802350937654498405421403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15472935833745329081123741 5802350937654498405421403)
          ·
            refine ⟨8703526406481747608132105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802350937654498405421403 8703526406481747608132105)
            ·
              refine ⟨6527644804861310706099079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8703526406481747608132105 6527644804861310706099079)
              ·
                refine ⟨9791467207291966059148619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527644804861310706099079 9791467207291966059148619)
                ·
                  refine ⟨14687200810937949088722929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791467207291966059148619 14687200810937949088722929)
                  ·
                    refine ⟨11015400608203461816542197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14687200810937949088722929 11015400608203461816542197)
                    ·
                      refine ⟨1032693807019074545300831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11015400608203461816542197 1032693807019074545300831)
                      ·
                        rfl

theorem cell23_2011164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2011164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011164 prefixEnd_2011164 := by exact prefixLift 2011164
  have htrace : WordTrace (prefixWord ++ tailWord_2011164) baseStart_2011164 baseEnd_2011164 := by
    simpa [prefixWord, tailWord_2011164, baseEnd_2011164] using wordTrace_append hprefix tailTrace_2011164
  have hstable : (prefixWord ++ tailWord_2011164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011164).length < 2 ^ (prefixWord ++ tailWord_2011164).sum := by decide
  have hdescent : baseEnd_2011164 < baseStart_2011164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011184 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_2011184 : Nat := 118140960795 + 2011184 * 2 ^ 59
def prefixEnd_2011184 : Nat := 4983230072969 + 3 ^ 40 * 2011184 * 2
def baseEnd_2011184 : Nat := 344234692210721489016913

theorem tailTrace_2011184 : CollatzResearch.WordTrace tailWord_2011184 prefixEnd_2011184 344234692210721489016913 := by
  unfold tailWord_2011184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36676953372915662863120303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48902604497220883817493737 36676953372915662863120303)
  ·
    refine ⟨55015430059373494294680455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36676953372915662863120303 55015430059373494294680455)
    ·
      refine ⟨82523145089060241442020683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55015430059373494294680455 82523145089060241442020683)
      ·
        refine ⟨123784717633590362163031025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82523145089060241442020683 123784717633590362163031025)
        ·
          refine ⟨92838538225192771622273269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123784717633590362163031025 92838538225192771622273269)
          ·
            refine ⟨8703612958611822339588119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92838538225192771622273269 8703612958611822339588119)
            ·
              refine ⟨13055419437917733509382179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703612958611822339588119 13055419437917733509382179)
              ·
                refine ⟨19583129156876600264073269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13055419437917733509382179 19583129156876600264073269)
                ·
                  refine ⟨1835918358457181274756869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19583129156876600264073269 1835918358457181274756869)
                  ·
                    refine ⟨344234692210721489016913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835918358457181274756869 344234692210721489016913)
                    ·
                      rfl

theorem cell23_2011184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_2011184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011184 prefixEnd_2011184 := by exact prefixLift 2011184
  have htrace : WordTrace (prefixWord ++ tailWord_2011184) baseStart_2011184 baseEnd_2011184 := by
    simpa [prefixWord, tailWord_2011184, baseEnd_2011184] using wordTrace_append hprefix tailTrace_2011184
  have hstable : (prefixWord ++ tailWord_2011184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011184).length < 2 ^ (prefixWord ++ tailWord_2011184).sum := by decide
  have hdescent : baseEnd_2011184 < baseStart_2011184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011214 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_2011214 : Nat := 118140960795 + 2011214 * 2 ^ 59
def prefixEnd_2011214 : Nat := 4983230072969 + 3 ^ 40 * 2011214 * 2
def baseEnd_2011214 : Nat := 114746609005755483297289

theorem tailTrace_2011214 : CollatzResearch.WordTrace tailWord_2011214 prefixEnd_2011214 114746609005755483297289 := by
  unfold tailWord_2011214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169375116965330106229087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48903333957148427233221797 9169375116965330106229087)
  ·
    refine ⟨13754062675447995159343631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9169375116965330106229087 13754062675447995159343631)
    ·
      refine ⟨20631094013171992739015447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13754062675447995159343631 20631094013171992739015447)
      ·
        refine ⟨30946641019757989108523171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20631094013171992739015447 30946641019757989108523171)
        ·
          refine ⟨46419961529636983662784757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30946641019757989108523171 46419961529636983662784757)
          ·
            refine ⟨4351871393403467218386071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46419961529636983662784757 4351871393403467218386071)
            ·
              refine ⟨6527807090105200827579107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351871393403467218386071 6527807090105200827579107)
              ·
                refine ⟨9791710635157801241368661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527807090105200827579107 9791710635157801241368661)
                ·
                  refine ⟨114746609005755483297289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9791710635157801241368661 114746609005755483297289)
                  ·
                    rfl

theorem cell23_2011214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_2011214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011214 prefixEnd_2011214 := by exact prefixLift 2011214
  have htrace : WordTrace (prefixWord ++ tailWord_2011214) baseStart_2011214 baseEnd_2011214 := by
    simpa [prefixWord, tailWord_2011214, baseEnd_2011214] using wordTrace_append hprefix tailTrace_2011214
  have hstable : (prefixWord ++ tailWord_2011214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011214).length < 2 ^ (prefixWord ++ tailWord_2011214).sum := by decide
  have hdescent : baseEnd_2011214 < baseStart_2011214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011218 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2011218 : Nat := 118140960795 + 2011218 * 2 ^ 59
def prefixEnd_2011218 : Nat := 4983230072969 + 3 ^ 40 * 2011218 * 2
def baseEnd_2011218 : Nat := 344240511658139111341861

theorem tailTrace_2011218 : CollatzResearch.WordTrace tailWord_2011218 prefixEnd_2011218 344240511658139111341861 := by
  unfold tailWord_2011218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18338786706927037383244577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48903431218472099688652205 18338786706927037383244577)
  ·
    refine ⟨13754090030195278037433433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18338786706927037383244577 13754090030195278037433433)
    ·
      refine ⟨10315567522646458528075075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13754090030195278037433433 10315567522646458528075075)
      ·
        refine ⟨15473351283969687792112613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315567522646458528075075 15473351283969687792112613)
        ·
          refine ⟨2901253365744316461021115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15473351283969687792112613 2901253365744316461021115)
          ·
            refine ⟨4351880048616474691531673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901253365744316461021115 4351880048616474691531673)
            ·
              refine ⟨3263910036462356018648755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4351880048616474691531673 3263910036462356018648755)
              ·
                refine ⟨4895865054693534027973133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3263910036462356018648755 4895865054693534027973133)
                ·
                  refine ⟨1835949395510075260489925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4895865054693534027973133 1835949395510075260489925)
                  ·
                    refine ⟨344240511658139111341861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835949395510075260489925 344240511658139111341861)
                    ·
                      rfl

theorem cell23_2011218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2011218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011218 prefixEnd_2011218 := by exact prefixLift 2011218
  have htrace : WordTrace (prefixWord ++ tailWord_2011218) baseStart_2011218 baseEnd_2011218 := by
    simpa [prefixWord, tailWord_2011218, baseEnd_2011218] using wordTrace_append hprefix tailTrace_2011218
  have hstable : (prefixWord ++ tailWord_2011218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011218).length < 2 ^ (prefixWord ++ tailWord_2011218).sum := by decide
  have hdescent : baseEnd_2011218 < baseStart_2011218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011241 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 3]
def baseStart_2011241 : Nat := 118140960795 + 2011241 * 2 ^ 59
def prefixEnd_2011241 : Nat := 4983230072969 + 3 ^ 40 * 2011241 * 2
def baseEnd_2011241 : Nat := 1032733345029470744037977

theorem tailTrace_2011241 : CollatzResearch.WordTrace tailWord_2011241 prefixEnd_2011241 1032733345029470744037977 := by
  unfold tailWord_2011241
  simp only [CollatzResearch.WordTrace]
  refine ⟨73355985706624824461065577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48903990471083216307377051 73355985706624824461065577)
  ·
    refine ⟨55016989279968618345799183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73355985706624824461065577 55016989279968618345799183)
    ·
      refine ⟨82525483919952927518698775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55016989279968618345799183 82525483919952927518698775)
      ·
        refine ⟨123788225879929391278048163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82525483919952927518698775 123788225879929391278048163)
        ·
          refine ⟨185682338819894086917072245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123788225879929391278048163 185682338819894086917072245)
          ·
            refine ⟨17407719264365070648475523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185682338819894086917072245 17407719264365070648475523)
            ·
              refine ⟨26111578896547605972713285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17407719264365070648475523 26111578896547605972713285)
              ·
                refine ⟨4895921043102676119883741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26111578896547605972713285 4895921043102676119883741)
                ·
                  refine ⟨1835970391163503544956403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4895921043102676119883741 1835970391163503544956403)
                  ·
                    refine ⟨2753955586745255317434605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835970391163503544956403 2753955586745255317434605)
                    ·
                      refine ⟨1032733345029470744037977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2753955586745255317434605 1032733345029470744037977)
                      ·
                        rfl

theorem cell23_2011241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_2011241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011241 prefixEnd_2011241 := by exact prefixLift 2011241
  have htrace : WordTrace (prefixWord ++ tailWord_2011241) baseStart_2011241 baseEnd_2011241 := by
    simpa [prefixWord, tailWord_2011241, baseEnd_2011241] using wordTrace_append hprefix tailTrace_2011241
  have hstable : (prefixWord ++ tailWord_2011241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011241).length < 2 ^ (prefixWord ++ tailWord_2011241).sum := by decide
  have hdescent : baseEnd_2011241 < baseStart_2011241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011261 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_2011261 : Nat := 118140960795 + 2011261 * 2 ^ 59
def prefixEnd_2011261 : Nat := 4983230072969 + 3 ^ 40 * 2011261 * 2
def baseEnd_2011261 : Nat := 344247871547520221929295

theorem tailTrace_2011261 : CollatzResearch.WordTrace tailWord_2011261 prefixEnd_2011261 344247871547520221929295 := by
  unfold tailWord_2011261
  simp only [CollatzResearch.WordTrace]
  refine ⟨73356715166552367876793637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48904476777701578584529091 73356715166552367876793637)
  ·
    refine ⟨13754384093728568976898807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73356715166552367876793637 13754384093728568976898807)
    ·
      refine ⟨20631576140592853465348211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13754384093728568976898807 20631576140592853465348211)
      ·
        refine ⟨30947364210889280198022317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20631576140592853465348211 30947364210889280198022317)
        ·
          refine ⟨11605261579083480074258369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30947364210889280198022317 11605261579083480074258369)
          ·
            refine ⟨8703946184312610055693777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11605261579083480074258369 8703946184312610055693777)
            ·
              refine ⟨6527959638234457541770333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8703946184312610055693777 6527959638234457541770333)
              ·
                refine ⟨2447984864337921578163875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6527959638234457541770333 2447984864337921578163875)
                ·
                  refine ⟨3671977296506882367245813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447984864337921578163875 3671977296506882367245813)
                  ·
                    refine ⟨344247871547520221929295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3671977296506882367245813 344247871547520221929295)
                    ·
                      rfl

theorem cell23_2011261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_2011261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011261 prefixEnd_2011261 := by exact prefixLift 2011261
  have htrace : WordTrace (prefixWord ++ tailWord_2011261) baseStart_2011261 baseEnd_2011261 := by
    simpa [prefixWord, tailWord_2011261, baseEnd_2011261] using wordTrace_append hprefix tailTrace_2011261
  have hstable : (prefixWord ++ tailWord_2011261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011261).length < 2 ^ (prefixWord ++ tailWord_2011261).sum := by decide
  have hdescent : baseEnd_2011261 < baseStart_2011261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011264 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_2011264 : Nat := 118140960795 + 2011264 * 2 ^ 59
def prefixEnd_2011264 : Nat := 4983230072969 + 3 ^ 40 * 2011264 * 2
def baseEnd_2011264 : Nat := 1032745155084524154050371

theorem tailTrace_2011264 : CollatzResearch.WordTrace tailWord_2011264 prefixEnd_2011264 1032745155084524154050371 := by
  unfold tailWord_2011264
  simp only [CollatzResearch.WordTrace]
  refine ⟨36678412292770749694576423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48904549723694332926101897 36678412292770749694576423)
  ·
    refine ⟨55017618439156124541864635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36678412292770749694576423 55017618439156124541864635)
    ·
      refine ⟨82526427658734186812796953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55017618439156124541864635 82526427658734186812796953)
      ·
        refine ⟨61894820744050640109597715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82526427658734186812796953 61894820744050640109597715)
        ·
          refine ⟨92842231116075960164396573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61894820744050640109597715 92842231116075960164396573)
          ·
            refine ⟨34815836668528485061648715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92842231116075960164396573 34815836668528485061648715)
            ·
              refine ⟨52223755002792727592473073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34815836668528485061648715 52223755002792727592473073)
              ·
                refine ⟨39167816252094545694354805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52223755002792727592473073 39167816252094545694354805)
                ·
                  refine ⟨3671982773633863658845763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39167816252094545694354805 3671982773633863658845763)
                  ·
                    refine ⟨5507974160450795488268645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3671982773633863658845763 5507974160450795488268645)
                    ·
                      refine ⟨1032745155084524154050371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5507974160450795488268645 1032745155084524154050371)
                      ·
                        rfl

theorem cell23_2011264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_2011264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011264 prefixEnd_2011264 := by exact prefixLift 2011264
  have htrace : WordTrace (prefixWord ++ tailWord_2011264) baseStart_2011264 baseEnd_2011264 := by
    simpa [prefixWord, tailWord_2011264, baseEnd_2011264] using wordTrace_append hprefix tailTrace_2011264
  have hstable : (prefixWord ++ tailWord_2011264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011264).length < 2 ^ (prefixWord ++ tailWord_2011264).sum := by decide
  have hdescent : baseEnd_2011264 < baseStart_2011264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011268 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_2011268 : Nat := 118140960795 + 2011268 * 2 ^ 59
def prefixEnd_2011268 : Nat := 4983230072969 + 3 ^ 40 * 2011268 * 2
def baseEnd_2011268 : Nat := 1032747209007142138400353

theorem tailTrace_2011268 : CollatzResearch.WordTrace tailWord_2011268 prefixEnd_2011268 1032747209007142138400353 := by
  unfold tailWord_2011268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36678485238763504036149229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48904646985018005381532305 36678485238763504036149229)
  ·
    refine ⟨13754431964536314013555961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36678485238763504036149229 13754431964536314013555961)
    ·
      refine ⟨10315823973402235510166971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13754431964536314013555961 10315823973402235510166971)
      ·
        refine ⟨15473735960103353265250457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315823973402235510166971 15473735960103353265250457)
        ·
          refine ⟨11605301970077514948937843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15473735960103353265250457 11605301970077514948937843)
          ·
            refine ⟨17407952955116272423406765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605301970077514948937843 17407952955116272423406765)
            ·
              refine ⟨6527982358168602158777537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17407952955116272423406765 6527982358168602158777537)
              ·
                refine ⟨4895986768626451619083153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527982358168602158777537 4895986768626451619083153)
                ·
                  refine ⟨3671990076469838714312365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4895986768626451619083153 3671990076469838714312365)
                  ·
                    refine ⟨1376996278676189517867137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671990076469838714312365 1376996278676189517867137)
                    ·
                      refine ⟨1032747209007142138400353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1376996278676189517867137 1032747209007142138400353)
                      ·
                        rfl

theorem cell23_2011268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_2011268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011268 prefixEnd_2011268 := by exact prefixLift 2011268
  have htrace : WordTrace (prefixWord ++ tailWord_2011268) baseStart_2011268 baseEnd_2011268 := by
    simpa [prefixWord, tailWord_2011268, baseEnd_2011268] using wordTrace_append hprefix tailTrace_2011268
  have hstable : (prefixWord ++ tailWord_2011268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011268).length < 2 ^ (prefixWord ++ tailWord_2011268).sum := by decide
  have hdescent : baseEnd_2011268 < baseStart_2011268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011298 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2011298 : Nat := 118140960795 + 2011298 * 2 ^ 59
def prefixEnd_2011298 : Nat := 4983230072969 + 3 ^ 40 * 2011298 * 2
def baseEnd_2011298 : Nat := 1032762613426777021025215

theorem tailTrace_2011298 : CollatzResearch.WordTrace tailWord_2011298 prefixEnd_2011298 1032762613426777021025215 := by
  unfold tailWord_2011298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18339516166854580798972637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48905376444945548797260365 18339516166854580798972637)
  ·
    refine ⟨6877318562570467799614739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18339516166854580798972637 6877318562570467799614739)
    ·
      refine ⟨10315977843855701699422109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877318562570467799614739 10315977843855701699422109)
      ·
        refine ⟨3868491691445888137283291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10315977843855701699422109 3868491691445888137283291)
        ·
          refine ⟨5802737537168832205924937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868491691445888137283291 5802737537168832205924937)
          ·
            refine ⟨4352053152876624154443703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5802737537168832205924937 4352053152876624154443703)
            ·
              refine ⟨6528079729314936231665555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352053152876624154443703 6528079729314936231665555)
              ·
                refine ⟨9792119593972404347498333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528079729314936231665555 9792119593972404347498333)
                ·
                  refine ⟨3672044847739651630311875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792119593972404347498333 3672044847739651630311875)
                  ·
                    refine ⟨5508067271609477445467813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3672044847739651630311875 5508067271609477445467813)
                    ·
                      refine ⟨1032762613426777021025215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5508067271609477445467813 1032762613426777021025215)
                      ·
                        rfl

theorem cell23_2011298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2011298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011298 prefixEnd_2011298 := by exact prefixLift 2011298
  have htrace : WordTrace (prefixWord ++ tailWord_2011298) baseStart_2011298 baseEnd_2011298 := by
    simpa [prefixWord, tailWord_2011298, baseEnd_2011298] using wordTrace_append hprefix tailTrace_2011298
  have hstable : (prefixWord ++ tailWord_2011298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011298).length < 2 ^ (prefixWord ++ tailWord_2011298).sum := by decide
  have hdescent : baseEnd_2011298 < baseStart_2011298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011301 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_2011301 : Nat := 118140960795 + 2011301 * 2 ^ 59
def prefixEnd_2011301 : Nat := 4983230072969 + 3 ^ 40 * 2011301 * 2
def baseEnd_2011301 : Nat := 1032764153868740509287701

theorem tailTrace_2011301 : CollatzResearch.WordTrace tailWord_2011301 prefixEnd_2011301 1032764153868740509287701 := by
  unfold tailWord_2011301
  simp only [CollatzResearch.WordTrace]
  refine ⟨73358174086407454708249757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48905449390938303138833171 73358174086407454708249757)
  ·
    refine ⟨27509315282402795515593659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73358174086407454708249757 27509315282402795515593659)
    ·
      refine ⟨41263972923604193273390489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27509315282402795515593659 41263972923604193273390489)
      ·
        refine ⟨30947979692703144955042867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41263972923604193273390489 30947979692703144955042867)
        ·
          refine ⟨46421969539054717432564301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30947979692703144955042867 46421969539054717432564301)
          ·
            refine ⟨17408238577145519037211613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46421969539054717432564301 17408238577145519037211613)
            ·
              refine ⟨6528089466429569638954355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17408238577145519037211613 6528089466429569638954355)
              ·
                refine ⟨9792134199644354458431533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528089466429569638954355 9792134199644354458431533)
                ·
                  refine ⟨3672050324866632921911825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9792134199644354458431533 3672050324866632921911825)
                  ·
                    refine ⟨2754037743649974691433869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3672050324866632921911825 2754037743649974691433869)
                    ·
                      refine ⟨1032764153868740509287701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2754037743649974691433869 1032764153868740509287701)
                      ·
                        rfl

theorem cell23_2011301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_2011301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011301 prefixEnd_2011301 := by exact prefixLift 2011301
  have htrace : WordTrace (prefixWord ++ tailWord_2011301) baseStart_2011301 baseEnd_2011301 := by
    simpa [prefixWord, tailWord_2011301, baseEnd_2011301] using wordTrace_append hprefix tailTrace_2011301
  have hstable : (prefixWord ++ tailWord_2011301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011301).length < 2 ^ (prefixWord ++ tailWord_2011301).sum := by decide
  have hdescent : baseEnd_2011301 < baseStart_2011301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011315 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 1, 2, 2]
def baseStart_2011315 : Nat := 118140960795 + 2011315 * 2 ^ 59
def prefixEnd_2011315 : Nat := 4983230072969 + 3 ^ 40 * 2011315 * 2
def baseEnd_2011315 : Nat := 1032771342597903454512637

theorem tailTrace_2011315 : CollatzResearch.WordTrace tailWord_2011315 prefixEnd_2011315 1032771342597903454512637 := by
  unfold tailWord_2011315
  simp only [CollatzResearch.WordTrace]
  refine ⟨73358684708356735099259399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48905789805571156732839599 73358684708356735099259399)
  ·
    refine ⟨110038027062535102648889099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73358684708356735099259399 110038027062535102648889099)
    ·
      refine ⟨165057040593802653973333649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110038027062535102648889099 165057040593802653973333649)
      ·
        refine ⟨123792780445351990480000237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165057040593802653973333649 123792780445351990480000237)
        ·
          refine ⟨46422292667006996430000089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123792780445351990480000237 46422292667006996430000089)
          ·
            refine ⟨34816719500255247322500067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46422292667006996430000089 34816719500255247322500067)
            ·
              refine ⟨52225079250382870983750101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34816719500255247322500067 52225079250382870983750101)
              ·
                refine ⟨1224025294930848538681643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52225079250382870983750101 1224025294930848538681643)
                ·
                  refine ⟨1836037942396272808022465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224025294930848538681643 1836037942396272808022465)
                  ·
                    refine ⟨1377028456797204606016849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1836037942396272808022465 1377028456797204606016849)
                    ·
                      refine ⟨1032771342597903454512637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377028456797204606016849 1032771342597903454512637)
                      ·
                        rfl

theorem cell23_2011315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 1, 2, 2].length) (baseStart_2011315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011315 prefixEnd_2011315 := by exact prefixLift 2011315
  have htrace : WordTrace (prefixWord ++ tailWord_2011315) baseStart_2011315 baseEnd_2011315 := by
    simpa [prefixWord, tailWord_2011315, baseEnd_2011315] using wordTrace_append hprefix tailTrace_2011315
  have hstable : (prefixWord ++ tailWord_2011315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011315).length < 2 ^ (prefixWord ++ tailWord_2011315).sum := by decide
  have hdescent : baseEnd_2011315 < baseStart_2011315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011326 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_2011326 : Nat := 118140960795 + 2011326 * 2 ^ 59
def prefixEnd_2011326 : Nat := 4983230072969 + 3 ^ 40 * 2011326 * 2
def baseEnd_2011326 : Nat := 1032776990885102911475087

theorem tailTrace_2011326 : CollatzResearch.WordTrace tailWord_2011326 prefixEnd_2011326 1032776990885102911475087 := by
  unfold tailWord_2011326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169885738914610497238729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48906057274211255985273221 9169885738914610497238729)
  ·
    refine ⟨6877414304185957872929047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9169885738914610497238729 6877414304185957872929047)
    ·
      refine ⟨10316121456278936809393571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877414304185957872929047 10316121456278936809393571)
      ·
        refine ⟨15474182184418405214090357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10316121456278936809393571 15474182184418405214090357)
        ·
          refine ⟨1450704579789225488820971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15474182184418405214090357 1450704579789225488820971)
          ·
            refine ⟨2176056869683838233231457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450704579789225488820971 2176056869683838233231457)
            ·
              refine ⟨1632042652262878674923593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176056869683838233231457 1632042652262878674923593)
              ·
                refine ⟨1224031989197159006192695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632042652262878674923593 1224031989197159006192695)
                ·
                  refine ⟨1836047983795738509289043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224031989197159006192695 1836047983795738509289043)
                  ·
                    refine ⟨2754071975693607763933565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1836047983795738509289043 2754071975693607763933565)
                    ·
                      refine ⟨1032776990885102911475087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2754071975693607763933565 1032776990885102911475087)
                      ·
                        rfl

theorem cell23_2011326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_2011326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011326 prefixEnd_2011326 := by exact prefixLift 2011326
  have htrace : WordTrace (prefixWord ++ tailWord_2011326) baseStart_2011326 baseEnd_2011326 := by
    simpa [prefixWord, tailWord_2011326, baseEnd_2011326] using wordTrace_append hprefix tailTrace_2011326
  have hstable : (prefixWord ++ tailWord_2011326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011326).length < 2 ^ (prefixWord ++ tailWord_2011326).sum := by decide
  have hdescent : baseEnd_2011326 < baseStart_2011326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011331 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 3]
def baseStart_2011331 : Nat := 118140960795 + 2011331 * 2 ^ 59
def prefixEnd_2011331 : Nat := 4983230072969 + 3 ^ 40 * 2011331 * 2
def baseEnd_2011331 : Nat := 1032779558288375391912563

theorem tailTrace_2011331 : CollatzResearch.WordTrace tailWord_2011331 prefixEnd_2011331 1032779558288375391912563 := by
  unfold tailWord_2011331
  simp only [CollatzResearch.WordTrace]
  refine ⟨73359268276298769831841847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48906178850865846554561231 73359268276298769831841847)
  ·
    refine ⟨110038902414448154747762771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73359268276298769831841847 110038902414448154747762771)
    ·
      refine ⟨165058353621672232121644157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110038902414448154747762771 165058353621672232121644157)
      ·
        refine ⟨61896882608127087045616559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165058353621672232121644157 61896882608127087045616559)
        ·
          refine ⟨92845323912190630568424839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61896882608127087045616559 92845323912190630568424839)
          ·
            refine ⟨139267985868285945852637259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92845323912190630568424839 139267985868285945852637259)
            ·
              refine ⟨208901978802428918778955889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139267985868285945852637259 208901978802428918778955889)
              ·
                refine ⟨156676484101821689084216917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208901978802428918778955889 156676484101821689084216917)
                ·
                  refine ⟨1836052548068222918955667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 156676484101821689084216917 1836052548068222918955667)
                  ·
                    refine ⟨2754078822102334378433501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1836052548068222918955667 2754078822102334378433501)
                    ·
                      refine ⟨1032779558288375391912563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2754078822102334378433501 1032779558288375391912563)
                      ·
                        rfl

theorem cell23_2011331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_2011331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011331 prefixEnd_2011331 := by exact prefixLift 2011331
  have htrace : WordTrace (prefixWord ++ tailWord_2011331) baseStart_2011331 baseEnd_2011331 := by
    simpa [prefixWord, tailWord_2011331, baseEnd_2011331] using wordTrace_append hprefix tailTrace_2011331
  have hstable : (prefixWord ++ tailWord_2011331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011331).length < 2 ^ (prefixWord ++ tailWord_2011331).sum := by decide
  have hdescent : baseEnd_2011331 < baseStart_2011331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011364 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_2011364 : Nat := 118140960795 + 2011364 * 2 ^ 59
def prefixEnd_2011364 : Nat := 4983230072969 + 3 ^ 40 * 2011364 * 2
def baseEnd_2011364 : Nat := 344265501049991254266637

theorem tailTrace_2011364 : CollatzResearch.WordTrace tailWord_2011364 prefixEnd_2011364 344265501049991254266637 := by
  unfold tailWord_2011364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36680235942589608233896573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48906981256786144311862097 36680235942589608233896573)
  ·
    refine ⟨13755088478471103087711215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36680235942589608233896573 13755088478471103087711215)
    ·
      refine ⟨20632632717706654631566823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13755088478471103087711215 20632632717706654631566823)
      ·
        refine ⟨30948949076559981947350235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20632632717706654631566823 30948949076559981947350235)
        ·
          refine ⟨46423423614839972921025353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30948949076559981947350235 46423423614839972921025353)
          ·
            refine ⟨34817567711129979690769015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46423423614839972921025353 34817567711129979690769015)
            ·
              refine ⟨52226351566694969536153523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34817567711129979690769015 52226351566694969536153523)
              ·
                refine ⟨78339527350042454304230285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52226351566694969536153523 78339527350042454304230285)
                ·
                  refine ⟨29377322756265920364086357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78339527350042454304230285 29377322756265920364086357)
                  ·
                    refine ⟨344265501049991254266637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29377322756265920364086357 344265501049991254266637)
                    ·
                      rfl

theorem cell23_2011364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_2011364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011364 prefixEnd_2011364 := by exact prefixLift 2011364
  have htrace : WordTrace (prefixWord ++ tailWord_2011364) baseStart_2011364 baseEnd_2011364 := by
    simpa [prefixWord, tailWord_2011364, baseEnd_2011364] using wordTrace_append hprefix tailTrace_2011364
  have hstable : (prefixWord ++ tailWord_2011364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011364).length < 2 ^ (prefixWord ++ tailWord_2011364).sum := by decide
  have hdescent : baseEnd_2011364 < baseStart_2011364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011375 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 1, 3, 2]
def baseStart_2011375 : Nat := 118140960795 + 2011375 * 2 ^ 59
def prefixEnd_2011375 : Nat := 4983230072969 + 3 ^ 40 * 2011375 * 2
def baseEnd_2011375 : Nat := 1032802151437173219762361

theorem tailTrace_2011375 : CollatzResearch.WordTrace tailWord_2011375 prefixEnd_2011375 1032802151437173219762361 := by
  unfold tailWord_2011375
  simp only [CollatzResearch.WordTrace]
  refine ⟨73360873088139365346443579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48907248725426243564295719 73360873088139365346443579)
  ·
    refine ⟨110041309632209048019665369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73360873088139365346443579 110041309632209048019665369)
    ·
      refine ⟨82530982224156786014749027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110041309632209048019665369 82530982224156786014749027)
      ·
        refine ⟨123796473336235179022123541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82530982224156786014749027 123796473336235179022123541)
        ·
          refine ⟨5802959687636024016662041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123796473336235179022123541 5802959687636024016662041)
          ·
            refine ⟨4352219765727018012496531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5802959687636024016662041 4352219765727018012496531)
            ·
              refine ⟨6528329648590527018744797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352219765727018012496531 6528329648590527018744797)
              ·
                refine ⟨2448123618221447632029299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6528329648590527018744797 2448123618221447632029299)
                ·
                  refine ⟨3672185427332171448043949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448123618221447632029299 3672185427332171448043949)
                  ·
                    refine ⟨1377069535249564293016481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3672185427332171448043949 1377069535249564293016481)
                    ·
                      refine ⟨1032802151437173219762361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377069535249564293016481 1032802151437173219762361)
                      ·
                        rfl

theorem cell23_2011375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 3, 2].length) (baseStart_2011375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011375 prefixEnd_2011375 := by exact prefixLift 2011375
  have htrace : WordTrace (prefixWord ++ tailWord_2011375) baseStart_2011375 baseEnd_2011375 := by
    simpa [prefixWord, tailWord_2011375, baseEnd_2011375] using wordTrace_append hprefix tailTrace_2011375
  have hstable : (prefixWord ++ tailWord_2011375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011375).length < 2 ^ (prefixWord ++ tailWord_2011375).sum := by decide
  have hdescent : baseEnd_2011375 < baseStart_2011375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011399 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2011399 : Nat := 118140960795 + 2011399 * 2 ^ 59
def prefixEnd_2011399 : Nat := 4983230072969 + 3 ^ 40 * 2011399 * 2
def baseEnd_2011399 : Nat := 1032814474972881125862251

theorem tailTrace_2011399 : CollatzResearch.WordTrace tailWord_2011399 prefixEnd_2011399 1032814474972881125862251 := by
  unfold tailWord_2011399
  simp only [CollatzResearch.WordTrace]
  refine ⟨73361748440052417445317251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48907832293368278296878167 73361748440052417445317251)
  ·
    refine ⟨110042622660078626167975877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73361748440052417445317251 110042622660078626167975877)
    ·
      refine ⟨20632991748764742406495477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110042622660078626167975877 20632991748764742406495477)
      ·
        refine ⟨1934342976446694600608951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20632991748764742406495477 1934342976446694600608951)
        ·
          refine ⟨2901514464670041900913427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934342976446694600608951 2901514464670041900913427)
          ·
            refine ⟨4352271697005062851370141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901514464670041900913427 4352271697005062851370141)
            ·
              refine ⟨1632101886376898569263803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4352271697005062851370141 1632101886376898569263803)
              ·
                refine ⟨2448152829565347853895705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632101886376898569263803 2448152829565347853895705)
                ·
                  refine ⟨1836114622174010890421779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2448152829565347853895705 1836114622174010890421779)
                  ·
                    refine ⟨2754171933261016335632669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1836114622174010890421779 2754171933261016335632669)
                    ·
                      refine ⟨1032814474972881125862251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2754171933261016335632669 1032814474972881125862251)
                      ·
                        rfl

theorem cell23_2011399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2011399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011399 prefixEnd_2011399 := by exact prefixLift 2011399
  have htrace : WordTrace (prefixWord ++ tailWord_2011399) baseStart_2011399 baseEnd_2011399 := by
    simpa [prefixWord, tailWord_2011399, baseEnd_2011399] using wordTrace_append hprefix tailTrace_2011399
  have hstable : (prefixWord ++ tailWord_2011399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011399).length < 2 ^ (prefixWord ++ tailWord_2011399).sum := by decide
  have hdescent : baseEnd_2011399 < baseStart_2011399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011401 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_2011401 : Nat := 118140960795 + 2011401 * 2 ^ 59
def prefixEnd_2011401 : Nat := 4983230072969 + 3 ^ 40 * 2011401 * 2
def baseEnd_2011401 : Nat := 1032815501934190118037241

theorem tailTrace_2011401 : CollatzResearch.WordTrace tailWord_2011401 prefixEnd_2011401 1032815501934190118037241 := by
  unfold tailWord_2011401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73361821386045171786890057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48907880924030114524593371 73361821386045171786890057)
  ·
    refine ⟨55021366039533878840167543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73361821386045171786890057 55021366039533878840167543)
    ·
      refine ⟨82532049059300818260251315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55021366039533878840167543 82532049059300818260251315)
      ·
        refine ⟨123798073588951227390376973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82532049059300818260251315 123798073588951227390376973)
        ·
          refine ⟨46424277595856710271391365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123798073588951227390376973 46424277595856710271391365)
          ·
            refine ⟨8704552049223133175885881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46424277595856710271391365 8704552049223133175885881)
            ·
              refine ⟨6528414036917349881914411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8704552049223133175885881 6528414036917349881914411)
              ·
                refine ⟨9792621055376024822871617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528414036917349881914411 9792621055376024822871617)
                ·
                  refine ⟨7344465791532018617153713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792621055376024822871617 7344465791532018617153713)
                  ·
                    refine ⟨5508349343649013962865285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344465791532018617153713 5508349343649013962865285)
                    ·
                      refine ⟨1032815501934190118037241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5508349343649013962865285 1032815501934190118037241)
                      ·
                        rfl

theorem cell23_2011401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_2011401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011401 prefixEnd_2011401 := by exact prefixLift 2011401
  have htrace : WordTrace (prefixWord ++ tailWord_2011401) baseStart_2011401 baseEnd_2011401 := by
    simpa [prefixWord, tailWord_2011401, baseEnd_2011401] using wordTrace_append hprefix tailTrace_2011401
  have hstable : (prefixWord ++ tailWord_2011401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011401).length < 2 ^ (prefixWord ++ tailWord_2011401).sum := by decide
  have hdescent : baseEnd_2011401 < baseStart_2011401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011445 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 5]
def baseStart_2011445 : Nat := 118140960795 + 2011445 * 2 ^ 59
def prefixEnd_2011445 : Nat := 4983230072969 + 3 ^ 40 * 2011445 * 2
def baseEnd_2011445 : Nat := 114759788342554216209671

theorem tailTrace_2011445 : CollatzResearch.WordTrace tailWord_2011445 prefixEnd_2011445 114759788342554216209671 := by
  unfold tailWord_2011445
  simp only [CollatzResearch.WordTrace]
  refine ⟨73363426197885767301491789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48908950798590511534327859 73363426197885767301491789)
  ·
    refine ⟨27511284824207162738059421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73363426197885767301491789 27511284824207162738059421)
    ·
      refine ⟨10316731809077686026772283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27511284824207162738059421 10316731809077686026772283)
      ·
        refine ⟨15475097713616529040158425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10316731809077686026772283 15475097713616529040158425)
        ·
          refine ⟨11606323285212396780118819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15475097713616529040158425 11606323285212396780118819)
          ·
            refine ⟨17409484927818595170178229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606323285212396780118819 17409484927818595170178229)
            ·
              refine ⟨1632139211982993297204209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17409484927818595170178229 1632139211982993297204209)
              ·
                refine ⟨1224104408987244972903157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632139211982993297204209 1224104408987244972903157)
                ·
                  refine ⟨114759788342554216209671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224104408987244972903157 114759788342554216209671)
                  ·
                    rfl

theorem cell23_2011445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_2011445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011445 prefixEnd_2011445 := by exact prefixLift 2011445
  have htrace : WordTrace (prefixWord ++ tailWord_2011445) baseStart_2011445 baseEnd_2011445 := by
    simpa [prefixWord, tailWord_2011445, baseEnd_2011445] using wordTrace_append hprefix tailTrace_2011445
  have hstable : (prefixWord ++ tailWord_2011445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011445).length < 2 ^ (prefixWord ++ tailWord_2011445).sum := by decide
  have hdescent : baseEnd_2011445 < baseStart_2011445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011491 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2011491 : Nat := 118140960795 + 2011491 * 2 ^ 59
def prefixEnd_2011491 : Nat := 4983230072969 + 3 ^ 40 * 2011491 * 2
def baseEnd_2011491 : Nat := 1032861715193094765911827

theorem tailTrace_2011491 : CollatzResearch.WordTrace tailWord_2011491 prefixEnd_2011491 1032861715193094765911827 := by
  unfold tailWord_2011491
  simp only [CollatzResearch.WordTrace]
  refine ⟨73365103955719117157666327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48910069303812744771777551 73365103955719117157666327)
  ·
    refine ⟨110047655933578675736499491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73365103955719117157666327 110047655933578675736499491)
    ·
      refine ⟨165071483900368013604749237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110047655933578675736499491 165071483900368013604749237)
      ·
        refine ⟨15475451615659501275445241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165071483900368013604749237 15475451615659501275445241)
        ·
          refine ⟨11606588711744625956583931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15475451615659501275445241 11606588711744625956583931)
          ·
            refine ⟨17409883067616938934875897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606588711744625956583931 17409883067616938934875897)
            ·
              refine ⟨13057412300712704201156923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17409883067616938934875897 13057412300712704201156923)
              ·
                refine ⟨19586118451069056301735385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13057412300712704201156923 19586118451069056301735385)
                ·
                  refine ⟨14689588838301792226301539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19586118451069056301735385 14689588838301792226301539)
                  ·
                    refine ⟨22034383257452688339452309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14689588838301792226301539 22034383257452688339452309)
                    ·
                      refine ⟨1032861715193094765911827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22034383257452688339452309 1032861715193094765911827)
                      ·
                        rfl

theorem cell23_2011491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2011491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011491 prefixEnd_2011491 := by exact prefixLift 2011491
  have htrace : WordTrace (prefixWord ++ tailWord_2011491) baseStart_2011491 baseEnd_2011491 := by
    simpa [prefixWord, tailWord_2011491, baseEnd_2011491] using wordTrace_append hprefix tailTrace_2011491
  have hstable : (prefixWord ++ tailWord_2011491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011491).length < 2 ^ (prefixWord ++ tailWord_2011491).sum := by decide
  have hdescent : baseEnd_2011491 < baseStart_2011491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011541 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2011541 : Nat := 118140960795 + 2011541 * 2 ^ 59
def prefixEnd_2011541 : Nat := 4983230072969 + 3 ^ 40 * 2011541 * 2
def baseEnd_2011541 : Nat := 1032887389225819570286597

theorem tailTrace_2011541 : CollatzResearch.WordTrace tailWord_2011541 prefixEnd_2011541 1032887389225819570286597 := by
  unfold tailWord_2011541
  simp only [CollatzResearch.WordTrace]
  refine ⟨73366927605537975696986477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48911285070358650464657651 73366927605537975696986477)
  ·
    refine ⟨27512597852076740886369929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73366927605537975696986477 27512597852076740886369929)
    ·
      refine ⟨20634448389057555664777447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27512597852076740886369929 20634448389057555664777447)
      ·
        refine ⟨30951672583586333497166171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20634448389057555664777447 30951672583586333497166171)
        ·
          refine ⟨46427508875379500245749257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30951672583586333497166171 46427508875379500245749257)
          ·
            refine ⟨34820631656534625184311943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46427508875379500245749257 34820631656534625184311943)
            ·
              refine ⟨52230947484801937776467915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34820631656534625184311943 52230947484801937776467915)
              ·
                refine ⟨78346421227202906664701873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52230947484801937776467915 78346421227202906664701873)
                ·
                  refine ⟨58759815920402179998526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78346421227202906664701873 58759815920402179998526405)
                  ·
                    refine ⟨11017465485075408749723701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58759815920402179998526405 11017465485075408749723701)
                    ·
                      refine ⟨1032887389225819570286597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11017465485075408749723701 1032887389225819570286597)
                      ·
                        rfl

theorem cell23_2011541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2011541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011541 prefixEnd_2011541 := by exact prefixLift 2011541
  have htrace : WordTrace (prefixWord ++ tailWord_2011541) baseStart_2011541 baseEnd_2011541 := by
    simpa [prefixWord, tailWord_2011541, baseEnd_2011541] using wordTrace_append hprefix tailTrace_2011541
  have hstable : (prefixWord ++ tailWord_2011541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011541).length < 2 ^ (prefixWord ++ tailWord_2011541).sum := by decide
  have hdescent : baseEnd_2011541 < baseStart_2011541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011561 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_2011561 : Nat := 118140960795 + 2011561 * 2 ^ 59
def prefixEnd_2011561 : Nat := 4983230072969 + 3 ^ 40 * 2011561 * 2
def baseEnd_2011561 : Nat := 344299219612969830678835

theorem tailTrace_2011561 : CollatzResearch.WordTrace tailWord_2011561 prefixEnd_2011561 344299219612969830678835 := by
  unfold tailWord_2011561
  simp only [CollatzResearch.WordTrace]
  refine ⟨73367657065465519112714537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48911771376977012741809691 73367657065465519112714537)
  ·
    refine ⟨55025742799099139334535903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73367657065465519112714537 55025742799099139334535903)
    ·
      refine ⟨82538614198648709001803855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55025742799099139334535903 82538614198648709001803855)
      ·
        refine ⟨123807921297973063502705783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82538614198648709001803855 123807921297973063502705783)
        ·
          refine ⟨185711881946959595254058675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123807921297973063502705783 185711881946959595254058675)
          ·
            refine ⟨278567822920439392881088013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185711881946959595254058675 278567822920439392881088013)
            ·
              refine ⟨104462933595164772330408005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278567822920439392881088013 104462933595164772330408005)
              ·
                refine ⟨19586800049093394811951501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104462933595164772330408005 19586800049093394811951501)
                ·
                  refine ⟨7345050018410023054481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19586800049093394811951501 7345050018410023054481813)
                  ·
                    refine ⟨344299219612969830678835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7345050018410023054481813 344299219612969830678835)
                    ·
                      rfl

theorem cell23_2011561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_2011561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011561 prefixEnd_2011561 := by exact prefixLift 2011561
  have htrace : WordTrace (prefixWord ++ tailWord_2011561) baseStart_2011561 baseEnd_2011561 := by
    simpa [prefixWord, tailWord_2011561, baseEnd_2011561] using wordTrace_append hprefix tailTrace_2011561
  have hstable : (prefixWord ++ tailWord_2011561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011561).length < 2 ^ (prefixWord ++ tailWord_2011561).sum := by decide
  have hdescent : baseEnd_2011561 < baseStart_2011561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011596 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2011596 : Nat := 118140960795 + 2011596 * 2 ^ 59
def prefixEnd_2011596 : Nat := 4983230072969 + 3 ^ 40 * 2011596 * 2
def baseEnd_2011596 : Nat := 1032915630661816855098845

theorem tailTrace_2011596 : CollatzResearch.WordTrace tailWord_2011596 prefixEnd_2011596 1032915630661816855098845 := by
  unfold tailWord_2011596
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684466810169360045119321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48912622413559146726825761 36684466810169360045119321)
  ·
    refine ⟨27513350107627020033839491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36684466810169360045119321 27513350107627020033839491)
    ·
      refine ⟨41270025161440530050759237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27513350107627020033839491 41270025161440530050759237)
      ·
        refine ⟨7738129717770099384517357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41270025161440530050759237 7738129717770099384517357)
        ·
          refine ⟨2901798644163787269194009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7738129717770099384517357 2901798644163787269194009)
          ·
            refine ⟨2176348983122840451895507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901798644163787269194009 2176348983122840451895507)
            ·
              refine ⟨3264523474684260677843261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176348983122840451895507 3264523474684260677843261)
              ·
                refine ⟨1224196303006597754191223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3264523474684260677843261 1224196303006597754191223)
                ·
                  refine ⟨1836294454509896631286835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224196303006597754191223 1836294454509896631286835)
                  ·
                    refine ⟨2754441681764844946930253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1836294454509896631286835 2754441681764844946930253)
                    ·
                      refine ⟨1032915630661816855098845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2754441681764844946930253 1032915630661816855098845)
                      ·
                        rfl

theorem cell23_2011596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2011596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011596 prefixEnd_2011596 := by exact prefixLift 2011596
  have htrace : WordTrace (prefixWord ++ tailWord_2011596) baseStart_2011596 baseEnd_2011596 := by
    simpa [prefixWord, tailWord_2011596, baseEnd_2011596] using wordTrace_append hprefix tailTrace_2011596
  have hstable : (prefixWord ++ tailWord_2011596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011596).length < 2 ^ (prefixWord ++ tailWord_2011596).sum := by decide
  have hdescent : baseEnd_2011596 < baseStart_2011596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011598 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_2011598 : Nat := 118140960795 + 2011598 * 2 ^ 59
def prefixEnd_2011598 : Nat := 4983230072969 + 3 ^ 40 * 2011598 * 2
def baseEnd_2011598 : Nat := 1032916657623125847273835

theorem tailTrace_2011598 : CollatzResearch.WordTrace tailWord_2011598 prefixEnd_2011598 1032916657623125847273835 := by
  unfold tailWord_2011598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9171125820791434303976431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48912671044220982954540965 9171125820791434303976431)
  ·
    refine ⟨13756688731187151455964647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9171125820791434303976431 13756688731187151455964647)
    ·
      refine ⟨20635033096780727183946971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756688731187151455964647 20635033096780727183946971)
      ·
        refine ⟨30952549645171090775920457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20635033096780727183946971 30952549645171090775920457)
        ·
          refine ⟨23214412233878318081940343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30952549645171090775920457 23214412233878318081940343)
          ·
            refine ⟨34821618350817477122910515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23214412233878318081940343 34821618350817477122910515)
            ·
              refine ⟨52232427526226215684365773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34821618350817477122910515 52232427526226215684365773)
              ·
                refine ⟨19587160322334830881637165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52232427526226215684365773 19587160322334830881637165)
                ·
                  refine ⟨7345185120875561580613937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19587160322334830881637165 7345185120875561580613937)
                  ·
                    refine ⟨5508888840656671185460453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345185120875561580613937 5508888840656671185460453)
                    ·
                      refine ⟨1032916657623125847273835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5508888840656671185460453 1032916657623125847273835)
                      ·
                        rfl

theorem cell23_2011598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_2011598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011598 prefixEnd_2011598 := by exact prefixLift 2011598
  have htrace : WordTrace (prefixWord ++ tailWord_2011598) baseStart_2011598 baseEnd_2011598 := by
    simpa [prefixWord, tailWord_2011598, baseEnd_2011598] using wordTrace_append hprefix tailTrace_2011598
  have hstable : (prefixWord ++ tailWord_2011598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011598).length < 2 ^ (prefixWord ++ tailWord_2011598).sum := by decide
  have hdescent : baseEnd_2011598 < baseStart_2011598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011605 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2011605 : Nat := 118140960795 + 2011605 * 2 ^ 59
def prefixEnd_2011605 : Nat := 4983230072969 + 3 ^ 40 * 2011605 * 2
def baseEnd_2011605 : Nat := 1032920251987707319886303

theorem tailTrace_2011605 : CollatzResearch.WordTrace tailWord_2011605 prefixEnd_2011605 1032920251987707319886303 := by
  unfold tailWord_2011605
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369261877306114627316269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48912841251537409751544179 73369261877306114627316269)
  ·
    refine ⟨27513473203989792985243601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73369261877306114627316269 27513473203989792985243601)
    ·
      refine ⟨20635104902992344738932701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27513473203989792985243601 20635104902992344738932701)
      ·
        refine ⟨7738164338622129277099763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20635104902992344738932701 7738164338622129277099763)
        ·
          refine ⟨11607246507933193915649645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738164338622129277099763 11607246507933193915649645)
          ·
            refine ⟨4352717440474947718368617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11607246507933193915649645 4352717440474947718368617)
            ·
              refine ⟨3264538080356210788776463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352717440474947718368617 3264538080356210788776463)
              ·
                refine ⟨4896807120534316183164695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264538080356210788776463 4896807120534316183164695)
                ·
                  refine ⟨7345210680801474274747043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896807120534316183164695 7345210680801474274747043)
                  ·
                    refine ⟨11017816021202211412120565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345210680801474274747043 11017816021202211412120565)
                    ·
                      refine ⟨1032920251987707319886303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11017816021202211412120565 1032920251987707319886303)
                      ·
                        rfl

theorem cell23_2011605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2011605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011605 prefixEnd_2011605 := by exact prefixLift 2011605
  have htrace : WordTrace (prefixWord ++ tailWord_2011605) baseStart_2011605 baseEnd_2011605 := by
    simpa [prefixWord, tailWord_2011605, baseEnd_2011605] using wordTrace_append hprefix tailTrace_2011605
  have hstable : (prefixWord ++ tailWord_2011605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011605).length < 2 ^ (prefixWord ++ tailWord_2011605).sum := by decide
  have hdescent : baseEnd_2011605 < baseStart_2011605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011629 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2011629 : Nat := 118140960795 + 2011629 * 2 ^ 59
def prefixEnd_2011629 : Nat := 4983230072969 + 3 ^ 40 * 2011629 * 2
def baseEnd_2011629 : Nat := 344310858507805075328731

theorem tailTrace_2011629 : CollatzResearch.WordTrace tailWord_2011629 prefixEnd_2011629 344310858507805075328731 := by
  unfold tailWord_2011629
  simp only [CollatzResearch.WordTrace]
  refine ⟨73370137229219166726189941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48913424819479444484126627 73370137229219166726189941)
  ·
    refine ⟨6878450365239296880580307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73370137229219166726189941 6878450365239296880580307)
    ·
      refine ⟨10317675547858945320870461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6878450365239296880580307 10317675547858945320870461)
      ·
        refine ⟨3869128330447104495326423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10317675547858945320870461 3869128330447104495326423)
        ·
          refine ⟨5803692495670656742989635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869128330447104495326423 5803692495670656742989635)
          ·
            refine ⟨8705538743505985114484453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803692495670656742989635 8705538743505985114484453)
            ·
              refine ⟨1632288514407372208965835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8705538743505985114484453 1632288514407372208965835)
              ·
                refine ⟨2448432771611058313448753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632288514407372208965835 2448432771611058313448753)
                ·
                  refine ⟨1836324578708293735086565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2448432771611058313448753 1836324578708293735086565)
                  ·
                    refine ⟨344310858507805075328731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836324578708293735086565 344310858507805075328731)
                    ·
                      rfl

theorem cell23_2011629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2011629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011629 prefixEnd_2011629 := by exact prefixLift 2011629
  have htrace : WordTrace (prefixWord ++ tailWord_2011629) baseStart_2011629 baseEnd_2011629 := by
    simpa [prefixWord, tailWord_2011629, baseEnd_2011629] using wordTrace_append hprefix tailTrace_2011629
  have hstable : (prefixWord ++ tailWord_2011629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011629).length < 2 ^ (prefixWord ++ tailWord_2011629).sum := by decide
  have hdescent : baseEnd_2011629 < baseStart_2011629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011652 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2011652 : Nat := 118140960795 + 2011652 * 2 ^ 59
def prefixEnd_2011652 : Nat := 4983230072969 + 3 ^ 40 * 2011652 * 2
def baseEnd_2011652 : Nat := 1032944385578468635998587

theorem tailTrace_2011652 : CollatzResearch.WordTrace tailWord_2011652 prefixEnd_2011652 1032944385578468635998587 := by
  unfold tailWord_2011652
  simp only [CollatzResearch.WordTrace]
  refine ⟨36685488054067920827138605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48913984072090561102851473 36685488054067920827138605)
  ·
    refine ⟨13757058020275470310176977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36685488054067920827138605 13757058020275470310176977)
    ·
      refine ⟨10317793515206602732632733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13757058020275470310176977 10317793515206602732632733)
      ·
        refine ⟨3869172568202476024737275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10317793515206602732632733 3869172568202476024737275)
        ·
          refine ⟨5803758852303714037105913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869172568202476024737275 5803758852303714037105913)
          ·
            refine ⟨4352819139227785527829435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5803758852303714037105913 4352819139227785527829435)
            ·
              refine ⟨6529228708841678291744153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352819139227785527829435 6529228708841678291744153)
              ·
                refine ⟨4896921531631258718808115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529228708841678291744153 4896921531631258718808115)
                ·
                  refine ⟨7345382297446888078212173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896921531631258718808115 7345382297446888078212173)
                  ·
                    refine ⟨2754518361542583029329565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7345382297446888078212173 2754518361542583029329565)
                    ·
                      refine ⟨1032944385578468635998587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2754518361542583029329565 1032944385578468635998587)
                      ·
                        rfl

theorem cell23_2011652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2011652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011652 prefixEnd_2011652 := by exact prefixLift 2011652
  have htrace : WordTrace (prefixWord ++ tailWord_2011652) baseStart_2011652 baseEnd_2011652 := by
    simpa [prefixWord, tailWord_2011652, baseEnd_2011652] using wordTrace_append hprefix tailTrace_2011652
  have hstable : (prefixWord ++ tailWord_2011652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011652).length < 2 ^ (prefixWord ++ tailWord_2011652).sum := by decide
  have hdescent : baseEnd_2011652 < baseStart_2011652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011698 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_2011698 : Nat := 118140960795 + 2011698 * 2 ^ 59
def prefixEnd_2011698 : Nat := 4983230072969 + 3 ^ 40 * 2011698 * 2
def baseEnd_2011698 : Nat := 114774222854286161780375

theorem tailTrace_2011698 : CollatzResearch.WordTrace tailWord_2011698 prefixEnd_2011698 114774222854286161780375 := by
  unfold tailWord_2011698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18343163466492297877612937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48915102577312794340301165 18343163466492297877612937)
  ·
    refine ⟨13757372599869223408209703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18343163466492297877612937 13757372599869223408209703)
    ·
      refine ⟨20636058899803835112314555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13757372599869223408209703 20636058899803835112314555)
      ·
        refine ⟨30954088349705752668471833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636058899803835112314555 30954088349705752668471833)
        ·
          refine ⟨23215566262279314501353875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30954088349705752668471833 23215566262279314501353875)
          ·
            refine ⟨34823349393418971752030813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23215566262279314501353875 34823349393418971752030813)
            ·
              refine ⟨13058756022532114407011555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34823349393418971752030813 13058756022532114407011555)
              ·
                refine ⟨19588134033798171610517333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13058756022532114407011555 19588134033798171610517333)
                ·
                  refine ⟨114774222854286161780375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19588134033798171610517333 114774222854286161780375)
                  ·
                    rfl

theorem cell23_2011698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_2011698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011698 prefixEnd_2011698 := by exact prefixLift 2011698
  have htrace : WordTrace (prefixWord ++ tailWord_2011698) baseStart_2011698 baseEnd_2011698 := by
    simpa [prefixWord, tailWord_2011698, baseEnd_2011698] using wordTrace_append hprefix tailTrace_2011698
  have hstable : (prefixWord ++ tailWord_2011698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011698).length < 2 ^ (prefixWord ++ tailWord_2011698).sum := by decide
  have hdescent : baseEnd_2011698 < baseStart_2011698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011732 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 5]
def baseStart_2011732 : Nat := 118140960795 + 2011732 * 2 ^ 59
def prefixEnd_2011732 : Nat := 4983230072969 + 3 ^ 40 * 2011732 * 2
def baseEnd_2011732 : Nat := 114776162670092035888691

theorem tailTrace_2011732 : CollatzResearch.WordTrace tailWord_2011732 prefixEnd_2011732 114776162670092035888691 := by
  unfold tailWord_2011732
  simp only [CollatzResearch.WordTrace]
  refine ⟨36686946973923007658594725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48915929298564010211459633 36686946973923007658594725)
  ·
    refine ⟨6878802557610563935986511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36686946973923007658594725 6878802557610563935986511)
    ·
      refine ⟨10318203836415845903979767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6878802557610563935986511 10318203836415845903979767)
      ·
        refine ⟨15477305754623768855969651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318203836415845903979767 15477305754623768855969651)
        ·
          refine ⟨23215958631935653283954477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15477305754623768855969651 23215958631935653283954477)
          ·
            refine ⟨8705984486975869981482929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23215958631935653283954477 8705984486975869981482929)
            ·
              refine ⟨6529488365231902486112197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705984486975869981482929 6529488365231902486112197)
              ·
                refine ⟨1224279068480981716146037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6529488365231902486112197 1224279068480981716146037)
                ·
                  refine ⟨114776162670092035888691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224279068480981716146037 114776162670092035888691)
                  ·
                    rfl

theorem cell23_2011732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_2011732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011732 prefixEnd_2011732 := by exact prefixLift 2011732
  have htrace : WordTrace (prefixWord ++ tailWord_2011732) baseStart_2011732 baseEnd_2011732 := by
    simpa [prefixWord, tailWord_2011732, baseEnd_2011732] using wordTrace_append hprefix tailTrace_2011732
  have hstable : (prefixWord ++ tailWord_2011732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011732).length < 2 ^ (prefixWord ++ tailWord_2011732).sum := by decide
  have hdescent : baseEnd_2011732 < baseStart_2011732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011766 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_2011766 : Nat := 118140960795 + 2011766 * 2 ^ 59
def prefixEnd_2011766 : Nat := 4983230072969 + 3 ^ 40 * 2011766 * 2
def baseEnd_2011766 : Nat := 114778102485897909997007

theorem tailTrace_2011766 : CollatzResearch.WordTrace tailWord_2011766 prefixEnd_2011766 114778102485897909997007 := by
  unfold tailWord_2011766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585945876857677445245447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48916756019815226082618101 4585945876857677445245447)
  ·
    refine ⟨6878918815286516167868171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4585945876857677445245447 6878918815286516167868171)
    ·
      refine ⟨10318378222929774251802257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6878918815286516167868171 10318378222929774251802257)
      ·
        refine ⟨7738783667197330688851693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10318378222929774251802257 7738783667197330688851693)
        ·
          refine ⟨2902043875198999008319385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7738783667197330688851693 2902043875198999008319385)
          ·
            refine ⟨2176532906399249256239539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2902043875198999008319385 2176532906399249256239539)
            ·
              refine ⟨3264799359598873884359309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176532906399249256239539 3264799359598873884359309)
              ·
                refine ⟨1224299759849577706634741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3264799359598873884359309 1224299759849577706634741)
                ·
                  refine ⟨114778102485897909997007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224299759849577706634741 114778102485897909997007)
                  ·
                    rfl

theorem cell23_2011766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_2011766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011766 prefixEnd_2011766 := by exact prefixLift 2011766
  have htrace : WordTrace (prefixWord ++ tailWord_2011766) baseStart_2011766 baseEnd_2011766 := by
    simpa [prefixWord, tailWord_2011766, baseEnd_2011766] using wordTrace_append hprefix tailTrace_2011766
  have hstable : (prefixWord ++ tailWord_2011766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011766).length < 2 ^ (prefixWord ++ tailWord_2011766).sum := by decide
  have hdescent : baseEnd_2011766 < baseStart_2011766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011852 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_2011852 : Nat := 118140960795 + 2011852 * 2 ^ 59
def prefixEnd_2011852 : Nat := 4983230072969 + 3 ^ 40 * 2011852 * 2
def baseEnd_2011852 : Nat := 344349027236455951165889

theorem tailTrace_2011852 : CollatzResearch.WordTrace tailWord_2011852 prefixEnd_2011852 344349027236455951165889 := by
  unfold tailWord_2011852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36689135353705637905778905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48918847138274183874371873 36689135353705637905778905)
  ·
    refine ⟨27516851515279228429334179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36689135353705637905778905 27516851515279228429334179)
    ·
      refine ⟨41275277272918842644001269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27516851515279228429334179 41275277272918842644001269)
      ·
        refine ⟨3869557244336141497875119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41275277272918842644001269 3869557244336141497875119)
        ·
          refine ⟨5804335866504212246812679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869557244336141497875119 5804335866504212246812679)
          ·
            refine ⟨8706503799756318370219019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804335866504212246812679 8706503799756318370219019)
            ·
              refine ⟨13059755699634477555328529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706503799756318370219019 13059755699634477555328529)
              ·
                refine ⟨9794816774725858166496397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13059755699634477555328529 9794816774725858166496397)
                ·
                  refine ⟨3673056290522196812436149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9794816774725858166496397 3673056290522196812436149)
                  ·
                    refine ⟨344349027236455951165889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3673056290522196812436149 344349027236455951165889)
                    ·
                      rfl

theorem cell23_2011852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_2011852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011852 prefixEnd_2011852 := by exact prefixLift 2011852
  have htrace : WordTrace (prefixWord ++ tailWord_2011852) baseStart_2011852 baseEnd_2011852 := by
    simpa [prefixWord, tailWord_2011852, baseEnd_2011852] using wordTrace_append hprefix tailTrace_2011852
  have hstable : (prefixWord ++ tailWord_2011852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011852).length < 2 ^ (prefixWord ++ tailWord_2011852).sum := by decide
  have hdescent : baseEnd_2011852 < baseStart_2011852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011872 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2011872 : Nat := 118140960795 + 2011872 * 2 ^ 59
def prefixEnd_2011872 : Nat := 4983230072969 + 3 ^ 40 * 2011872 * 2
def baseEnd_2011872 : Nat := 1033057351322457775247575

theorem tailTrace_2011872 : CollatzResearch.WordTrace tailWord_2011872 prefixEnd_2011872 1033057351322457775247575 := by
  unfold tailWord_2011872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36689500083669409613642935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48919333444892546151523913 36689500083669409613642935)
  ·
    refine ⟨55034250125504114420464403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36689500083669409613642935 55034250125504114420464403)
    ·
      refine ⟨82551375188256171630696605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55034250125504114420464403 82551375188256171630696605)
      ·
        refine ⟨30956765695596064361511227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82551375188256171630696605 30956765695596064361511227)
        ·
          refine ⟨46435148543394096542266841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30956765695596064361511227 46435148543394096542266841)
          ·
            refine ⟨34826361407545572406700131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46435148543394096542266841 34826361407545572406700131)
            ·
              refine ⟨52239542111318358610050197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34826361407545572406700131 52239542111318358610050197)
              ·
                refine ⟨2448728536468048059846103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52239542111318358610050197 2448728536468048059846103)
                ·
                  refine ⟨3673092804702072089769155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448728536468048059846103 3673092804702072089769155)
                  ·
                    refine ⟨5509639207053108134653733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3673092804702072089769155 5509639207053108134653733)
                    ·
                      refine ⟨1033057351322457775247575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5509639207053108134653733 1033057351322457775247575)
                      ·
                        rfl

theorem cell23_2011872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2011872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011872 prefixEnd_2011872 := by exact prefixLift 2011872
  have htrace : WordTrace (prefixWord ++ tailWord_2011872) baseStart_2011872 baseEnd_2011872 := by
    simpa [prefixWord, tailWord_2011872, baseEnd_2011872] using wordTrace_append hprefix tailTrace_2011872
  have hstable : (prefixWord ++ tailWord_2011872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011872).length < 2 ^ (prefixWord ++ tailWord_2011872).sum := by decide
  have hdescent : baseEnd_2011872 < baseStart_2011872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011876 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_2011876 : Nat := 118140960795 + 2011876 * 2 ^ 59
def prefixEnd_2011876 : Nat := 4983230072969 + 3 ^ 40 * 2011876 * 2
def baseEnd_2011876 : Nat := 1033059405245075759597557

theorem tailTrace_2011876 : CollatzResearch.WordTrace tailWord_2011876 prefixEnd_2011876 1033059405245075759597557 := by
  unfold tailWord_2011876
  simp only [CollatzResearch.WordTrace]
  refine ⟨36689573029662163955215741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48919430706216218606954321 36689573029662163955215741)
  ·
    refine ⟨13758589886123311483205903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36689573029662163955215741 13758589886123311483205903)
    ·
      refine ⟨20637884829184967224808855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13758589886123311483205903 20637884829184967224808855)
      ·
        refine ⟨30956827243777450837213283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20637884829184967224808855 30956827243777450837213283)
        ·
          refine ⟨46435240865666176255819925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30956827243777450837213283 46435240865666176255819925)
          ·
            refine ⟨2176651915578102011991559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46435240865666176255819925 2176651915578102011991559)
            ·
              refine ⟨3264977873367153017987339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176651915578102011991559 3264977873367153017987339)
              ·
                refine ⟨4897466810050729526981009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3264977873367153017987339 4897466810050729526981009)
                ·
                  refine ⟨3673100107538047145235757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4897466810050729526981009 3673100107538047145235757)
                  ·
                    refine ⟨1377412540326767679463409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673100107538047145235757 1377412540326767679463409)
                    ·
                      refine ⟨1033059405245075759597557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377412540326767679463409 1033059405245075759597557)
                      ·
                        rfl

theorem cell23_2011876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_2011876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011876 prefixEnd_2011876 := by exact prefixLift 2011876
  have htrace : WordTrace (prefixWord ++ tailWord_2011876) baseStart_2011876 baseEnd_2011876 := by
    simpa [prefixWord, tailWord_2011876, baseEnd_2011876] using wordTrace_append hprefix tailTrace_2011876
  have hstable : (prefixWord ++ tailWord_2011876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011876).length < 2 ^ (prefixWord ++ tailWord_2011876).sum := by decide
  have hdescent : baseEnd_2011876 < baseStart_2011876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011882 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2011882 : Nat := 118140960795 + 2011882 * 2 ^ 59
def prefixEnd_2011882 : Nat := 4983230072969 + 3 ^ 40 * 2011882 * 2
def baseEnd_2011882 : Nat := 344354162043000912040843

theorem tailTrace_2011882 : CollatzResearch.WordTrace tailWord_2011882 prefixEnd_2011882 344354162043000912040843 := by
  unfold tailWord_2011882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18344841224325647733787475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48919576598201727290099933 18344841224325647733787475)
  ·
    refine ⟨27517261836488471600681213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18344841224325647733787475 27517261836488471600681213)
    ·
      refine ⟨10318973188683176850255455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27517261836488471600681213 10318973188683176850255455)
      ·
        refine ⟨15478459783024765275383183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318973188683176850255455 15478459783024765275383183)
        ·
          refine ⟨23217689674537147913074775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478459783024765275383183 23217689674537147913074775)
          ·
            refine ⟨34826534511805721869612163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23217689674537147913074775 34826534511805721869612163)
            ·
              refine ⟨52239801767708582804418245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34826534511805721869612163 52239801767708582804418245)
              ·
                refine ⟨9794962831445359275828421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52239801767708582804418245 9794962831445359275828421)
                ·
                  refine ⟨1836555530896004864217829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9794962831445359275828421 1836555530896004864217829)
                  ·
                    refine ⟨344354162043000912040843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836555530896004864217829 344354162043000912040843)
                    ·
                      rfl

theorem cell23_2011882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2011882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011882 prefixEnd_2011882 := by exact prefixLift 2011882
  have htrace : WordTrace (prefixWord ++ tailWord_2011882) baseStart_2011882 baseEnd_2011882 := by
    simpa [prefixWord, tailWord_2011882, baseEnd_2011882] using wordTrace_append hprefix tailTrace_2011882
  have hstable : (prefixWord ++ tailWord_2011882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011882).length < 2 ^ (prefixWord ++ tailWord_2011882).sum := by decide
  have hdescent : baseEnd_2011882 < baseStart_2011882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011886 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2011886 : Nat := 118140960795 + 2011886 * 2 ^ 59
def prefixEnd_2011886 : Nat := 4983230072969 + 3 ^ 40 * 2011886 * 2
def baseEnd_2011886 : Nat := 344354846683873573490837

theorem tailTrace_2011886 : CollatzResearch.WordTrace tailWord_2011886 prefixEnd_2011886 344354846683873573490837 := by
  unfold tailWord_2011886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172438848661012452286939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48919673859525399745530341 9172438848661012452286939)
  ·
    refine ⟨13758658272991518678430409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9172438848661012452286939 13758658272991518678430409)
    ·
      refine ⟨10318993704743639008822807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13758658272991518678430409 10318993704743639008822807)
      ·
        refine ⟨15478490557115458513234211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318993704743639008822807 15478490557115458513234211)
        ·
          refine ⟨23217735835673187769851317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478490557115458513234211 23217735835673187769851317)
          ·
            refine ⟨2176662734594361353423561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23217735835673187769851317 2176662734594361353423561)
            ·
              refine ⟨1632497050945771015067671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176662734594361353423561 1632497050945771015067671)
              ·
                refine ⟨2448745576418656522601507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632497050945771015067671 2448745576418656522601507)
                ·
                  refine ⟨3673118364627984783902261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2448745576418656522601507 3673118364627984783902261)
                  ·
                    refine ⟨344354846683873573490837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3673118364627984783902261 344354846683873573490837)
                    ·
                      rfl

theorem cell23_2011886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2011886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011886 prefixEnd_2011886 := by exact prefixLift 2011886
  have htrace : WordTrace (prefixWord ++ tailWord_2011886) baseStart_2011886 baseEnd_2011886 := by
    simpa [prefixWord, tailWord_2011886, baseEnd_2011886] using wordTrace_append hprefix tailTrace_2011886
  have hstable : (prefixWord ++ tailWord_2011886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011886).length < 2 ^ (prefixWord ++ tailWord_2011886).sum := by decide
  have hdescent : baseEnd_2011886 < baseStart_2011886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011889 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_2011889 : Nat := 118140960795 + 2011889 * 2 ^ 59
def prefixEnd_2011889 : Nat := 4983230072969 + 3 ^ 40 * 2011889 * 2
def baseEnd_2011889 : Nat := 1033066080493584208734997

theorem tailTrace_2011889 : CollatzResearch.WordTrace tailWord_2011889 prefixEnd_2011889 1033066080493584208734997 := by
  unfold tailWord_2011889
  simp only [CollatzResearch.WordTrace]
  refine ⟨73379620208277231130654721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48919746805518154087103147 73379620208277231130654721)
  ·
    refine ⟨55034715156207923347991041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73379620208277231130654721 55034715156207923347991041)
    ·
      refine ⟨41276036367155942510993281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55034715156207923347991041 41276036367155942510993281)
      ·
        refine ⟨30957027275366956883244961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41276036367155942510993281 30957027275366956883244961)
        ·
          refine ⟨23217770456525217662433721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30957027275366956883244961 23217770456525217662433721)
          ·
            refine ⟨17413327842393913246825291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23217770456525217662433721 17413327842393913246825291)
            ·
              refine ⟨26119991763590869870237937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17413327842393913246825291 26119991763590869870237937)
              ·
                refine ⟨19589993822693152402678453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26119991763590869870237937 19589993822693152402678453)
                ·
                  refine ⟨1836561920877483037751105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19589993822693152402678453 1836561920877483037751105)
                  ·
                    refine ⟨1377421440658112278313329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1836561920877483037751105 1377421440658112278313329)
                    ·
                      refine ⟨1033066080493584208734997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377421440658112278313329 1033066080493584208734997)
                      ·
                        rfl

theorem cell23_2011889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_2011889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011889 prefixEnd_2011889 := by exact prefixLift 2011889
  have htrace : WordTrace (prefixWord ++ tailWord_2011889) baseStart_2011889 baseEnd_2011889 := by
    simpa [prefixWord, tailWord_2011889, baseEnd_2011889] using wordTrace_append hprefix tailTrace_2011889
  have hstable : (prefixWord ++ tailWord_2011889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011889).length < 2 ^ (prefixWord ++ tailWord_2011889).sum := by decide
  have hdescent : baseEnd_2011889 < baseStart_2011889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011905 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2011905 : Nat := 118140960795 + 2011905 * 2 ^ 59
def prefixEnd_2011905 : Nat := 4983230072969 + 3 ^ 40 * 2011905 * 2
def baseEnd_2011905 : Nat := 1033074296184056146134923

theorem tailTrace_2011905 : CollatzResearch.WordTrace tailWord_2011905 prefixEnd_2011905 1033074296184056146134923 := by
  unfold tailWord_2011905
  simp only [CollatzResearch.WordTrace]
  refine ⟨73380203776219265863237169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48920135850812843908824779 73380203776219265863237169)
  ·
    refine ⟨55035152832164449397427877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73380203776219265863237169 55035152832164449397427877)
    ·
      refine ⟨10319091156030834262017727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55035152832164449397427877 10319091156030834262017727)
      ·
        refine ⟨15478636734046251393026591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10319091156030834262017727 15478636734046251393026591)
        ·
          refine ⟨23217955101069377089539887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478636734046251393026591 23217955101069377089539887)
          ·
            refine ⟨34826932651604065634309831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23217955101069377089539887 34826932651604065634309831)
            ·
              refine ⟨52240398977406098451464747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34826932651604065634309831 52240398977406098451464747)
              ·
                refine ⟨78360598466109147677197121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52240398977406098451464747 78360598466109147677197121)
                ·
                  refine ⟨58770448849581860757897841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78360598466109147677197121 58770448849581860757897841)
                  ·
                    refine ⟨44077836637186395568423381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58770448849581860757897841 44077836637186395568423381)
                    ·
                      refine ⟨1033074296184056146134923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44077836637186395568423381 1033074296184056146134923)
                      ·
                        rfl

theorem cell23_2011905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2011905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011905 prefixEnd_2011905 := by exact prefixLift 2011905
  have htrace : WordTrace (prefixWord ++ tailWord_2011905) baseStart_2011905 baseEnd_2011905 := by
    simpa [prefixWord, tailWord_2011905, baseEnd_2011905] using wordTrace_append hprefix tailTrace_2011905
  have hstable : (prefixWord ++ tailWord_2011905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011905).length < 2 ^ (prefixWord ++ tailWord_2011905).sum := by decide
  have hdescent : baseEnd_2011905 < baseStart_2011905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011946 : List Nat := [3, 1, 4, 3, 2, 1, 9]
def baseStart_2011946 : Nat := 118140960795 + 2011946 * 2 ^ 59
def prefixEnd_2011946 : Nat := 4983230072969 + 3 ^ 40 * 2011946 * 2
def baseEnd_2011946 : Nat := 12754263566554203527435

theorem tailTrace_2011946 : CollatzResearch.WordTrace tailWord_2011946 prefixEnd_2011946 12754263566554203527435 := by
  unfold tailWord_2011946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345424792267682466369923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48921132779380486576986461 18345424792267682466369923)
  ·
    refine ⟨27518137188401523699554885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18345424792267682466369923 27518137188401523699554885)
    ·
      refine ⟨5159650722825285693666541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27518137188401523699554885 5159650722825285693666541)
      ·
        refine ⟨1934869021059482135124953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5159650722825285693666541 1934869021059482135124953)
        ·
          refine ⟨1451151765794611601343715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934869021059482135124953 1451151765794611601343715)
          ·
            refine ⟨2176727648691917402015573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451151765794611601343715 2176727648691917402015573)
            ·
              refine ⟨12754263566554203527435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2176727648691917402015573 12754263566554203527435)
              ·
                rfl

theorem cell23_2011946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 9].length) (baseStart_2011946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011946 prefixEnd_2011946 := by exact prefixLift 2011946
  have htrace : WordTrace (prefixWord ++ tailWord_2011946) baseStart_2011946 baseEnd_2011946 := by
    simpa [prefixWord, tailWord_2011946, baseEnd_2011946] using wordTrace_append hprefix tailTrace_2011946
  have hstable : (prefixWord ++ tailWord_2011946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011946).length < 2 ^ (prefixWord ++ tailWord_2011946).sum := by decide
  have hdescent : baseEnd_2011946 < baseStart_2011946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011995 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_2011995 : Nat := 118140960795 + 2011995 * 2 ^ 59
def prefixEnd_2011995 : Nat := 4983230072969 + 3 ^ 40 * 2011995 * 2
def baseEnd_2011995 : Nat := 1033120509442960794009509

theorem tailTrace_2011995 : CollatzResearch.WordTrace tailWord_2011995 prefixEnd_2011995 1033120509442960794009509 := by
  unfold tailWord_2011995
  simp only [CollatzResearch.WordTrace]
  refine ⟨73383486345893211234013439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48922324230595474156008959 73383486345893211234013439)
  ·
    refine ⟨110075229518839816851020159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73383486345893211234013439 110075229518839816851020159)
    ·
      refine ⟨165112844278259725276530239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110075229518839816851020159 165112844278259725276530239)
      ·
        refine ⟨247669266417389587914795359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165112844278259725276530239 247669266417389587914795359)
        ·
          refine ⟨371503899626084381872193039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247669266417389587914795359 371503899626084381872193039)
          ·
            refine ⟨557255849439126572808289559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371503899626084381872193039 557255849439126572808289559)
            ·
              refine ⟨835883774158689859212434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557255849439126572808289559 835883774158689859212434339)
              ·
                refine ⟨1253825661238034788818651509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835883774158689859212434339 1253825661238034788818651509)
                ·
                  refine ⟨117546155741065761451748579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1253825661238034788818651509 117546155741065761451748579)
                  ·
                    refine ⟨176319233611598642177622869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117546155741065761451748579 176319233611598642177622869)
                    ·
                      refine ⟨1033120509442960794009509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 176319233611598642177622869 1033120509442960794009509)
                      ·
                        rfl

theorem cell23_2011995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_2011995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011995 prefixEnd_2011995 := by exact prefixLift 2011995
  have htrace : WordTrace (prefixWord ++ tailWord_2011995) baseStart_2011995 baseEnd_2011995 := by
    simpa [prefixWord, tailWord_2011995, baseEnd_2011995] using wordTrace_append hprefix tailTrace_2011995
  have hstable : (prefixWord ++ tailWord_2011995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011995).length < 2 ^ (prefixWord ++ tailWord_2011995).sum := by decide
  have hdescent : baseEnd_2011995 < baseStart_2011995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011996 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2011996 : Nat := 118140960795 + 2011996 * 2 ^ 59
def prefixEnd_2011996 : Nat := 4983230072969 + 3 ^ 40 * 2011996 * 2
def baseEnd_2011996 : Nat := 1033121022923615290097005

theorem tailTrace_2011996 : CollatzResearch.WordTrace tailWord_2011996 prefixEnd_2011996 1033121022923615290097005 := by
  unfold tailWord_2011996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691761409444794202399921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48922348545926392269866561 36691761409444794202399921)
  ·
    refine ⟨27518821057083595651799941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36691761409444794202399921 27518821057083595651799941)
    ·
      refine ⟨5159778948203174184712489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27518821057083595651799941 5159778948203174184712489)
      ·
        refine ⟨3869834211152380638534367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5159778948203174184712489 3869834211152380638534367)
        ·
          refine ⟨5804751316728570957801551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869834211152380638534367 5804751316728570957801551)
          ·
            refine ⟨8707126975092856436702327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804751316728570957801551 8707126975092856436702327)
            ·
              refine ⟨13060690462639284655053491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707126975092856436702327 13060690462639284655053491)
              ·
                refine ⟨19591035693958926982580237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060690462639284655053491 19591035693958926982580237)
                ·
                  refine ⟨7346638385234597618467589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19591035693958926982580237 7346638385234597618467589)
                  ·
                    refine ⟨1377494697231487053462673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346638385234597618467589 1377494697231487053462673)
                    ·
                      refine ⟨1033121022923615290097005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377494697231487053462673 1033121022923615290097005)
                      ·
                        rfl

theorem cell23_2011996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2011996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2011996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2011996 prefixEnd_2011996 := by exact prefixLift 2011996
  have htrace : WordTrace (prefixWord ++ tailWord_2011996) baseStart_2011996 baseEnd_2011996 := by
    simpa [prefixWord, tailWord_2011996, baseEnd_2011996] using wordTrace_append hprefix tailTrace_2011996
  have hstable : (prefixWord ++ tailWord_2011996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011996).length < 2 ^ (prefixWord ++ tailWord_2011996).sum := by decide
  have hdescent : baseEnd_2011996 < baseStart_2011996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012030 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2012030 : Nat := 118140960795 + 2012030 * 2 ^ 59
def prefixEnd_2012030 : Nat := 4983230072969 + 3 ^ 40 * 2012030 * 2
def baseEnd_2012030 : Nat := 1033138481265868157071849

theorem tailTrace_2012030 : CollatzResearch.WordTrace tailWord_2012030 prefixEnd_2012030 1033138481265868157071849 := by
  unfold tailWord_2012030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9173095362595801526442193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48923175267177608141025029 9173095362595801526442193)
  ·
    refine ⟨6879821521946851144831645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9173095362595801526442193 6879821521946851144831645)
    ·
      refine ⟨2579933070730069179311867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6879821521946851144831645 2579933070730069179311867)
      ·
        refine ⟨3869899606095103768967801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579933070730069179311867 3869899606095103768967801)
        ·
          refine ⟨2902424704571327826725851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3869899606095103768967801 2902424704571327826725851)
          ·
            refine ⟨4353637056856991740088777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902424704571327826725851 4353637056856991740088777)
            ·
              refine ⟨3265227792642743805066583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4353637056856991740088777 3265227792642743805066583)
              ·
                refine ⟨4897841688964115707599875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265227792642743805066583 4897841688964115707599875)
                ·
                  refine ⟨7346762533446173561399813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897841688964115707599875 7346762533446173561399813)
                  ·
                    refine ⟨1377517975021157542762465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346762533446173561399813 1377517975021157542762465)
                    ·
                      refine ⟨1033138481265868157071849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377517975021157542762465 1033138481265868157071849)
                      ·
                        rfl

theorem cell23_2012030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2012030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012030 prefixEnd_2012030 := by exact prefixLift 2012030
  have htrace : WordTrace (prefixWord ++ tailWord_2012030) baseStart_2012030 baseEnd_2012030 := by
    simpa [prefixWord, tailWord_2012030, baseEnd_2012030] using wordTrace_append hprefix tailTrace_2012030
  have hstable : (prefixWord ++ tailWord_2012030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012030).length < 2 ^ (prefixWord ++ tailWord_2012030).sum := by decide
  have hdescent : baseEnd_2012030 < baseStart_2012030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012089 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2012089 : Nat := 118140960795 + 2012089 * 2 ^ 59
def prefixEnd_2012089 : Nat := 4983230072969 + 3 ^ 40 * 2012089 * 2
def baseEnd_2012089 : Nat := 1033168776624483426234077

theorem tailTrace_2012089 : CollatzResearch.WordTrace tailWord_2012089 prefixEnd_2012089 1033168776624483426234077 := by
  unfold tailWord_2012089
  simp only [CollatzResearch.WordTrace]
  refine ⟨73386914807552665287935321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48924609871701776858623547 73386914807552665287935321)
  ·
    refine ⟨55040186105664498965951491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73386914807552665287935321 55040186105664498965951491)
    ·
      refine ⟨82560279158496748448927237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55040186105664498965951491 82560279158496748448927237)
      ·
        refine ⟨15480052342218140334173857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82560279158496748448927237 15480052342218140334173857)
        ·
          refine ⟨11610039256663605250630393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15480052342218140334173857 11610039256663605250630393)
          ·
            refine ⟨8707529442497703937972795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11610039256663605250630393 8707529442497703937972795)
            ·
              refine ⟨13061294163746555906959193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707529442497703937972795 13061294163746555906959193)
              ·
                refine ⟨9795970622809916930219395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13061294163746555906959193 9795970622809916930219395)
                ·
                  refine ⟨14693955934214875395329093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9795970622809916930219395 14693955934214875395329093)
                  ·
                    refine ⟨2755116737665289136624205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14693955934214875395329093 2755116737665289136624205)
                    ·
                      refine ⟨1033168776624483426234077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755116737665289136624205 1033168776624483426234077)
                      ·
                        rfl

theorem cell23_2012089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2012089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012089 prefixEnd_2012089 := by exact prefixLift 2012089
  have htrace : WordTrace (prefixWord ++ tailWord_2012089) baseStart_2012089 baseEnd_2012089 := by
    simpa [prefixWord, tailWord_2012089, baseEnd_2012089] using wordTrace_append hprefix tailTrace_2012089
  have hstable : (prefixWord ++ tailWord_2012089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012089).length < 2 ^ (prefixWord ++ tailWord_2012089).sum := by decide
  have hdescent : baseEnd_2012089 < baseStart_2012089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012130 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2012130 : Nat := 118140960795 + 2012130 * 2 ^ 59
def prefixEnd_2012130 : Nat := 4983230072969 + 3 ^ 40 * 2012130 * 2
def baseEnd_2012130 : Nat := 344396609777105921940463

theorem tailTrace_2012130 : CollatzResearch.WordTrace tailWord_2012130 prefixEnd_2012130 344396609777105921940463 := by
  unfold tailWord_2012130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347102550101032322544461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48925606800269419526785229 18347102550101032322544461)
  ·
    refine ⟨6880163456287887120954173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18347102550101032322544461 6880163456287887120954173)
    ·
      refine ⟨2580061296107957670357815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6880163456287887120954173 2580061296107957670357815)
      ·
        refine ⟨3870091944161936505536723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580061296107957670357815 3870091944161936505536723)
        ·
          refine ⟨5805137916242904758305085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870091944161936505536723 5805137916242904758305085)
          ·
            refine ⟨2176926718591089284364407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5805137916242904758305085 2176926718591089284364407)
            ·
              refine ⟨3265390077886633926546611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176926718591089284364407 3265390077886633926546611)
              ·
                refine ⟨4898085116829950889819917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265390077886633926546611 4898085116829950889819917)
                ·
                  refine ⟨1836781918811231583682469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4898085116829950889819917 1836781918811231583682469)
                  ·
                    refine ⟨344396609777105921940463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836781918811231583682469 344396609777105921940463)
                    ·
                      rfl

theorem cell23_2012130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2012130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012130 prefixEnd_2012130 := by exact prefixLift 2012130
  have htrace : WordTrace (prefixWord ++ tailWord_2012130) baseStart_2012130 baseEnd_2012130 := by
    simpa [prefixWord, tailWord_2012130, baseEnd_2012130] using wordTrace_append hprefix tailTrace_2012130
  have hstable : (prefixWord ++ tailWord_2012130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012130).length < 2 ^ (prefixWord ++ tailWord_2012130).sum := by decide
  have hdescent : baseEnd_2012130 < baseStart_2012130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012156 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_2012156 : Nat := 118140960795 + 2012156 * 2 ^ 59
def prefixEnd_2012156 : Nat := 4983230072969 + 3 ^ 40 * 2012156 * 2
def baseEnd_2012156 : Nat := 344401059942778221365423

theorem tailTrace_2012156 : CollatzResearch.WordTrace tailWord_2012156 prefixEnd_2012156 344401059942778221365423 := by
  unfold tailWord_2012156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36694679249154967865312161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48926238998873290487082881 36694679249154967865312161)
  ·
    refine ⟨27521009436866225898984121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36694679249154967865312161 27521009436866225898984121)
    ·
      refine ⟨20640757077649669424238091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27521009436866225898984121 20640757077649669424238091)
      ·
        refine ⟨30961135616474504136357137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20640757077649669424238091 30961135616474504136357137)
        ·
          refine ⟨23220851712355878102267853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30961135616474504136357137 23220851712355878102267853)
          ·
            refine ⟨8707819392133454288350445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23220851712355878102267853 8707819392133454288350445)
            ·
              refine ⟨3265432272050045358131417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8707819392133454288350445 3265432272050045358131417)
              ·
                refine ⟨2449074204037534018598563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265432272050045358131417 2449074204037534018598563)
                ·
                  refine ⟨3673611306056301027897845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449074204037534018598563 3673611306056301027897845)
                  ·
                    refine ⟨344401059942778221365423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3673611306056301027897845 344401059942778221365423)
                    ·
                      rfl

theorem cell23_2012156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_2012156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012156 prefixEnd_2012156 := by exact prefixLift 2012156
  have htrace : WordTrace (prefixWord ++ tailWord_2012156) baseStart_2012156 baseEnd_2012156 := by
    simpa [prefixWord, tailWord_2012156, baseEnd_2012156] using wordTrace_append hprefix tailTrace_2012156
  have hstable : (prefixWord ++ tailWord_2012156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012156).length < 2 ^ (prefixWord ++ tailWord_2012156).sum := by decide
  have hdescent : baseEnd_2012156 < baseStart_2012156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012169 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_2012169 : Nat := 118140960795 + 2012169 * 2 ^ 59
def prefixEnd_2012169 : Nat := 4983230072969 + 3 ^ 40 * 2012169 * 2
def baseEnd_2012169 : Nat := 344403285025614371077903

theorem tailTrace_2012169 : CollatzResearch.WordTrace tailWord_2012169 prefixEnd_2012169 344403285025614371077903 := by
  unfold tailWord_2012169
  simp only [CollatzResearch.WordTrace]
  refine ⟨73389832647262838950847561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48926555098175225967231707 73389832647262838950847561)
  ·
    refine ⟨55042374485447129213135671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73389832647262838950847561 55042374485447129213135671)
    ·
      refine ⟨82563561728170693819703507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55042374485447129213135671 82563561728170693819703507)
      ·
        refine ⟨123845342592256040729555261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82563561728170693819703507 123845342592256040729555261)
        ·
          refine ⟨46442003472096015273583223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123845342592256040729555261 46442003472096015273583223)
          ·
            refine ⟨69663005208144022910374835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46442003472096015273583223 69663005208144022910374835)
            ·
              refine ⟨104494507812216034365562253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69663005208144022910374835 104494507812216034365562253)
              ·
                refine ⟨39185440429581012887085845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104494507812216034365562253 39185440429581012887085845)
                ·
                  refine ⟨1836817520136609979082149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39185440429581012887085845 1836817520136609979082149)
                  ·
                    refine ⟨344403285025614371077903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836817520136609979082149 344403285025614371077903)
                    ·
                      rfl

theorem cell23_2012169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_2012169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012169 prefixEnd_2012169 := by exact prefixLift 2012169
  have htrace : WordTrace (prefixWord ++ tailWord_2012169) baseStart_2012169 baseEnd_2012169 := by
    simpa [prefixWord, tailWord_2012169, baseEnd_2012169] using wordTrace_append hprefix tailTrace_2012169
  have hstable : (prefixWord ++ tailWord_2012169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012169).length < 2 ^ (prefixWord ++ tailWord_2012169).sum := by decide
  have hdescent : baseEnd_2012169 < baseStart_2012169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012216 : List Nat := [2, 1, 2, 1, 5, 2, 3, 7]
def baseStart_2012216 : Nat := 118140960795 + 2012216 * 2 ^ 59
def prefixEnd_2012216 : Nat := 4983230072969 + 3 ^ 40 * 2012216 * 2
def baseEnd_2012216 : Nat := 38267925506207571457259

theorem tailTrace_2012216 : CollatzResearch.WordTrace tailWord_2012216 prefixEnd_2012216 38267925506207571457259 := by
  unfold tailWord_2012216
  simp only [CollatzResearch.WordTrace]
  refine ⟨36695773439046282988904251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48927697918728377318539001 36695773439046282988904251)
  ·
    refine ⟨55043660158569424483356377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36695773439046282988904251 55043660158569424483356377)
    ·
      refine ⟨41282745118927068362517283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55043660158569424483356377 41282745118927068362517283)
      ·
        refine ⟨61924117678390602543775925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41282745118927068362517283 61924117678390602543775925)
        ·
          refine ⟨5805386032349118988478993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61924117678390602543775925 5805386032349118988478993)
          ·
            refine ⟨4354039524261839241359245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5805386032349118988478993 4354039524261839241359245)
            ·
              refine ⟨1632764821598189715509717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4354039524261839241359245 1632764821598189715509717)
              ·
                refine ⟨38267925506207571457259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1632764821598189715509717 38267925506207571457259)
                ·
                  rfl

theorem cell23_2012216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 7].length) (baseStart_2012216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012216 prefixEnd_2012216 := by exact prefixLift 2012216
  have htrace : WordTrace (prefixWord ++ tailWord_2012216) baseStart_2012216 baseEnd_2012216 := by
    simpa [prefixWord, tailWord_2012216, baseEnd_2012216] using wordTrace_append hprefix tailTrace_2012216
  have hstable : (prefixWord ++ tailWord_2012216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012216).length < 2 ^ (prefixWord ++ tailWord_2012216).sum := by decide
  have hdescent : baseEnd_2012216 < baseStart_2012216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012249 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_2012249 : Nat := 118140960795 + 2012249 * 2 ^ 59
def prefixEnd_2012249 : Nat := 4983230072969 + 3 ^ 40 * 2012249 * 2
def baseEnd_2012249 : Nat := 1033250933529202800233341

theorem tailTrace_2012249 : CollatzResearch.WordTrace tailWord_2012249 prefixEnd_2012249 1033250933529202800233341 := by
  unfold tailWord_2012249
  simp only [CollatzResearch.WordTrace]
  refine ⟨73392750486973012613759801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48928500324648675075839867 73392750486973012613759801)
  ·
    refine ⟨55044562865229759460319851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73392750486973012613759801 55044562865229759460319851)
    ·
      refine ⟨82566844297844639190479777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55044562865229759460319851 82566844297844639190479777)
      ·
        refine ⟨61925133223383479392859833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82566844297844639190479777 61925133223383479392859833)
        ·
          refine ⟨46443849917537609544644875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61925133223383479392859833 46443849917537609544644875)
          ·
            refine ⟨69665774876306414316967313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46443849917537609544644875 69665774876306414316967313)
            ·
              refine ⟨52249331157229810737725485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69665774876306414316967313 52249331157229810737725485)
              ·
                refine ⟨19593499183961179026647057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52249331157229810737725485 19593499183961179026647057)
                ·
                  refine ⟨14695124387970884269985293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593499183961179026647057 14695124387970884269985293)
                  ·
                    refine ⟨5510671645489081601244485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14695124387970884269985293 5510671645489081601244485)
                    ·
                      refine ⟨1033250933529202800233341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5510671645489081601244485 1033250933529202800233341)
                      ·
                        rfl

theorem cell23_2012249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_2012249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012249 prefixEnd_2012249 := by exact prefixLift 2012249
  have htrace : WordTrace (prefixWord ++ tailWord_2012249) baseStart_2012249 baseEnd_2012249 := by
    simpa [prefixWord, tailWord_2012249, baseEnd_2012249] using wordTrace_append hprefix tailTrace_2012249
  have hstable : (prefixWord ++ tailWord_2012249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012249).length < 2 ^ (prefixWord ++ tailWord_2012249).sum := by decide
  have hdescent : baseEnd_2012249 < baseStart_2012249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012254 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2012254 : Nat := 118140960795 + 2012254 * 2 ^ 59
def prefixEnd_2012254 : Nat := 4983230072969 + 3 ^ 40 * 2012254 * 2
def baseEnd_2012254 : Nat := 344417833644158426890273

theorem tailTrace_2012254 : CollatzResearch.WordTrace tailWord_2012254 prefixEnd_2012254 344417833644158426890273 := by
  unfold tailWord_2012254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174116606494362308461477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48928621901303265645127877 9174116606494362308461477)
  ·
    refine ⟨1720146863717692932836527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9174116606494362308461477 1720146863717692932836527)
    ·
      refine ⟨2580220295576539399254791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720146863717692932836527 2580220295576539399254791)
      ·
        refine ⟨3870330443364809098882187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580220295576539399254791 3870330443364809098882187)
        ·
          refine ⟨5805495665047213648323281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870330443364809098882187 5805495665047213648323281)
          ·
            refine ⟨4354121748785410236242461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5805495665047213648323281 4354121748785410236242461)
            ·
              refine ⟨1632795655794528838590923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4354121748785410236242461 1632795655794528838590923)
              ·
                refine ⟨2449193483691793257886385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632795655794528838590923 2449193483691793257886385)
                ·
                  refine ⟨1836895112768844943414789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449193483691793257886385 1836895112768844943414789)
                  ·
                    refine ⟨344417833644158426890273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836895112768844943414789 344417833644158426890273)
                    ·
                      rfl

theorem cell23_2012254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2012254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012254 prefixEnd_2012254 := by exact prefixLift 2012254
  have htrace : WordTrace (prefixWord ++ tailWord_2012254) baseStart_2012254 baseEnd_2012254 := by
    simpa [prefixWord, tailWord_2012254, baseEnd_2012254] using wordTrace_append hprefix tailTrace_2012254
  have hstable : (prefixWord ++ tailWord_2012254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012254).length < 2 ^ (prefixWord ++ tailWord_2012254).sum := by decide
  have hdescent : baseEnd_2012254 < baseStart_2012254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012270 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_2012270 : Nat := 118140960795 + 2012270 * 2 ^ 59
def prefixEnd_2012270 : Nat := 4983230072969 + 3 ^ 40 * 2012270 * 2
def baseEnd_2012270 : Nat := 1033261716622947218070745

theorem tailTrace_2012270 : CollatzResearch.WordTrace tailWord_2012270 prefixEnd_2012270 1033261716622947218070745 := by
  unfold tailWord_2012270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174189552487116650034283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48929010946597955466849509 9174189552487116650034283)
  ·
    refine ⟨13761284328730674975051425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174189552487116650034283 13761284328730674975051425)
    ·
      refine ⟨10320963246548006231288569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13761284328730674975051425 10320963246548006231288569)
      ·
        refine ⟨7740722434911004673466427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10320963246548006231288569 7740722434911004673466427)
        ·
          refine ⟨11611083652366507010199641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740722434911004673466427 11611083652366507010199641)
          ·
            refine ⟨8708312739274880257649731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611083652366507010199641 8708312739274880257649731)
            ·
              refine ⟨13062469108912320386474597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708312739274880257649731 13062469108912320386474597)
              ·
                refine ⟨2449212957921060072463987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13062469108912320386474597 2449212957921060072463987)
                ·
                  refine ⟨3673819436881590108695981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449212957921060072463987 3673819436881590108695981)
                  ·
                    refine ⟨1377682288830596290760993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673819436881590108695981 1377682288830596290760993)
                    ·
                      refine ⟨1033261716622947218070745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377682288830596290760993 1033261716622947218070745)
                      ·
                        rfl

theorem cell23_2012270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_2012270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012270 prefixEnd_2012270 := by exact prefixLift 2012270
  have htrace : WordTrace (prefixWord ++ tailWord_2012270) baseStart_2012270 baseEnd_2012270 := by
    simpa [prefixWord, tailWord_2012270, baseEnd_2012270] using wordTrace_append hprefix tailTrace_2012270
  have hstable : (prefixWord ++ tailWord_2012270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012270).length < 2 ^ (prefixWord ++ tailWord_2012270).sum := by decide
  have hdescent : baseEnd_2012270 < baseStart_2012270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012309 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2012309 : Nat := 118140960795 + 2012309 * 2 ^ 59
def prefixEnd_2012309 : Nat := 4983230072969 + 3 ^ 40 * 2012309 * 2
def baseEnd_2012309 : Nat := 1033281742368472565483065

theorem tailTrace_2012309 : CollatzResearch.WordTrace tailWord_2012309 prefixEnd_2012309 1033281742368472565483065 := by
  unfold tailWord_2012309
  simp only [CollatzResearch.WordTrace]
  refine ⟨73394938866755642860943981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48929959244503761907295987 73394938866755642860943981)
  ·
    refine ⟨27523102075033366072853993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73394938866755642860943981 27523102075033366072853993)
    ·
      refine ⟨20642326556275024554640495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27523102075033366072853993 20642326556275024554640495)
      ·
        refine ⟨30963489834412536831960743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20642326556275024554640495 30963489834412536831960743)
        ·
          refine ⟨46445234751618805247941115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30963489834412536831960743 46445234751618805247941115)
          ·
            refine ⟨69667852127428207871911673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46445234751618805247941115 69667852127428207871911673)
            ·
              refine ⟨52250889095571155903933755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69667852127428207871911673 52250889095571155903933755)
              ·
                refine ⟨78376333643356733855900633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52250889095571155903933755 78376333643356733855900633)
                ·
                  refine ⟨58782250232517550391925475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78376333643356733855900633 58782250232517550391925475)
                  ·
                    refine ⟨88173375348776325587888213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58782250232517550391925475 88173375348776325587888213)
                    ·
                      refine ⟨1033281742368472565483065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88173375348776325587888213 1033281742368472565483065)
                      ·
                        rfl

theorem cell23_2012309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2012309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012309 prefixEnd_2012309 := by exact prefixLift 2012309
  have htrace : WordTrace (prefixWord ++ tailWord_2012309) baseStart_2012309 baseEnd_2012309 := by
    simpa [prefixWord, tailWord_2012309, baseEnd_2012309] using wordTrace_append hprefix tailTrace_2012309
  have hstable : (prefixWord ++ tailWord_2012309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012309).length < 2 ^ (prefixWord ++ tailWord_2012309).sum := by decide
  have hdescent : baseEnd_2012309 < baseStart_2012309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012329 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_2012329 : Nat := 118140960795 + 2012329 * 2 ^ 59
def prefixEnd_2012329 : Nat := 4983230072969 + 3 ^ 40 * 2012329 * 2
def baseEnd_2012329 : Nat := 1033292011981562487232973

theorem tailTrace_2012329 : CollatzResearch.WordTrace tailWord_2012329 prefixEnd_2012329 1033292011981562487232973 := by
  unfold tailWord_2012329
  simp only [CollatzResearch.WordTrace]
  refine ⟨73395668326683186276672041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48930445551122124184448027 73395668326683186276672041)
  ·
    refine ⟨55046751245012389707504031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73395668326683186276672041 55046751245012389707504031)
    ·
      refine ⟨82570126867518584561256047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55046751245012389707504031 82570126867518584561256047)
      ·
        refine ⟨123855190301277876841884071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82570126867518584561256047 123855190301277876841884071)
        ·
          refine ⟨185782785451916815262826107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123855190301277876841884071 185782785451916815262826107)
          ·
            refine ⟨278674178177875222894239161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185782785451916815262826107 278674178177875222894239161)
            ·
              refine ⟨209005633633406417170679371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278674178177875222894239161 209005633633406417170679371)
              ·
                refine ⟨313508450450109625756019057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209005633633406417170679371 313508450450109625756019057)
                ·
                  refine ⟨235131337837582219317014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313508450450109625756019057 235131337837582219317014293)
                  ·
                    refine ⟨11021781461136666530485045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 235131337837582219317014293 11021781461136666530485045)
                    ·
                      refine ⟨1033292011981562487232973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11021781461136666530485045 1033292011981562487232973)
                      ·
                        rfl

theorem cell23_2012329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_2012329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012329 prefixEnd_2012329 := by exact prefixLift 2012329
  have htrace : WordTrace (prefixWord ++ tailWord_2012329) baseStart_2012329 baseEnd_2012329 := by
    simpa [prefixWord, tailWord_2012329, baseEnd_2012329] using wordTrace_append hprefix tailTrace_2012329
  have hstable : (prefixWord ++ tailWord_2012329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012329).length < 2 ^ (prefixWord ++ tailWord_2012329).sum := by decide
  have hdescent : baseEnd_2012329 < baseStart_2012329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012430 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_2012430 : Nat := 118140960795 + 2012430 * 2 ^ 59
def prefixEnd_2012430 : Nat := 4983230072969 + 3 ^ 40 * 2012430 * 2
def baseEnd_2012430 : Nat := 114815985947518510230001

theorem tailTrace_2012430 : CollatzResearch.WordTrace tailWord_2012430 prefixEnd_2012430 114815985947518510230001 := by
  unfold tailWord_2012430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174919012414660065762343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48932901399544853684065829 9174919012414660065762343)
  ·
    refine ⟨13762378518621990098643515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174919012414660065762343 13762378518621990098643515)
    ·
      refine ⟨20643567777932985147965273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762378518621990098643515 20643567777932985147965273)
      ·
        refine ⟨15482675833449738860973955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20643567777932985147965273 15482675833449738860973955)
        ·
          refine ⟨23224013750174608291460933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482675833449738860973955 23224013750174608291460933)
          ·
            refine ⟨4354502578157739054648925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23224013750174608291460933 4354502578157739054648925)
            ·
              refine ⟨1632938466809152145493347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4354502578157739054648925 1632938466809152145493347)
              ·
                refine ⟨2449407700213728218240021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632938466809152145493347 2449407700213728218240021)
                ·
                  refine ⟨114815985947518510230001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2449407700213728218240021 114815985947518510230001)
                  ·
                    rfl

theorem cell23_2012430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_2012430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012430 prefixEnd_2012430 := by exact prefixLift 2012430
  have htrace : WordTrace (prefixWord ++ tailWord_2012430) baseStart_2012430 baseEnd_2012430 := by
    simpa [prefixWord, tailWord_2012430, baseEnd_2012430] using wordTrace_append hprefix tailTrace_2012430
  have hstable : (prefixWord ++ tailWord_2012430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012430).length < 2 ^ (prefixWord ++ tailWord_2012430).sum := by decide
  have hdescent : baseEnd_2012430 < baseStart_2012430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012433 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_2012433 : Nat := 118140960795 + 2012433 * 2 ^ 59
def prefixEnd_2012433 : Nat := 4983230072969 + 3 ^ 40 * 2012433 * 2
def baseEnd_2012433 : Nat := 1033345413969630080332495

theorem tailTrace_2012433 : CollatzResearch.WordTrace tailWord_2012433 prefixEnd_2012433 1033345413969630080332495 := by
  unfold tailWord_2012433
  simp only [CollatzResearch.WordTrace]
  refine ⟨73399461518306412038457953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48932974345537608025638635 73399461518306412038457953)
  ·
    refine ⟨55049596138729809028843465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73399461518306412038457953 55049596138729809028843465)
    ·
      refine ⟨41287197104047356771632599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55049596138729809028843465 41287197104047356771632599)
      ·
        refine ⟨61930795656071035157448899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41287197104047356771632599 61930795656071035157448899)
        ·
          refine ⟨92896193484106552736173349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61930795656071035157448899 92896193484106552736173349)
          ·
            refine ⟨17418036278269978638032503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92896193484106552736173349 17418036278269978638032503)
            ·
              refine ⟨26127054417404967957048755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17418036278269978638032503 26127054417404967957048755)
              ·
                refine ⟨39190581626107451935573133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26127054417404967957048755 39190581626107451935573133)
                ·
                  refine ⟨14696468109790294475839925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39190581626107451935573133 14696468109790294475839925)
                  ·
                    refine ⟨1377793885292840107109993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14696468109790294475839925 1377793885292840107109993)
                    ·
                      refine ⟨1033345413969630080332495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377793885292840107109993 1033345413969630080332495)
                      ·
                        rfl

theorem cell23_2012433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_2012433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012433 prefixEnd_2012433 := by exact prefixLift 2012433
  have htrace : WordTrace (prefixWord ++ tailWord_2012433) baseStart_2012433 baseEnd_2012433 := by
    simpa [prefixWord, tailWord_2012433, baseEnd_2012433] using wordTrace_append hprefix tailTrace_2012433
  have hstable : (prefixWord ++ tailWord_2012433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012433).length < 2 ^ (prefixWord ++ tailWord_2012433).sum := by decide
  have hdescent : baseEnd_2012433 < baseStart_2012433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012440 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2012440 : Nat := 118140960795 + 2012440 * 2 ^ 59
def prefixEnd_2012440 : Nat := 4983230072969 + 3 ^ 40 * 2012440 * 2
def baseEnd_2012440 : Nat := 1033349008334211552944963

theorem tailTrace_2012440 : CollatzResearch.WordTrace tailWord_2012440 prefixEnd_2012440 1033349008334211552944963 := by
  unfold tailWord_2012440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36699858414640526116981387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48933144552854034822641849 36699858414640526116981387)
  ·
    refine ⟨55049787621960789175472081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36699858414640526116981387 55049787621960789175472081)
    ·
      refine ⟨41287340716470591881604061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55049787621960789175472081 41287340716470591881604061)
      ·
        refine ⟨15482752768676471955601523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41287340716470591881604061 15482752768676471955601523)
        ·
          refine ⟨23224129153014707933402285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15482752768676471955601523 23224129153014707933402285)
          ·
            refine ⟨8709048432380515475025857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23224129153014707933402285 8709048432380515475025857)
            ·
              refine ⟨6531786324285386606269393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8709048432380515475025857 6531786324285386606269393)
              ·
                refine ⟨4898839743214039954702045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6531786324285386606269393 4898839743214039954702045)
                ·
                  refine ⟨1837064903705264983013267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4898839743214039954702045 1837064903705264983013267)
                  ·
                    refine ⟨2755597355557897474519901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1837064903705264983013267 2755597355557897474519901)
                    ·
                      refine ⟨1033349008334211552944963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755597355557897474519901 1033349008334211552944963)
                      ·
                        rfl

theorem cell23_2012440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2012440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012440 prefixEnd_2012440 := by exact prefixLift 2012440
  have htrace : WordTrace (prefixWord ++ tailWord_2012440) baseStart_2012440 baseEnd_2012440 := by
    simpa [prefixWord, tailWord_2012440, baseEnd_2012440] using wordTrace_append hprefix tailTrace_2012440
  have hstable : (prefixWord ++ tailWord_2012440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012440).length < 2 ^ (prefixWord ++ tailWord_2012440).sum := by decide
  have hdescent : baseEnd_2012440 < baseStart_2012440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012474 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3]
def baseStart_2012474 : Nat := 118140960795 + 2012474 * 2 ^ 59
def prefixEnd_2012474 : Nat := 4983230072969 + 3 ^ 40 * 2012474 * 2
def baseEnd_2012474 : Nat := 1033366466676464419919807

theorem tailTrace_2012474 : CollatzResearch.WordTrace tailWord_2012474 prefixEnd_2012474 1033366466676464419919807 := by
  unfold tailWord_2012474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350239227789469010175119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48933971274105250693800317 18350239227789469010175119)
  ·
    refine ⟨27525358841684203515262679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18350239227789469010175119 27525358841684203515262679)
    ·
      refine ⟨41288038262526305272894019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27525358841684203515262679 41288038262526305272894019)
      ·
        refine ⟨61932057393789457909341029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41288038262526305272894019 61932057393789457909341029)
        ·
          refine ⟨11612260761335523358001443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61932057393789457909341029 11612260761335523358001443)
          ·
            refine ⟨17418391142003285037002165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612260761335523358001443 17418391142003285037002165)
            ·
              refine ⟨1632974169562807972218953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17418391142003285037002165 1632974169562807972218953)
              ·
                refine ⟨1224730627172105979164215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632974169562807972218953 1224730627172105979164215)
                ·
                  refine ⟨1837095940758158968746323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224730627172105979164215 1837095940758158968746323)
                  ·
                    refine ⟨2755643911137238453119485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1837095940758158968746323 2755643911137238453119485)
                    ·
                      refine ⟨1033366466676464419919807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755643911137238453119485 1033366466676464419919807)
                      ·
                        rfl

theorem cell23_2012474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_2012474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012474 prefixEnd_2012474 := by exact prefixLift 2012474
  have htrace : WordTrace (prefixWord ++ tailWord_2012474) baseStart_2012474 baseEnd_2012474 := by
    simpa [prefixWord, tailWord_2012474, baseEnd_2012474] using wordTrace_append hprefix tailTrace_2012474
  have hstable : (prefixWord ++ tailWord_2012474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012474).length < 2 ^ (prefixWord ++ tailWord_2012474).sum := by decide
  have hdescent : baseEnd_2012474 < baseStart_2012474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012483 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3]
def baseStart_2012483 : Nat := 118140960795 + 2012483 * 2 ^ 59
def prefixEnd_2012483 : Nat := 4983230072969 + 3 ^ 40 * 2012483 * 2
def baseEnd_2012483 : Nat := 1033371088002354884707265

theorem tailTrace_2012483 : CollatzResearch.WordTrace tailWord_2012483 prefixEnd_2012483 1033371088002354884707265 := by
  unfold tailWord_2012483
  simp only [CollatzResearch.WordTrace]
  refine ⟨73401285168125270577778103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48934190112083513718518735 73401285168125270577778103)
  ·
    refine ⟨110101927752187905866667155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73401285168125270577778103 110101927752187905866667155)
    ·
      refine ⟨165152891628281858800000733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110101927752187905866667155 165152891628281858800000733)
      ·
        refine ⟨61932334360605697050000275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165152891628281858800000733 61932334360605697050000275)
        ·
          refine ⟨92898501540908545575000413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61932334360605697050000275 92898501540908545575000413)
          ·
            refine ⟨34836938077840704590625155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92898501540908545575000413 34836938077840704590625155)
            ·
              refine ⟨52255407116761056885937733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34836938077840704590625155 52255407116761056885937733)
              ·
                refine ⟨9797888834392698166113325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52255407116761056885937733 9797888834392698166113325)
                ·
                  refine ⟨3674208312897261812292497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9797888834392698166113325 3674208312897261812292497)
                  ·
                    refine ⟨2755656234672946359219373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3674208312897261812292497 2755656234672946359219373)
                    ·
                      refine ⟨1033371088002354884707265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755656234672946359219373 1033371088002354884707265)
                      ·
                        rfl

theorem cell23_2012483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_2012483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012483 prefixEnd_2012483 := by exact prefixLift 2012483
  have htrace : WordTrace (prefixWord ++ tailWord_2012483) baseStart_2012483 baseEnd_2012483 := by
    simpa [prefixWord, tailWord_2012483, baseEnd_2012483] using wordTrace_append hprefix tailTrace_2012483
  have hstable : (prefixWord ++ tailWord_2012483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012483).length < 2 ^ (prefixWord ++ tailWord_2012483).sum := by decide
  have hdescent : baseEnd_2012483 < baseStart_2012483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012500 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2012500 : Nat := 118140960795 + 2012500 * 2 ^ 59
def prefixEnd_2012500 : Nat := 4983230072969 + 3 ^ 40 * 2012500 * 2
def baseEnd_2012500 : Nat := 1033379817173481318194687

theorem tailTrace_2012500 : CollatzResearch.WordTrace tailWord_2012500 prefixEnd_2012500 1033379817173481318194687 := by
  unfold tailWord_2012500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36700952604531841240573477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48934603472709121654097969 36700952604531841240573477)
  ·
    refine ⟨6881428613349720232607527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36700952604531841240573477 6881428613349720232607527)
    ·
      refine ⟨10322142920024580348911291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6881428613349720232607527 10322142920024580348911291)
      ·
        refine ⟨15483214380036870523366937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322142920024580348911291 15483214380036870523366937)
        ·
          refine ⟨11612410785027652892525203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15483214380036870523366937 11612410785027652892525203)
          ·
            refine ⟨17418616177541479338787805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11612410785027652892525203 17418616177541479338787805)
            ·
              refine ⟨6531981066578054752045427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17418616177541479338787805 6531981066578054752045427)
              ·
                refine ⟨9797971599867082128068141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531981066578054752045427 9797971599867082128068141)
                ·
                  refine ⟨3674239349950155798025553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9797971599867082128068141 3674239349950155798025553)
                  ·
                    refine ⟨2755679512462616848519165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3674239349950155798025553 2755679512462616848519165)
                    ·
                      refine ⟨1033379817173481318194687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755679512462616848519165 1033379817173481318194687)
                      ·
                        rfl

theorem cell23_2012500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2012500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012500 prefixEnd_2012500 := by exact prefixLift 2012500
  have htrace : WordTrace (prefixWord ++ tailWord_2012500) baseStart_2012500 baseEnd_2012500 := by
    simpa [prefixWord, tailWord_2012500, baseEnd_2012500] using wordTrace_append hprefix tailTrace_2012500
  have hstable : (prefixWord ++ tailWord_2012500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012500).length < 2 ^ (prefixWord ++ tailWord_2012500).sum := by decide
  have hdescent : baseEnd_2012500 < baseStart_2012500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012517 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_2012517 : Nat := 118140960795 + 2012517 * 2 ^ 59
def prefixEnd_2012517 : Nat := 4983230072969 + 3 ^ 40 * 2012517 * 2
def baseEnd_2012517 : Nat := 1033388546344607751682109

theorem tailTrace_2012517 : CollatzResearch.WordTrace tailWord_2012517 prefixEnd_2012517 1033388546344607751682109 := by
  unfold tailWord_2012517
  simp only [CollatzResearch.WordTrace]
  refine ⟨73402525250002094384515805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48935016833334729589677203 73402525250002094384515805)
  ·
    refine ⟨27525946968750785394193427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73402525250002094384515805 27525946968750785394193427)
    ·
      refine ⟨41288920453126178091290141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27525946968750785394193427 41288920453126178091290141)
      ·
        refine ⟨15483345169922316784233803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41288920453126178091290141 15483345169922316784233803)
        ·
          refine ⟨23225017754883475176350705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483345169922316784233803 23225017754883475176350705)
          ·
            refine ⟨17418763316162606382263029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23225017754883475176350705 17418763316162606382263029)
            ·
              refine ⟨1633009060890244348337159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17418763316162606382263029 1633009060890244348337159)
              ·
                refine ⟨2449513591335366522505739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633009060890244348337159 2449513591335366522505739)
                ·
                  refine ⟨3674270387003049783758609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449513591335366522505739 3674270387003049783758609)
                  ·
                    refine ⟨2755702790252287337818957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3674270387003049783758609 2755702790252287337818957)
                    ·
                      refine ⟨1033388546344607751682109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755702790252287337818957 1033388546344607751682109)
                      ·
                        rfl

theorem cell23_2012517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_2012517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012517 prefixEnd_2012517 := by exact prefixLift 2012517
  have htrace : WordTrace (prefixWord ++ tailWord_2012517) baseStart_2012517 baseEnd_2012517 := by
    simpa [prefixWord, tailWord_2012517, baseEnd_2012517] using wordTrace_append hprefix tailTrace_2012517
  have hstable : (prefixWord ++ tailWord_2012517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012517).length < 2 ^ (prefixWord ++ tailWord_2012517).sum := by decide
  have hdescent : baseEnd_2012517 < baseStart_2012517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012540 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_2012540 : Nat := 118140960795 + 2012540 * 2 ^ 59
def prefixEnd_2012540 : Nat := 4983230072969 + 3 ^ 40 * 2012540 * 2
def baseEnd_2012540 : Nat := 1033400356399661161694503

theorem tailTrace_2012540 : CollatzResearch.WordTrace tailWord_2012540 prefixEnd_2012540 1033400356399661161694503 := by
  unfold tailWord_2012540
  simp only [CollatzResearch.WordTrace]
  refine ⟨36701682064459384656301537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48935576085945846208402049 36701682064459384656301537)
  ·
    refine ⟨27526261548344538492226153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36701682064459384656301537 27526261548344538492226153)
    ·
      refine ⟨20644696161258403869169615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27526261548344538492226153 20644696161258403869169615)
      ·
        refine ⟨30967044241887605803754423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20644696161258403869169615 30967044241887605803754423)
        ·
          refine ⟨46450566362831408705631635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30967044241887605803754423 46450566362831408705631635)
          ·
            refine ⟨69675849544247113058447453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46450566362831408705631635 69675849544247113058447453)
            ·
              refine ⟨26128443579092667396917795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69675849544247113058447453 26128443579092667396917795)
              ·
                refine ⟨39192665368639001095376693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26128443579092667396917795 39192665368639001095376693)
                ·
                  refine ⟨3674312378309906352691565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39192665368639001095376693 3674312378309906352691565)
                  ·
                    refine ⟨1377867141866214882259337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674312378309906352691565 1377867141866214882259337)
                    ·
                      refine ⟨1033400356399661161694503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1377867141866214882259337 1033400356399661161694503)
                      ·
                        rfl

theorem cell23_2012540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_2012540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012540 prefixEnd_2012540 := by exact prefixLift 2012540
  have htrace : WordTrace (prefixWord ++ tailWord_2012540) baseStart_2012540 baseEnd_2012540 := by
    simpa [prefixWord, tailWord_2012540, baseEnd_2012540] using wordTrace_append hprefix tailTrace_2012540
  have hstable : (prefixWord ++ tailWord_2012540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012540).length < 2 ^ (prefixWord ++ tailWord_2012540).sum := by decide
  have hdescent : baseEnd_2012540 < baseStart_2012540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012547 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 3]
def baseStart_2012547 : Nat := 118140960795 + 2012547 * 2 ^ 59
def prefixEnd_2012547 : Nat := 4983230072969 + 3 ^ 40 * 2012547 * 2
def baseEnd_2012547 : Nat := 1033403950764242634306971

theorem tailTrace_2012547 : CollatzResearch.WordTrace tailWord_2012547 prefixEnd_2012547 1033403950764242634306971 := by
  unfold tailWord_2012547
  simp only [CollatzResearch.WordTrace]
  refine ⟨73403619439893409508107895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48935746293262273005405263 73403619439893409508107895)
  ·
    refine ⟨110105429159840114262161843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73403619439893409508107895 110105429159840114262161843)
    ·
      refine ⟨165158143739760171393242765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110105429159840114262161843 165158143739760171393242765)
      ·
        refine ⟨61934303902410064272466037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165158143739760171393242765 61934303902410064272466037)
        ·
          refine ⟨5806340990850943525543691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61934303902410064272466037 5806340990850943525543691)
          ·
            refine ⟨8709511486276415288315537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806340990850943525543691 8709511486276415288315537)
            ·
              refine ⟨6532133614707311466236653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8709511486276415288315537 6532133614707311466236653)
              ·
                refine ⟨2449550105515241799838745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6532133614707311466236653 2449550105515241799838745)
                ·
                  refine ⟨1837162579136431349879059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449550105515241799838745 1837162579136431349879059)
                  ·
                    refine ⟨2755743868704647024818589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1837162579136431349879059 2755743868704647024818589)
                    ·
                      refine ⟨1033403950764242634306971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755743868704647024818589 1033403950764242634306971)
                      ·
                        rfl

theorem cell23_2012547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_2012547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012547 prefixEnd_2012547 := by exact prefixLift 2012547
  have htrace : WordTrace (prefixWord ++ tailWord_2012547) baseStart_2012547 baseEnd_2012547 := by
    simpa [prefixWord, tailWord_2012547, baseEnd_2012547] using wordTrace_append hprefix tailTrace_2012547
  have hstable : (prefixWord ++ tailWord_2012547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012547).length < 2 ^ (prefixWord ++ tailWord_2012547).sum := by decide
  have hdescent : baseEnd_2012547 < baseStart_2012547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012623 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 7]
def baseStart_2012623 : Nat := 118140960795 + 2012623 * 2 ^ 59
def prefixEnd_2012623 : Nat := 4983230072969 + 3 ^ 40 * 2012623 * 2
def baseEnd_2012623 : Nat := 344480991764661445652207

theorem tailTrace_2012623 : CollatzResearch.WordTrace tailWord_2012623 prefixEnd_2012623 344480991764661445652207 := by
  unfold tailWord_2012623
  simp only [CollatzResearch.WordTrace]
  refine ⟨73406391387618074487874523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48937594258412049658583015 73406391387618074487874523)
  ·
    refine ⟨110109587081427111731811785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73406391387618074487874523 110109587081427111731811785)
    ·
      refine ⟨82582190311070333798858839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110109587081427111731811785 82582190311070333798858839)
      ·
        refine ⟨123873285466605500698288259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82582190311070333798858839 123873285466605500698288259)
        ·
          refine ⟨185809928199908251047432389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123873285466605500698288259 185809928199908251047432389)
          ·
            refine ⟨34839361537482797071393573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185809928199908251047432389 34839361537482797071393573)
            ·
              refine ⟨6532380288278024450886295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34839361537482797071393573 6532380288278024450886295)
              ·
                refine ⟨9798570432417036676329443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6532380288278024450886295 9798570432417036676329443)
                ·
                  refine ⟨14697855648625555014494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798570432417036676329443 14697855648625555014494165)
                  ·
                    refine ⟨344480991764661445652207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14697855648625555014494165 344480991764661445652207)
                    ·
                      rfl

theorem cell23_2012623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_2012623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012623 prefixEnd_2012623 := by exact prefixLift 2012623
  have htrace : WordTrace (prefixWord ++ tailWord_2012623) baseStart_2012623 baseEnd_2012623 := by
    simpa [prefixWord, tailWord_2012623, baseEnd_2012623] using wordTrace_append hprefix tailTrace_2012623
  have hstable : (prefixWord ++ tailWord_2012623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012623).length < 2 ^ (prefixWord ++ tailWord_2012623).sum := by decide
  have hdescent : baseEnd_2012623 < baseStart_2012623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012674 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2012674 : Nat := 118140960795 + 2012674 * 2 ^ 59
def prefixEnd_2012674 : Nat := 4983230072969 + 3 ^ 40 * 2012674 * 2
def baseEnd_2012674 : Nat := 344489720935787879139629

theorem tailTrace_2012674 : CollatzResearch.WordTrace tailWord_2012674 prefixEnd_2012674 344489720935787879139629 := by
  unfold tailWord_2012674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352062877608327549495269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48938834340288873465320717 18352062877608327549495269)
  ·
    refine ⟨3441011789551561415530363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18352062877608327549495269 3441011789551561415530363)
    ·
      refine ⟨5161517684327342123295545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441011789551561415530363 5161517684327342123295545)
      ·
        refine ⟨3871138263245506592471659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5161517684327342123295545 3871138263245506592471659)
        ·
          refine ⟨5806707394868259888707489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871138263245506592471659 5806707394868259888707489)
          ·
            refine ⟨4355030546151194916530617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5806707394868259888707489 4355030546151194916530617)
            ·
              refine ⟨3266272909613396187397963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355030546151194916530617 3266272909613396187397963)
              ·
                refine ⟨4899409364420094281096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266272909613396187397963 4899409364420094281096945)
                ·
                  refine ⟨3674557023315070710822709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4899409364420094281096945 3674557023315070710822709)
                  ·
                    refine ⟨344489720935787879139629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3674557023315070710822709 344489720935787879139629)
                    ·
                      rfl

theorem cell23_2012674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2012674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012674 prefixEnd_2012674 := by exact prefixLift 2012674
  have htrace : WordTrace (prefixWord ++ tailWord_2012674) baseStart_2012674 baseEnd_2012674 := by
    simpa [prefixWord, tailWord_2012674, baseEnd_2012674] using wordTrace_append hprefix tailTrace_2012674
  have hstable : (prefixWord ++ tailWord_2012674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012674).length < 2 ^ (prefixWord ++ tailWord_2012674).sum := by decide
  have hdescent : baseEnd_2012674 < baseStart_2012674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012680 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_2012680 : Nat := 118140960795 + 2012680 * 2 ^ 59
def prefixEnd_2012680 : Nat := 4983230072969 + 3 ^ 40 * 2012680 * 2
def baseEnd_2012680 : Nat := 1033472243691290613943859

theorem tailTrace_2012680 : CollatzResearch.WordTrace tailWord_2012680 prefixEnd_2012680 1033472243691290613943859 := by
  unfold tailWord_2012680
  simp only [CollatzResearch.WordTrace]
  refine ⟨36704235174205786611349747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48938980232274382148466329 36704235174205786611349747)
  ·
    refine ⟨55056352761308679917024621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36704235174205786611349747 55056352761308679917024621)
    ·
      refine ⟨20646132285490754968884233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55056352761308679917024621 20646132285490754968884233)
      ·
        refine ⟨15484599214118066226663175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20646132285490754968884233 15484599214118066226663175)
        ·
          refine ⟨23226898821177099339994763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15484599214118066226663175 23226898821177099339994763)
          ·
            refine ⟨34840348231765649009992145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23226898821177099339994763 34840348231765649009992145)
            ·
              refine ⟨26130261173824236757494109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34840348231765649009992145 26130261173824236757494109)
              ·
                refine ⟨9798847940184088784060291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26130261173824236757494109 9798847940184088784060291)
                ·
                  refine ⟨14698271910276133176090437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9798847940184088784060291 14698271910276133176090437)
                  ·
                    refine ⟨2755925983176774970516957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14698271910276133176090437 2755925983176774970516957)
                    ·
                      refine ⟨1033472243691290613943859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755925983176774970516957 1033472243691290613943859)
                      ·
                        rfl

theorem cell23_2012680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_2012680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012680 prefixEnd_2012680 := by exact prefixLift 2012680
  have htrace : WordTrace (prefixWord ++ tailWord_2012680) baseStart_2012680 baseEnd_2012680 := by
    simpa [prefixWord, tailWord_2012680, baseEnd_2012680] using wordTrace_append hprefix tailTrace_2012680
  have hstable : (prefixWord ++ tailWord_2012680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012680).length < 2 ^ (prefixWord ++ tailWord_2012680).sum := by decide
  have hdescent : baseEnd_2012680 < baseStart_2012680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012727 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_2012727 : Nat := 118140960795 + 2012727 * 2 ^ 59
def prefixEnd_2012727 : Nat := 4983230072969 + 3 ^ 40 * 2012727 * 2
def baseEnd_2012727 : Nat := 1033496377282051930056143

theorem tailTrace_2012727 : CollatzResearch.WordTrace tailWord_2012727 prefixEnd_2012727 1033496377282051930056143 := by
  unfold tailWord_2012727
  simp only [CollatzResearch.WordTrace]
  refine ⟨73410184579241300249660435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48940123052827533499773623 73410184579241300249660435)
  ·
    refine ⟨110115276868861950374490653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73410184579241300249660435 110115276868861950374490653)
    ·
      refine ⟨41293228825823231390433995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110115276868861950374490653 41293228825823231390433995)
      ·
        refine ⟨61939843238734847085650993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41293228825823231390433995 61939843238734847085650993)
        ·
          refine ⟨46454882429051135314238245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61939843238734847085650993 46454882429051135314238245)
          ·
            refine ⟨8710290455447087871419671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46454882429051135314238245 8710290455447087871419671)
            ·
              refine ⟨13065435683170631807129507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710290455447087871419671 13065435683170631807129507)
              ·
                refine ⟨19598153524755947710694261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065435683170631807129507 19598153524755947710694261)
                ·
                  refine ⟨1837326892945870097877587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19598153524755947710694261 1837326892945870097877587)
                  ·
                    refine ⟨2755990339418805146816381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1837326892945870097877587 2755990339418805146816381)
                    ·
                      refine ⟨1033496377282051930056143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2755990339418805146816381 1033496377282051930056143)
                      ·
                        rfl

theorem cell23_2012727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_2012727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012727 prefixEnd_2012727 := by exact prefixLift 2012727
  have htrace : WordTrace (prefixWord ++ tailWord_2012727) baseStart_2012727 baseEnd_2012727 := by
    simpa [prefixWord, tailWord_2012727, baseEnd_2012727] using wordTrace_append hprefix tailTrace_2012727
  have hstable : (prefixWord ++ tailWord_2012727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012727).length < 2 ^ (prefixWord ++ tailWord_2012727).sum := by decide
  have hdescent : baseEnd_2012727 < baseStart_2012727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012730 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_2012730 : Nat := 118140960795 + 2012730 * 2 ^ 59
def prefixEnd_2012730 : Nat := 4983230072969 + 3 ^ 40 * 2012730 * 2
def baseEnd_2012730 : Nat := 344499305908005139439543

theorem tailTrace_2012730 : CollatzResearch.WordTrace tailWord_2012730 prefixEnd_2012730 344499305908005139439543 := by
  unfold tailWord_2012730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352573499557607940504911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48940195998820287841346429 18352573499557607940504911)
  ·
    refine ⟨27528860249336411910757367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18352573499557607940504911 27528860249336411910757367)
    ·
      refine ⟨41293290374004617866136051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27528860249336411910757367 41293290374004617866136051)
      ·
        refine ⟨61939935561006926799204077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41293290374004617866136051 61939935561006926799204077)
        ·
          refine ⟨23227475835377597549701529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61939935561006926799204077 23227475835377597549701529)
          ·
            refine ⟨17420606876533198162276147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23227475835377597549701529 17420606876533198162276147)
            ·
              refine ⟨26130910314799797243414221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17420606876533198162276147 26130910314799797243414221)
              ·
                refine ⟨9799091368049923966280333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26130910314799797243414221 9799091368049923966280333)
                ·
                  refine ⟨3674659263018721487355125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9799091368049923966280333 3674659263018721487355125)
                  ·
                    refine ⟨344499305908005139439543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3674659263018721487355125 344499305908005139439543)
                    ·
                      rfl

theorem cell23_2012730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_2012730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012730 prefixEnd_2012730 := by exact prefixLift 2012730
  have htrace : WordTrace (prefixWord ++ tailWord_2012730) baseStart_2012730 baseEnd_2012730 := by
    simpa [prefixWord, tailWord_2012730, baseEnd_2012730] using wordTrace_append hprefix tailTrace_2012730
  have hstable : (prefixWord ++ tailWord_2012730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012730).length < 2 ^ (prefixWord ++ tailWord_2012730).sum := by decide
  have hdescent : baseEnd_2012730 < baseStart_2012730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012777 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_2012777 : Nat := 118140960795 + 2012777 * 2 ^ 59
def prefixEnd_2012777 : Nat := 4983230072969 + 3 ^ 40 * 2012777 * 2
def baseEnd_2012777 : Nat := 344507350438258911476971

theorem tailTrace_2012777 : CollatzResearch.WordTrace tailWord_2012777 prefixEnd_2012777 344507350438258911476971 := by
  unfold tailWord_2012777
  simp only [CollatzResearch.WordTrace]
  refine ⟨73412008229060158788980585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48941338819373439192653723 73412008229060158788980585)
  ·
    refine ⟨55059006171795119091735439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73412008229060158788980585 55059006171795119091735439)
    ·
      refine ⟨82588509257692678637603159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55059006171795119091735439 82588509257692678637603159)
      ·
        refine ⟨123882763886539017956404739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82588509257692678637603159 123882763886539017956404739)
        ·
          refine ⟨185824145829808526934607109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123882763886539017956404739 185824145829808526934607109)
          ·
            refine ⟨34842027343089098800238833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185824145829808526934607109 34842027343089098800238833)
            ·
              refine ⟨26131520507316824100179125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34842027343089098800238833 26131520507316824100179125)
              ·
                refine ⟨2449830047560952259391793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26131520507316824100179125 2449830047560952259391793)
                ·
                  refine ⟨1837372535670714194543845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449830047560952259391793 1837372535670714194543845)
                  ·
                    refine ⟨344507350438258911476971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1837372535670714194543845 344507350438258911476971)
                    ·
                      rfl

theorem cell23_2012777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_2012777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012777 prefixEnd_2012777 := by exact prefixLift 2012777
  have htrace : WordTrace (prefixWord ++ tailWord_2012777) baseStart_2012777 baseEnd_2012777 := by
    simpa [prefixWord, tailWord_2012777, baseEnd_2012777] using wordTrace_append hprefix tailTrace_2012777
  have hstable : (prefixWord ++ tailWord_2012777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012777).length < 2 ^ (prefixWord ++ tailWord_2012777).sum := by decide
  have hdescent : baseEnd_2012777 < baseStart_2012777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012784 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_2012784 : Nat := 118140960795 + 2012784 * 2 ^ 59
def prefixEnd_2012784 : Nat := 4983230072969 + 3 ^ 40 * 2012784 * 2
def baseEnd_2012784 : Nat := 1033525645679358207043381

theorem tailTrace_2012784 : CollatzResearch.WordTrace tailWord_2012784 prefixEnd_2012784 1033525645679358207043381 := by
  unfold tailWord_2012784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706131770017399492242703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48941509026689865989656937 36706131770017399492242703)
  ·
    refine ⟨55059197655026099238364055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36706131770017399492242703 55059197655026099238364055)
    ·
      refine ⟨82588796482539148857546083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55059197655026099238364055 82588796482539148857546083)
      ·
        refine ⟨123883194723808723286319125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82588796482539148857546083 123883194723808723286319125)
        ·
          refine ⟨5807024752678533904046209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123883194723808723286319125 5807024752678533904046209)
          ·
            refine ⟨4355268564508900428034657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5807024752678533904046209 4355268564508900428034657)
            ·
              refine ⟨3266451423381675321025993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355268564508900428034657 3266451423381675321025993)
              ·
                refine ⟨2449838567536256490769495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266451423381675321025993 2449838567536256490769495)
                ·
                  refine ⟨3674757851304384736154243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449838567536256490769495 3674757851304384736154243)
                  ·
                    refine ⟨5512136776956577104231365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3674757851304384736154243 5512136776956577104231365)
                    ·
                      refine ⟨1033525645679358207043381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5512136776956577104231365 1033525645679358207043381)
                      ·
                        rfl

theorem cell23_2012784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_2012784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012784 prefixEnd_2012784 := by exact prefixLift 2012784
  have htrace : WordTrace (prefixWord ++ tailWord_2012784) baseStart_2012784 baseEnd_2012784 := by
    simpa [prefixWord, tailWord_2012784, baseEnd_2012784] using wordTrace_append hprefix tailTrace_2012784
  have hstable : (prefixWord ++ tailWord_2012784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012784).length < 2 ^ (prefixWord ++ tailWord_2012784).sum := by decide
  have hdescent : baseEnd_2012784 < baseStart_2012784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012804 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2012804 : Nat := 118140960795 + 2012804 * 2 ^ 59
def prefixEnd_2012804 : Nat := 4983230072969 + 3 ^ 40 * 2012804 * 2
def baseEnd_2012804 : Nat := 1033535915292448128793289

theorem tailTrace_2012804 : CollatzResearch.WordTrace tailWord_2012804 prefixEnd_2012804 1033535915292448128793289 := by
  unfold tailWord_2012804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706496499981171200106733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48941995333308228266808977 36706496499981171200106733)
  ·
    refine ⟨13764936187492939200040025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36706496499981171200106733 13764936187492939200040025)
    ·
      refine ⟨10323702140619704400030019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13764936187492939200040025 10323702140619704400030019)
      ·
        refine ⟨15485553210929556600045029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10323702140619704400030019 15485553210929556600045029)
        ·
          refine ⟨2903541227049291862508443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15485553210929556600045029 2903541227049291862508443)
          ·
            refine ⟨4355311840573937793762665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903541227049291862508443 4355311840573937793762665)
            ·
              refine ⟨3266483880430453345321999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355311840573937793762665 3266483880430453345321999)
              ·
                refine ⟨4899725820645680017982999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266483880430453345321999 4899725820645680017982999)
                ·
                  refine ⟨7349588730968520026974499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4899725820645680017982999 7349588730968520026974499)
                  ·
                    refine ⟨11024383096452780040461749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7349588730968520026974499 11024383096452780040461749)
                    ·
                      refine ⟨1033535915292448128793289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11024383096452780040461749 1033535915292448128793289)
                      ·
                        rfl

theorem cell23_2012804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2012804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012804 prefixEnd_2012804 := by exact prefixLift 2012804
  have htrace : WordTrace (prefixWord ++ tailWord_2012804) baseStart_2012804 baseEnd_2012804 := by
    simpa [prefixWord, tailWord_2012804, baseEnd_2012804] using wordTrace_append hprefix tailTrace_2012804
  have hstable : (prefixWord ++ tailWord_2012804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012804).length < 2 ^ (prefixWord ++ tailWord_2012804).sum := by decide
  have hdescent : baseEnd_2012804 < baseStart_2012804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012828 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_2012828 : Nat := 118140960795 + 2012828 * 2 ^ 59
def prefixEnd_2012828 : Nat := 4983230072969 + 3 ^ 40 * 2012828 * 2
def baseEnd_2012828 : Nat := 344516079609385344964393

theorem tailTrace_2012828 : CollatzResearch.WordTrace tailWord_2012828 prefixEnd_2012828 344516079609385344964393 := by
  unfold tailWord_2012828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706934175937697249543569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48942578901250262999391425 36706934175937697249543569)
  ·
    refine ⟨27530200631953272937157677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36706934175937697249543569 27530200631953272937157677)
    ·
      refine ⟨10323825236982477351434129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27530200631953272937157677 10323825236982477351434129)
      ·
        refine ⟨7742868927736858013575597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10323825236982477351434129 7742868927736858013575597)
        ·
          refine ⟨2903575847901321755090849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7742868927736858013575597 2903575847901321755090849)
          ·
            refine ⟨2177681885925991316318137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2903575847901321755090849 2177681885925991316318137)
            ·
              refine ⟨1633261414444493487238603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2177681885925991316318137 1633261414444493487238603)
              ·
                refine ⟨2449892121666740230857905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633261414444493487238603 2449892121666740230857905)
                ·
                  refine ⟨1837419091250055173143429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449892121666740230857905 1837419091250055173143429)
                  ·
                    refine ⟨344516079609385344964393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1837419091250055173143429 344516079609385344964393)
                    ·
                      rfl

theorem cell23_2012828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_2012828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012828 prefixEnd_2012828 := by exact prefixLift 2012828
  have htrace : WordTrace (prefixWord ++ tailWord_2012828) baseStart_2012828 baseEnd_2012828 := by
    simpa [prefixWord, tailWord_2012828, baseEnd_2012828] using wordTrace_append hprefix tailTrace_2012828
  have hstable : (prefixWord ++ tailWord_2012828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012828).length < 2 ^ (prefixWord ++ tailWord_2012828).sum := by decide
  have hdescent : baseEnd_2012828 < baseStart_2012828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012884 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2012884 : Nat := 118140960795 + 2012884 * 2 ^ 59
def prefixEnd_2012884 : Nat := 4983230072969 + 3 ^ 40 * 2012884 * 2
def baseEnd_2012884 : Nat := 344525664581602605264307

theorem tailTrace_2012884 : CollatzResearch.WordTrace tailWord_2012884 prefixEnd_2012884 344525664581602605264307 := by
  unfold tailWord_2012884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36707955419836258031562853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48943940559781677375417137 36707955419836258031562853)
  ·
    refine ⟨6882741641219298380918035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36707955419836258031562853 6882741641219298380918035)
    ·
      refine ⟨10324112461828947571377053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6882741641219298380918035 10324112461828947571377053)
      ·
        refine ⟨3871542173185855339266395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10324112461828947571377053 3871542173185855339266395)
        ·
          refine ⟨5807313259778783008899593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871542173185855339266395 5807313259778783008899593)
          ·
            refine ⟨4355484944834087256674695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5807313259778783008899593 4355484944834087256674695)
            ·
              refine ⟨6533227417251130885012043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355484944834087256674695 6533227417251130885012043)
              ·
                refine ⟨9799841125876696327518065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533227417251130885012043 9799841125876696327518065)
                ·
                  refine ⟨7349880844407522245638549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799841125876696327518065 7349880844407522245638549)
                  ·
                    refine ⟨344525664581602605264307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7349880844407522245638549 344525664581602605264307)
                    ·
                      rfl

theorem cell23_2012884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2012884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012884 prefixEnd_2012884 := by exact prefixLift 2012884
  have htrace : WordTrace (prefixWord ++ tailWord_2012884) baseStart_2012884 baseEnd_2012884 := by
    simpa [prefixWord, tailWord_2012884, baseEnd_2012884] using wordTrace_append hprefix tailTrace_2012884
  have hstable : (prefixWord ++ tailWord_2012884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012884).length < 2 ^ (prefixWord ++ tailWord_2012884).sum := by decide
  have hdescent : baseEnd_2012884 < baseStart_2012884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012887 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2012887 : Nat := 118140960795 + 2012887 * 2 ^ 59
def prefixEnd_2012887 : Nat := 4983230072969 + 3 ^ 40 * 2012887 * 2
def baseEnd_2012887 : Nat := 1033578534186771304055407

theorem tailTrace_2012887 : CollatzResearch.WordTrace tailWord_2012887 prefixEnd_2012887 1033578534186771304055407 := by
  unfold tailWord_2012887
  simp only [CollatzResearch.WordTrace]
  refine ⟨73416020258661647575484915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48944013505774431716989943 73416020258661647575484915)
  ·
    refine ⟨110124030387992471363227373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73416020258661647575484915 110124030387992471363227373)
    ·
      refine ⟨41296511395497176761210265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110124030387992471363227373 41296511395497176761210265)
      ·
        refine ⟨30972383546622882570907699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41296511395497176761210265 30972383546622882570907699)
        ·
          refine ⟨46458575319934323856361549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30972383546622882570907699 46458575319934323856361549)
          ·
            refine ⟨17421965744975371446135581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46458575319934323856361549 17421965744975371446135581)
            ·
              refine ⟨6533237154365764292300843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17421965744975371446135581 6533237154365764292300843)
              ·
                refine ⟨9799855731548646438451265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533237154365764292300843 9799855731548646438451265)
                ·
                  refine ⟨7349891798661484828838449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9799855731548646438451265 7349891798661484828838449)
                  ·
                    refine ⟨5512418848996113621628837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7349891798661484828838449 5512418848996113621628837)
                    ·
                      refine ⟨1033578534186771304055407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5512418848996113621628837 1033578534186771304055407)
                      ·
                        rfl

theorem cell23_2012887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2012887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012887 prefixEnd_2012887 := by exact prefixLift 2012887
  have htrace : WordTrace (prefixWord ++ tailWord_2012887) baseStart_2012887 baseEnd_2012887 := by
    simpa [prefixWord, tailWord_2012887, baseEnd_2012887] using wordTrace_append hprefix tailTrace_2012887
  have hstable : (prefixWord ++ tailWord_2012887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012887).length < 2 ^ (prefixWord ++ tailWord_2012887).sum := by decide
  have hdescent : baseEnd_2012887 < baseStart_2012887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012927 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 2, 5]
def baseStart_2012927 : Nat := 118140960795 + 2012927 * 2 ^ 59
def prefixEnd_2012927 : Nat := 4983230072969 + 3 ^ 40 * 2012927 * 2
def baseEnd_2012927 : Nat := 344533024470983715851741

theorem tailTrace_2012927 : CollatzResearch.WordTrace tailWord_2012927 prefixEnd_2012927 344533024470983715851741 := by
  unfold tailWord_2012927
  simp only [CollatzResearch.WordTrace]
  refine ⟨73417479178516734406941035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48944986119011156271294023 73417479178516734406941035)
  ·
    refine ⟨110126218767775101610411553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73417479178516734406941035 110126218767775101610411553)
    ·
      refine ⟨82594664075831326207808665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110126218767775101610411553 82594664075831326207808665)
      ·
        refine ⟨61945998056873494655856499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82594664075831326207808665 61945998056873494655856499)
        ·
          refine ⟨92918997085310241983784749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61945998056873494655856499 92918997085310241983784749)
          ·
            refine ⟨34844623906991340743919281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92918997085310241983784749 34844623906991340743919281)
            ·
              refine ⟨26133467930243505557939461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34844623906991340743919281 26133467930243505557939461)
              ·
                refine ⟨4900025236920657292113649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26133467930243505557939461 4900025236920657292113649)
                ·
                  refine ⟨3675018927690492969085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900025236920657292113649 3675018927690492969085237)
                  ·
                    refine ⟨344533024470983715851741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3675018927690492969085237 344533024470983715851741)
                    ·
                      rfl

theorem cell23_2012927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_2012927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012927 prefixEnd_2012927 := by exact prefixLift 2012927
  have htrace : WordTrace (prefixWord ++ tailWord_2012927) baseStart_2012927 baseEnd_2012927 := by
    simpa [prefixWord, tailWord_2012927, baseEnd_2012927] using wordTrace_append hprefix tailTrace_2012927
  have hstable : (prefixWord ++ tailWord_2012927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012927).length < 2 ^ (prefixWord ++ tailWord_2012927).sum := by decide
  have hdescent : baseEnd_2012927 < baseStart_2012927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012947 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4]
def baseStart_2012947 : Nat := 118140960795 + 2012947 * 2 ^ 59
def prefixEnd_2012947 : Nat := 4983230072969 + 3 ^ 40 * 2012947 * 2
def baseEnd_2012947 : Nat := 1033609343026041069305131

theorem tailTrace_2012947 : CollatzResearch.WordTrace tailWord_2012947 prefixEnd_2012947 1033609343026041069305131 := by
  unfold tailWord_2012947
  simp only [CollatzResearch.WordTrace]
  refine ⟨73418208638444277822669095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48945472425629518548446063 73418208638444277822669095)
  ·
    refine ⟨110127312957666416734003643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73418208638444277822669095 110127312957666416734003643)
    ·
      refine ⟨165190969436499625101005465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110127312957666416734003643 165190969436499625101005465)
      ·
        refine ⟨123893227077374718825754099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165190969436499625101005465 123893227077374718825754099)
        ·
          refine ⟨185839840616062078238631149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123893227077374718825754099 185839840616062078238631149)
          ·
            refine ⟨69689940231023279339486681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185839840616062078238631149 69689940231023279339486681)
            ·
              refine ⟨52267455173267459504615011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69689940231023279339486681 52267455173267459504615011)
              ·
                refine ⟨78401182759901189256922517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52267455173267459504615011 78401182759901189256922517)
                ·
                  refine ⟨3675055441870368246418243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78401182759901189256922517 3675055441870368246418243)
                  ·
                    refine ⟨5512583162805552369627365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675055441870368246418243 5512583162805552369627365)
                    ·
                      refine ⟨1033609343026041069305131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5512583162805552369627365 1033609343026041069305131)
                      ·
                        rfl

theorem cell23_2012947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_2012947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012947 prefixEnd_2012947 := by exact prefixLift 2012947
  have htrace : WordTrace (prefixWord ++ tailWord_2012947) baseStart_2012947 baseEnd_2012947 := by
    simpa [prefixWord, tailWord_2012947, baseEnd_2012947] using wordTrace_append hprefix tailTrace_2012947
  have hstable : (prefixWord ++ tailWord_2012947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012947).length < 2 ^ (prefixWord ++ tailWord_2012947).sum := by decide
  have hdescent : baseEnd_2012947 < baseStart_2012947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012964 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2012964 : Nat := 118140960795 + 2012964 * 2 ^ 59
def prefixEnd_2012964 : Nat := 4983230072969 + 3 ^ 40 * 2012964 * 2
def baseEnd_2012964 : Nat := 1033618072197167502792553

theorem tailTrace_2012964 : CollatzResearch.WordTrace tailWord_2012964 prefixEnd_2012964 1033618072197167502792553 := by
  unfold tailWord_2012964
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709414339691344863018973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48945885786255126484025297 36709414339691344863018973)
  ·
    refine ⟨13766030377384254323632115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36709414339691344863018973 13766030377384254323632115)
    ·
      refine ⟨20649045566076381485448173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13766030377384254323632115 20649045566076381485448173)
      ·
        refine ⟨7743392087278643057043065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20649045566076381485448173 7743392087278643057043065)
        ·
          refine ⟨5807544065458982292782299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7743392087278643057043065 5807544065458982292782299)
          ·
            refine ⟨8711316098188473439173449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807544065458982292782299 8711316098188473439173449)
            ·
              refine ⟨6533487073641355079380087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8711316098188473439173449 6533487073641355079380087)
              ·
                refine ⟨9800230610462032619070131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533487073641355079380087 9800230610462032619070131)
                ·
                  refine ⟨14700345915693048928605197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9800230610462032619070131 14700345915693048928605197)
                  ·
                    refine ⟨5512629718384893348226949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14700345915693048928605197 5512629718384893348226949)
                    ·
                      refine ⟨1033618072197167502792553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5512629718384893348226949 1033618072197167502792553)
                      ·
                        rfl

theorem cell23_2012964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2012964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012964 prefixEnd_2012964 := by exact prefixLift 2012964
  have htrace : WordTrace (prefixWord ++ tailWord_2012964) baseStart_2012964 baseEnd_2012964 := by
    simpa [prefixWord, tailWord_2012964, baseEnd_2012964] using wordTrace_append hprefix tailTrace_2012964
  have hstable : (prefixWord ++ tailWord_2012964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012964).length < 2 ^ (prefixWord ++ tailWord_2012964).sum := by decide
  have hdescent : baseEnd_2012964 < baseStart_2012964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012981 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2012981 : Nat := 118140960795 + 2012981 * 2 ^ 59
def prefixEnd_2012981 : Nat := 4983230072969 + 3 ^ 40 * 2012981 * 2
def baseEnd_2012981 : Nat := 1033626801368293936279975

theorem tailTrace_2012981 : CollatzResearch.WordTrace tailWord_2012981 prefixEnd_2012981 1033626801368293936279975 := by
  unfold tailWord_2012981
  simp only [CollatzResearch.WordTrace]
  refine ⟨73419448720321101629406797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48946299146880734419604531 73419448720321101629406797)
  ·
    refine ⟨27532293270120413111027549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73419448720321101629406797 27532293270120413111027549)
    ·
      refine ⟨10324609976295154916635331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27532293270120413111027549 10324609976295154916635331)
      ·
        refine ⟨15486914964442732374952997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10324609976295154916635331 15486914964442732374952997)
        ·
          refine ⟨2903796555833012320303687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15486914964442732374952997 2903796555833012320303687)
          ·
            refine ⟨4355694833749518480455531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903796555833012320303687 4355694833749518480455531)
            ·
              refine ⟨6533542250624277720683297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355694833749518480455531 6533542250624277720683297)
              ·
                refine ⟨4900156687968208290512473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533542250624277720683297 4900156687968208290512473)
                ·
                  refine ⟨3675117515976156217884355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900156687968208290512473 3675117515976156217884355)
                  ·
                    refine ⟨5512676273964234326826533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675117515976156217884355 5512676273964234326826533)
                    ·
                      refine ⟨1033626801368293936279975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5512676273964234326826533 1033626801368293936279975)
                      ·
                        rfl

theorem cell23_2012981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2012981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012981 prefixEnd_2012981 := by exact prefixLift 2012981
  have htrace : WordTrace (prefixWord ++ tailWord_2012981) baseStart_2012981 baseEnd_2012981 := by
    simpa [prefixWord, tailWord_2012981, baseEnd_2012981] using wordTrace_append hprefix tailTrace_2012981
  have hstable : (prefixWord ++ tailWord_2012981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012981).length < 2 ^ (prefixWord ++ tailWord_2012981).sum := by decide
  have hdescent : baseEnd_2012981 < baseStart_2012981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012984 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_2012984 : Nat := 118140960795 + 2012984 * 2 ^ 59
def prefixEnd_2012984 : Nat := 4983230072969 + 3 ^ 40 * 2012984 * 2
def baseEnd_2012984 : Nat := 1033628341810257424542461

theorem tailTrace_2012984 : CollatzResearch.WordTrace tailWord_2012984 prefixEnd_2012984 1033628341810257424542461 := by
  unfold tailWord_2012984
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709779069655116570883003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48946372092873488761177337 36709779069655116570883003)
  ·
    refine ⟨55064668604482674856324505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36709779069655116570883003 55064668604482674856324505)
    ·
      refine ⟨41298501453362006142243379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55064668604482674856324505 41298501453362006142243379)
      ·
        refine ⟨61947752180043009213365069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41298501453362006142243379 61947752180043009213365069)
        ·
          refine ⟨23230407067516128455011901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61947752180043009213365069 23230407067516128455011901)
          ·
            refine ⟨8711402650318548170629463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23230407067516128455011901 8711402650318548170629463)
            ·
              refine ⟨13067103975477822255944195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8711402650318548170629463 13067103975477822255944195)
              ·
                refine ⟨19600655963216733383916293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13067103975477822255944195 19600655963216733383916293)
                ·
                  refine ⟨3675122993103137509484305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19600655963216733383916293 3675122993103137509484305)
                  ·
                    refine ⟨2756342244827353132113229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3675122993103137509484305 2756342244827353132113229)
                    ·
                      refine ⟨1033628341810257424542461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2756342244827353132113229 1033628341810257424542461)
                      ·
                        rfl

theorem cell23_2012984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_2012984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2012984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2012984 prefixEnd_2012984 := by exact prefixLift 2012984
  have htrace : WordTrace (prefixWord ++ tailWord_2012984) baseStart_2012984 baseEnd_2012984 := by
    simpa [prefixWord, tailWord_2012984, baseEnd_2012984] using wordTrace_append hprefix tailTrace_2012984
  have hstable : (prefixWord ++ tailWord_2012984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012984).length < 2 ^ (prefixWord ++ tailWord_2012984).sum := by decide
  have hdescent : baseEnd_2012984 < baseStart_2012984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013041 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_2013041 : Nat := 118140960795 + 2013041 * 2 ^ 59
def prefixEnd_2013041 : Nat := 4983230072969 + 3 ^ 40 * 2013041 * 2
def baseEnd_2013041 : Nat := 1033657610207563701529699

theorem tailTrace_2013041 : CollatzResearch.WordTrace tailWord_2013041 prefixEnd_2013041 1033657610207563701529699 := by
  unfold tailWord_2013041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73421637100103731876590977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48947758066735821251060651 73421637100103731876590977)
  ·
    refine ⟨55066227825077798907443233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73421637100103731876590977 55066227825077798907443233)
    ·
      refine ⟨41299670868808349180582425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55066227825077798907443233 41299670868808349180582425)
      ·
        refine ⟨30974753151606261885436819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41299670868808349180582425 30974753151606261885436819)
        ·
          refine ⟨46462129727409392828155229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30974753151606261885436819 46462129727409392828155229)
          ·
            refine ⟨17423298647778522310558211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46462129727409392828155229 17423298647778522310558211)
            ·
              refine ⟨26134947971667783465837317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17423298647778522310558211 26134947971667783465837317)
              ·
                refine ⟨4900302744687709399844497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26134947971667783465837317 4900302744687709399844497)
                ·
                  refine ⟨3675227058515782049883373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900302744687709399844497 3675227058515782049883373)
                  ·
                    refine ⟨1378210146943418268706265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675227058515782049883373 1378210146943418268706265)
                    ·
                      refine ⟨1033657610207563701529699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378210146943418268706265 1033657610207563701529699)
                      ·
                        rfl

theorem cell23_2013041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_2013041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013041 prefixEnd_2013041 := by exact prefixLift 2013041
  have htrace : WordTrace (prefixWord ++ tailWord_2013041) baseStart_2013041 baseEnd_2013041 := by
    simpa [prefixWord, tailWord_2013041, baseEnd_2013041] using wordTrace_append hprefix tailTrace_2013041
  have hstable : (prefixWord ++ tailWord_2013041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013041).length < 2 ^ (prefixWord ++ tailWord_2013041).sum := by decide
  have hdescent : baseEnd_2013041 < baseStart_2013041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013105 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2013105 : Nat := 118140960795 + 2013105 * 2 ^ 59
def prefixEnd_2013105 : Nat := 4983230072969 + 3 ^ 40 * 2013105 * 2
def baseEnd_2013105 : Nat := 1033690472969451451129405

theorem tailTrace_2013105 : CollatzResearch.WordTrace tailWord_2013105 prefixEnd_2013105 1033690472969451451129405 := by
  unfold tailWord_2013105
  simp only [CollatzResearch.WordTrace]
  refine ⟨73423971371871870806920769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48949314247914580537947179 73423971371871870806920769)
  ·
    refine ⟨55067978528903903105190577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73423971371871870806920769 55067978528903903105190577)
    ·
      refine ⟨41300983896677927328892933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55067978528903903105190577 41300983896677927328892933)
      ·
        refine ⟨7743934480627111374167425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41300983896677927328892933 7743934480627111374167425)
        ·
          refine ⟨5807950860470333530625569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7743934480627111374167425 5807950860470333530625569)
          ·
            refine ⟨4355963145352750147969177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5807950860470333530625569 4355963145352750147969177)
            ·
              refine ⟨3266972359014562610976883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4355963145352750147969177 3266972359014562610976883)
              ·
                refine ⟨4900458538521843916465325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266972359014562610976883 4900458538521843916465325)
                ·
                  refine ⟨1837671951945691468674497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4900458538521843916465325 1837671951945691468674497)
                  ·
                    refine ⟨1378253963959268601505873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1837671951945691468674497 1378253963959268601505873)
                    ·
                      refine ⟨1033690472969451451129405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378253963959268601505873 1033690472969451451129405)
                      ·
                        rfl

theorem cell23_2013105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2013105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013105 prefixEnd_2013105 := by exact prefixLift 2013105
  have htrace : WordTrace (prefixWord ++ tailWord_2013105) baseStart_2013105 baseEnd_2013105 := by
    simpa [prefixWord, tailWord_2013105, baseEnd_2013105] using wordTrace_append hprefix tailTrace_2013105
  have hstable : (prefixWord ++ tailWord_2013105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013105).length < 2 ^ (prefixWord ++ tailWord_2013105).sum := by decide
  have hdescent : baseEnd_2013105 < baseStart_2013105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013118 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2013118 : Nat := 118140960795 + 2013118 * 2 ^ 59
def prefixEnd_2013118 : Nat := 4983230072969 + 3 ^ 40 * 2013118 * 2
def baseEnd_2013118 : Nat := 1033697148217959900266845

theorem tailTrace_2013118 : CollatzResearch.WordTrace tailWord_2013118 prefixEnd_2013118 1033697148217959900266845 := by
  unfold tailWord_2013118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178055690103096753393001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48949630347216516018096005 9178055690103096753393001)
  ·
    refine ⟨6883541767577322565044751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9178055690103096753393001 6883541767577322565044751)
    ·
      refine ⟨10325312651365983847567127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883541767577322565044751 10325312651365983847567127)
      ·
        refine ⟨15487968977048975771350691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325312651365983847567127 15487968977048975771350691)
        ·
          refine ⟨23231953465573463657026037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15487968977048975771350691 23231953465573463657026037)
          ·
            refine ⟨2177995637397512217846191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23231953465573463657026037 2177995637397512217846191)
            ·
              refine ⟨3266993456096268326769287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177995637397512217846191 3266993456096268326769287)
              ·
                refine ⟨4900490184144402490153931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266993456096268326769287 4900490184144402490153931)
                ·
                  refine ⟨7350735276216603735230897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900490184144402490153931 7350735276216603735230897)
                  ·
                    refine ⟨5513051457162452801423173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7350735276216603735230897 5513051457162452801423173)
                    ·
                      refine ⟨1033697148217959900266845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5513051457162452801423173 1033697148217959900266845)
                      ·
                        rfl

theorem cell23_2013118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2013118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013118 prefixEnd_2013118 := by exact prefixLift 2013118
  have htrace : WordTrace (prefixWord ++ tailWord_2013118) baseStart_2013118 baseEnd_2013118 := by
    simpa [prefixWord, tailWord_2013118, baseEnd_2013118] using wordTrace_append hprefix tailTrace_2013118
  have hstable : (prefixWord ++ tailWord_2013118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013118).length < 2 ^ (prefixWord ++ tailWord_2013118).sum := by decide
  have hdescent : baseEnd_2013118 < baseStart_2013118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013134 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_2013134 : Nat := 118140960795 + 2013134 * 2 ^ 59
def prefixEnd_2013134 : Nat := 4983230072969 + 3 ^ 40 * 2013134 * 2
def baseEnd_2013134 : Nat := 1033705363908431837666771

theorem tailTrace_2013134 : CollatzResearch.WordTrace tailWord_2013134 prefixEnd_2013134 1033705363908431837666771 := by
  unfold tailWord_2013134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178128636095851094965807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48950019392511205839817637 9178128636095851094965807)
  ·
    refine ⟨13767192954143776642448711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9178128636095851094965807 13767192954143776642448711)
    ·
      refine ⟨20650789431215664963673067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13767192954143776642448711 20650789431215664963673067)
      ·
        refine ⟨30976184146823497445509601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20650789431215664963673067 30976184146823497445509601)
        ·
          refine ⟨23232138110117623084132201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30976184146823497445509601 23232138110117623084132201)
          ·
            refine ⟨17424103582588217313099151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23232138110117623084132201 17424103582588217313099151)
            ·
              refine ⟨26136155373882325969648727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17424103582588217313099151 26136155373882325969648727)
              ·
                refine ⟨39204233060823488954473091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26136155373882325969648727 39204233060823488954473091)
                ·
                  refine ⟨58806349591235233431709637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39204233060823488954473091 58806349591235233431709637)
                  ·
                    refine ⟨11026190548356606268445557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58806349591235233431709637 11026190548356606268445557)
                    ·
                      refine ⟨1033705363908431837666771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11026190548356606268445557 1033705363908431837666771)
                      ·
                        rfl

theorem cell23_2013134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_2013134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013134 prefixEnd_2013134 := by exact prefixLift 2013134
  have htrace : WordTrace (prefixWord ++ tailWord_2013134) baseStart_2013134 baseEnd_2013134 := by
    simpa [prefixWord, tailWord_2013134, baseEnd_2013134] using wordTrace_append hprefix tailTrace_2013134
  have hstable : (prefixWord ++ tailWord_2013134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013134).length < 2 ^ (prefixWord ++ tailWord_2013134).sum := by decide
  have hdescent : baseEnd_2013134 < baseStart_2013134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013182 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2013182 : Nat := 118140960795 + 2013182 * 2 ^ 59
def prefixEnd_2013182 : Nat := 4983230072969 + 3 ^ 40 * 2013182 * 2
def baseEnd_2013182 : Nat := 1033730010979847649866551

theorem tailTrace_2013182 : CollatzResearch.WordTrace tailWord_2013182 prefixEnd_2013182 1033730010979847649866551 := by
  unfold tailWord_2013182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178347474074114119684225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48951186528395275304982533 9178347474074114119684225)
  ·
    refine ⟨6883760605555585589763169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9178347474074114119684225 6883760605555585589763169)
    ·
      refine ⟨5162820454166689192322377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6883760605555585589763169 5162820454166689192322377)
      ·
        refine ⟨3872115340625016894241783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5162820454166689192322377 3872115340625016894241783)
        ·
          refine ⟨5808173010937525341362675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872115340625016894241783 5808173010937525341362675)
          ·
            refine ⟨8712259516406288012044013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808173010937525341362675 8712259516406288012044013)
            ·
              refine ⟨3267097318652358004516505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8712259516406288012044013 3267097318652358004516505)
              ·
                refine ⟨2450322988989268503387379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267097318652358004516505 2450322988989268503387379)
                ·
                  refine ⟨3675484483483902755081069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450322988989268503387379 3675484483483902755081069)
                  ·
                    refine ⟨1378306681306463533155401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3675484483483902755081069 1378306681306463533155401)
                    ·
                      refine ⟨1033730010979847649866551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378306681306463533155401 1033730010979847649866551)
                      ·
                        rfl

theorem cell23_2013182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2013182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013182 prefixEnd_2013182 := by exact prefixLift 2013182
  have htrace : WordTrace (prefixWord ++ tailWord_2013182) baseStart_2013182 baseEnd_2013182 := by
    simpa [prefixWord, tailWord_2013182, baseEnd_2013182] using wordTrace_append hprefix tailTrace_2013182
  have hstable : (prefixWord ++ tailWord_2013182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013182).length < 2 ^ (prefixWord ++ tailWord_2013182).sum := by decide
  have hdescent : baseEnd_2013182 < baseStart_2013182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013212 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_2013212 : Nat := 118140960795 + 2013212 * 2 ^ 59
def prefixEnd_2013212 : Nat := 4983230072969 + 3 ^ 40 * 2013212 * 2
def baseEnd_2013212 : Nat := 1033745415399482532491413

theorem tailTrace_2013212 : CollatzResearch.WordTrace tailWord_2013212 prefixEnd_2013212 1033745415399482532491413 := by
  unfold tailWord_2013212
  simp only [CollatzResearch.WordTrace]
  refine ⟨36713936991242114040532945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48951915988322818720710593 36713936991242114040532945)
  ·
    refine ⟨27535452743431585530399709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36713936991242114040532945 27535452743431585530399709)
    ·
      refine ⟨10325794778786844573899891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27535452743431585530399709 10325794778786844573899891)
      ·
        refine ⟨15488692168180266860849837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325794778786844573899891 15488692168180266860849837)
        ·
          refine ⟨5808259563067600072818689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15488692168180266860849837 5808259563067600072818689)
          ·
            refine ⟨4356194672300700054614017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808259563067600072818689 4356194672300700054614017)
            ·
              refine ⟨3267146004225525040960513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356194672300700054614017 3267146004225525040960513)
              ·
                refine ⟨2450359503169143780720385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267146004225525040960513 2450359503169143780720385)
                ·
                  refine ⟨1837769627376857835540289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2450359503169143780720385 1837769627376857835540289)
                  ·
                    refine ⟨1378327220532643376655217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1837769627376857835540289 1378327220532643376655217)
                    ·
                      refine ⟨1033745415399482532491413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378327220532643376655217 1033745415399482532491413)
                      ·
                        rfl

theorem cell23_2013212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_2013212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013212 prefixEnd_2013212 := by exact prefixLift 2013212
  have htrace : WordTrace (prefixWord ++ tailWord_2013212) baseStart_2013212 baseEnd_2013212 := by
    simpa [prefixWord, tailWord_2013212, baseEnd_2013212] using wordTrace_append hprefix tailTrace_2013212
  have hstable : (prefixWord ++ tailWord_2013212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013212).length < 2 ^ (prefixWord ++ tailWord_2013212).sum := by decide
  have hdescent : baseEnd_2013212 < baseStart_2013212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013218 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2013218 : Nat := 118140960795 + 2013218 * 2 ^ 59
def prefixEnd_2013218 : Nat := 4983230072969 + 3 ^ 40 * 2013218 * 2
def baseEnd_2013218 : Nat := 114860944031489945446265

theorem tailTrace_2013218 : CollatzResearch.WordTrace tailWord_2013218 prefixEnd_2013218 114860944031489945446265 := by
  unfold tailWord_2013218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357023205115622776446077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48952061880308327403856205 18357023205115622776446077)
  ·
    refine ⟨6883883701918358541167279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18357023205115622776446077 6883883701918358541167279)
    ·
      refine ⟨10325825552877537811750919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6883883701918358541167279 10325825552877537811750919)
      ·
        refine ⟨15488738329316306717626379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10325825552877537811750919 15488738329316306717626379)
        ·
          refine ⟨23233107493974460076439569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15488738329316306717626379 23233107493974460076439569)
          ·
            refine ⟨17424830620480845057329677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23233107493974460076439569 17424830620480845057329677)
            ·
              refine ⟨6534311482680316896498629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17424830620480845057329677 6534311482680316896498629)
              ·
                refine ⟨1225183403002559418093493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6534311482680316896498629 1225183403002559418093493)
                ·
                  refine ⟨114860944031489945446265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1225183403002559418093493 114860944031489945446265)
                  ·
                    rfl

theorem cell23_2013218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2013218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013218 prefixEnd_2013218 := by exact prefixLift 2013218
  have htrace : WordTrace (prefixWord ++ tailWord_2013218) baseStart_2013218 baseEnd_2013218 := by
    simpa [prefixWord, tailWord_2013218, baseEnd_2013218] using wordTrace_append hprefix tailTrace_2013218
  have hstable : (prefixWord ++ tailWord_2013218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013218).length < 2 ^ (prefixWord ++ tailWord_2013218).sum := by decide
  have hdescent : baseEnd_2013218 < baseStart_2013218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013248 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_2013248 : Nat := 118140960795 + 2013248 * 2 ^ 59
def prefixEnd_2013248 : Nat := 4983230072969 + 3 ^ 40 * 2013248 * 2
def baseEnd_2013248 : Nat := 344587966901014797213749

theorem tailTrace_2013248 : CollatzResearch.WordTrace tailWord_2013248 prefixEnd_2013248 344587966901014797213749 := by
  unfold tailWord_2013248
  simp only [CollatzResearch.WordTrace]
  refine ⟨36714593505176903114688199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48952791340235870819584265 36714593505176903114688199)
  ·
    refine ⟨55071890257765354672032299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36714593505176903114688199 55071890257765354672032299)
    ·
      refine ⟨82607835386648032008048449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55071890257765354672032299 82607835386648032008048449)
      ·
        refine ⟨61955876539986024006036337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82607835386648032008048449 61955876539986024006036337)
        ·
          refine ⟨46466907404989518004527253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61955876539986024006036337 46466907404989518004527253)
          ·
            refine ⟨2178136284608883656462215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46466907404989518004527253 2178136284608883656462215)
            ·
              refine ⟨3267204426913325484693323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178136284608883656462215 3267204426913325484693323)
              ·
                refine ⟨4900806640369988227039985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267204426913325484693323 4900806640369988227039985)
                ·
                  refine ⟨3675604980277491170279989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900806640369988227039985 3675604980277491170279989)
                  ·
                    refine ⟨344587966901014797213749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3675604980277491170279989 344587966901014797213749)
                    ·
                      rfl

theorem cell23_2013248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_2013248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013248 prefixEnd_2013248 := by exact prefixLift 2013248
  have htrace : WordTrace (prefixWord ++ tailWord_2013248) baseStart_2013248 baseEnd_2013248 := by
    simpa [prefixWord, tailWord_2013248, baseEnd_2013248] using wordTrace_append hprefix tailTrace_2013248
  have hstable : (prefixWord ++ tailWord_2013248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013248).length < 2 ^ (prefixWord ++ tailWord_2013248).sum := by decide
  have hdescent : baseEnd_2013248 < baseStart_2013248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013251 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4]
def baseStart_2013251 : Nat := 118140960795 + 2013251 * 2 ^ 59
def prefixEnd_2013251 : Nat := 4983230072969 + 3 ^ 40 * 2013251 * 2
def baseEnd_2013251 : Nat := 1033765441145007879903733

theorem tailTrace_2013251 : CollatzResearch.WordTrace tailWord_2013251 prefixEnd_2013251 1033765441145007879903733 := by
  unfold tailWord_2013251
  simp only [CollatzResearch.WordTrace]
  refine ⟨73429296429342937741735607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48952864286228625161157071 73429296429342937741735607)
  ·
    refine ⟨110143944644014406612603411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73429296429342937741735607 110143944644014406612603411)
    ·
      refine ⟨165215916966021609918905117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110143944644014406612603411 165215916966021609918905117)
      ·
        refine ⟨61955968862258103719589419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165215916966021609918905117 61955968862258103719589419)
        ·
          refine ⟨92933953293387155579384129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61955968862258103719589419 92933953293387155579384129)
          ·
            refine ⟨69700464970040366684538097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92933953293387155579384129 69700464970040366684538097)
            ·
              refine ⟨52275348727530275013403573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69700464970040366684538097 52275348727530275013403573)
              ·
                refine ⟨4900813943205963282506585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52275348727530275013403573 4900813943205963282506585)
                ·
                  refine ⟨3675610457404472461879939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4900813943205963282506585 3675610457404472461879939)
                  ·
                    refine ⟨5513415686106708692819909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675610457404472461879939 5513415686106708692819909)
                    ·
                      refine ⟨1033765441145007879903733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5513415686106708692819909 1033765441145007879903733)
                      ·
                        rfl

theorem cell23_2013251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_2013251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013251 prefixEnd_2013251 := by exact prefixLift 2013251
  have htrace : WordTrace (prefixWord ++ tailWord_2013251) baseStart_2013251 baseEnd_2013251 := by
    simpa [prefixWord, tailWord_2013251, baseEnd_2013251] using wordTrace_append hprefix tailTrace_2013251
  have hstable : (prefixWord ++ tailWord_2013251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013251).length < 2 ^ (prefixWord ++ tailWord_2013251).sum := by decide
  have hdescent : baseEnd_2013251 < baseStart_2013251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013372 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_2013372 : Nat := 118140960795 + 2013372 * 2 ^ 59
def prefixEnd_2013372 : Nat := 4983230072969 + 3 ^ 40 * 2013372 * 2
def baseEnd_2013372 : Nat := 344609190768067302163559

theorem tailTrace_2013372 : CollatzResearch.WordTrace tailWord_2013372 prefixEnd_2013372 344609190768067302163559 := by
  unfold tailWord_2013372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36716854830952287703445185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48955806441269716937926913 36716854830952287703445185)
  ·
    refine ⟨27537641123214215777583889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36716854830952287703445185 27537641123214215777583889)
    ·
      refine ⟨20653230842410661833187917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27537641123214215777583889 20653230842410661833187917)
      ·
        refine ⟨7744961565903998187445469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20653230842410661833187917 7744961565903998187445469)
        ·
          refine ⟨2904360587213999320292051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7744961565903998187445469 2904360587213999320292051)
          ·
            refine ⟨4356540880820998980438077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904360587213999320292051 4356540880820998980438077)
            ·
              refine ⟨1633702830307874617664279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4356540880820998980438077 1633702830307874617664279)
              ·
                refine ⟨2450554245461811926496419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633702830307874617664279 2450554245461811926496419)
                ·
                  refine ⟨3675831368192717889744629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450554245461811926496419 3675831368192717889744629)
                  ·
                    refine ⟨344609190768067302163559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3675831368192717889744629 344609190768067302163559)
                    ·
                      rfl

theorem cell23_2013372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_2013372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013372 prefixEnd_2013372 := by exact prefixLift 2013372
  have htrace : WordTrace (prefixWord ++ tailWord_2013372) baseStart_2013372 baseEnd_2013372 := by
    simpa [prefixWord, tailWord_2013372, baseEnd_2013372] using wordTrace_append hprefix tailTrace_2013372
  have hstable : (prefixWord ++ tailWord_2013372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013372).length < 2 ^ (prefixWord ++ tailWord_2013372).sum := by decide
  have hdescent : baseEnd_2013372 < baseStart_2013372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013401 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2013401 : Nat := 118140960795 + 2013401 * 2 ^ 59
def prefixEnd_2013401 : Nat := 4983230072969 + 3 ^ 40 * 2013401 * 2
def baseEnd_2013401 : Nat := 1033842463243182293028043

theorem tailTrace_2013401 : CollatzResearch.WordTrace tailWord_2013401 prefixEnd_2013401 1033842463243182293028043 := by
  unfold tailWord_2013401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73434767378799513359696057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48956511585866342239797371 73434767378799513359696057)
  ·
    refine ⟨55076075534099635019772043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73434767378799513359696057 55076075534099635019772043)
    ·
      refine ⟨82614113301149452529658065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55076075534099635019772043 82614113301149452529658065)
      ·
        refine ⟨61960584975862089397243549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82614113301149452529658065 61960584975862089397243549)
        ·
          refine ⟨23235219365948283523966331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61960584975862089397243549 23235219365948283523966331)
          ·
            refine ⟨34852829048922425285949497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23235219365948283523966331 34852829048922425285949497)
            ·
              refine ⟨26139621786691818964462123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34852829048922425285949497 26139621786691818964462123)
              ·
                refine ⟨39209432680037728446693185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26139621786691818964462123 39209432680037728446693185)
                ·
                  refine ⟨29407074510028296335019889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39209432680037728446693185 29407074510028296335019889)
                  ·
                    refine ⟨22055305882521222251264917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29407074510028296335019889 22055305882521222251264917)
                    ·
                      refine ⟨1033842463243182293028043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22055305882521222251264917 1033842463243182293028043)
                      ·
                        rfl

theorem cell23_2013401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2013401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013401 prefixEnd_2013401 := by exact prefixLift 2013401
  have htrace : WordTrace (prefixWord ++ tailWord_2013401) baseStart_2013401 baseEnd_2013401 := by
    simpa [prefixWord, tailWord_2013401, baseEnd_2013401] using wordTrace_append hprefix tailTrace_2013401
  have hstable : (prefixWord ++ tailWord_2013401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013401).length < 2 ^ (prefixWord ++ tailWord_2013401).sum := by decide
  have hdescent : baseEnd_2013401 < baseStart_2013401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013405 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2013405 : Nat := 118140960795 + 2013405 * 2 ^ 59
def prefixEnd_2013405 : Nat := 4983230072969 + 3 ^ 40 * 2013405 * 2
def baseEnd_2013405 : Nat := 1033844517165800277378025

theorem tailTrace_2013405 : CollatzResearch.WordTrace tailWord_2013405 prefixEnd_2013405 1033844517165800277378025 := by
  unfold tailWord_2013405
  simp only [CollatzResearch.WordTrace]
  refine ⟨73434913270785022042841669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48956608847190014695227779 73434913270785022042841669)
  ·
    refine ⟨13769046238272191633032813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73434913270785022042841669 13769046238272191633032813)
    ·
      refine ⟨5163392339352071862387305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13769046238272191633032813 5163392339352071862387305)
      ·
        refine ⟨3872544254514053896790479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5163392339352071862387305 3872544254514053896790479)
        ·
          refine ⟨5808816381771080845185719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872544254514053896790479 5808816381771080845185719)
          ·
            refine ⟨8713224572656621267778579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808816381771080845185719 8713224572656621267778579)
            ·
              refine ⟨13069836858984931901667869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713224572656621267778579 13069836858984931901667869)
              ·
                refine ⟨4901188822119349463125451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13069836858984931901667869 4901188822119349463125451)
                ·
                  refine ⟨7351783233179024194688177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901188822119349463125451 7351783233179024194688177)
                  ·
                    refine ⟨5513837424884268146016133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7351783233179024194688177 5513837424884268146016133)
                    ·
                      refine ⟨1033844517165800277378025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5513837424884268146016133 1033844517165800277378025)
                      ·
                        rfl

theorem cell23_2013405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2013405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013405 prefixEnd_2013405 := by exact prefixLift 2013405
  have htrace : WordTrace (prefixWord ++ tailWord_2013405) baseStart_2013405 baseEnd_2013405 := by
    simpa [prefixWord, tailWord_2013405, baseEnd_2013405] using wordTrace_append hprefix tailTrace_2013405
  have hstable : (prefixWord ++ tailWord_2013405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013405).length < 2 ^ (prefixWord ++ tailWord_2013405).sum := by decide
  have hdescent : baseEnd_2013405 < baseStart_2013405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013415 : List Nat := [1, 1, 5, 3, 1, 2, 3, 7]
def baseStart_2013415 : Nat := 118140960795 + 2013415 * 2 ^ 59
def prefixEnd_2013415 : Nat := 4983230072969 + 3 ^ 40 * 2013415 * 2
def baseEnd_2013415 : Nat := 38290727850827601416777

theorem tailTrace_2013415 : CollatzResearch.WordTrace tailWord_2013415 prefixEnd_2013415 38290727850827601416777 := by
  unfold tailWord_2013415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73435278000748793750705699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48956852000499195833803799 73435278000748793750705699)
  ·
    refine ⟨110152917001123190626058549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73435278000748793750705699 110152917001123190626058549)
    ·
      refine ⟨10326835968855299121192989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110152917001123190626058549 10326835968855299121192989)
      ·
        refine ⟨3872563488320737170447371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10326835968855299121192989 3872563488320737170447371)
        ·
          refine ⟨5808845232481105755671057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872563488320737170447371 5808845232481105755671057)
          ·
            refine ⟨4356633924360829316753293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808845232481105755671057 4356633924360829316753293)
            ·
              refine ⟨1633737721635310993782485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4356633924360829316753293 1633737721635310993782485)
              ·
                refine ⟨38290727850827601416777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1633737721635310993782485 38290727850827601416777)
                ·
                  rfl

theorem cell23_2013415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 7].length) (baseStart_2013415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013415 prefixEnd_2013415 := by exact prefixLift 2013415
  have htrace : WordTrace (prefixWord ++ tailWord_2013415) baseStart_2013415 baseEnd_2013415 := by
    simpa [prefixWord, tailWord_2013415, baseEnd_2013415] using wordTrace_append hprefix tailTrace_2013415
  have hstable : (prefixWord ++ tailWord_2013415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013415).length < 2 ^ (prefixWord ++ tailWord_2013415).sum := by decide
  have hdescent : baseEnd_2013415 < baseStart_2013415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013426 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2013426 : Nat := 118140960795 + 2013426 * 2 ^ 59
def prefixEnd_2013426 : Nat := 4983230072969 + 3 ^ 40 * 2013426 * 2
def baseEnd_2013426 : Nat := 1033855300259544695215429

theorem tailTrace_2013426 : CollatzResearch.WordTrace tailWord_2013426 prefixEnd_2013426 1033855300259544695215429 := by
  unfold tailWord_2013426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358919800927235657339033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48957119469139295086237421 18358919800927235657339033)
  ·
    refine ⟨13769189850695426743004275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18358919800927235657339033 13769189850695426743004275)
    ·
      refine ⟨20653784776043140114506413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769189850695426743004275 20653784776043140114506413)
      ·
        refine ⟨7745169291016177542939905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20653784776043140114506413 7745169291016177542939905)
        ·
          refine ⟨5808876968262133157204929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7745169291016177542939905 5808876968262133157204929)
          ·
            refine ⟨4356657726196599867903697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808876968262133157204929 4356657726196599867903697)
            ·
              refine ⟨3267493294647449900927773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356657726196599867903697 3267493294647449900927773)
              ·
                refine ⟨1225309985492793712847915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267493294647449900927773 1225309985492793712847915)
                ·
                  refine ⟨1837964978239190569271873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225309985492793712847915 1837964978239190569271873)
                  ·
                    refine ⟨1378473733679392926953905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1837964978239190569271873 1378473733679392926953905)
                    ·
                      refine ⟨1033855300259544695215429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378473733679392926953905 1033855300259544695215429)
                      ·
                        rfl

theorem cell23_2013426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2013426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013426 prefixEnd_2013426 := by exact prefixLift 2013426
  have htrace : WordTrace (prefixWord ++ tailWord_2013426) baseStart_2013426 baseEnd_2013426 := by
    simpa [prefixWord, tailWord_2013426, baseEnd_2013426] using wordTrace_append hprefix tailTrace_2013426
  have hstable : (prefixWord ++ tailWord_2013426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013426).length < 2 ^ (prefixWord ++ tailWord_2013426).sum := by decide
  have hdescent : baseEnd_2013426 < baseStart_2013426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013468 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2013468 : Nat := 118140960795 + 2013468 * 2 ^ 59
def prefixEnd_2013468 : Nat := 4983230072969 + 3 ^ 40 * 2013468 * 2
def baseEnd_2013468 : Nat := 1033876866447033530890235

theorem tailTrace_2013468 : CollatzResearch.WordTrace tailWord_2013468 prefixEnd_2013468 1033876866447033530890235 := by
  unfold tailWord_2013468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36718605534778391901192529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48958140713037855868256705 36718605534778391901192529)
  ·
    refine ⟨27538954151083793925894397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36718605534778391901192529 27538954151083793925894397)
    ·
      refine ⟨10327107806656422722210399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27538954151083793925894397 10327107806656422722210399)
      ·
        refine ⟨15490661709984634083315599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327107806656422722210399 15490661709984634083315599)
        ·
          refine ⟨23235992564976951124973399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15490661709984634083315599 23235992564976951124973399)
          ·
            refine ⟨34853988847465426687460099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23235992564976951124973399 34853988847465426687460099)
            ·
              refine ⟨52280983271198140031190149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34853988847465426687460099 52280983271198140031190149)
              ·
                refine ⟨9802684363349651255848153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52280983271198140031190149 9802684363349651255848153)
                ·
                  refine ⟨7352013272512238441886115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802684363349651255848153 7352013272512238441886115)
                  ·
                    refine ⟨11028019908768357662829173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352013272512238441886115 11028019908768357662829173)
                    ·
                      refine ⟨1033876866447033530890235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11028019908768357662829173 1033876866447033530890235)
                      ·
                        rfl

theorem cell23_2013468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2013468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013468 prefixEnd_2013468 := by exact prefixLift 2013468
  have htrace : WordTrace (prefixWord ++ tailWord_2013468) baseStart_2013468 baseEnd_2013468 := by
    simpa [prefixWord, tailWord_2013468, baseEnd_2013468] using wordTrace_append hprefix tailTrace_2013468
  have hstable : (prefixWord ++ tailWord_2013468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013468).length < 2 ^ (prefixWord ++ tailWord_2013468).sum := by decide
  have hdescent : baseEnd_2013468 < baseStart_2013468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013518 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2013518 : Nat := 118140960795 + 2013518 * 2 ^ 59
def prefixEnd_2013518 : Nat := 4983230072969 + 3 ^ 40 * 2013518 * 2
def baseEnd_2013518 : Nat := 344634180159919445088335

theorem tailTrace_2013518 : CollatzResearch.WordTrace tailWord_2013518 prefixEnd_2013518 344634180159919445088335 := by
  unfold tailWord_2013518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179879339921955292713151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48959356479583761561136805 9179879339921955292713151)
  ·
    refine ⟨13769819009882932939069727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9179879339921955292713151 13769819009882932939069727)
    ·
      refine ⟨20654728514824399408604591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13769819009882932939069727 20654728514824399408604591)
      ·
        refine ⟨30982092772236599112906887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20654728514824399408604591 30982092772236599112906887)
        ·
          refine ⟨46473139158354898669360331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982092772236599112906887 46473139158354898669360331)
          ·
            refine ⟨69709708737532348004040497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46473139158354898669360331 69709708737532348004040497)
            ·
              refine ⟨52282281553149261003030373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69709708737532348004040497 52282281553149261003030373)
              ·
                refine ⟨9802927791215486438068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52282281553149261003030373 9802927791215486438068195)
                ·
                  refine ⟨14704391686823229657102293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9802927791215486438068195 14704391686823229657102293)
                  ·
                    refine ⟨344634180159919445088335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14704391686823229657102293 344634180159919445088335)
                    ·
                      rfl

theorem cell23_2013518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2013518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013518 prefixEnd_2013518 := by exact prefixLift 2013518
  have htrace : WordTrace (prefixWord ++ tailWord_2013518) baseStart_2013518 baseEnd_2013518 := by
    simpa [prefixWord, tailWord_2013518, baseEnd_2013518] using wordTrace_append hprefix tailTrace_2013518
  have hstable : (prefixWord ++ tailWord_2013518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013518).length < 2 ^ (prefixWord ++ tailWord_2013518).sum := by decide
  have hdescent : baseEnd_2013518 < baseStart_2013518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013555 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 4, 4, 2]
def baseStart_2013555 : Nat := 118140960795 + 2013555 * 2 ^ 59
def prefixEnd_2013555 : Nat := 4983230072969 + 3 ^ 40 * 2013555 * 2
def baseEnd_2013555 : Nat := 1033921539263974690502335

theorem tailTrace_2013555 : CollatzResearch.WordTrace tailWord_2013555 prefixEnd_2013555 1033921539263974690502335 := by
  unfold tailWord_2013555
  simp only [CollatzResearch.WordTrace]
  refine ⟨73440384220241597660802119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48960256146827731773868079 73440384220241597660802119)
  ·
    refine ⟨110160576330362396491203179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73440384220241597660802119 110160576330362396491203179)
    ·
      refine ⟨165240864495543594736804769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110160576330362396491203179 165240864495543594736804769)
      ·
        refine ⟨123930648371657696052603577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165240864495543594736804769 123930648371657696052603577)
        ·
          refine ⟨92947986278743272039452683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123930648371657696052603577 92947986278743272039452683)
          ·
            refine ⟨139421979418114908059179025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92947986278743272039452683 139421979418114908059179025)
            ·
              refine ⟨104566484563586181044384269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139421979418114908059179025 104566484563586181044384269)
              ·
                refine ⟨39212431711344817891644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104566484563586181044384269 39212431711344817891644101)
                ·
                  refine ⟨7352330945877153354683269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39212431711344817891644101 7352330945877153354683269)
                  ·
                    refine ⟨1378562052351966254003113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352330945877153354683269 1378562052351966254003113)
                    ·
                      refine ⟨1033921539263974690502335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378562052351966254003113 1033921539263974690502335)
                      ·
                        rfl

theorem cell23_2013555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 4, 2].length) (baseStart_2013555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013555 prefixEnd_2013555 := by exact prefixLift 2013555
  have htrace : WordTrace (prefixWord ++ tailWord_2013555) baseStart_2013555 baseEnd_2013555 := by
    simpa [prefixWord, tailWord_2013555, baseEnd_2013555] using wordTrace_append hprefix tailTrace_2013555
  have hstable : (prefixWord ++ tailWord_2013555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013555).length < 2 ^ (prefixWord ++ tailWord_2013555).sum := by decide
  have hdescent : baseEnd_2013555 < baseStart_2013555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013568 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_2013568 : Nat := 118140960795 + 2013568 * 2 ^ 59
def prefixEnd_2013568 : Nat := 4983230072969 + 3 ^ 40 * 2013568 * 2
def baseEnd_2013568 : Nat := 1033928214512483139639775

theorem tailTrace_2013568 : CollatzResearch.WordTrace tailWord_2013568 prefixEnd_2013568 1033928214512483139639775 := by
  unfold tailWord_2013568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720429184597250440512679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48960572246129667254016905 36720429184597250440512679)
  ·
    refine ⟨55080643776895875660769019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36720429184597250440512679 55080643776895875660769019)
    ·
      refine ⟨82620965665343813491153529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55080643776895875660769019 82620965665343813491153529)
      ·
        refine ⟨61965724249007860118365147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82620965665343813491153529 61965724249007860118365147)
        ·
          refine ⟨92948586373511790177547721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61965724249007860118365147 92948586373511790177547721)
          ·
            refine ⟨69711439780133842633160791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92948586373511790177547721 69711439780133842633160791)
            ·
              refine ⟨104567159670200763949741187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69711439780133842633160791 104567159670200763949741187)
              ·
                refine ⟨156850739505301145924611781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104567159670200763949741187 156850739505301145924611781)
                ·
                  refine ⟨29409513657243964860864709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156850739505301145924611781 29409513657243964860864709)
                  ·
                    refine ⟨5514283810733243411412133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29409513657243964860864709 5514283810733243411412133)
                    ·
                      refine ⟨1033928214512483139639775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5514283810733243411412133 1033928214512483139639775)
                      ·
                        rfl

theorem cell23_2013568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_2013568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013568 prefixEnd_2013568 := by exact prefixLift 2013568
  have htrace : WordTrace (prefixWord ++ tailWord_2013568) baseStart_2013568 baseEnd_2013568 := by
    simpa [prefixWord, tailWord_2013568, baseEnd_2013568] using wordTrace_append hprefix tailTrace_2013568
  have hstable : (prefixWord ++ tailWord_2013568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013568).length < 2 ^ (prefixWord ++ tailWord_2013568).sum := by decide
  have hdescent : baseEnd_2013568 < baseStart_2013568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013572 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_2013572 : Nat := 118140960795 + 2013572 * 2 ^ 59
def prefixEnd_2013572 : Nat := 4983230072969 + 3 ^ 40 * 2013572 * 2
def baseEnd_2013572 : Nat := 1033930268435101123989757

theorem tailTrace_2013572 : CollatzResearch.WordTrace tailWord_2013572 prefixEnd_2013572 1033930268435101123989757 := by
  unfold tailWord_2013572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720502130590004782085485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48960669507453339709447313 36720502130590004782085485)
  ·
    refine ⟨13770188298971251793282057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36720502130590004782085485 13770188298971251793282057)
    ·
      refine ⟨10327641224228438844961543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13770188298971251793282057 10327641224228438844961543)
      ·
        refine ⟨15491461836342658267442315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327641224228438844961543 15491461836342658267442315)
        ·
          refine ⟨23237192754513987401163473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15491461836342658267442315 23237192754513987401163473)
          ·
            refine ⟨17427894565885490550872605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23237192754513987401163473 17427894565885490550872605)
            ·
              refine ⟨6535460462207058956577227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17427894565885490550872605 6535460462207058956577227)
              ·
                refine ⟨9803190693310588434865841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535460462207058956577227 9803190693310588434865841)
                ·
                  refine ⟨7352393019982941326149381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9803190693310588434865841 7352393019982941326149381)
                  ·
                    refine ⟨1378573691246801498653009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7352393019982941326149381 1378573691246801498653009)
                    ·
                      refine ⟨1033930268435101123989757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378573691246801498653009 1033930268435101123989757)
                      ·
                        rfl

theorem cell23_2013572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_2013572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013572 prefixEnd_2013572 := by exact prefixLift 2013572
  have htrace : WordTrace (prefixWord ++ tailWord_2013572) baseStart_2013572 baseEnd_2013572 := by
    simpa [prefixWord, tailWord_2013572, baseEnd_2013572] using wordTrace_append hprefix tailTrace_2013572
  have hstable : (prefixWord ++ tailWord_2013572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013572).length < 2 ^ (prefixWord ++ tailWord_2013572).sum := by decide
  have hdescent : baseEnd_2013572 < baseStart_2013572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013575 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2013575 : Nat := 118140960795 + 2013575 * 2 ^ 59
def prefixEnd_2013575 : Nat := 4983230072969 + 3 ^ 40 * 2013575 * 2
def baseEnd_2013575 : Nat := 1033931808877064612252243

theorem tailTrace_2013575 : CollatzResearch.WordTrace tailWord_2013575 prefixEnd_2013575 1033931808877064612252243 := by
  unfold tailWord_2013575
  simp only [CollatzResearch.WordTrace]
  refine ⟨73441113680169141076530179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48960742453446094051020119 73441113680169141076530179)
  ·
    refine ⟨110161670520253711614795269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73441113680169141076530179 110161670520253711614795269)
    ·
      refine ⟨20655313222547570927774113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110161670520253711614795269 20655313222547570927774113)
      ·
        refine ⟨15491484916910678195830585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20655313222547570927774113 15491484916910678195830585)
        ·
          refine ⟨11618613687683008646872939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15491484916910678195830585 11618613687683008646872939)
          ·
            refine ⟨17427920531524512970309409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618613687683008646872939 17427920531524512970309409)
            ·
              refine ⟨13070940398643384727732057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17427920531524512970309409 13070940398643384727732057)
              ·
                refine ⟨9803205298982538545799043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070940398643384727732057 9803205298982538545799043)
                ·
                  refine ⟨14704807948473807818698565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803205298982538545799043 14704807948473807818698565)
                  ·
                    refine ⟨2757151490338838966005981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14704807948473807818698565 2757151490338838966005981)
                    ·
                      refine ⟨1033931808877064612252243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2757151490338838966005981 1033931808877064612252243)
                      ·
                        rfl

theorem cell23_2013575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2013575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013575 prefixEnd_2013575 := by exact prefixLift 2013575
  have htrace : WordTrace (prefixWord ++ tailWord_2013575) baseStart_2013575 baseEnd_2013575 := by
    simpa [prefixWord, tailWord_2013575, baseEnd_2013575] using wordTrace_append hprefix tailTrace_2013575
  have hstable : (prefixWord ++ tailWord_2013575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013575).length < 2 ^ (prefixWord ++ tailWord_2013575).sum := by decide
  have hdescent : baseEnd_2013575 < baseStart_2013575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013582 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2013582 : Nat := 118140960795 + 2013582 * 2 ^ 59
def prefixEnd_2013582 : Nat := 4983230072969 + 3 ^ 40 * 2013582 * 2
def baseEnd_2013582 : Nat := 344645134413882028288237

theorem tailTrace_2013582 : CollatzResearch.WordTrace tailWord_2013582 prefixEnd_2013582 344645134413882028288237 := by
  unfold tailWord_2013582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9180171123892972659004375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48960912660762520848023333 9180171123892972659004375)
  ·
    refine ⟨13770256685839458988506563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9180171123892972659004375 13770256685839458988506563)
    ·
      refine ⟨20655385028759188482759845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13770256685839458988506563 20655385028759188482759845)
      ·
        refine ⟨3872884692892347840517471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20655385028759188482759845 3872884692892347840517471)
        ·
          refine ⟨5809327039338521760776207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872884692892347840517471 5809327039338521760776207)
          ·
            refine ⟨8713990559007782641164311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809327039338521760776207 8713990559007782641164311)
            ·
              refine ⟨13070985838511673961746467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713990559007782641164311 13070985838511673961746467)
              ·
                refine ⟨19606478757767510942619701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070985838511673961746467 19606478757767510942619701)
                ·
                  refine ⟨1838107383540704150870597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19606478757767510942619701 1838107383540704150870597)
                  ·
                    refine ⟨344645134413882028288237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838107383540704150870597 344645134413882028288237)
                    ·
                      rfl

theorem cell23_2013582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2013582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013582 prefixEnd_2013582 := by exact prefixLift 2013582
  have htrace : WordTrace (prefixWord ++ tailWord_2013582) baseStart_2013582 baseEnd_2013582 := by
    simpa [prefixWord, tailWord_2013582, baseEnd_2013582] using wordTrace_append hprefix tailTrace_2013582
  have hstable : (prefixWord ++ tailWord_2013582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013582).length < 2 ^ (prefixWord ++ tailWord_2013582).sum := by decide
  have hdescent : baseEnd_2013582 < baseStart_2013582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013592 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2013592 : Nat := 118140960795 + 2013592 * 2 ^ 59
def prefixEnd_2013592 : Nat := 4983230072969 + 3 ^ 40 * 2013592 * 2
def baseEnd_2013592 : Nat := 1033940538048191045739665

theorem tailTrace_2013592 : CollatzResearch.WordTrace tailWord_2013592 prefixEnd_2013592 1033940538048191045739665 := by
  unfold tailWord_2013592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720866860553776489949515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48961155814071701986599353 36720866860553776489949515)
  ·
    refine ⟨55081300290830664734924273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36720866860553776489949515 55081300290830664734924273)
    ·
      refine ⟨41310975218122998551193205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55081300290830664734924273 41310975218122998551193205)
      ·
        refine ⟨3872903926699031114174363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41310975218122998551193205 3872903926699031114174363)
        ·
          refine ⟨5809355890048546671261545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872903926699031114174363 5809355890048546671261545)
          ·
            refine ⟨4357016917536410003446159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5809355890048546671261545 4357016917536410003446159)
            ·
              refine ⟨6535525376304615005169239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357016917536410003446159 6535525376304615005169239)
              ·
                refine ⟨9803288064456922507753859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535525376304615005169239 9803288064456922507753859)
                ·
                  refine ⟨14704932096685383761630789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803288064456922507753859 14704932096685383761630789)
                  ·
                    refine ⟨2757174768128509455305773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14704932096685383761630789 2757174768128509455305773)
                    ·
                      refine ⟨1033940538048191045739665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2757174768128509455305773 1033940538048191045739665)
                      ·
                        rfl

theorem cell23_2013592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2013592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013592 prefixEnd_2013592 := by exact prefixLift 2013592
  have htrace : WordTrace (prefixWord ++ tailWord_2013592) baseStart_2013592 baseEnd_2013592 := by
    simpa [prefixWord, tailWord_2013592, baseEnd_2013592] using wordTrace_append hprefix tailTrace_2013592
  have hstable : (prefixWord ++ tailWord_2013592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013592).length < 2 ^ (prefixWord ++ tailWord_2013592).sum := by decide
  have hdescent : baseEnd_2013592 < baseStart_2013592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013599 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 1, 4]
def baseStart_2013599 : Nat := 118140960795 + 2013599 * 2 ^ 59
def prefixEnd_2013599 : Nat := 4983230072969 + 3 ^ 40 * 2013599 * 2
def baseEnd_2013599 : Nat := 344648044137590839450711

theorem tailTrace_2013599 : CollatzResearch.WordTrace tailWord_2013599 prefixEnd_2013599 344648044137590839450711 := by
  unfold tailWord_2013599
  simp only [CollatzResearch.WordTrace]
  refine ⟨73441989032082193175403851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48961326021388128783602567 73441989032082193175403851)
  ·
    refine ⟨110162983548123289763105777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73441989032082193175403851 110162983548123289763105777)
    ·
      refine ⟨82622237661092467322329333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110162983548123289763105777 82622237661092467322329333)
      ·
        refine ⟨7745834780727418811468375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82622237661092467322329333 7745834780727418811468375)
        ·
          refine ⟨11618752171091128217202563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745834780727418811468375 11618752171091128217202563)
          ·
            refine ⟨17428128256636692325803845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618752171091128217202563 17428128256636692325803845)
            ·
              refine ⟨3267774048119379811088221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17428128256636692325803845 3267774048119379811088221)
              ·
                refine ⟨1225415268044767429158083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267774048119379811088221 1225415268044767429158083)
                ·
                  refine ⟨1838122902067151143737125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225415268044767429158083 1838122902067151143737125)
                  ·
                    refine ⟨344648044137590839450711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838122902067151143737125 344648044137590839450711)
                    ·
                      rfl

theorem cell23_2013599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 4].length) (baseStart_2013599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013599 prefixEnd_2013599 := by exact prefixLift 2013599
  have htrace : WordTrace (prefixWord ++ tailWord_2013599) baseStart_2013599 baseEnd_2013599 := by
    simpa [prefixWord, tailWord_2013599, baseEnd_2013599] using wordTrace_append hprefix tailTrace_2013599
  have hstable : (prefixWord ++ tailWord_2013599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013599).length < 2 ^ (prefixWord ++ tailWord_2013599).sum := by decide
  have hdescent : baseEnd_2013599 < baseStart_2013599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013642 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_2013642 : Nat := 118140960795 + 2013642 * 2 ^ 59
def prefixEnd_2013642 : Nat := 4983230072969 + 3 ^ 40 * 2013642 * 2
def baseEnd_2013642 : Nat := 344655404026971950038145

theorem tailTrace_2013642 : CollatzResearch.WordTrace tailWord_2013642 prefixEnd_2013642 344655404026971950038145 := by
  unfold tailWord_2013642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360889342731602879804795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48962371580617607679479453 18360889342731602879804795)
  ·
    refine ⟨27541334014097404319707193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18360889342731602879804795 27541334014097404319707193)
    ·
      refine ⟨20656000510573053239780395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27541334014097404319707193 20656000510573053239780395)
      ·
        refine ⟨30984000765859579859670593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20656000510573053239780395 30984000765859579859670593)
        ·
          refine ⟨23238000574394684894752945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30984000765859579859670593 23238000574394684894752945)
          ·
            refine ⟨17428500430796013671064709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23238000574394684894752945 17428500430796013671064709)
            ·
              refine ⟨3267843830774252563324633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17428500430796013671064709 3267843830774252563324633)
              ·
                refine ⟨2450882873080689422493475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267843830774252563324633 2450882873080689422493475)
                ·
                  refine ⟨3676324309621034133740213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450882873080689422493475 3676324309621034133740213)
                  ·
                    refine ⟨344655404026971950038145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3676324309621034133740213 344655404026971950038145)
                    ·
                      rfl

theorem cell23_2013642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_2013642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013642 prefixEnd_2013642 := by exact prefixLift 2013642
  have htrace : WordTrace (prefixWord ++ tailWord_2013642) baseStart_2013642 baseEnd_2013642 := by
    simpa [prefixWord, tailWord_2013642, baseEnd_2013642] using wordTrace_append hprefix tailTrace_2013642
  have hstable : (prefixWord ++ tailWord_2013642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013642).length < 2 ^ (prefixWord ++ tailWord_2013642).sum := by decide
  have hdescent : baseEnd_2013642 < baseStart_2013642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013650 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2013650 : Nat := 118140960795 + 2013650 * 2 ^ 59
def prefixEnd_2013650 : Nat := 4983230072969 + 3 ^ 40 * 2013650 * 2
def baseEnd_2013650 : Nat := 344656773308717272938133

theorem tailTrace_2013650 : CollatzResearch.WordTrace tailWord_2013650 prefixEnd_2013650 344656773308717272938133 := by
  unfold tailWord_2013650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360962288724357221377601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48962566103264952590340269 18360962288724357221377601)
  ·
    refine ⟨13770721716543267916033201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18360962288724357221377601 13770721716543267916033201)
    ·
      refine ⟨10328041287407450937024901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13770721716543267916033201 10328041287407450937024901)
      ·
        refine ⟨1936507741388897050692169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10328041287407450937024901 1936507741388897050692169)
        ·
          refine ⟨1452380806041672788019127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936507741388897050692169 1452380806041672788019127)
          ·
            refine ⟨2178571209062509182028691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452380806041672788019127 2178571209062509182028691)
            ·
              refine ⟨3267856813593763773043037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178571209062509182028691 3267856813593763773043037)
              ·
                refine ⟨1225446305097661414891139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267856813593763773043037 1225446305097661414891139)
                ·
                  refine ⟨1838169457646492122336709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225446305097661414891139 1838169457646492122336709)
                  ·
                    refine ⟨344656773308717272938133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838169457646492122336709 344656773308717272938133)
                    ·
                      rfl

theorem cell23_2013650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2013650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013650 prefixEnd_2013650 := by exact prefixLift 2013650
  have htrace : WordTrace (prefixWord ++ tailWord_2013650) baseStart_2013650 baseEnd_2013650 := by
    simpa [prefixWord, tailWord_2013650, baseEnd_2013650] using wordTrace_append hprefix tailTrace_2013650
  have hstable : (prefixWord ++ tailWord_2013650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013650).length < 2 ^ (prefixWord ++ tailWord_2013650).sum := by decide
  have hdescent : baseEnd_2013650 < baseStart_2013650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013672 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2013672 : Nat := 118140960795 + 2013672 * 2 ^ 59
def prefixEnd_2013672 : Nat := 4983230072969 + 3 ^ 40 * 2013672 * 2
def baseEnd_2013672 : Nat := 344660538833516910913099

theorem tailTrace_2013672 : CollatzResearch.WordTrace tailWord_2013672 prefixEnd_2013672 344660538833516910913099 := by
  unfold tailWord_2013672
  simp only [CollatzResearch.WordTrace]
  refine ⟨36722325780408863321405635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48963101040545151095207513 36722325780408863321405635)
  ·
    refine ⟨55083488670613294982108453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36722325780408863321405635 55083488670613294982108453)
    ·
      refine ⟨10328154125739992809145335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55083488670613294982108453 10328154125739992809145335)
      ·
        refine ⟨15492231188609989213718003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328154125739992809145335 15492231188609989213718003)
        ·
          refine ⟨23238346782914983820577005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15492231188609989213718003 23238346782914983820577005)
          ·
            refine ⟨8714380043593118932716377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23238346782914983820577005 8714380043593118932716377)
            ·
              refine ⟨6535785032694839199537283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8714380043593118932716377 6535785032694839199537283)
              ·
                refine ⟨9803677549042258799305925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535785032694839199537283 9803677549042258799305925)
                ·
                  refine ⟨1838189540445423524869861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9803677549042258799305925 1838189540445423524869861)
                  ·
                    refine ⟨344660538833516910913099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838189540445423524869861 344660538833516910913099)
                    ·
                      rfl

theorem cell23_2013672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2013672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013672 prefixEnd_2013672 := by exact prefixLift 2013672
  have htrace : WordTrace (prefixWord ++ tailWord_2013672) baseStart_2013672 baseEnd_2013672 := by
    simpa [prefixWord, tailWord_2013672, baseEnd_2013672] using wordTrace_append hprefix tailTrace_2013672
  have hstable : (prefixWord ++ tailWord_2013672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013672).length < 2 ^ (prefixWord ++ tailWord_2013672).sum := by decide
  have hdescent : baseEnd_2013672 < baseStart_2013672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013689 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 2, 4]
def baseStart_2013689 : Nat := 118140960795 + 2013689 * 2 ^ 59
def prefixEnd_2013689 : Nat := 4983230072969 + 3 ^ 40 * 2013689 * 2
def baseEnd_2013689 : Nat := 344663448557225722075573

theorem tailTrace_2013689 : CollatzResearch.WordTrace tailWord_2013689 prefixEnd_2013689 344663448557225722075573 := by
  unfold tailWord_2013689
  simp only [CollatzResearch.WordTrace]
  refine ⟨73445271601756138546180121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48963514401170759030786747 73445271601756138546180121)
  ·
    refine ⟨55083953701317103909635091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73445271601756138546180121 55083953701317103909635091)
    ·
      refine ⟨82625930551975655864452637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55083953701317103909635091 82625930551975655864452637)
      ·
        refine ⟨30984723956990870949169739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82625930551975655864452637 30984723956990870949169739)
        ·
          refine ⟨46477085935486306423754609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30984723956990870949169739 46477085935486306423754609)
          ·
            refine ⟨34857814451614729817815957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46477085935486306423754609 34857814451614729817815957)
            ·
              refine ⟨1633960052419440460210123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34857814451614729817815957 1633960052419440460210123)
              ·
                refine ⟨2450940078629160690315185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633960052419440460210123 2450940078629160690315185)
                ·
                  refine ⟨1838205058971870517736389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2450940078629160690315185 1838205058971870517736389)
                  ·
                    refine ⟨344663448557225722075573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1838205058971870517736389 344663448557225722075573)
                    ·
                      rfl

theorem cell23_2013689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_2013689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013689 prefixEnd_2013689 := by exact prefixLift 2013689
  have htrace : WordTrace (prefixWord ++ tailWord_2013689) baseStart_2013689 baseEnd_2013689 := by
    simpa [prefixWord, tailWord_2013689, baseEnd_2013689] using wordTrace_append hprefix tailTrace_2013689
  have hstable : (prefixWord ++ tailWord_2013689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013689).length < 2 ^ (prefixWord ++ tailWord_2013689).sum := by decide
  have hdescent : baseEnd_2013689 < baseStart_2013689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013716 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2013716 : Nat := 118140960795 + 2013716 * 2 ^ 59
def prefixEnd_2013716 : Nat := 4983230072969 + 3 ^ 40 * 2013716 * 2
def baseEnd_2013716 : Nat := 1034004209649348560589095

theorem tailTrace_2013716 : CollatzResearch.WordTrace tailWord_2013716 prefixEnd_2013716 1034004209649348560589095 := by
  unfold tailWord_2013716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36723128186329161078706501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48964170915105548104942001 36723128186329161078706501)
  ·
    refine ⟨6885586534936717702257469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36723128186329161078706501 6885586534936717702257469)
    ·
      refine ⟨2582094950601269138346551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6885586534936717702257469 2582094950601269138346551)
      ·
        refine ⟨3873142425901903707519827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582094950601269138346551 3873142425901903707519827)
        ·
          refine ⟨5809713638852855561279741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873142425901903707519827 5809713638852855561279741)
          ·
            refine ⟨2178642614569820835479903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5809713638852855561279741 2178642614569820835479903)
            ·
              refine ⟨3267963921854731253219855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178642614569820835479903 3267963921854731253219855)
              ·
                refine ⟨4901945882782096879829783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267963921854731253219855 4901945882782096879829783)
                ·
                  refine ⟨7352918824173145319744675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901945882782096879829783 7352918824173145319744675)
                  ·
                    refine ⟨11029378236259717979617013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352918824173145319744675 11029378236259717979617013)
                    ·
                      refine ⟨1034004209649348560589095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11029378236259717979617013 1034004209649348560589095)
                      ·
                        rfl

theorem cell23_2013716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2013716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013716 prefixEnd_2013716 := by exact prefixLift 2013716
  have htrace : WordTrace (prefixWord ++ tailWord_2013716) baseStart_2013716 baseEnd_2013716 := by
    simpa [prefixWord, tailWord_2013716, baseEnd_2013716] using wordTrace_append hprefix tailTrace_2013716
  have hstable : (prefixWord ++ tailWord_2013716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013716).length < 2 ^ (prefixWord ++ tailWord_2013716).sum := by decide
  have hdescent : baseEnd_2013716 < baseStart_2013716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013745 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2013745 : Nat := 118140960795 + 2013745 * 2 ^ 59
def prefixEnd_2013745 : Nat := 4983230072969 + 3 ^ 40 * 2013745 * 2
def baseEnd_2013745 : Nat := 344673033529442982375487

theorem tailTrace_2013745 : CollatzResearch.WordTrace tailWord_2013745 prefixEnd_2013745 344673033529442982375487 := by
  unfold tailWord_2013745
  simp only [CollatzResearch.WordTrace]
  refine ⟨73447314089553260110218689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48964876059702173406812459 73447314089553260110218689)
  ·
    refine ⟨55085485567164945082664017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73447314089553260110218689 55085485567164945082664017)
    ·
      refine ⟨41314114175373708811998013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55085485567164945082664017 41314114175373708811998013)
      ·
        refine ⟨15492792815765140804499255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41314114175373708811998013 15492792815765140804499255)
        ·
          refine ⟨23239189223647711206748883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15492792815765140804499255 23239189223647711206748883)
          ·
            refine ⟨34858783835471566810123325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23239189223647711206748883 34858783835471566810123325)
            ·
              refine ⟨13072043938301837553796247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34858783835471566810123325 13072043938301837553796247)
              ·
                refine ⟨19608065907452756330694371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072043938301837553796247 19608065907452756330694371)
                ·
                  refine ⟨29412098861179134496041557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19608065907452756330694371 29412098861179134496041557)
                  ·
                    refine ⟨344673033529442982375487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29412098861179134496041557 344673033529442982375487)
                    ·
                      rfl

theorem cell23_2013745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2013745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013745 prefixEnd_2013745 := by exact prefixLift 2013745
  have htrace : WordTrace (prefixWord ++ tailWord_2013745) baseStart_2013745 baseEnd_2013745 := by
    simpa [prefixWord, tailWord_2013745, baseEnd_2013745] using wordTrace_append hprefix tailTrace_2013745
  have hstable : (prefixWord ++ tailWord_2013745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013745).length < 2 ^ (prefixWord ++ tailWord_2013745).sum := by decide
  have hdescent : baseEnd_2013745 < baseStart_2013745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013764 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2013764 : Nat := 118140960795 + 2013764 * 2 ^ 59
def prefixEnd_2013764 : Nat := 4983230072969 + 3 ^ 40 * 2013764 * 2
def baseEnd_2013764 : Nat := 1034028856720764372788875

theorem tailTrace_2013764 : CollatzResearch.WordTrace tailWord_2013764 prefixEnd_2013764 1034028856720764372788875 := by
  unfold tailWord_2013764
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724003538242213177580173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48965338050989617570106897 36724003538242213177580173)
  ·
    refine ⟨13771501326840829941592565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36724003538242213177580173 13771501326840829941592565)
    ·
      refine ⟨1291078249391327807024303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13771501326840829941592565 1291078249391327807024303)
      ·
        refine ⟨1936617374086991710536455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291078249391327807024303 1936617374086991710536455)
        ·
          refine ⟨2904926061130487565804683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936617374086991710536455 2904926061130487565804683)
          ·
            refine ⟨4357389091695731348707025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904926061130487565804683 4357389091695731348707025)
            ·
              refine ⟨3268041818771798511530269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4357389091695731348707025 3268041818771798511530269)
              ·
                refine ⟨1225515682039424441823851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3268041818771798511530269 1225515682039424441823851)
                ·
                  refine ⟨1838273523059136662735777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225515682039424441823851 1838273523059136662735777)
                  ·
                    refine ⟨1378705142294352497051833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1838273523059136662735777 1378705142294352497051833)
                    ·
                      refine ⟨1034028856720764372788875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378705142294352497051833 1034028856720764372788875)
                      ·
                        rfl

theorem cell23_2013764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2013764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013764 prefixEnd_2013764 := by exact prefixLift 2013764
  have htrace : WordTrace (prefixWord ++ tailWord_2013764) baseStart_2013764 baseEnd_2013764 := by
    simpa [prefixWord, tailWord_2013764, baseEnd_2013764] using wordTrace_append hprefix tailTrace_2013764
  have hstable : (prefixWord ++ tailWord_2013764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013764).length < 2 ^ (prefixWord ++ tailWord_2013764).sum := by decide
  have hdescent : baseEnd_2013764 < baseStart_2013764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013773 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2013773 : Nat := 118140960795 + 2013773 * 2 ^ 59
def prefixEnd_2013773 : Nat := 4983230072969 + 3 ^ 40 * 2013773 * 2
def baseEnd_2013773 : Nat := 1034033478046654837576333

theorem tailTrace_2013773 : CollatzResearch.WordTrace tailWord_2013773 prefixEnd_2013773 1034033478046654837576333 := by
  unfold tailWord_2013773
  simp only [CollatzResearch.WordTrace]
  refine ⟨73448335333451820892237973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48965556888967880594825315 73448335333451820892237973)
  ·
    refine ⟨3442890718755554104323655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73448335333451820892237973 3442890718755554104323655)
    ·
      refine ⟨5164336078133331156485483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442890718755554104323655 5164336078133331156485483)
      ·
        refine ⟨7746504117199996734728225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164336078133331156485483 7746504117199996734728225)
        ·
          refine ⟨5809878087899997551046169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7746504117199996734728225 5809878087899997551046169)
          ·
            refine ⟨4357408565924998163284627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5809878087899997551046169 4357408565924998163284627)
            ·
              refine ⟨6536112848887497244926941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357408565924998163284627 6536112848887497244926941)
              ·
                refine ⟨2451042318332811466847603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6536112848887497244926941 2451042318332811466847603)
                ·
                  refine ⟨3676563477499217200271405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451042318332811466847603 3676563477499217200271405)
                  ·
                    refine ⟨1378711304062206450101777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3676563477499217200271405 1378711304062206450101777)
                    ·
                      refine ⟨1034033478046654837576333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378711304062206450101777 1034033478046654837576333)
                      ·
                        rfl

theorem cell23_2013773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2013773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013773 prefixEnd_2013773 := by exact prefixLift 2013773
  have htrace : WordTrace (prefixWord ++ tailWord_2013773) baseStart_2013773 baseEnd_2013773 := by
    simpa [prefixWord, tailWord_2013773, baseEnd_2013773] using wordTrace_append hprefix tailTrace_2013773
  have hstable : (prefixWord ++ tailWord_2013773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013773).length < 2 ^ (prefixWord ++ tailWord_2013773).sum := by decide
  have hdescent : baseEnd_2013773 < baseStart_2013773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013894 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_2013894 : Nat := 118140960795 + 2013894 * 2 ^ 59
def prefixEnd_2013894 : Nat := 4983230072969 + 3 ^ 40 * 2013894 * 2
def baseEnd_2013894 : Nat := 114899512133983207129253

theorem tailTrace_2013894 : CollatzResearch.WordTrace tailWord_2013894 prefixEnd_2013894 114899512133983207129253 := by
  unfold tailWord_2013894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295398392687920579918523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48968499044008972371595157 2295398392687920579918523)
  ·
    refine ⟨3443097589031880869877785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295398392687920579918523 3443097589031880869877785)
    ·
      refine ⟨2582323191773910652408339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443097589031880869877785 2582323191773910652408339)
      ·
        refine ⟨3873484787660865978612509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582323191773910652408339 3873484787660865978612509)
        ·
          refine ⟨1452556795372824741979691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3873484787660865978612509 1452556795372824741979691)
          ·
            refine ⟨2178835193059237112969537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452556795372824741979691 2178835193059237112969537)
            ·
              refine ⟨1634126394794427834727153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178835193059237112969537 1634126394794427834727153)
              ·
                refine ⟨1225594796095820876045365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634126394794427834727153 1225594796095820876045365)
                ·
                  refine ⟨114899512133983207129253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1225594796095820876045365 114899512133983207129253)
                  ·
                    rfl

theorem cell23_2013894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_2013894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013894 prefixEnd_2013894 := by exact prefixLift 2013894
  have htrace : WordTrace (prefixWord ++ tailWord_2013894) baseStart_2013894 baseEnd_2013894 := by
    simpa [prefixWord, tailWord_2013894, baseEnd_2013894] using wordTrace_append hprefix tailTrace_2013894
  have hstable : (prefixWord ++ tailWord_2013894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013894).length < 2 ^ (prefixWord ++ tailWord_2013894).sum := by decide
  have hdescent : baseEnd_2013894 < baseStart_2013894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013916 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 6]
def baseStart_2013916 : Nat := 118140960795 + 2013916 * 2 ^ 59
def prefixEnd_2013916 : Nat := 4983230072969 + 3 ^ 40 * 2013916 * 2
def baseEnd_2013916 : Nat := 114900767308916419787575

theorem tailTrace_2013916 : CollatzResearch.WordTrace tailWord_2013916 prefixEnd_2013916 114900767308916419787575 := by
  unfold tailWord_2013916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36726775485966878157346801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48969033981289170876462401 36726775485966878157346801)
  ·
    refine ⟨27545081614475158618010101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36726775485966878157346801 27545081614475158618010101)
    ·
      refine ⟨2582351401357046120438447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27545081614475158618010101 2582351401357046120438447)
      ·
        refine ⟨3873527102035569180657671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582351401357046120438447 3873527102035569180657671)
        ·
          refine ⟨5810290653053353770986507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873527102035569180657671 5810290653053353770986507)
          ·
            refine ⟨8715435979580030656479761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810290653053353770986507 8715435979580030656479761)
            ·
              refine ⟨6536576984685022992359821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8715435979580030656479761 6536576984685022992359821)
              ·
                refine ⟨2451216369256883622134933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6536576984685022992359821 2451216369256883622134933)
                ·
                  refine ⟨114900767308916419787575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2451216369256883622134933 114900767308916419787575)
                  ·
                    rfl

theorem cell23_2013916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_2013916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013916 prefixEnd_2013916 := by exact prefixLift 2013916
  have htrace : WordTrace (prefixWord ++ tailWord_2013916) baseStart_2013916 baseEnd_2013916 := by
    simpa [prefixWord, tailWord_2013916, baseEnd_2013916] using wordTrace_append hprefix tailTrace_2013916
  have hstable : (prefixWord ++ tailWord_2013916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013916).length < 2 ^ (prefixWord ++ tailWord_2013916).sum := by decide
  have hdescent : baseEnd_2013916 < baseStart_2013916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013946 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_2013946 : Nat := 118140960795 + 2013946 * 2 ^ 59
def prefixEnd_2013946 : Nat := 4983230072969 + 3 ^ 40 * 2013946 * 2
def baseEnd_2013946 : Nat := 344707436733294220237679

theorem tailTrace_2013946 : CollatzResearch.WordTrace tailWord_2013946 prefixEnd_2013946 344707436733294220237679 := by
  unfold tailWord_2013946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363661290456267859571423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48969763441216714292190461 18363661290456267859571423)
  ·
    refine ⟨27545491935684401789357135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363661290456267859571423 27545491935684401789357135)
    ·
      refine ⟨41318237903526602684035703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27545491935684401789357135 41318237903526602684035703)
      ·
        refine ⟨61977356855289904026053555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41318237903526602684035703 61977356855289904026053555)
        ·
          refine ⟨92966035282934856039080333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61977356855289904026053555 92966035282934856039080333)
          ·
            refine ⟨34862263231100571014655125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92966035282934856039080333 34862263231100571014655125)
            ·
              refine ⟨1634168588957839266311959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34862263231100571014655125 1634168588957839266311959)
              ·
                refine ⟨2451252883436758899467939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634168588957839266311959 2451252883436758899467939)
                ·
                  refine ⟨3676879325155138349201909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451252883436758899467939 3676879325155138349201909)
                  ·
                    refine ⟨344707436733294220237679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3676879325155138349201909 344707436733294220237679)
                    ·
                      rfl

theorem cell23_2013946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_2013946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013946 prefixEnd_2013946 := by exact prefixLift 2013946
  have htrace : WordTrace (prefixWord ++ tailWord_2013946) baseStart_2013946 baseEnd_2013946 := by
    simpa [prefixWord, tailWord_2013946, baseEnd_2013946] using wordTrace_append hprefix tailTrace_2013946
  have hstable : (prefixWord ++ tailWord_2013946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013946).length < 2 ^ (prefixWord ++ tailWord_2013946).sum := by decide
  have hdescent : baseEnd_2013946 < baseStart_2013946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013969 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_2013969 : Nat := 118140960795 + 2013969 * 2 ^ 59
def prefixEnd_2013969 : Nat := 4983230072969 + 3 ^ 40 * 2013969 * 2
def baseEnd_2013969 : Nat := 1034134120254936070725431

theorem tailTrace_2013969 : CollatzResearch.WordTrace tailWord_2013969 prefixEnd_2013969 1034134120254936070725431 := by
  unfold tailWord_2013969
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455484040741746366372961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48970322693827830910915307 73455484040741746366372961)
  ·
    refine ⟨55091613030556309774779721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73455484040741746366372961 55091613030556309774779721)
    ·
      refine ⟨41318709772917232331084791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55091613030556309774779721 41318709772917232331084791)
      ·
        refine ⟨61978064659375848496627187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41318709772917232331084791 61978064659375848496627187)
        ·
          refine ⟨92967096989063772744940781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61978064659375848496627187 92967096989063772744940781)
          ·
            refine ⟨34862661370898914779352793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92967096989063772744940781 34862661370898914779352793)
            ·
              refine ⟨26146996028174186084514595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34862661370898914779352793 26146996028174186084514595)
              ·
                refine ⟨39220494042261279126771893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146996028174186084514595 39220494042261279126771893)
                ·
                  refine ⟨3676921316461994918134865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39220494042261279126771893 3676921316461994918134865)
                  ·
                    refine ⟨2757690987346496188601149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3676921316461994918134865 2757690987346496188601149)
                    ·
                      refine ⟨1034134120254936070725431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2757690987346496188601149 1034134120254936070725431)
                      ·
                        rfl

theorem cell23_2013969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_2013969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013969 prefixEnd_2013969 := by exact prefixLift 2013969
  have htrace : WordTrace (prefixWord ++ tailWord_2013969) baseStart_2013969 baseEnd_2013969 := by
    simpa [prefixWord, tailWord_2013969, baseEnd_2013969] using wordTrace_append hprefix tailTrace_2013969
  have hstable : (prefixWord ++ tailWord_2013969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013969).length < 2 ^ (prefixWord ++ tailWord_2013969).sum := by decide
  have hdescent : baseEnd_2013969 < baseStart_2013969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013983 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 3, 2, 2]
def baseStart_2013983 : Nat := 118140960795 + 2013983 * 2 ^ 59
def prefixEnd_2013983 : Nat := 4983230072969 + 3 ^ 40 * 2013983 * 2
def baseEnd_2013983 : Nat := 1034141308984099015950367

theorem tailTrace_2013983 : CollatzResearch.WordTrace tailWord_2013983 prefixEnd_2013983 1034141308984099015950367 := by
  unfold tailWord_2013983
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455994662691026757382603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48970663108460684504921735 73455994662691026757382603)
  ·
    refine ⟨110183991994036540136073905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73455994662691026757382603 110183991994036540136073905)
    ·
      refine ⟨82637993995527405102055429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110183991994036540136073905 82637993995527405102055429)
      ·
        refine ⟨15494623874161388456635393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82637993995527405102055429 15494623874161388456635393)
        ·
          refine ⟨11620967905621041342476545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15494623874161388456635393 11620967905621041342476545)
          ·
            refine ⟨8715725929215781006857409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620967905621041342476545 8715725929215781006857409)
            ·
              refine ⟨6536794446911835755143057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8715725929215781006857409 6536794446911835755143057)
              ·
                refine ⟨4902595835183876816357293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536794446911835755143057 4902595835183876816357293)
                ·
                  refine ⟨1838473438193953806133985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4902595835183876816357293 1838473438193953806133985)
                  ·
                    refine ⟨1378855078645465354600489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1838473438193953806133985 1378855078645465354600489)
                    ·
                      refine ⟨1034141308984099015950367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378855078645465354600489 1034141308984099015950367)
                      ·
                        rfl

theorem cell23_2013983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_2013983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013983 prefixEnd_2013983 := by exact prefixLift 2013983
  have htrace : WordTrace (prefixWord ++ tailWord_2013983) baseStart_2013983 baseEnd_2013983 := by
    simpa [prefixWord, tailWord_2013983, baseEnd_2013983] using wordTrace_append hprefix tailTrace_2013983
  have hstable : (prefixWord ++ tailWord_2013983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013983).length < 2 ^ (prefixWord ++ tailWord_2013983).sum := by decide
  have hdescent : baseEnd_2013983 < baseStart_2013983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013994 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2013994 : Nat := 118140960795 + 2013994 * 2 ^ 59
def prefixEnd_2013994 : Nat := 4983230072969 + 3 ^ 40 * 2013994 * 2
def baseEnd_2013994 : Nat := 1034146957271298472912817

theorem tailTrace_2013994 : CollatzResearch.WordTrace tailWord_2013994 prefixEnd_2013994 1034146957271298472912817 := by
  unfold tailWord_2013994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364098966412793909008259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48970930577100783757355357 18364098966412793909008259)
  ·
    refine ⟨27546148449619190863512389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18364098966412793909008259 27546148449619190863512389)
    ·
      refine ⟨5164902834303598286908573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27546148449619190863512389 5164902834303598286908573)
      ·
        refine ⟨1936838562863849357590715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5164902834303598286908573 1936838562863849357590715)
        ·
          refine ⟨2905257844295774036386073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936838562863849357590715 2905257844295774036386073)
          ·
            refine ⟨2178943383221830527289555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905257844295774036386073 2178943383221830527289555)
            ·
              refine ⟨3268415074832745790934333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178943383221830527289555 3268415074832745790934333)
              ·
                refine ⟨1225655653062279671600375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3268415074832745790934333 1225655653062279671600375)
                ·
                  refine ⟨1838483479593419507400563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225655653062279671600375 1838483479593419507400563)
                  ·
                    refine ⟨2757725219390129261100845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1838483479593419507400563 2757725219390129261100845)
                    ·
                      refine ⟨1034146957271298472912817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2757725219390129261100845 1034146957271298472912817)
                      ·
                        rfl

theorem cell23_2013994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2013994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2013994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2013994 prefixEnd_2013994 := by exact prefixLift 2013994
  have htrace : WordTrace (prefixWord ++ tailWord_2013994) baseStart_2013994 baseEnd_2013994 := by
    simpa [prefixWord, tailWord_2013994, baseEnd_2013994] using wordTrace_append hprefix tailTrace_2013994
  have hstable : (prefixWord ++ tailWord_2013994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013994).length < 2 ^ (prefixWord ++ tailWord_2013994).sum := by decide
  have hdescent : baseEnd_2013994 < baseStart_2013994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014059 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_2014059 : Nat := 118140960795 + 2014059 * 2 ^ 59
def prefixEnd_2014059 : Nat := 4983230072969 + 3 ^ 40 * 2014059 * 2
def baseEnd_2014059 : Nat := 1034180333513840718600017

theorem tailTrace_2014059 : CollatzResearch.WordTrace tailWord_2014059 prefixEnd_2014059 1034180333513840718600017 := by
  unfold tailWord_2014059
  simp only [CollatzResearch.WordTrace]
  refine ⟨73458766610415691737149231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48972511073610461158099487 73458766610415691737149231)
  ·
    refine ⟨110188149915623537605723847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73458766610415691737149231 110188149915623537605723847)
    ·
      refine ⟨165282224873435306408585771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110188149915623537605723847 165282224873435306408585771)
      ·
        refine ⟨247923337310152959612878657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165282224873435306408585771 247923337310152959612878657)
        ·
          refine ⟨185942502982614719709658993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247923337310152959612878657 185942502982614719709658993)
          ·
            refine ⟨139456877236961039782244245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185942502982614719709658993 139456877236961039782244245)
            ·
              refine ⟨6537041120482548739792699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139456877236961039782244245 6537041120482548739792699)
              ·
                refine ⟨9805561680723823109689049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537041120482548739792699 9805561680723823109689049)
                ·
                  refine ⟨7354171260542867332266787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9805561680723823109689049 7354171260542867332266787)
                  ·
                    refine ⟨11031256890814300998400181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7354171260542867332266787 11031256890814300998400181)
                    ·
                      refine ⟨1034180333513840718600017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11031256890814300998400181 1034180333513840718600017)
                      ·
                        rfl

theorem cell23_2014059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_2014059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014059 prefixEnd_2014059 := by exact prefixLift 2014059
  have htrace : WordTrace (prefixWord ++ tailWord_2014059) baseStart_2014059 baseEnd_2014059 := by
    simpa [prefixWord, tailWord_2014059, baseEnd_2014059] using wordTrace_append hprefix tailTrace_2014059
  have hstable : (prefixWord ++ tailWord_2014059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014059).length < 2 ^ (prefixWord ++ tailWord_2014059).sum := by decide
  have hdescent : baseEnd_2014059 < baseStart_2014059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014060 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_2014060 : Nat := 118140960795 + 2014060 * 2 ^ 59
def prefixEnd_2014060 : Nat := 4983230072969 + 3 ^ 40 * 2014060 * 2
def baseEnd_2014060 : Nat := 1034180846994495214687513

theorem tailTrace_2014060 : CollatzResearch.WordTrace tailWord_2014060 prefixEnd_2014060 1034180846994495214687513 := by
  unfold tailWord_2014060
  simp only [CollatzResearch.WordTrace]
  refine ⟨36729401541706034453967817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48972535388941379271957089 36729401541706034453967817)
  ·
    refine ⟨27547051156279525840475863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36729401541706034453967817 27547051156279525840475863)
    ·
      refine ⟨41320576734419288760713795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27547051156279525840475863 41320576734419288760713795)
      ·
        refine ⟨61980865101628933141070693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41320576734419288760713795 61980865101628933141070693)
        ·
          refine ⟨11621412206555424963950755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61980865101628933141070693 11621412206555424963950755)
          ·
            refine ⟨17432118309833137445926133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621412206555424963950755 17432118309833137445926133)
            ·
              refine ⟨1634261091546856635555575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17432118309833137445926133 1634261091546856635555575)
              ·
                refine ⟨2451391637320284953333363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634261091546856635555575 2451391637320284953333363)
                ·
                  refine ⟨3677087455980427430000045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451391637320284953333363 3677087455980427430000045)
                  ·
                    refine ⟨1378907795992660286250017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677087455980427430000045 1378907795992660286250017)
                    ·
                      refine ⟨1034180846994495214687513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378907795992660286250017 1034180846994495214687513)
                      ·
                        rfl

theorem cell23_2014060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_2014060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014060 prefixEnd_2014060 := by exact prefixLift 2014060
  have htrace : WordTrace (prefixWord ++ tailWord_2014060) baseStart_2014060 baseEnd_2014060 := by
    simpa [prefixWord, tailWord_2014060, baseEnd_2014060] using wordTrace_append hprefix tailTrace_2014060
  have hstable : (prefixWord ++ tailWord_2014060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014060).length < 2 ^ (prefixWord ++ tailWord_2014060).sum := by decide
  have hdescent : baseEnd_2014060 < baseStart_2014060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014090 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2014090 : Nat := 118140960795 + 2014090 * 2 ^ 59
def prefixEnd_2014090 : Nat := 4983230072969 + 3 ^ 40 * 2014090 * 2
def baseEnd_2014090 : Nat := 1034196251414130097312375

theorem tailTrace_2014090 : CollatzResearch.WordTrace tailWord_2014090 prefixEnd_2014090 1034196251414130097312375 := by
  unfold tailWord_2014090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364974318325846007881931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48973264848868922687685149 18364974318325846007881931)
  ·
    refine ⟨27547461477488769011822897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18364974318325846007881931 27547461477488769011822897)
    ·
      refine ⟨20660596108116576758867173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27547461477488769011822897 20660596108116576758867173)
      ·
        refine ⟨3873861770271858142287595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20660596108116576758867173 3873861770271858142287595)
        ·
          refine ⟨5810792655407787213431393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873861770271858142287595 5810792655407787213431393)
          ·
            refine ⟨4358094491555840410073545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810792655407787213431393 4358094491555840410073545)
            ·
              refine ⟨3268570868666880307555159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358094491555840410073545 3268570868666880307555159)
              ·
                refine ⟨4902856303000320461332739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3268570868666880307555159 4902856303000320461332739)
                ·
                  refine ⟨7354284454500480691999109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902856303000320461332739 7354284454500480691999109)
                  ·
                    refine ⟨1378928335218840129749833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7354284454500480691999109 1378928335218840129749833)
                    ·
                      refine ⟨1034196251414130097312375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1378928335218840129749833 1034196251414130097312375)
                      ·
                        rfl

theorem cell23_2014090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2014090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014090 prefixEnd_2014090 := by exact prefixLift 2014090
  have htrace : WordTrace (prefixWord ++ tailWord_2014090) baseStart_2014090 baseEnd_2014090 := by
    simpa [prefixWord, tailWord_2014090, baseEnd_2014090] using wordTrace_append hprefix tailTrace_2014090
  have hstable : (prefixWord ++ tailWord_2014090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014090).length < 2 ^ (prefixWord ++ tailWord_2014090).sum := by decide
  have hdescent : baseEnd_2014090 < baseStart_2014090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014113 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 5]
def baseStart_2014113 : Nat := 118140960795 + 2014113 * 2 ^ 59
def prefixEnd_2014113 : Nat := 4983230072969 + 3 ^ 40 * 2014113 * 2
def baseEnd_2014113 : Nat := 114912006829909278591641

theorem tailTrace_2014113 : CollatzResearch.WordTrace tailWord_2014113 prefixEnd_2014113 114912006829909278591641 := by
  unfold tailWord_2014113
  simp only [CollatzResearch.WordTrace]
  refine ⟨73460736152220058959614993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48973824101480039306409995 73460736152220058959614993)
  ·
    refine ⟨55095552114165044219711245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73460736152220058959614993 55095552114165044219711245)
    ·
      refine ⟨20660832042811891582391717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55095552114165044219711245 20660832042811891582391717)
      ·
        refine ⟨3873906008027229671698447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20660832042811891582391717 3873906008027229671698447)
        ·
          refine ⟨5810859012040844507547671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873906008027229671698447 5810859012040844507547671)
          ·
            refine ⟨8716288518061266761321507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810859012040844507547671 8716288518061266761321507)
            ·
              refine ⟨13074432777091900141982261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716288518061266761321507 13074432777091900141982261)
              ·
                refine ⟨1225728072852365638310837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13074432777091900141982261 1225728072852365638310837)
                ·
                  refine ⟨114912006829909278591641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1225728072852365638310837 114912006829909278591641)
                  ·
                    rfl

theorem cell23_2014113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 5].length) (baseStart_2014113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014113 prefixEnd_2014113 := by exact prefixLift 2014113
  have htrace : WordTrace (prefixWord ++ tailWord_2014113) baseStart_2014113 baseEnd_2014113 := by
    simpa [prefixWord, tailWord_2014113, baseEnd_2014113] using wordTrace_append hprefix tailTrace_2014113
  have hstable : (prefixWord ++ tailWord_2014113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014113).length < 2 ^ (prefixWord ++ tailWord_2014113).sum := by decide
  have hdescent : baseEnd_2014113 < baseStart_2014113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014149 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_2014149 : Nat := 118140960795 + 2014149 * 2 ^ 59
def prefixEnd_2014149 : Nat := 4983230072969 + 3 ^ 40 * 2014149 * 2
def baseEnd_2014149 : Nat := 1034226546772745366474603

theorem tailTrace_2014149 : CollatzResearch.WordTrace tailWord_2014149 prefixEnd_2014149 1034226546772745366474603 := by
  unfold tailWord_2014149
  simp only [CollatzResearch.WordTrace]
  refine ⟨73462049180089637107925501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48974699453393091405283667 73462049180089637107925501)
  ·
    refine ⟨27548268442533613915472063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73462049180089637107925501 27548268442533613915472063)
    ·
      refine ⟨41322402663800420873208095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27548268442533613915472063 41322402663800420873208095)
      ·
        refine ⟨61983603995700631309812143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41322402663800420873208095 61983603995700631309812143)
        ·
          refine ⟨92975405993550946964718215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61983603995700631309812143 92975405993550946964718215)
          ·
            refine ⟨139463108990326420447077323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92975405993550946964718215 139463108990326420447077323)
            ·
              refine ⟨209194663485489630670615985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139463108990326420447077323 209194663485489630670615985)
              ·
                refine ⟨156895997614117223002961989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209194663485489630670615985 156895997614117223002961989)
                ·
                  refine ⟨29417999552646979313055373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156895997614117223002961989 29417999552646979313055373)
                  ·
                    refine ⟨11031749832242617242395765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29417999552646979313055373 11031749832242617242395765)
                    ·
                      refine ⟨1034226546772745366474603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11031749832242617242395765 1034226546772745366474603)
                      ·
                        rfl

theorem cell23_2014149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_2014149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014149 prefixEnd_2014149 := by exact prefixLift 2014149
  have htrace : WordTrace (prefixWord ++ tailWord_2014149) baseStart_2014149 baseEnd_2014149 := by
    simpa [prefixWord, tailWord_2014149, baseEnd_2014149] using wordTrace_append hprefix tailTrace_2014149
  have hstable : (prefixWord ++ tailWord_2014149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014149).length < 2 ^ (prefixWord ++ tailWord_2014149).sum := by decide
  have hdescent : baseEnd_2014149 < baseStart_2014149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014183 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2014183 : Nat := 118140960795 + 2014183 * 2 ^ 59
def prefixEnd_2014183 : Nat := 4983230072969 + 3 ^ 40 * 2014183 * 2
def baseEnd_2014183 : Nat := 1034244005114998233449447

theorem tailTrace_2014183 : CollatzResearch.WordTrace tailWord_2014183 prefixEnd_2014183 1034244005114998233449447 := by
  unfold tailWord_2014183
  simp only [CollatzResearch.WordTrace]
  refine ⟨73463289261966460914663203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48975526174644307276442135 73463289261966460914663203)
  ·
    refine ⟨110194933892949691371994805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73463289261966460914663203 110194933892949691371994805)
    ·
      refine ⟨10330775052464033566124513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110194933892949691371994805 10330775052464033566124513)
      ·
        refine ⟨7748081289348025174593385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10330775052464033566124513 7748081289348025174593385)
        ·
          refine ⟨5811060967011018880945039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7748081289348025174593385 5811060967011018880945039)
          ·
            refine ⟨8716591450516528321417559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811060967011018880945039 8716591450516528321417559)
            ·
              refine ⟨13074887175774792482126339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716591450516528321417559 13074887175774792482126339)
              ·
                refine ⟨19612330763662188723189509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074887175774792482126339 19612330763662188723189509)
                ·
                  refine ⟨3677312018186660385598033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19612330763662188723189509 3677312018186660385598033)
                  ·
                    refine ⟨2757984013639995289198525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3677312018186660385598033 2757984013639995289198525)
                    ·
                      refine ⟨1034244005114998233449447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2757984013639995289198525 1034244005114998233449447)
                      ·
                        rfl

theorem cell23_2014183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2014183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014183 prefixEnd_2014183 := by exact prefixLift 2014183
  have htrace : WordTrace (prefixWord ++ tailWord_2014183) baseStart_2014183 baseEnd_2014183 := by
    simpa [prefixWord, tailWord_2014183, baseEnd_2014183] using wordTrace_append hprefix tailTrace_2014183
  have hstable : (prefixWord ++ tailWord_2014183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014183).length < 2 ^ (prefixWord ++ tailWord_2014183).sum := by decide
  have hdescent : baseEnd_2014183 < baseStart_2014183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014186 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_2014186 : Nat := 118140960795 + 2014186 * 2 ^ 59
def prefixEnd_2014186 : Nat := 4983230072969 + 3 ^ 40 * 2014186 * 2
def baseEnd_2014186 : Nat := 114916171728551302412437

theorem tailTrace_2014186 : CollatzResearch.WordTrace tailWord_2014186 prefixEnd_2014186 114916171728551302412437 := by
  unfold tailWord_2014186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18365849670238898106755603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48975599120637061618014941 18365849670238898106755603)
  ·
    refine ⟨27548774505358347160133405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18365849670238898106755603 27548774505358347160133405)
    ·
      refine ⟨10330790439509380185050027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27548774505358347160133405 10330790439509380185050027)
      ·
        refine ⟨15496185659264070277575041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330790439509380185050027 15496185659264070277575041)
        ·
          refine ⟨11622139244448052708181281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15496185659264070277575041 11622139244448052708181281)
          ·
            refine ⟨8716604433336039531135961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11622139244448052708181281 8716604433336039531135961)
            ·
              refine ⟨6537453325002029648351971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716604433336039531135961 6537453325002029648351971)
              ·
                refine ⟨9806179987503044472527957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537453325002029648351971 9806179987503044472527957)
                ·
                  refine ⟨114916171728551302412437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9806179987503044472527957 114916171728551302412437)
                  ·
                    rfl

theorem cell23_2014186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_2014186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014186 prefixEnd_2014186 := by exact prefixLift 2014186
  have htrace : WordTrace (prefixWord ++ tailWord_2014186) baseStart_2014186 baseEnd_2014186 := by
    simpa [prefixWord, tailWord_2014186, baseEnd_2014186] using wordTrace_append hprefix tailTrace_2014186
  have hstable : (prefixWord ++ tailWord_2014186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014186).length < 2 ^ (prefixWord ++ tailWord_2014186).sum := by decide
  have hdescent : baseEnd_2014186 < baseStart_2014186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014213 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_2014213 : Nat := 118140960795 + 2014213 * 2 ^ 59
def prefixEnd_2014213 : Nat := 4983230072969 + 3 ^ 40 * 2014213 * 2
def baseEnd_2014213 : Nat := 1034259409534633116074309

theorem tailTrace_2014213 : CollatzResearch.WordTrace tailWord_2014213 prefixEnd_2014213 1034259409534633116074309 := by
  unfold tailWord_2014213
  simp only [CollatzResearch.WordTrace]
  refine ⟨73464383451857776038255293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48976255634571850692170195 73464383451857776038255293)
  ·
    refine ⟨27549143794446666014345735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73464383451857776038255293 27549143794446666014345735)
    ·
      refine ⟨41323715691669999021518603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27549143794446666014345735 41323715691669999021518603)
      ·
        refine ⟨61985573537504998532277905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41323715691669999021518603 61985573537504998532277905)
        ·
          refine ⟨46489180153128748899208429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61985573537504998532277905 46489180153128748899208429)
          ·
            refine ⟨17433442557423280837203161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46489180153128748899208429 17433442557423280837203161)
            ·
              refine ⟨13075081918067460627902371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17433442557423280837203161 13075081918067460627902371)
              ·
                refine ⟨19612622877101190941853557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075081918067460627902371 19612622877101190941853557)
                ·
                  refine ⟨1838683394728236650798771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19612622877101190941853557 1838683394728236650798771)
                  ·
                    refine ⟨2758025092092354976198157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1838683394728236650798771 2758025092092354976198157)
                    ·
                      refine ⟨1034259409534633116074309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758025092092354976198157 1034259409534633116074309)
                      ·
                        rfl

theorem cell23_2014213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_2014213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014213 prefixEnd_2014213 := by exact prefixLift 2014213
  have htrace : WordTrace (prefixWord ++ tailWord_2014213) baseStart_2014213 baseEnd_2014213 := by
    simpa [prefixWord, tailWord_2014213, baseEnd_2014213] using wordTrace_append hprefix tailTrace_2014213
  have hstable : (prefixWord ++ tailWord_2014213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014213).length < 2 ^ (prefixWord ++ tailWord_2014213).sum := by decide
  have hdescent : baseEnd_2014213 < baseStart_2014213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014256 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_2014256 : Nat := 118140960795 + 2014256 * 2 ^ 59
def prefixEnd_2014256 : Nat := 4983230072969 + 3 ^ 40 * 2014256 * 2
def baseEnd_2014256 : Nat := 1034281489202776447836611

theorem tailTrace_2014256 : CollatzResearch.WordTrace tailWord_2014256 prefixEnd_2014256 1034281489202776447836611 := by
  unfold tailWord_2014256
  simp only [CollatzResearch.WordTrace]
  refine ⟨36732975895350997191035311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48977301193801329588047081 36732975895350997191035311)
  ·
    refine ⟨55099463843026495786552967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36732975895350997191035311 55099463843026495786552967)
    ·
      refine ⟨82649195764539743679829451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55099463843026495786552967 82649195764539743679829451)
      ·
        refine ⟨123973793646809615519744177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82649195764539743679829451 123973793646809615519744177)
        ·
          refine ⟨92980345235107211639808133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123973793646809615519744177 92980345235107211639808133)
          ·
            refine ⟨17433814731582602182464025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92980345235107211639808133 17433814731582602182464025)
            ·
              refine ⟨13075361048686951636848019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17433814731582602182464025 13075361048686951636848019)
              ·
                refine ⟨19613041573030427455272029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075361048686951636848019 19613041573030427455272029)
                ·
                  refine ⟨7354890589886410295727011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19613041573030427455272029 7354890589886410295727011)
                  ·
                    refine ⟨11032335884829615443590517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7354890589886410295727011 11032335884829615443590517)
                    ·
                      refine ⟨1034281489202776447836611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11032335884829615443590517 1034281489202776447836611)
                      ·
                        rfl

theorem cell23_2014256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_2014256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014256 prefixEnd_2014256 := by exact prefixLift 2014256
  have htrace : WordTrace (prefixWord ++ tailWord_2014256) baseStart_2014256 baseEnd_2014256 := by
    simpa [prefixWord, tailWord_2014256, baseEnd_2014256] using wordTrace_append hprefix tailTrace_2014256
  have hstable : (prefixWord ++ tailWord_2014256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014256).length < 2 ^ (prefixWord ++ tailWord_2014256).sum := by decide
  have hdescent : baseEnd_2014256 < baseStart_2014256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014266 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_2014266 : Nat := 118140960795 + 2014266 * 2 ^ 59
def prefixEnd_2014266 : Nat := 4983230072969 + 3 ^ 40 * 2014266 * 2
def baseEnd_2014266 : Nat := 1034286624009321408711565

theorem tailTrace_2014266 : CollatzResearch.WordTrace tailWord_2014266 prefixEnd_2014266 1034286624009321408711565 := by
  unfold tailWord_2014266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18366579130166441522483663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48977544347110510726623101 18366579130166441522483663)
  ·
    refine ⟨27549868695249662283725495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18366579130166441522483663 27549868695249662283725495)
    ·
      refine ⟨41324803042874493425588243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27549868695249662283725495 41324803042874493425588243)
      ·
        refine ⟨61987204564311740138382365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41324803042874493425588243 61987204564311740138382365)
        ·
          refine ⟨23245201711616902551893387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61987204564311740138382365 23245201711616902551893387)
          ·
            refine ⟨34867802567425353827840081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23245201711616902551893387 34867802567425353827840081)
            ·
              refine ⟨26150851925569015370880061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34867802567425353827840081 26150851925569015370880061)
              ·
                refine ⟨9806569472088380764080023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26150851925569015370880061 9806569472088380764080023)
                ·
                  refine ⟨14709854208132571146120035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806569472088380764080023 14709854208132571146120035)
                  ·
                    refine ⟨22064781312198856719180053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14709854208132571146120035 22064781312198856719180053)
                    ·
                      refine ⟨1034286624009321408711565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22064781312198856719180053 1034286624009321408711565)
                      ·
                        rfl

theorem cell23_2014266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_2014266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014266 prefixEnd_2014266 := by exact prefixLift 2014266
  have htrace : WordTrace (prefixWord ++ tailWord_2014266) baseStart_2014266 baseEnd_2014266 := by
    simpa [prefixWord, tailWord_2014266, baseEnd_2014266] using wordTrace_append hprefix tailTrace_2014266
  have hstable : (prefixWord ++ tailWord_2014266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014266).length < 2 ^ (prefixWord ++ tailWord_2014266).sum := by decide
  have hdescent : baseEnd_2014266 < baseStart_2014266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014270 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2014270 : Nat := 118140960795 + 2014270 * 2 ^ 59
def prefixEnd_2014270 : Nat := 4983230072969 + 3 ^ 40 * 2014270 * 2
def baseEnd_2014270 : Nat := 1034288677931939393061547

theorem tailTrace_2014270 : CollatzResearch.WordTrace tailWord_2014270 prefixEnd_2014270 1034288677931939393061547 := by
  unfold tailWord_2014270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183307801581409346635033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48977641608434183182053509 9183307801581409346635033)
  ·
    refine ⟨6887480851186057009976275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9183307801581409346635033 6887480851186057009976275)
    ·
      refine ⟨10331221276779085514964413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887480851186057009976275 10331221276779085514964413)
      ·
        refine ⟨3874207978792157068111655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10331221276779085514964413 3874207978792157068111655)
        ·
          refine ⟨5811311968188235602167483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874207978792157068111655 5811311968188235602167483)
          ·
            refine ⟨8716967952282353403251225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811311968188235602167483 8716967952282353403251225)
            ·
              refine ⟨6537725964211765052438419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716967952282353403251225 6537725964211765052438419)
              ·
                refine ⟨9806588946317647578657629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537725964211765052438419 9806588946317647578657629)
                ·
                  refine ⟨3677470854869117841996611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9806588946317647578657629 3677470854869117841996611)
                  ·
                    refine ⟨5516206282303676762994917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677470854869117841996611 5516206282303676762994917)
                    ·
                      refine ⟨1034288677931939393061547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5516206282303676762994917 1034288677931939393061547)
                      ·
                        rfl

theorem cell23_2014270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2014270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014270 prefixEnd_2014270 := by exact prefixLift 2014270
  have htrace : WordTrace (prefixWord ++ tailWord_2014270) baseStart_2014270 baseEnd_2014270 := by
    simpa [prefixWord, tailWord_2014270, baseEnd_2014270] using wordTrace_append hprefix tailTrace_2014270
  have hstable : (prefixWord ++ tailWord_2014270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014270).length < 2 ^ (prefixWord ++ tailWord_2014270).sum := by decide
  have hdescent : baseEnd_2014270 < baseStart_2014270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014336 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_2014336 : Nat := 118140960795 + 2014336 * 2 ^ 59
def prefixEnd_2014336 : Nat := 4983230072969 + 3 ^ 40 * 2014336 * 2
def baseEnd_2014336 : Nat := 344774189218378711612081

theorem tailTrace_2014336 : CollatzResearch.WordTrace tailWord_2014336 prefixEnd_2014336 344774189218378711612081 := by
  unfold tailWord_2014336
  simp only [CollatzResearch.WordTrace]
  refine ⟨36734434815206084022491431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48979246420274778696655241 36734434815206084022491431)
  ·
    refine ⟨55101652222809126033737147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36734434815206084022491431 55101652222809126033737147)
    ·
      refine ⟨82652478334213689050605721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55101652222809126033737147 82652478334213689050605721)
      ·
        refine ⟨61989358750660266787954291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82652478334213689050605721 61989358750660266787954291)
        ·
          refine ⟨92984038125990400181931437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61989358750660266787954291 92984038125990400181931437)
          ·
            refine ⟨34869014297246400068224289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92984038125990400181931437 34869014297246400068224289)
            ·
              refine ⟨26151760722934800051168217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34869014297246400068224289 26151760722934800051168217)
              ·
                refine ⟨19613820542201100038376163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26151760722934800051168217 19613820542201100038376163)
                ·
                  refine ⟨29420730813301650057564245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19613820542201100038376163 29420730813301650057564245)
                  ·
                    refine ⟨344774189218378711612081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29420730813301650057564245 344774189218378711612081)
                    ·
                      rfl

theorem cell23_2014336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_2014336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014336 prefixEnd_2014336 := by exact prefixLift 2014336
  have htrace : WordTrace (prefixWord ++ tailWord_2014336) baseStart_2014336 baseEnd_2014336 := by
    simpa [prefixWord, tailWord_2014336, baseEnd_2014336] using wordTrace_append hprefix tailTrace_2014336
  have hstable : (prefixWord ++ tailWord_2014336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014336).length < 2 ^ (prefixWord ++ tailWord_2014336).sum := by decide
  have hdescent : baseEnd_2014336 < baseStart_2014336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014381 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2014381 : Nat := 118140960795 + 2014381 * 2 ^ 59
def prefixEnd_2014381 : Nat := 4983230072969 + 3 ^ 40 * 2014381 * 2
def baseEnd_2014381 : Nat := 1034345674284588458773537

theorem tailTrace_2014381 : CollatzResearch.WordTrace tailWord_2014381 prefixEnd_2014381 1034345674284588458773537 := by
  unfold tailWord_2014381
  simp only [CollatzResearch.WordTrace]
  refine ⟨73470510915249140730370997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48980340610166093820247331 73470510915249140730370997)
  ·
    refine ⟨6887860398304606943472281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73470510915249140730370997 6887860398304606943472281)
    ·
      refine ⟨5165895298728455207604211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6887860398304606943472281 5165895298728455207604211)
      ·
        refine ⟨7748842948092682811406317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165895298728455207604211 7748842948092682811406317)
        ·
          refine ⟨2905816105534756054277369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7748842948092682811406317 2905816105534756054277369)
          ·
            refine ⟨2179362079151067040708027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905816105534756054277369 2179362079151067040708027)
            ·
              refine ⟨3269043118726600561062041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179362079151067040708027 3269043118726600561062041)
              ·
                refine ⟨2451782339044950420796531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269043118726600561062041 2451782339044950420796531)
                ·
                  refine ⟨3677673508567425631194797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451782339044950420796531 3677673508567425631194797)
                  ·
                    refine ⟨1379127565712784611698049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677673508567425631194797 1379127565712784611698049)
                    ·
                      refine ⟨1034345674284588458773537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379127565712784611698049 1034345674284588458773537)
                      ·
                        rfl

theorem cell23_2014381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2014381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014381 prefixEnd_2014381 := by exact prefixLift 2014381
  have htrace : WordTrace (prefixWord ++ tailWord_2014381) baseStart_2014381 baseEnd_2014381 := by
    simpa [prefixWord, tailWord_2014381, baseEnd_2014381] using wordTrace_append hprefix tailTrace_2014381
  have hstable : (prefixWord ++ tailWord_2014381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014381).length < 2 ^ (prefixWord ++ tailWord_2014381).sum := by decide
  have hdescent : baseEnd_2014381 < baseStart_2014381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014423 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_2014423 : Nat := 118140960795 + 2014423 * 2 ^ 59
def prefixEnd_2014423 : Nat := 4983230072969 + 3 ^ 40 * 2014423 * 2
def baseEnd_2014423 : Nat := 1034367240472077294448343

theorem tailTrace_2014423 : CollatzResearch.WordTrace tailWord_2014423 prefixEnd_2014423 1034367240472077294448343 := by
  unfold tailWord_2014423
  simp only [CollatzResearch.WordTrace]
  refine ⟨73472042781096981903399923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48981361854064654602266615 73472042781096981903399923)
  ·
    refine ⟨110208064171645472855099885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73472042781096981903399923 110208064171645472855099885)
    ·
      refine ⟨41328024064367052320662457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110208064171645472855099885 41328024064367052320662457)
      ·
        refine ⟨30996018048275289240496843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41328024064367052320662457 30996018048275289240496843)
        ·
          refine ⟨46494027072412933860745265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30996018048275289240496843 46494027072412933860745265)
          ·
            refine ⟨34870520304309700395558949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46494027072412933860745265 34870520304309700395558949)
            ·
              refine ⟨6538222557058068824167303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34870520304309700395558949 6538222557058068824167303)
              ·
                refine ⟨9807333835587103236250955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538222557058068824167303 9807333835587103236250955)
                ·
                  refine ⟨14711000753380654854376433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807333835587103236250955 14711000753380654854376433)
                  ·
                    refine ⟨11033250565035491140782325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14711000753380654854376433 11033250565035491140782325)
                    ·
                      refine ⟨1034367240472077294448343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11033250565035491140782325 1034367240472077294448343)
                      ·
                        rfl

theorem cell23_2014423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_2014423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014423 prefixEnd_2014423 := by exact prefixLift 2014423
  have htrace : WordTrace (prefixWord ++ tailWord_2014423) baseStart_2014423 baseEnd_2014423 := by
    simpa [prefixWord, tailWord_2014423, baseEnd_2014423] using wordTrace_append hprefix tailTrace_2014423
  have hstable : (prefixWord ++ tailWord_2014423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014423).length < 2 ^ (prefixWord ++ tailWord_2014423).sum := by decide
  have hdescent : baseEnd_2014423 < baseStart_2014423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014447 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 2, 5]
def baseStart_2014447 : Nat := 118140960795 + 2014447 * 2 ^ 59
def prefixEnd_2014447 : Nat := 4983230072969 + 3 ^ 40 * 2014447 * 2
def baseEnd_2014447 : Nat := 344793188002595066849411

theorem tailTrace_2014447 : CollatzResearch.WordTrace tailWord_2014447 prefixEnd_2014447 344793188002595066849411 := by
  unfold tailWord_2014447
  simp only [CollatzResearch.WordTrace]
  refine ⟨73472918133010034002273595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48981945422006689334849063 73472918133010034002273595)
  ·
    refine ⟨110209377199515051003410393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73472918133010034002273595 110209377199515051003410393)
    ·
      refine ⟨82657032899636288252557795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110209377199515051003410393 82657032899636288252557795)
      ·
        refine ⟨123985549349454432378836693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82657032899636288252557795 123985549349454432378836693)
        ·
          refine ⟨2905911312877838258878985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 123985549349454432378836693 2905911312877838258878985)
          ·
            refine ⟨2179433484658378694159239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905911312877838258878985 2179433484658378694159239)
            ·
              refine ⟨3269150226987568041238859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179433484658378694159239 3269150226987568041238859)
              ·
                refine ⟨4903725340481352061858289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269150226987568041238859 4903725340481352061858289)
                ·
                  refine ⟨3677794005361014046393717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903725340481352061858289 3677794005361014046393717)
                  ·
                    refine ⟨344793188002595066849411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3677794005361014046393717 344793188002595066849411)
                    ·
                      rfl

theorem cell23_2014447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_2014447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014447 prefixEnd_2014447 := by exact prefixLift 2014447
  have htrace : WordTrace (prefixWord ++ tailWord_2014447) baseStart_2014447 baseEnd_2014447 := by
    simpa [prefixWord, tailWord_2014447, baseEnd_2014447] using wordTrace_append hprefix tailTrace_2014447
  have hstable : (prefixWord ++ tailWord_2014447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014447).length < 2 ^ (prefixWord ++ tailWord_2014447).sum := by decide
  have hdescent : baseEnd_2014447 < baseStart_2014447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014463 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_2014463 : Nat := 118140960795 + 2014463 * 2 ^ 59
def prefixEnd_2014463 : Nat := 4983230072969 + 3 ^ 40 * 2014463 * 2
def baseEnd_2014463 : Nat := 1034387779698257137948159

theorem tailTrace_2014463 : CollatzResearch.WordTrace tailWord_2014463 prefixEnd_2014463 1034387779698257137948159 := by
  unfold tailWord_2014463
  simp only [CollatzResearch.WordTrace]
  refine ⟨73473501700952068734856043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48982334467301379156570695 73473501700952068734856043)
  ·
    refine ⟨110210252551428103102284065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73473501700952068734856043 110210252551428103102284065)
    ·
      refine ⟨82657689413571077326713049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110210252551428103102284065 82657689413571077326713049)
      ·
        refine ⟨61993267060178307995034787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82657689413571077326713049 61993267060178307995034787)
        ·
          refine ⟨92989900590267461992552181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61993267060178307995034787 92989900590267461992552181)
          ·
            refine ⟨8717803180337574561801767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92989900590267461992552181 8717803180337574561801767)
            ·
              refine ⟨13076704770506361842702651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717803180337574561801767 13076704770506361842702651)
              ·
                refine ⟨19615057155759542764053977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076704770506361842702651 19615057155759542764053977)
                ·
                  refine ⟨14711292866819657073040483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19615057155759542764053977 14711292866819657073040483)
                  ·
                    refine ⟨22066939300229485609560725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14711292866819657073040483 22066939300229485609560725)
                    ·
                      refine ⟨1034387779698257137948159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22066939300229485609560725 1034387779698257137948159)
                      ·
                        rfl

theorem cell23_2014463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_2014463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014463 prefixEnd_2014463 := by exact prefixLift 2014463
  have htrace : WordTrace (prefixWord ++ tailWord_2014463) baseStart_2014463 baseEnd_2014463 := by
    simpa [prefixWord, tailWord_2014463, baseEnd_2014463] using wordTrace_append hprefix tailTrace_2014463
  have hstable : (prefixWord ++ tailWord_2014463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014463).length < 2 ^ (prefixWord ++ tailWord_2014463).sum := by decide
  have hdescent : baseEnd_2014463 < baseStart_2014463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014473 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 8]
def baseStart_2014473 : Nat := 118140960795 + 2014473 * 2 ^ 59
def prefixEnd_2014473 : Nat := 4983230072969 + 3 ^ 40 * 2014473 * 2
def baseEnd_2014473 : Nat := 114932546056089122091457

theorem tailTrace_2014473 : CollatzResearch.WordTrace tailWord_2014473 prefixEnd_2014473 114932546056089122091457 := by
  unfold tailWord_2014473
  simp only [CollatzResearch.WordTrace]
  refine ⟨73473866430915840442720073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48982577620610560295146715 73473866430915840442720073)
  ·
    refine ⟨55105399823186880332040055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73473866430915840442720073 55105399823186880332040055)
    ·
      refine ⟨82658099734780320498060083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55105399823186880332040055 82658099734780320498060083)
      ·
        refine ⟨123987149602170480747090125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82658099734780320498060083 123987149602170480747090125)
        ·
          refine ⟨46495181100813930280158797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123987149602170480747090125 46495181100813930280158797)
          ·
            refine ⟨17435692912805223855059549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46495181100813930280158797 17435692912805223855059549)
            ·
              refine ⟨6538384842301958945647331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17435692912805223855059549 6538384842301958945647331)
              ·
                refine ⟨9807577263452938418470997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538384842301958945647331 9807577263452938418470997)
                ·
                  refine ⟨114932546056089122091457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9807577263452938418470997 114932546056089122091457)
                  ·
                    rfl

theorem cell23_2014473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_2014473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014473 prefixEnd_2014473 := by exact prefixLift 2014473
  have htrace : WordTrace (prefixWord ++ tailWord_2014473) baseStart_2014473 baseEnd_2014473 := by
    simpa [prefixWord, tailWord_2014473, baseEnd_2014473] using wordTrace_append hprefix tailTrace_2014473
  have hstable : (prefixWord ++ tailWord_2014473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014473).length < 2 ^ (prefixWord ++ tailWord_2014473).sum := by decide
  have hdescent : baseEnd_2014473 < baseStart_2014473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014500 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2014500 : Nat := 118140960795 + 2014500 * 2 ^ 59
def prefixEnd_2014500 : Nat := 4983230072969 + 3 ^ 40 * 2014500 * 2
def baseEnd_2014500 : Nat := 1034406778482473493185489

theorem tailTrace_2014500 : CollatzResearch.WordTrace tailWord_2014500 prefixEnd_2014500 1034406778482473493185489 := by
  unfold tailWord_2014500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36737425600909012026976477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48983234134545349369301969 36737425600909012026976477)
  ·
    refine ⟨13776534600340879510116179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36737425600909012026976477 13776534600340879510116179)
    ·
      refine ⟨20664801900511319265174269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13776534600340879510116179 20664801900511319265174269)
      ·
        refine ⟨7749300712691744724440351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20664801900511319265174269 7749300712691744724440351)
        ·
          refine ⟨11623951069037617086660527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749300712691744724440351 11623951069037617086660527)
          ·
            refine ⟨17435926603556425629990791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623951069037617086660527 17435926603556425629990791)
            ·
              refine ⟨26153889905334638444986187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17435926603556425629990791 26153889905334638444986187)
              ·
                refine ⟨39230834858001957667479281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26153889905334638444986187 39230834858001957667479281)
                ·
                  refine ⟨29423126143501468250609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39230834858001957667479281 29423126143501468250609461)
                  ·
                    refine ⟨2758418075953262648494637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29423126143501468250609461 2758418075953262648494637)
                    ·
                      refine ⟨1034406778482473493185489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758418075953262648494637 1034406778482473493185489)
                      ·
                        rfl

theorem cell23_2014500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2014500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014500 prefixEnd_2014500 := by exact prefixLift 2014500
  have htrace : WordTrace (prefixWord ++ tailWord_2014500) baseStart_2014500 baseEnd_2014500 := by
    simpa [prefixWord, tailWord_2014500, baseEnd_2014500] using wordTrace_append hprefix tailTrace_2014500
  have hstable : (prefixWord ++ tailWord_2014500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014500).length < 2 ^ (prefixWord ++ tailWord_2014500).sum := by decide
  have hdescent : baseEnd_2014500 < baseStart_2014500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014523 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_2014523 : Nat := 118140960795 + 2014523 * 2 ^ 59
def prefixEnd_2014523 : Nat := 4983230072969 + 3 ^ 40 * 2014523 * 2
def baseEnd_2014523 : Nat := 1034418588537526903197883

theorem tailTrace_2014523 : CollatzResearch.WordTrace tailWord_2014523 prefixEnd_2014523 1034418588537526903197883 := by
  unfold tailWord_2014523
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475690080734698982040223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48983793387156465988026815 73475690080734698982040223)
  ·
    refine ⟨110213535121102048473060335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73475690080734698982040223 110213535121102048473060335)
    ·
      refine ⟨165320302681653072709590503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110213535121102048473060335 165320302681653072709590503)
      ·
        refine ⟨247980454022479609064385755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165320302681653072709590503 247980454022479609064385755)
        ·
          refine ⟨371970681033719413596578633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247980454022479609064385755 371970681033719413596578633)
          ·
            refine ⟨278978010775289560197433975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371970681033719413596578633 278978010775289560197433975)
            ·
              refine ⟨418467016162934340296150963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278978010775289560197433975 418467016162934340296150963)
              ·
                refine ⟨627700524244401510444226445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418467016162934340296150963 627700524244401510444226445)
                ·
                  refine ⟨235387696591650566416584917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627700524244401510444226445 235387696591650566416584917)
                  ·
                    refine ⟨5516899138866810150388709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235387696591650566416584917 5516899138866810150388709)
                    ·
                      refine ⟨1034418588537526903197883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5516899138866810150388709 1034418588537526903197883)
                      ·
                        rfl

theorem cell23_2014523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_2014523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014523 prefixEnd_2014523 := by exact prefixLift 2014523
  have htrace : WordTrace (prefixWord ++ tailWord_2014523) baseStart_2014523 baseEnd_2014523 := by
    simpa [prefixWord, tailWord_2014523, baseEnd_2014523] using wordTrace_append hprefix tailTrace_2014523
  have hstable : (prefixWord ++ tailWord_2014523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014523).length < 2 ^ (prefixWord ++ tailWord_2014523).sum := by decide
  have hdescent : baseEnd_2014523 < baseStart_2014523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014527 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 4, 3, 2]
def baseStart_2014527 : Nat := 118140960795 + 2014527 * 2 ^ 59
def prefixEnd_2014527 : Nat := 4983230072969 + 3 ^ 40 * 2014527 * 2
def baseEnd_2014527 : Nat := 1034420642460144887547865

theorem tailTrace_2014527 : CollatzResearch.WordTrace tailWord_2014527 prefixEnd_2014527 1034420642460144887547865 := by
  unfold tailWord_2014527
  simp only [CollatzResearch.WordTrace]
  refine ⟨73475835972720207665185835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48983890648480138443457223 73475835972720207665185835)
  ·
    refine ⟨110213753959080311497778753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73475835972720207665185835 110213753959080311497778753)
    ·
      refine ⟨82660315469310233623334065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110213753959080311497778753 82660315469310233623334065)
      ·
        refine ⟨61995236601982675217500549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82660315469310233623334065 61995236601982675217500549)
        ·
          refine ⟨11624106862871751603281353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61995236601982675217500549 11624106862871751603281353)
          ·
            refine ⟨8718080147153813702461015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11624106862871751603281353 8718080147153813702461015)
            ·
              refine ⟨13077120220730720553691523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718080147153813702461015 13077120220730720553691523)
              ·
                refine ⟨19615680331096080830537285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13077120220730720553691523 19615680331096080830537285)
                ·
                  refine ⟨3677940062080515155725741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19615680331096080830537285 3677940062080515155725741)
                  ·
                    refine ⟨1379227523280193183397153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3677940062080515155725741 1379227523280193183397153)
                    ·
                      refine ⟨1034420642460144887547865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379227523280193183397153 1034420642460144887547865)
                      ·
                        rfl

theorem cell23_2014527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_2014527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014527 prefixEnd_2014527 := by exact prefixLift 2014527
  have htrace : WordTrace (prefixWord ++ tailWord_2014527) baseStart_2014527 baseEnd_2014527 := by
    simpa [prefixWord, tailWord_2014527, baseEnd_2014527] using wordTrace_append hprefix tailTrace_2014527
  have hstable : (prefixWord ++ tailWord_2014527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014527).length < 2 ^ (prefixWord ++ tailWord_2014527).sum := by decide
  have hdescent : baseEnd_2014527 < baseStart_2014527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014543 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_2014543 : Nat := 118140960795 + 2014543 * 2 ^ 59
def prefixEnd_2014543 : Nat := 4983230072969 + 3 ^ 40 * 2014543 * 2
def baseEnd_2014543 : Nat := 1034428858150616824947791

theorem tailTrace_2014543 : CollatzResearch.WordTrace tailWord_2014543 prefixEnd_2014543 1034428858150616824947791 := by
  unfold tailWord_2014543
  simp only [CollatzResearch.WordTrace]
  refine ⟨73476419540662242397768283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48984279693774828265178855 73476419540662242397768283)
  ·
    refine ⟨110214629310993363596652425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73476419540662242397768283 110214629310993363596652425)
    ·
      refine ⟨82660971983245022697489319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110214629310993363596652425 82660971983245022697489319)
      ·
        refine ⟨123991457974867534046233979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82660971983245022697489319 123991457974867534046233979)
        ·
          refine ⟨185987186962301301069350969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123991457974867534046233979 185987186962301301069350969)
          ·
            refine ⟨139490390221725975802013227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185987186962301301069350969 139490390221725975802013227)
            ·
              refine ⟨209235585332588963703019841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139490390221725975802013227 209235585332588963703019841)
              ·
                refine ⟨156926688999441722777264881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209235585332588963703019841 156926688999441722777264881)
                ·
                  refine ⟨117695016749581292082948661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156926688999441722777264881 117695016749581292082948661)
                  ·
                    refine ⟨11033907820273246132776437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117695016749581292082948661 11033907820273246132776437)
                    ·
                      refine ⟨1034428858150616824947791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11033907820273246132776437 1034428858150616824947791)
                      ·
                        rfl

theorem cell23_2014543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_2014543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014543 prefixEnd_2014543 := by exact prefixLift 2014543
  have htrace : WordTrace (prefixWord ++ tailWord_2014543) baseStart_2014543 baseEnd_2014543 := by
    simpa [prefixWord, tailWord_2014543, baseEnd_2014543] using wordTrace_append hprefix tailTrace_2014543
  have hstable : (prefixWord ++ tailWord_2014543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014543).length < 2 ^ (prefixWord ++ tailWord_2014543).sum := by decide
  have hdescent : baseEnd_2014543 < baseStart_2014543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014567 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2014567 : Nat := 118140960795 + 2014567 * 2 ^ 59
def prefixEnd_2014567 : Nat := 4983230072969 + 3 ^ 40 * 2014567 * 2
def baseEnd_2014567 : Nat := 344813727228774910349227

theorem tailTrace_2014567 : CollatzResearch.WordTrace tailWord_2014567 prefixEnd_2014567 344813727228774910349227 := by
  unfold tailWord_2014567
  simp only [CollatzResearch.WordTrace]
  refine ⟨73477294892575294496641955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48984863261716862997761303 73477294892575294496641955)
  ·
    refine ⟨110215942338862941744962933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73477294892575294496641955 110215942338862941744962933)
    ·
      refine ⟨10332744594268400788590275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110215942338862941744962933 10332744594268400788590275)
      ·
        refine ⟨15499116891402601182885413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332744594268400788590275 15499116891402601182885413)
        ·
          refine ⟨2906084417137987721791015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15499116891402601182885413 2906084417137987721791015)
          ·
            refine ⟨4359126625706981582686523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906084417137987721791015 4359126625706981582686523)
            ·
              refine ⟨6538689938560472374029785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359126625706981582686523 6538689938560472374029785)
              ·
                refine ⟨4904017453920354280522339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6538689938560472374029785 4904017453920354280522339)
                ·
                  refine ⟨7356026180880531420783509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904017453920354280522339 7356026180880531420783509)
                  ·
                    refine ⟨344813727228774910349227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7356026180880531420783509 344813727228774910349227)
                    ·
                      rfl

theorem cell23_2014567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2014567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014567 prefixEnd_2014567 := by exact prefixLift 2014567
  have htrace : WordTrace (prefixWord ++ tailWord_2014567) baseStart_2014567 baseEnd_2014567 := by
    simpa [prefixWord, tailWord_2014567, baseEnd_2014567] using wordTrace_append hprefix tailTrace_2014567
  have hstable : (prefixWord ++ tailWord_2014567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014567).length < 2 ^ (prefixWord ++ tailWord_2014567).sum := by decide
  have hdescent : baseEnd_2014567 < baseStart_2014567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014577 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_2014577 : Nat := 118140960795 + 2014577 * 2 ^ 59
def prefixEnd_2014577 : Nat := 4983230072969 + 3 ^ 40 * 2014577 * 2
def baseEnd_2014577 : Nat := 1034446316492869691922635

theorem tailTrace_2014577 : CollatzResearch.WordTrace tailWord_2014577 prefixEnd_2014577 1034446316492869691922635 := by
  unfold tailWord_2014577
  simp only [CollatzResearch.WordTrace]
  refine ⟨73477659622539066204505985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48985106415026044136337323 73477659622539066204505985)
  ·
    refine ⟨55108244716904299653379489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73477659622539066204505985 55108244716904299653379489)
    ·
      refine ⟨41331183537678224740034617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55108244716904299653379489 41331183537678224740034617)
      ·
        refine ⟨30998387653258668555025963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41331183537678224740034617 30998387653258668555025963)
        ·
          refine ⟨46497581479888002832538945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30998387653258668555025963 46497581479888002832538945)
          ·
            refine ⟨34873186109916002124404209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46497581479888002832538945 34873186109916002124404209)
            ·
              refine ⟨26154889582437001593303157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34873186109916002124404209 26154889582437001593303157)
              ·
                refine ⟨2452020898353468899372171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26154889582437001593303157 2452020898353468899372171)
                ·
                  refine ⟨3678031347530203349058257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452020898353468899372171 3678031347530203349058257)
                  ·
                    refine ⟨2758523510647652511793693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678031347530203349058257 2758523510647652511793693)
                    ·
                      refine ⟨1034446316492869691922635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758523510647652511793693 1034446316492869691922635)
                      ·
                        rfl

theorem cell23_2014577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_2014577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014577 prefixEnd_2014577 := by exact prefixLift 2014577
  have htrace : WordTrace (prefixWord ++ tailWord_2014577) baseStart_2014577 baseEnd_2014577 := by
    simpa [prefixWord, tailWord_2014577, baseEnd_2014577] using wordTrace_append hprefix tailTrace_2014577
  have hstable : (prefixWord ++ tailWord_2014577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014577).length < 2 ^ (prefixWord ++ tailWord_2014577).sum := by decide
  have hdescent : baseEnd_2014577 < baseStart_2014577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014650 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_2014650 : Nat := 118140960795 + 2014650 * 2 ^ 59
def prefixEnd_2014650 : Nat := 4983230072969 + 3 ^ 40 * 2014650 * 2
def baseEnd_2014650 : Nat := 1034483800580647906309799

theorem tailTrace_2014650 : CollatzResearch.WordTrace tailWord_2014650 prefixEnd_2014650 1034483800580647906309799 := by
  unfold tailWord_2014650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370080537818649917978351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48986881434183066447942269 18370080537818649917978351)
  ·
    refine ⟨27555120806727974876967527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18370080537818649917978351 27555120806727974876967527)
    ·
      refine ⟨41332681210091962315451291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27555120806727974876967527 41332681210091962315451291)
      ·
        refine ⟨61999021815137943473176937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41332681210091962315451291 61999021815137943473176937)
        ·
          refine ⟨46499266361353457604882703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61999021815137943473176937 46499266361353457604882703)
          ·
            refine ⟨69748899542030186407324055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46499266361353457604882703 69748899542030186407324055)
            ·
              refine ⟨104623349313045279610986083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69748899542030186407324055 104623349313045279610986083)
              ·
                refine ⟨156935023969567919416479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104623349313045279610986083 156935023969567919416479125)
                ·
                  refine ⟨7356329248573496222647459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156935023969567919416479125 7356329248573496222647459)
                  ·
                    refine ⟨11034493872860244333971189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7356329248573496222647459 11034493872860244333971189)
                    ·
                      refine ⟨1034483800580647906309799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11034493872860244333971189 1034483800580647906309799)
                      ·
                        rfl

theorem cell23_2014650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_2014650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014650 prefixEnd_2014650 := by exact prefixLift 2014650
  have htrace : WordTrace (prefixWord ++ tailWord_2014650) baseStart_2014650 baseEnd_2014650 := by
    simpa [prefixWord, tailWord_2014650, baseEnd_2014650] using wordTrace_append hprefix tailTrace_2014650
  have hstable : (prefixWord ++ tailWord_2014650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014650).length < 2 ^ (prefixWord ++ tailWord_2014650).sum := by decide
  have hdescent : baseEnd_2014650 < baseStart_2014650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014700 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_2014700 : Nat := 118140960795 + 2014700 * 2 ^ 59
def prefixEnd_2014700 : Nat := 4983230072969 + 3 ^ 40 * 2014700 * 2
def baseEnd_2014700 : Nat := 344836491537790903561523

theorem tailTrace_2014700 : CollatzResearch.WordTrace tailWord_2014700 prefixEnd_2014700 344836491537790903561523 := by
  unfold tailWord_2014700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36741072900546729105616777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48988097200728972140822369 36741072900546729105616777)
  ·
    refine ⟨27555804675410046829212583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36741072900546729105616777 27555804675410046829212583)
    ·
      refine ⟨41333707013115070243818875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27555804675410046829212583 41333707013115070243818875)
      ·
        refine ⟨62000560519672605365728313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41333707013115070243818875 62000560519672605365728313)
        ·
          refine ⟨46500420389754454024296235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62000560519672605365728313 46500420389754454024296235)
          ·
            refine ⟨69750630584631681036444353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46500420389754454024296235 69750630584631681036444353)
            ·
              refine ⟨52312972938473760777333265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69750630584631681036444353 52312972938473760777333265)
              ·
                refine ⟨39234729703855320582999949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52312972938473760777333265 39234729703855320582999949)
                ·
                  refine ⟨14713023638945745218624981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39234729703855320582999949 14713023638945745218624981)
                  ·
                    refine ⟨344836491537790903561523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14713023638945745218624981 344836491537790903561523)
                    ·
                      rfl

theorem cell23_2014700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_2014700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014700 prefixEnd_2014700 := by exact prefixLift 2014700
  have htrace : WordTrace (prefixWord ++ tailWord_2014700) baseStart_2014700 baseEnd_2014700 := by
    simpa [prefixWord, tailWord_2014700, baseEnd_2014700] using wordTrace_append hprefix tailTrace_2014700
  have hstable : (prefixWord ++ tailWord_2014700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014700).length < 2 ^ (prefixWord ++ tailWord_2014700).sum := by decide
  have hdescent : baseEnd_2014700 < baseStart_2014700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014754 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_2014754 : Nat := 118140960795 + 2014754 * 2 ^ 59
def prefixEnd_2014754 : Nat := 4983230072969 + 3 ^ 40 * 2014754 * 2
def baseEnd_2014754 : Nat := 1034537202568715499409321

theorem tailTrace_2014754 : CollatzResearch.WordTrace tailWord_2014754 prefixEnd_2014754 1034537202568715499409321 := by
  unfold tailWord_2014754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371028835724456358424829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48989410228598550289132877 18371028835724456358424829)
  ·
    refine ⟨6889135813396671134409311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18371028835724456358424829 6889135813396671134409311)
    ·
      refine ⟨10333703720095006701613967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889135813396671134409311 10333703720095006701613967)
      ·
        refine ⟨15500555580142510052420951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10333703720095006701613967 15500555580142510052420951)
        ·
          refine ⟨23250833370213765078631427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15500555580142510052420951 23250833370213765078631427)
          ·
            refine ⟨34876250055320647617947141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250833370213765078631427 34876250055320647617947141)
            ·
              refine ⟨6539296885372621428365089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34876250055320647617947141 6539296885372621428365089)
              ·
                refine ⟨4904472664029466071273817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539296885372621428365089 4904472664029466071273817)
                ·
                  refine ⟨3678354498022099553455363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904472664029466071273817 3678354498022099553455363)
                  ·
                    refine ⟨5517531747033149330183045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3678354498022099553455363 5517531747033149330183045)
                    ·
                      refine ⟨1034537202568715499409321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5517531747033149330183045 1034537202568715499409321)
                      ·
                        rfl

theorem cell23_2014754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_2014754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014754 prefixEnd_2014754 := by exact prefixLift 2014754
  have htrace : WordTrace (prefixWord ++ tailWord_2014754) baseStart_2014754 baseEnd_2014754 := by
    simpa [prefixWord, tailWord_2014754, baseEnd_2014754] using wordTrace_append hprefix tailTrace_2014754
  have hstable : (prefixWord ++ tailWord_2014754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014754).length < 2 ^ (prefixWord ++ tailWord_2014754).sum := by decide
  have hdescent : baseEnd_2014754 < baseStart_2014754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014757 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_2014757 : Nat := 118140960795 + 2014757 * 2 ^ 59
def prefixEnd_2014757 : Nat := 4983230072969 + 3 ^ 40 * 2014757 * 2
def baseEnd_2014757 : Nat := 1034538743010678987671807

theorem tailTrace_2014757 : CollatzResearch.WordTrace tailWord_2014757 prefixEnd_2014757 1034538743010678987671807 := by
  unfold tailWord_2014757
  simp only [CollatzResearch.WordTrace]
  refine ⟨73484224761886956946058525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48989483174591304630705683 73484224761886956946058525)
  ·
    refine ⟨27556584285707608854771947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73484224761886956946058525 27556584285707608854771947)
    ·
      refine ⟨41334876428561413282157921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27556584285707608854771947 41334876428561413282157921)
      ·
        refine ⟨31001157321421059961618441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41334876428561413282157921 31001157321421059961618441)
        ·
          refine ⟨23250867991065794971213831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31001157321421059961618441 23250867991065794971213831)
          ·
            refine ⟨34876301986598692456820747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250867991065794971213831 34876301986598692456820747)
            ·
              refine ⟨52314452979898038685231121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34876301986598692456820747 52314452979898038685231121)
              ·
                refine ⟨39235839734923529013923341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52314452979898038685231121 39235839734923529013923341)
                ·
                  refine ⟨14713439900596323380221253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39235839734923529013923341 14713439900596323380221253)
                  ·
                    refine ⟨2758769981361810633791485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14713439900596323380221253 2758769981361810633791485)
                    ·
                      refine ⟨1034538743010678987671807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758769981361810633791485 1034538743010678987671807)
                      ·
                        rfl

theorem cell23_2014757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_2014757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014757 prefixEnd_2014757 := by exact prefixLift 2014757
  have htrace : WordTrace (prefixWord ++ tailWord_2014757) baseStart_2014757 baseEnd_2014757 := by
    simpa [prefixWord, tailWord_2014757, baseEnd_2014757] using wordTrace_append hprefix tailTrace_2014757
  have hstable : (prefixWord ++ tailWord_2014757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014757).length < 2 ^ (prefixWord ++ tailWord_2014757).sum := by decide
  have hdescent : baseEnd_2014757 < baseStart_2014757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014781 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2014781 : Nat := 118140960795 + 2014781 * 2 ^ 59
def prefixEnd_2014781 : Nat := 4983230072969 + 3 ^ 40 * 2014781 * 2
def baseEnd_2014781 : Nat := 344850355515462297923899

theorem tailTrace_2014781 : CollatzResearch.WordTrace tailWord_2014781 prefixEnd_2014781 344850355515462297923899 := by
  unfold tailWord_2014781
  simp only [CollatzResearch.WordTrace]
  refine ⟨73485100113800009044932197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48990066742533339363288131 73485100113800009044932197)
  ·
    refine ⟨13778456271337501695924787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73485100113800009044932197 13778456271337501695924787)
    ·
      refine ⟨20667684407006252543887181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13778456271337501695924787 20667684407006252543887181)
      ·
        refine ⟨7750381652627344703957693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20667684407006252543887181 7750381652627344703957693)
        ·
          refine ⟨2906393119735254263984135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7750381652627344703957693 2906393119735254263984135)
          ·
            refine ⟨4359589679602881395976203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906393119735254263984135 4359589679602881395976203)
            ·
              refine ⟨6539384519404322093964305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359589679602881395976203 6539384519404322093964305)
              ·
                refine ⟨4904538389553241570473229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539384519404322093964305 4904538389553241570473229)
                ·
                  refine ⟨1839201896082465588927461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4904538389553241570473229 1839201896082465588927461)
                  ·
                    refine ⟨344850355515462297923899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1839201896082465588927461 344850355515462297923899)
                    ·
                      rfl

theorem cell23_2014781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2014781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014781 prefixEnd_2014781 := by exact prefixLift 2014781
  have htrace : WordTrace (prefixWord ++ tailWord_2014781) baseStart_2014781 baseEnd_2014781 := by
    simpa [prefixWord, tailWord_2014781, baseEnd_2014781] using wordTrace_append hprefix tailTrace_2014781
  have hstable : (prefixWord ++ tailWord_2014781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014781).length < 2 ^ (prefixWord ++ tailWord_2014781).sum := by decide
  have hdescent : baseEnd_2014781 < baseStart_2014781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014821 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2014821 : Nat := 118140960795 + 2014821 * 2 ^ 59
def prefixEnd_2014821 : Nat := 4983230072969 + 3 ^ 40 * 2014821 * 2
def baseEnd_2014821 : Nat := 1034571605772566737271513

theorem tailTrace_2014821 : CollatzResearch.WordTrace tailWord_2014821 prefixEnd_2014821 1034571605772566737271513 := by
  unfold tailWord_2014821
  simp only [CollatzResearch.WordTrace]
  refine ⟨73486559033655095876388317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48991039355770063917592211 73486559033655095876388317)
  ·
    refine ⟨27557459637620660953645619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73486559033655095876388317 27557459637620660953645619)
    ·
      refine ⟨41336189456430991430468429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27557459637620660953645619 41336189456430991430468429)
      ·
        refine ⟨15501071046161621786425661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41336189456430991430468429 15501071046161621786425661)
        ·
          refine ⟨5812901642310608169909623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15501071046161621786425661 5812901642310608169909623)
          ·
            refine ⟨8719352463465912254864435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812901642310608169909623 8719352463465912254864435)
            ·
              refine ⟨13079028695198868382296653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719352463465912254864435 13079028695198868382296653)
              ·
                refine ⟨4904635760699575643361245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13079028695198868382296653 4904635760699575643361245)
                ·
                  refine ⟨1839238410262340866260467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4904635760699575643361245 1839238410262340866260467)
                  ·
                    refine ⟨2758857615393511299390701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839238410262340866260467 2758857615393511299390701)
                    ·
                      refine ⟨1034571605772566737271513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758857615393511299390701 1034571605772566737271513)
                      ·
                        rfl

theorem cell23_2014821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2014821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014821 prefixEnd_2014821 := by exact prefixLift 2014821
  have htrace : WordTrace (prefixWord ++ tailWord_2014821) baseStart_2014821 baseEnd_2014821 := by
    simpa [prefixWord, tailWord_2014821, baseEnd_2014821] using wordTrace_append hprefix tailTrace_2014821
  have hstable : (prefixWord ++ tailWord_2014821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014821).length < 2 ^ (prefixWord ++ tailWord_2014821).sum := by decide
  have hdescent : baseEnd_2014821 < baseStart_2014821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014838 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2014838 : Nat := 118140960795 + 2014838 * 2 ^ 59
def prefixEnd_2014838 : Nat := 4983230072969 + 3 ^ 40 * 2014838 * 2
def baseEnd_2014838 : Nat := 1034580334943693170758935

theorem tailTrace_2014838 : CollatzResearch.WordTrace tailWord_2014838 prefixEnd_2014838 1034580334943693170758935 := by
  unfold tailWord_2014838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592948692162094236234823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48991452716395671853171445 4592948692162094236234823)
  ·
    refine ⟨6889423038243141354352235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4592948692162094236234823 6889423038243141354352235)
    ·
      refine ⟨10334134557364712031528353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889423038243141354352235 10334134557364712031528353)
      ·
        refine ⟨7750600918023534023646265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10334134557364712031528353 7750600918023534023646265)
        ·
          refine ⟨5812950688517650517734699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7750600918023534023646265 5812950688517650517734699)
          ·
            refine ⟨8719426032776475776602049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812950688517650517734699 8719426032776475776602049)
            ·
              refine ⟨6539569524582356832451537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8719426032776475776602049 6539569524582356832451537)
              ·
                refine ⟨4904677143436767624338653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539569524582356832451537 4904677143436767624338653)
                ·
                  refine ⟨1839253928788787859126995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4904677143436767624338653 1839253928788787859126995)
                  ·
                    refine ⟨2758880893183181788690493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839253928788787859126995 2758880893183181788690493)
                    ·
                      refine ⟨1034580334943693170758935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758880893183181788690493 1034580334943693170758935)
                      ·
                        rfl

theorem cell23_2014838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2014838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014838 prefixEnd_2014838 := by exact prefixLift 2014838
  have htrace : WordTrace (prefixWord ++ tailWord_2014838) baseStart_2014838 baseEnd_2014838 := by
    simpa [prefixWord, tailWord_2014838, baseEnd_2014838] using wordTrace_append hprefix tailTrace_2014838
  have hstable : (prefixWord ++ tailWord_2014838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014838).length < 2 ^ (prefixWord ++ tailWord_2014838).sum := by decide
  have hdescent : baseEnd_2014838 < baseStart_2014838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014844 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_2014844 : Nat := 118140960795 + 2014844 * 2 ^ 59
def prefixEnd_2014844 : Nat := 4983230072969 + 3 ^ 40 * 2014844 * 2
def baseEnd_2014844 : Nat := 1034583415827620147283907

theorem tailTrace_2014844 : CollatzResearch.WordTrace tailWord_2014844 prefixEnd_2014844 1034583415827620147283907 := by
  unfold tailWord_2014844
  simp only [CollatzResearch.WordTrace]
  refine ⟨36743698956285885402237793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48991598608381180536317057 36743698956285885402237793)
  ·
    refine ⟨27557774217214414051678345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36743698956285885402237793 27557774217214414051678345)
    ·
      refine ⟨20668330662910810538758759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27557774217214414051678345 20668330662910810538758759)
      ·
        refine ⟨31002495994366215808138139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668330662910810538758759 31002495994366215808138139)
        ·
          refine ⟨46503743991549323712207209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31002495994366215808138139 46503743991549323712207209)
          ·
            refine ⟨34877807993661992784155407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46503743991549323712207209 34877807993661992784155407)
            ·
              refine ⟨52316711990492989176233111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34877807993661992784155407 52316711990492989176233111)
              ·
                refine ⟨78475067985739483764349667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52316711990492989176233111 78475067985739483764349667)
                ·
                  refine ⟨117712601978609225646524501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78475067985739483764349667 117712601978609225646524501)
                  ·
                    refine ⟨1379444554436826863045209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117712601978609225646524501 1379444554436826863045209)
                    ·
                      refine ⟨1034583415827620147283907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379444554436826863045209 1034583415827620147283907)
                      ·
                        rfl

theorem cell23_2014844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_2014844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014844 prefixEnd_2014844 := by exact prefixLift 2014844
  have htrace : WordTrace (prefixWord ++ tailWord_2014844) baseStart_2014844 baseEnd_2014844 := by
    simpa [prefixWord, tailWord_2014844, baseEnd_2014844] using wordTrace_append hprefix tailTrace_2014844
  have hstable : (prefixWord ++ tailWord_2014844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014844).length < 2 ^ (prefixWord ++ tailWord_2014844).sum := by decide
  have hdescent : baseEnd_2014844 < baseStart_2014844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014855 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_2014855 : Nat := 118140960795 + 2014855 * 2 ^ 59
def prefixEnd_2014855 : Nat := 4983230072969 + 3 ^ 40 * 2014855 * 2
def baseEnd_2014855 : Nat := 1034589064114819604246357

theorem tailTrace_2014855 : CollatzResearch.WordTrace tailWord_2014855 prefixEnd_2014855 1034589064114819604246357 := by
  unfold tailWord_2014855
  simp only [CollatzResearch.WordTrace]
  refine ⟨73487799115531919683126019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48991866077021279788750679 73487799115531919683126019)
  ·
    refine ⟨110231698673297879524689029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73487799115531919683126019 110231698673297879524689029)
    ·
      refine ⟨20668443501243352410879193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110231698673297879524689029 20668443501243352410879193)
      ·
        refine ⟨15501332625932514308159395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20668443501243352410879193 15501332625932514308159395)
        ·
          refine ⟨23251998938898771462239093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15501332625932514308159395 23251998938898771462239093)
          ·
            refine ⟨2179874900521759824584915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23251998938898771462239093 2179874900521759824584915)
            ·
              refine ⟨3269812350782639736877373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179874900521759824584915 3269812350782639736877373)
              ·
                refine ⟨1226179631543489901329015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269812350782639736877373 1226179631543489901329015)
                ·
                  refine ⟨1839269447315234851993523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226179631543489901329015 1839269447315234851993523)
                  ·
                    refine ⟨2758904170972852277990285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839269447315234851993523 2758904170972852277990285)
                    ·
                      refine ⟨1034589064114819604246357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2758904170972852277990285 1034589064114819604246357)
                      ·
                        rfl

theorem cell23_2014855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_2014855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014855 prefixEnd_2014855 := by exact prefixLift 2014855
  have htrace : WordTrace (prefixWord ++ tailWord_2014855) baseStart_2014855 baseEnd_2014855 := by
    simpa [prefixWord, tailWord_2014855, baseEnd_2014855] using wordTrace_append hprefix tailTrace_2014855
  have hstable : (prefixWord ++ tailWord_2014855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014855).length < 2 ^ (prefixWord ++ tailWord_2014855).sum := by decide
  have hdescent : baseEnd_2014855 < baseStart_2014855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014884 : List Nat := [2, 3, 1, 2, 2, 3, 2, 8]
def baseStart_2014884 : Nat := 118140960795 + 2014884 * 2 ^ 59
def prefixEnd_2014884 : Nat := 4983230072969 + 3 ^ 40 * 2014884 * 2
def baseEnd_2014884 : Nat := 38318665001992592251249

theorem tailTrace_2014884 : CollatzResearch.WordTrace tailWord_2014884 prefixEnd_2014884 38318665001992592251249 := by
  unfold tailWord_2014884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744428416213428817965853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48992571221617905090621137 36744428416213428817965853)
  ·
    refine ⟨13779160656080035806737195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36744428416213428817965853 13779160656080035806737195)
    ·
      refine ⟨20668740984120053710105793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779160656080035806737195 20668740984120053710105793)
      ·
        refine ⟨15501555738090040282579345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20668740984120053710105793 15501555738090040282579345)
        ·
          refine ⟨11626166803567530211934509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15501555738090040282579345 11626166803567530211934509)
          ·
            refine ⟨4359812551337823829475441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11626166803567530211934509 4359812551337823829475441)
            ·
              refine ⟨3269859413503367872106581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359812551337823829475441 3269859413503367872106581)
              ·
                refine ⟨38318665001992592251249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3269859413503367872106581 38318665001992592251249)
                ·
                  rfl

theorem cell23_2014884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 8].length) (baseStart_2014884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014884 prefixEnd_2014884 := by exact prefixLift 2014884
  have htrace : WordTrace (prefixWord ++ tailWord_2014884) baseStart_2014884 baseEnd_2014884 := by
    simpa [prefixWord, tailWord_2014884, baseEnd_2014884] using wordTrace_append hprefix tailTrace_2014884
  have hstable : (prefixWord ++ tailWord_2014884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014884).length < 2 ^ (prefixWord ++ tailWord_2014884).sum := by decide
  have hdescent : baseEnd_2014884 < baseStart_2014884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014907 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_2014907 : Nat := 118140960795 + 2014907 * 2 ^ 59
def prefixEnd_2014907 : Nat := 4983230072969 + 3 ^ 40 * 2014907 * 2
def baseEnd_2014907 : Nat := 1034615765108853400796117

theorem tailTrace_2014907 : CollatzResearch.WordTrace tailWord_2014907 prefixEnd_2014907 1034615765108853400796117 := by
  unfold tailWord_2014907
  simp only [CollatzResearch.WordTrace]
  refine ⟨73489695711343532564018975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48993130474229021709345983 73489695711343532564018975)
  ·
    refine ⟨110234543567015298846028463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73489695711343532564018975 110234543567015298846028463)
    ·
      refine ⟨165351815350522948269042695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110234543567015298846028463 165351815350522948269042695)
      ·
        refine ⟨248027723025784422403564043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165351815350522948269042695 248027723025784422403564043)
        ·
          refine ⟨372041584538676633605346065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248027723025784422403564043 372041584538676633605346065)
          ·
            refine ⟨279031188404007475204009549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372041584538676633605346065 279031188404007475204009549)
            ·
              refine ⟨104636695651502803201503581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279031188404007475204009549 104636695651502803201503581)
              ·
                refine ⟨39238760869313551200563843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104636695651502803201503581 39238760869313551200563843)
                ·
                  refine ⟨58858141303970326800845765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39238760869313551200563843 58858141303970326800845765)
                  ·
                    refine ⟨11035901494494436275158581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58858141303970326800845765 11035901494494436275158581)
                    ·
                      refine ⟨1034615765108853400796117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11035901494494436275158581 1034615765108853400796117)
                      ·
                        rfl

theorem cell23_2014907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_2014907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014907 prefixEnd_2014907 := by exact prefixLift 2014907
  have htrace : WordTrace (prefixWord ++ tailWord_2014907) baseStart_2014907 baseEnd_2014907 := by
    simpa [prefixWord, tailWord_2014907, baseEnd_2014907] using wordTrace_append hprefix tailTrace_2014907
  have hstable : (prefixWord ++ tailWord_2014907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014907).length < 2 ^ (prefixWord ++ tailWord_2014907).sum := by decide
  have hdescent : baseEnd_2014907 < baseStart_2014907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014917 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_2014917 : Nat := 118140960795 + 2014917 * 2 ^ 59
def prefixEnd_2014917 : Nat := 4983230072969 + 3 ^ 40 * 2014917 * 2
def baseEnd_2014917 : Nat := 1034620899915398361671071

theorem tailTrace_2014917 : CollatzResearch.WordTrace tailWord_2014917 prefixEnd_2014917 1034620899915398361671071 := by
  unfold tailWord_2014917
  simp only [CollatzResearch.WordTrace]
  refine ⟨73490060441307304271883005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48993373627538202847922003 73490060441307304271883005)
  ·
    refine ⟨27558772665490239101956127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73490060441307304271883005 27558772665490239101956127)
    ·
      refine ⟨41338158998235358652934191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27558772665490239101956127 41338158998235358652934191)
      ·
        refine ⟨62007238497353037979401287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41338158998235358652934191 62007238497353037979401287)
        ·
          refine ⟨93010857746029556969101931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62007238497353037979401287 93010857746029556969101931)
          ·
            refine ⟨139516286619044335453652897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93010857746029556969101931 139516286619044335453652897)
            ·
              refine ⟨104637214964283251590239673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139516286619044335453652897 104637214964283251590239673)
              ·
                refine ⟨78477911223212438692679755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104637214964283251590239673 78477911223212438692679755)
                ·
                  refine ⟨117716866834818658039019633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78477911223212438692679755 117716866834818658039019633)
                  ·
                    refine ⟨88287650126113993529264725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117716866834818658039019633 88287650126113993529264725)
                    ·
                      refine ⟨1034620899915398361671071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88287650126113993529264725 1034620899915398361671071)
                      ·
                        rfl

theorem cell23_2014917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_2014917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014917 prefixEnd_2014917 := by exact prefixLift 2014917
  have htrace : WordTrace (prefixWord ++ tailWord_2014917) baseStart_2014917 baseEnd_2014917 := by
    simpa [prefixWord, tailWord_2014917, baseEnd_2014917] using wordTrace_append hprefix tailTrace_2014917
  have hstable : (prefixWord ++ tailWord_2014917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014917).length < 2 ^ (prefixWord ++ tailWord_2014917).sum := by decide
  have hdescent : baseEnd_2014917 < baseStart_2014917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014927 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 8]
def baseStart_2014927 : Nat := 118140960795 + 2014927 * 2 ^ 59
def prefixEnd_2014927 : Nat := 4983230072969 + 3 ^ 40 * 2014927 * 2
def baseEnd_2014927 : Nat := 344875344907314440848675

theorem tailTrace_2014927 : CollatzResearch.WordTrace tailWord_2014927 prefixEnd_2014927 344875344907314440848675 := by
  unfold tailWord_2014927
  simp only [CollatzResearch.WordTrace]
  refine ⟨73490425171271075979747035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48993616780847383986498023 73490425171271075979747035)
  ·
    refine ⟨110235637756906613969620553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73490425171271075979747035 110235637756906613969620553)
    ·
      refine ⟨82676728317679960477215415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110235637756906613969620553 82676728317679960477215415)
      ·
        refine ⟨124015092476519940715823123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82676728317679960477215415 124015092476519940715823123)
        ·
          refine ⟨186022638714779911073734685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124015092476519940715823123 186022638714779911073734685)
          ·
            refine ⟨69758489518042466652650507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186022638714779911073734685 69758489518042466652650507)
            ·
              refine ⟨104637734277063699978975761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69758489518042466652650507 104637734277063699978975761)
              ·
                refine ⟨78478300707797774984231821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104637734277063699978975761 78478300707797774984231821)
                ·
                  refine ⟨29429362765424165619086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78478300707797774984231821 29429362765424165619086933)
                  ·
                    refine ⟨344875344907314440848675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29429362765424165619086933 344875344907314440848675)
                    ·
                      rfl

theorem cell23_2014927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_2014927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014927 prefixEnd_2014927 := by exact prefixLift 2014927
  have htrace : WordTrace (prefixWord ++ tailWord_2014927) baseStart_2014927 baseEnd_2014927 := by
    simpa [prefixWord, tailWord_2014927, baseEnd_2014927] using wordTrace_append hprefix tailTrace_2014927
  have hstable : (prefixWord ++ tailWord_2014927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014927).length < 2 ^ (prefixWord ++ tailWord_2014927).sum := by decide
  have hdescent : baseEnd_2014927 < baseStart_2014927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014954 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2014954 : Nat := 118140960795 + 2014954 * 2 ^ 59
def prefixEnd_2014954 : Nat := 4983230072969 + 3 ^ 40 * 2014954 * 2
def baseEnd_2014954 : Nat := 1034639898699614716908401

theorem tailTrace_2014954 : CollatzResearch.WordTrace tailWord_2014954 prefixEnd_2014954 1034639898699614716908401 := by
  unfold tailWord_2014954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372852485543314897744979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48994273294782173060653277 18372852485543314897744979)
  ·
    refine ⟨27559278728314972346617469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18372852485543314897744979 27559278728314972346617469)
    ·
      refine ⟨10334729523118114629981551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27559278728314972346617469 10334729523118114629981551)
      ·
        refine ⟨15502094284677171944972327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334729523118114629981551 15502094284677171944972327)
        ·
          refine ⟨23253141427015757917458491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502094284677171944972327 23253141427015757917458491)
          ·
            refine ⟨34879712140523636876187737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253141427015757917458491 34879712140523636876187737)
            ·
              refine ⟨26159784105392727657140803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34879712140523636876187737 26159784105392727657140803)
              ·
                refine ⟨39239676158089091485711205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26159784105392727657140803 39239676158089091485711205)
                ·
                  refine ⟨7357439279641704653570851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39239676158089091485711205 7357439279641704653570851)
                  ·
                    refine ⟨11036158919462556980356277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7357439279641704653570851 11036158919462556980356277)
                    ·
                      refine ⟨1034639898699614716908401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11036158919462556980356277 1034639898699614716908401)
                      ·
                        rfl

theorem cell23_2014954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2014954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014954 prefixEnd_2014954 := by exact prefixLift 2014954
  have htrace : WordTrace (prefixWord ++ tailWord_2014954) baseStart_2014954 baseEnd_2014954 := by
    simpa [prefixWord, tailWord_2014954, baseEnd_2014954] using wordTrace_append hprefix tailTrace_2014954
  have hstable : (prefixWord ++ tailWord_2014954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014954).length < 2 ^ (prefixWord ++ tailWord_2014954).sum := by decide
  have hdescent : baseEnd_2014954 < baseStart_2014954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014996 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2014996 : Nat := 118140960795 + 2014996 * 2 ^ 59
def prefixEnd_2014996 : Nat := 4983230072969 + 3 ^ 40 * 2014996 * 2
def baseEnd_2014996 : Nat := 1034661464887103552583209

theorem tailTrace_2014996 : CollatzResearch.WordTrace tailWord_2014996 prefixEnd_2014996 1034661464887103552583209 := by
  unfold tailWord_2014996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746470904010550382004421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48995294538680733842672561 36746470904010550382004421)
  ·
    refine ⟨6889963294501978196625829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36746470904010550382004421 6889963294501978196625829)
    ·
      refine ⟨1291868117719120911867343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6889963294501978196625829 1291868117719120911867343)
      ·
        refine ⟨1937802176578681367801015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291868117719120911867343 1937802176578681367801015)
        ·
          refine ⟨2906703264868022051701523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937802176578681367801015 2906703264868022051701523)
          ·
            refine ⟨4360054897302033077552285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906703264868022051701523 4360054897302033077552285)
            ·
              refine ⟨1635020586488262404082107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4360054897302033077552285 1635020586488262404082107)
              ·
                refine ⟨2452530879732393606123161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635020586488262404082107 2452530879732393606123161)
                ·
                  refine ⟨1839398159799295204592371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452530879732393606123161 1839398159799295204592371)
                  ·
                    refine ⟨2759097239698942806888557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839398159799295204592371 2759097239698942806888557)
                    ·
                      refine ⟨1034661464887103552583209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2759097239698942806888557 1034661464887103552583209)
                      ·
                        rfl

theorem cell23_2014996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2014996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2014996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2014996 prefixEnd_2014996 := by exact prefixLift 2014996
  have htrace : WordTrace (prefixWord ++ tailWord_2014996) baseStart_2014996 baseEnd_2014996 := by
    simpa [prefixWord, tailWord_2014996, baseEnd_2014996] using wordTrace_append hprefix tailTrace_2014996
  have hstable : (prefixWord ++ tailWord_2014996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014996).length < 2 ^ (prefixWord ++ tailWord_2014996).sum := by decide
  have hdescent : baseEnd_2014996 < baseStart_2014996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015002 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_2015002 : Nat := 118140960795 + 2015002 * 2 ^ 59
def prefixEnd_2015002 : Nat := 4983230072969 + 3 ^ 40 * 2015002 * 2
def baseEnd_2015002 : Nat := 1034664545771030529108181

theorem tailTrace_2015002 : CollatzResearch.WordTrace tailWord_2015002 prefixEnd_2015002 1034664545771030529108181 := by
  unfold tailWord_2015002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373290161499840947181815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48995440430666242525818173 18373290161499840947181815)
  ·
    refine ⟨27559935242249761420772723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373290161499840947181815 27559935242249761420772723)
    ·
      refine ⟨41339902863374642131159085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27559935242249761420772723 41339902863374642131159085)
      ·
        refine ⟨15502463573765490799184657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41339902863374642131159085 15502463573765490799184657)
        ·
          refine ⟨11626847680324118099388493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15502463573765490799184657 11626847680324118099388493)
          ·
            refine ⟨4360067880121544287270685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11626847680324118099388493 4360067880121544287270685)
            ·
              refine ⟨1635025455045579107726507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4360067880121544287270685 1635025455045579107726507)
              ·
                refine ⟨2452538182568368661589761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635025455045579107726507 2452538182568368661589761)
                ·
                  refine ⟨1839403636926276496192321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452538182568368661589761 1839403636926276496192321)
                  ·
                    refine ⟨1379552727694707372144241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1839403636926276496192321 1379552727694707372144241)
                    ·
                      refine ⟨1034664545771030529108181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379552727694707372144241 1034664545771030529108181)
                      ·
                        rfl

theorem cell23_2015002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_2015002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015002 prefixEnd_2015002 := by exact prefixLift 2015002
  have htrace : WordTrace (prefixWord ++ tailWord_2015002) baseStart_2015002 baseEnd_2015002 := by
    simpa [prefixWord, tailWord_2015002, baseEnd_2015002] using wordTrace_append hprefix tailTrace_2015002
  have hstable : (prefixWord ++ tailWord_2015002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015002).length < 2 ^ (prefixWord ++ tailWord_2015002).sum := by decide
  have hdescent : baseEnd_2015002 < baseStart_2015002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015004 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_2015004 : Nat := 118140960795 + 2015004 * 2 ^ 59
def prefixEnd_2015004 : Nat := 4983230072969 + 3 ^ 40 * 2015004 * 2
def baseEnd_2015004 : Nat := 344888524244113173761057

theorem tailTrace_2015004 : CollatzResearch.WordTrace tailWord_2015004 prefixEnd_2015004 344888524244113173761057 := by
  unfold tailWord_2015004
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746616795996059065150033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48995489061328078753533377 36746616795996059065150033)
  ·
    refine ⟨27559962596997044298862525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36746616795996059065150033 27559962596997044298862525)
    ·
      refine ⟨10334985973873891612073447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27559962596997044298862525 10334985973873891612073447)
      ·
        refine ⟨15502478960810837418110171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334985973873891612073447 15502478960810837418110171)
        ·
          refine ⟨23253718441216256127165257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502478960810837418110171 23253718441216256127165257)
          ·
            refine ⟨17440288830912192095373943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23253718441216256127165257 17440288830912192095373943)
            ·
              refine ⟨26160433246368288143060915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17440288830912192095373943 26160433246368288143060915)
              ·
                refine ⟨39240649869552432214591373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26160433246368288143060915 39240649869552432214591373)
                ·
                  refine ⟨14715243701082162080471765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39240649869552432214591373 14715243701082162080471765)
                  ·
                    refine ⟨344888524244113173761057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14715243701082162080471765 344888524244113173761057)
                    ·
                      rfl

theorem cell23_2015004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_2015004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015004 prefixEnd_2015004 := by exact prefixLift 2015004
  have htrace : WordTrace (prefixWord ++ tailWord_2015004) baseStart_2015004 baseEnd_2015004 := by
    simpa [prefixWord, tailWord_2015004, baseEnd_2015004] using wordTrace_append hprefix tailTrace_2015004
  have hstable : (prefixWord ++ tailWord_2015004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015004).length < 2 ^ (prefixWord ++ tailWord_2015004).sum := by decide
  have hdescent : baseEnd_2015004 < baseStart_2015004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015011 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 5, 2]
def baseStart_2015011 : Nat := 118140960795 + 2015011 * 2 ^ 59
def prefixEnd_2015011 : Nat := 4983230072969 + 3 ^ 40 * 2015011 * 2
def baseEnd_2015011 : Nat := 1034669167096920993895639

theorem tailTrace_2015011 : CollatzResearch.WordTrace tailWord_2015011 prefixEnd_2015011 1034669167096920993895639 := by
  unfold tailWord_2015011
  simp only [CollatzResearch.WordTrace]
  refine ⟨73493488902966758325804887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48995659268644505550536591 73493488902966758325804887)
  ·
    refine ⟨110240233354450137488707331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73493488902966758325804887 110240233354450137488707331)
    ·
      refine ⟨165360350031675206233060997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110240233354450137488707331 165360350031675206233060997)
      ·
        refine ⟨31005065630939101168698937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165360350031675206233060997 31005065630939101168698937)
        ·
          refine ⟨23253799223204325876524203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31005065630939101168698937 23253799223204325876524203)
          ·
            refine ⟨34880698834806488814786305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253799223204325876524203 34880698834806488814786305)
            ·
              refine ⟨26160524126104866611089729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34880698834806488814786305 26160524126104866611089729)
              ·
                refine ⟨19620393094578649958317297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26160524126104866611089729 19620393094578649958317297)
                ·
                  refine ⟨14715294820933987468737973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620393094578649958317297 14715294820933987468737973)
                  ·
                    refine ⟨1379558889462561325194185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14715294820933987468737973 1379558889462561325194185)
                    ·
                      refine ⟨1034669167096920993895639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379558889462561325194185 1034669167096920993895639)
                      ·
                        rfl

theorem cell23_2015011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_2015011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015011 prefixEnd_2015011 := by exact prefixLift 2015011
  have htrace : WordTrace (prefixWord ++ tailWord_2015011) baseStart_2015011 baseEnd_2015011 := by
    simpa [prefixWord, tailWord_2015011, baseEnd_2015011] using wordTrace_append hprefix tailTrace_2015011
  have hstable : (prefixWord ++ tailWord_2015011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015011).length < 2 ^ (prefixWord ++ tailWord_2015011).sum := by decide
  have hdescent : baseEnd_2015011 < baseStart_2015011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015038 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2015038 : Nat := 118140960795 + 2015038 * 2 ^ 59
def prefixEnd_2015038 : Nat := 4983230072969 + 3 ^ 40 * 2015038 * 2
def baseEnd_2015038 : Nat := 344894343691530796086005

theorem tailTrace_2015038 : CollatzResearch.WordTrace tailWord_2015038 prefixEnd_2015038 344894343691530796086005 := by
  unfold tailWord_2015038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9186809209233617742129721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48996315782579294624691845 9186809209233617742129721)
  ·
    refine ⟨6890106906925213306597291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9186809209233617742129721 6890106906925213306597291)
    ·
      refine ⟨10335160360387819959895937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890106906925213306597291 10335160360387819959895937)
      ·
        refine ⟨7751370270290864969921953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10335160360387819959895937 7751370270290864969921953)
        ·
          refine ⟨5813527702718148727441465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7751370270290864969921953 5813527702718148727441465)
          ·
            refine ⟨4360145777038611545581099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813527702718148727441465 4360145777038611545581099)
            ·
              refine ⟨6540218665557917318371649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360145777038611545581099 6540218665557917318371649)
              ·
                refine ⟨4905163999168437988778737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6540218665557917318371649 4905163999168437988778737)
                ·
                  refine ⟨3678872999376328491584053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4905163999168437988778737 3678872999376328491584053)
                  ·
                    refine ⟨344894343691530796086005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3678872999376328491584053 344894343691530796086005)
                    ·
                      rfl

theorem cell23_2015038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2015038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015038 prefixEnd_2015038 := by exact prefixLift 2015038
  have htrace : WordTrace (prefixWord ++ tailWord_2015038) baseStart_2015038 baseEnd_2015038 := by
    simpa [prefixWord, tailWord_2015038, baseEnd_2015038] using wordTrace_append hprefix tailTrace_2015038
  have hstable : (prefixWord ++ tailWord_2015038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015038).length < 2 ^ (prefixWord ++ tailWord_2015038).sum := by decide
  have hdescent : baseEnd_2015038 < baseStart_2015038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015126 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2015126 : Nat := 118140960795 + 2015126 * 2 ^ 59
def prefixEnd_2015126 : Nat := 4983230072969 + 3 ^ 40 * 2015126 * 2
def baseEnd_2015126 : Nat := 1034728217372188043957611

theorem tailTrace_2015126 : CollatzResearch.WordTrace tailWord_2015126 prefixEnd_2015126 1034728217372188043957611 := by
  unfold tailWord_2015126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4593605206096883310390077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48998455531700088644160821 4593605206096883310390077)
  ·
    refine ⟨1722601952286331241396279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4593605206096883310390077 1722601952286331241396279)
    ·
      refine ⟨2583902928429496862094419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722601952286331241396279 2583902928429496862094419)
      ·
        refine ⟨3875854392644245293141629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583902928429496862094419 3875854392644245293141629)
        ·
          refine ⟨1453445397241591984928111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3875854392644245293141629 1453445397241591984928111)
          ·
            refine ⟨2180168095862387977392167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453445397241591984928111 2180168095862387977392167)
            ·
              refine ⟨3270252143793581966088251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180168095862387977392167 3270252143793581966088251)
              ·
                refine ⟨4905378215690372949132377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270252143793581966088251 4905378215690372949132377)
                ·
                  refine ⟨3679033661767779711849283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4905378215690372949132377 3679033661767779711849283)
                  ·
                    refine ⟨5518550492651669567773925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3679033661767779711849283 5518550492651669567773925)
                    ·
                      refine ⟨1034728217372188043957611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5518550492651669567773925 1034728217372188043957611)
                      ·
                        rfl

theorem cell23_2015126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2015126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015126 prefixEnd_2015126 := by exact prefixLift 2015126
  have htrace : WordTrace (prefixWord ++ tailWord_2015126) baseStart_2015126 baseEnd_2015126 := by
    simpa [prefixWord, tailWord_2015126, baseEnd_2015126] using wordTrace_append hprefix tailTrace_2015126
  have hstable : (prefixWord ++ tailWord_2015126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015126).length < 2 ^ (prefixWord ++ tailWord_2015126).sum := by decide
  have hdescent : baseEnd_2015126 < baseStart_2015126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015135 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 5, 2]
def baseStart_2015135 : Nat := 118140960795 + 2015135 * 2 ^ 59
def prefixEnd_2015135 : Nat := 4983230072969 + 3 ^ 40 * 2015135 * 2
def baseEnd_2015135 : Nat := 1034732838698078508745069

theorem tailTrace_2015135 : CollatzResearch.WordTrace tailWord_2015135 prefixEnd_2015135 1034732838698078508745069 := by
  unfold tailWord_2015135
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498011554517527503318859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48998674369678351668879239 73498011554517527503318859)
  ·
    refine ⟨110247017331776291254978289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73498011554517527503318859 110247017331776291254978289)
    ·
      refine ⟨82685262998832218441233717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110247017331776291254978289 82685262998832218441233717)
      ·
        refine ⟨7751743406140520478865661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82685262998832218441233717 7751743406140520478865661)
        ·
          refine ⟨2906903777302695179574623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7751743406140520478865661 2906903777302695179574623)
          ·
            refine ⟨4360355665954042769361935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906903777302695179574623 4360355665954042769361935)
            ·
              refine ⟨6540533498931064154042903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360355665954042769361935 6540533498931064154042903)
              ·
                refine ⟨9810800248396596231064355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540533498931064154042903 9810800248396596231064355)
                ·
                  refine ⟨14716200372594894346596533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810800248396596231064355 14716200372594894346596533)
                  ·
                    refine ⟨1379643784930771344993425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14716200372594894346596533 1379643784930771344993425)
                    ·
                      refine ⟨1034732838698078508745069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379643784930771344993425 1034732838698078508745069)
                      ·
                        rfl

theorem cell23_2015135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_2015135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015135 prefixEnd_2015135 := by exact prefixLift 2015135
  have htrace : WordTrace (prefixWord ++ tailWord_2015135) baseStart_2015135 baseEnd_2015135 := by
    simpa [prefixWord, tailWord_2015135, baseEnd_2015135] using wordTrace_append hprefix tailTrace_2015135
  have hstable : (prefixWord ++ tailWord_2015135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015135).length < 2 ^ (prefixWord ++ tailWord_2015135).sum := by decide
  have hdescent : baseEnd_2015135 < baseStart_2015135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015151 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_2015151 : Nat := 118140960795 + 2015151 * 2 ^ 59
def prefixEnd_2015151 : Nat := 4983230072969 + 3 ^ 40 * 2015151 * 2
def baseEnd_2015151 : Nat := 1034741054388550446144995

theorem tailTrace_2015151 : CollatzResearch.WordTrace tailWord_2015151 prefixEnd_2015151 1034741054388550446144995 := by
  unfold tailWord_2015151
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498595122459562235901307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48999063414973041490600871 73498595122459562235901307)
  ·
    refine ⟨110247892683689343353851961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73498595122459562235901307 110247892683689343353851961)
    ·
      refine ⟨82685919512767007515388971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110247892683689343353851961 82685919512767007515388971)
      ·
        refine ⟨124028879269150511273083457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82685919512767007515388971 124028879269150511273083457)
        ·
          refine ⟨93021659451862883454812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124028879269150511273083457 93021659451862883454812593)
          ·
            refine ⟨69766244588897162591109445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93021659451862883454812593 69766244588897162591109445)
            ·
              refine ⟨13081170860418217985833021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69766244588897162591109445 13081170860418217985833021)
              ·
                refine ⟨4905439072656831744687383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13081170860418217985833021 4905439072656831744687383)
                ·
                  refine ⟨7358158608985247617031075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905439072656831744687383 7358158608985247617031075)
                  ·
                    refine ⟨11037237913477871425546613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358158608985247617031075 11037237913477871425546613)
                    ·
                      refine ⟨1034741054388550446144995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11037237913477871425546613 1034741054388550446144995)
                      ·
                        rfl

theorem cell23_2015151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_2015151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015151 prefixEnd_2015151 := by exact prefixLift 2015151
  have htrace : WordTrace (prefixWord ++ tailWord_2015151) baseStart_2015151 baseEnd_2015151 := by
    simpa [prefixWord, tailWord_2015151, baseEnd_2015151] using wordTrace_append hprefix tailTrace_2015151
  have hstable : (prefixWord ++ tailWord_2015151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015151).length < 2 ^ (prefixWord ++ tailWord_2015151).sum := by decide
  have hdescent : baseEnd_2015151 < baseStart_2015151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015161 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2015161 : Nat := 118140960795 + 2015161 * 2 ^ 59
def prefixEnd_2015161 : Nat := 4983230072969 + 3 ^ 40 * 2015161 * 2
def baseEnd_2015161 : Nat := 1034746189195095407019949

theorem tailTrace_2015161 : CollatzResearch.WordTrace tailWord_2015161 prefixEnd_2015161 1034746189195095407019949 := by
  unfold tailWord_2015161
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498959852423333943765337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48999306568282222629176891 73498959852423333943765337)
  ·
    refine ⟨55124219889317500457824003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73498959852423333943765337 55124219889317500457824003)
    ·
      refine ⟨82686329833976250686736005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55124219889317500457824003 82686329833976250686736005)
      ·
        refine ⟨15503686843870547003763001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82686329833976250686736005 15503686843870547003763001)
        ·
          refine ⟨11627765132902910252822251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503686843870547003763001 11627765132902910252822251)
          ·
            refine ⟨17441647699354365379233377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11627765132902910252822251 17441647699354365379233377)
            ·
              refine ⟨13081235774515774034425033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17441647699354365379233377 13081235774515774034425033)
              ·
                refine ⟨9810926830886830525818775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13081235774515774034425033 9810926830886830525818775)
                ·
                  refine ⟨14716390246330245788728163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810926830886830525818775 14716390246330245788728163)
                  ·
                    refine ⟨22074585369495368683092245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14716390246330245788728163 22074585369495368683092245)
                    ·
                      refine ⟨1034746189195095407019949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22074585369495368683092245 1034746189195095407019949)
                      ·
                        rfl

theorem cell23_2015161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2015161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015161 prefixEnd_2015161 := by exact prefixLift 2015161
  have htrace : WordTrace (prefixWord ++ tailWord_2015161) baseStart_2015161 baseEnd_2015161 := by
    simpa [prefixWord, tailWord_2015161, baseEnd_2015161] using wordTrace_append hprefix tailTrace_2015161
  have hstable : (prefixWord ++ tailWord_2015161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015161).length < 2 ^ (prefixWord ++ tailWord_2015161).sum := by decide
  have hdescent : baseEnd_2015161 < baseStart_2015161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015178 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2015178 : Nat := 118140960795 + 2015178 * 2 ^ 59
def prefixEnd_2015178 : Nat := 4983230072969 + 3 ^ 40 * 2015178 * 2
def baseEnd_2015178 : Nat := 1034754918366221840507371

theorem tailTrace_2015178 : CollatzResearch.WordTrace tailWord_2015178 prefixEnd_2015178 1034754918366221840507371 := by
  unfold tailWord_2015178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374894973340436461783547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48999719928907830564756125 18374894973340436461783547)
  ·
    refine ⟨27562342460010654692675321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18374894973340436461783547 27562342460010654692675321)
    ·
      refine ⟨20671756845007991019506491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27562342460010654692675321 20671756845007991019506491)
      ·
        refine ⟨31007635267511986529259737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671756845007991019506491 31007635267511986529259737)
        ·
          refine ⟨23255726450633989896944803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31007635267511986529259737 23255726450633989896944803)
          ·
            refine ⟨34883589675950984845417205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255726450633989896944803 34883589675950984845417205)
            ·
              refine ⟨3270336532120404829257863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34883589675950984845417205 3270336532120404829257863)
              ·
                refine ⟨4905504798180607243886795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270336532120404829257863 4905504798180607243886795)
                ·
                  refine ⟨7358257197270910865830193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905504798180607243886795 7358257197270910865830193)
                  ·
                    refine ⟨5518692897953183149372645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7358257197270910865830193 5518692897953183149372645)
                    ·
                      refine ⟨1034754918366221840507371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5518692897953183149372645 1034754918366221840507371)
                      ·
                        rfl

theorem cell23_2015178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2015178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015178 prefixEnd_2015178 := by exact prefixLift 2015178
  have htrace : WordTrace (prefixWord ++ tailWord_2015178) baseStart_2015178 baseEnd_2015178 := by
    simpa [prefixWord, tailWord_2015178, baseEnd_2015178] using wordTrace_append hprefix tailTrace_2015178
  have hstable : (prefixWord ++ tailWord_2015178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015178).length < 2 ^ (prefixWord ++ tailWord_2015178).sum := by decide
  have hdescent : baseEnd_2015178 < baseStart_2015178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015199 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 1, 2, 2]
def baseStart_2015199 : Nat := 118140960795 + 2015199 * 2 ^ 59
def prefixEnd_2015199 : Nat := 4983230072969 + 3 ^ 40 * 2015199 * 2
def baseEnd_2015199 : Nat := 1034765701459966258344775

theorem tailTrace_2015199 : CollatzResearch.WordTrace tailWord_2015199 prefixEnd_2015199 1034765701459966258344775 := by
  unfold tailWord_2015199
  simp only [CollatzResearch.WordTrace]
  refine ⟨73500345826285666433648651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49000230550857110955765767 73500345826285666433648651)
  ·
    refine ⟨110250518739428499650472977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73500345826285666433648651 110250518739428499650472977)
    ·
      refine ⟨82687889054571374737854733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110250518739428499650472977 82687889054571374737854733)
      ·
        refine ⟨31007958395464265526695525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82687889054571374737854733 31007958395464265526695525)
        ·
          refine ⟨5813992199149549786255411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31007958395464265526695525 5813992199149549786255411)
          ·
            refine ⟨8720988298724324679383117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813992199149549786255411 8720988298724324679383117)
            ·
              refine ⟨3270370612021621754768669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8720988298724324679383117 3270370612021621754768669)
              ·
                refine ⟨1226388979508108158038251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3270370612021621754768669 1226388979508108158038251)
                ·
                  refine ⟨1839583469262162237057377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226388979508108158038251 1839583469262162237057377)
                  ·
                    refine ⟨1379687601946621677793033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1839583469262162237057377 1379687601946621677793033)
                    ·
                      refine ⟨1034765701459966258344775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379687601946621677793033 1034765701459966258344775)
                      ·
                        rfl

theorem cell23_2015199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_2015199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015199 prefixEnd_2015199 := by exact prefixLift 2015199
  have htrace : WordTrace (prefixWord ++ tailWord_2015199) baseStart_2015199 baseEnd_2015199 := by
    simpa [prefixWord, tailWord_2015199, baseEnd_2015199] using wordTrace_append hprefix tailTrace_2015199
  have hstable : (prefixWord ++ tailWord_2015199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015199).length < 2 ^ (prefixWord ++ tailWord_2015199).sum := by decide
  have hdescent : baseEnd_2015199 < baseStart_2015199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015202 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2015202 : Nat := 118140960795 + 2015202 * 2 ^ 59
def prefixEnd_2015202 : Nat := 4983230072969 + 3 ^ 40 * 2015202 * 2
def baseEnd_2015202 : Nat := 1034767241901929746607261

theorem tailTrace_2015202 : CollatzResearch.WordTrace tailWord_2015202 prefixEnd_2015202 1034767241901929746607261 := by
  unfold tailWord_2015202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375113811318699486501965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49000303496849865297338573 18375113811318699486501965)
  ·
    refine ⟨6890667679244512307438237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18375113811318699486501965 6890667679244512307438237)
    ·
      refine ⟨2584000379716692115289339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6890667679244512307438237 2584000379716692115289339)
      ·
        refine ⟨3876000569575038172934009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584000379716692115289339 3876000569575038172934009)
        ·
          refine ⟨2907000427181278629700507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876000569575038172934009 2907000427181278629700507)
          ·
            refine ⟨4360500640771917944550761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907000427181278629700507 4360500640771917944550761)
            ·
              refine ⟨3270375480578938458413071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360500640771917944550761 3270375480578938458413071)
              ·
                refine ⟨4905563220868407687619607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270375480578938458413071 4905563220868407687619607)
                ·
                  refine ⟨7358344831302611531429411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905563220868407687619607 7358344831302611531429411)
                  ·
                    refine ⟨11037517246953917297144117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358344831302611531429411 11037517246953917297144117)
                    ·
                      refine ⟨1034767241901929746607261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11037517246953917297144117 1034767241901929746607261)
                      ·
                        rfl

theorem cell23_2015202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2015202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015202 prefixEnd_2015202 := by exact prefixLift 2015202
  have htrace : WordTrace (prefixWord ++ tailWord_2015202) baseStart_2015202 baseEnd_2015202 := by
    simpa [prefixWord, tailWord_2015202, baseEnd_2015202] using wordTrace_append hprefix tailTrace_2015202
  have hstable : (prefixWord ++ tailWord_2015202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015202).length < 2 ^ (prefixWord ++ tailWord_2015202).sum := by decide
  have hdescent : baseEnd_2015202 < baseStart_2015202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015215 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 3]
def baseStart_2015215 : Nat := 118140960795 + 2015215 * 2 ^ 59
def prefixEnd_2015215 : Nat := 4983230072969 + 3 ^ 40 * 2015215 * 2
def baseEnd_2015215 : Nat := 1034773917150438195744701

theorem tailTrace_2015215 : CollatzResearch.WordTrace tailWord_2015215 prefixEnd_2015215 1034773917150438195744701 := by
  unfold tailWord_2015215
  simp only [CollatzResearch.WordTrace]
  refine ⟨73500929394227701166231099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49000619596151800777487399 73500929394227701166231099)
  ·
    refine ⟨110251394091341551749346649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73500929394227701166231099 110251394091341551749346649)
    ·
      refine ⟨82688545568506163812009987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110251394091341551749346649 82688545568506163812009987)
      ·
        refine ⟨124032818352759245718014981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82688545568506163812009987 124032818352759245718014981)
        ·
          refine ⟨23256153441142358572127809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124032818352759245718014981 23256153441142358572127809)
          ·
            refine ⟨17442115080856768929095857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23256153441142358572127809 17442115080856768929095857)
            ·
              refine ⟨13081586310642576696821893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17442115080856768929095857 13081586310642576696821893)
              ·
                refine ⟨2452797433245483130654105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13081586310642576696821893 2452797433245483130654105)
                ·
                  refine ⟨1839598074934112347990579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452797433245483130654105 1839598074934112347990579)
                  ·
                    refine ⟨2759397112401168521985869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839598074934112347990579 2759397112401168521985869)
                    ·
                      refine ⟨1034773917150438195744701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2759397112401168521985869 1034773917150438195744701)
                      ·
                        rfl

theorem cell23_2015215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_2015215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015215 prefixEnd_2015215 := by exact prefixLift 2015215
  have htrace : WordTrace (prefixWord ++ tailWord_2015215) baseStart_2015215 baseEnd_2015215 := by
    simpa [prefixWord, tailWord_2015215, baseEnd_2015215] using wordTrace_append hprefix tailTrace_2015215
  have hstable : (prefixWord ++ tailWord_2015215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015215).length < 2 ^ (prefixWord ++ tailWord_2015215).sum := by decide
  have hdescent : baseEnd_2015215 < baseStart_2015215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015231 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 2, 6]
def baseStart_2015231 : Nat := 118140960795 + 2015231 * 2 ^ 59
def prefixEnd_2015231 : Nat := 4983230072969 + 3 ^ 40 * 2015231 * 2
def baseEnd_2015231 : Nat := 344927377613636711048209

theorem tailTrace_2015231 : CollatzResearch.WordTrace tailWord_2015231 prefixEnd_2015231 344927377613636711048209 := by
  unfold tailWord_2015231
  simp only [CollatzResearch.WordTrace]
  refine ⟨73501512962169735898813547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49001008641446490599209031 73501512962169735898813547)
  ·
    refine ⟨110252269443254603848220321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73501512962169735898813547 110252269443254603848220321)
    ·
      refine ⟨82689202082440952886165241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110252269443254603848220321 82689202082440952886165241)
      ·
        refine ⟨62016901561830714664623931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82689202082440952886165241 62016901561830714664623931)
        ·
          refine ⟨93025352342746071996935897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62016901561830714664623931 93025352342746071996935897)
          ·
            refine ⟨69769014257059553997701923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93025352342746071996935897 69769014257059553997701923)
            ·
              refine ⟨104653521385589330996552885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69769014257059553997701923 104653521385589330996552885)
              ·
                refine ⟨9811267629898999780926833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104653521385589330996552885 9811267629898999780926833)
                ·
                  refine ⟨7358450722424249835695125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811267629898999780926833 7358450722424249835695125)
                  ·
                    refine ⟨344927377613636711048209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7358450722424249835695125 344927377613636711048209)
                    ·
                      rfl

theorem cell23_2015231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_2015231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015231 prefixEnd_2015231 := by exact prefixLift 2015231
  have htrace : WordTrace (prefixWord ++ tailWord_2015231) baseStart_2015231 baseEnd_2015231 := by
    simpa [prefixWord, tailWord_2015231, baseEnd_2015231] using wordTrace_append hprefix tailTrace_2015231
  have hstable : (prefixWord ++ tailWord_2015231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015231).length < 2 ^ (prefixWord ++ tailWord_2015231).sum := by decide
  have hdescent : baseEnd_2015231 < baseStart_2015231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015236 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2015236 : Nat := 118140960795 + 2015236 * 2 ^ 59
def prefixEnd_2015236 : Nat := 4983230072969 + 3 ^ 40 * 2015236 * 2
def baseEnd_2015236 : Nat := 1034784700244182613582105

theorem tailTrace_2015236 : CollatzResearch.WordTrace tailWord_2015236 prefixEnd_2015236 1034784700244182613582105 := by
  unfold tailWord_2015236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36750847663575810876372781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49001130218101081168497041 36750847663575810876372781)
  ·
    refine ⟨13781567873840929078639793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36750847663575810876372781 13781567873840929078639793)
    ·
      refine ⟨10336175905380696808979845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13781567873840929078639793 10336175905380696808979845)
      ·
        refine ⟨1938032982258880651683721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10336175905380696808979845 1938032982258880651683721)
        ·
          refine ⟨1453524736694160488762791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938032982258880651683721 1453524736694160488762791)
          ·
            refine ⟨2180287105041240733144187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453524736694160488762791 2180287105041240733144187)
            ·
              refine ⟨3270430657561861099716281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180287105041240733144187 3270430657561861099716281)
              ·
                refine ⟨2452822993171395824787211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270430657561861099716281 2452822993171395824787211)
                ·
                  refine ⟨3679234489757093737180817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452822993171395824787211 3679234489757093737180817)
                  ·
                    refine ⟨2759425867317820302885613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3679234489757093737180817 2759425867317820302885613)
                    ·
                      refine ⟨1034784700244182613582105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2759425867317820302885613 1034784700244182613582105)
                      ·
                        rfl

theorem cell23_2015236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2015236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015236 prefixEnd_2015236 := by exact prefixLift 2015236
  have htrace : WordTrace (prefixWord ++ tailWord_2015236) baseStart_2015236 baseEnd_2015236 := by
    simpa [prefixWord, tailWord_2015236, baseEnd_2015236] using wordTrace_append hprefix tailTrace_2015236
  have hstable : (prefixWord ++ tailWord_2015236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015236).length < 2 ^ (prefixWord ++ tailWord_2015236).sum := by decide
  have hdescent : baseEnd_2015236 < baseStart_2015236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015242 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_2015242 : Nat := 118140960795 + 2015242 * 2 ^ 59
def prefixEnd_2015242 : Nat := 4983230072969 + 3 ^ 40 * 2015242 * 2
def baseEnd_2015242 : Nat := 1034787781128109590107077

theorem tailTrace_2015242 : CollatzResearch.WordTrace tailWord_2015242 prefixEnd_2015242 1034787781128109590107077 := by
  unfold tailWord_2015242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375478541282471194365995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49001276110086589851642653 18375478541282471194365995)
  ·
    refine ⟨27563217811923706791548993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18375478541282471194365995 27563217811923706791548993)
    ·
      refine ⟨20672413358942780093661745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27563217811923706791548993 20672413358942780093661745)
      ·
        refine ⟨15504310019207085070246309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20672413358942780093661745 15504310019207085070246309)
        ·
          refine ⟨2907058128601328450671183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15504310019207085070246309 2907058128601328450671183)
          ·
            refine ⟨4360587192901992676006775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907058128601328450671183 4360587192901992676006775)
            ·
              refine ⟨6540880789352989014010163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360587192901992676006775 6540880789352989014010163)
              ·
                refine ⟨9811321184029483521015245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540880789352989014010163 9811321184029483521015245)
                ·
                  refine ⟨3679245444011056320380717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9811321184029483521015245 3679245444011056320380717)
                  ·
                    refine ⟨1379717041504146120142769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679245444011056320380717 1379717041504146120142769)
                    ·
                      refine ⟨1034787781128109590107077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379717041504146120142769 1034787781128109590107077)
                      ·
                        rfl

theorem cell23_2015242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_2015242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015242 prefixEnd_2015242 := by exact prefixLift 2015242
  have htrace : WordTrace (prefixWord ++ tailWord_2015242) baseStart_2015242 baseEnd_2015242 := by
    simpa [prefixWord, tailWord_2015242, baseEnd_2015242] using wordTrace_append hprefix tailTrace_2015242
  have hstable : (prefixWord ++ tailWord_2015242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015242).length < 2 ^ (prefixWord ++ tailWord_2015242).sum := by decide
  have hdescent : baseEnd_2015242 < baseStart_2015242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015258 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2015258 : Nat := 118140960795 + 2015258 * 2 ^ 59
def prefixEnd_2015258 : Nat := 4983230072969 + 3 ^ 40 * 2015258 * 2
def baseEnd_2015258 : Nat := 1034795996818581527507003

theorem tailTrace_2015258 : CollatzResearch.WordTrace tailWord_2015258 prefixEnd_2015258 1034795996818581527507003 := by
  unfold tailWord_2015258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375624433267979877511607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49001665155381279673364285 18375624433267979877511607)
  ·
    refine ⟨27563436649901969816267411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18375624433267979877511607 27563436649901969816267411)
    ·
      refine ⟨41345154974852954724401117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27563436649901969816267411 41345154974852954724401117)
      ·
        refine ⟨15504433115569858021650419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41345154974852954724401117 15504433115569858021650419)
        ·
          refine ⟨23256649673354787032475629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15504433115569858021650419 23256649673354787032475629)
          ·
            refine ⟨8721243627508045137178361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23256649673354787032475629 8721243627508045137178361)
            ·
              refine ⟨6540932720631033852883771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8721243627508045137178361 6540932720631033852883771)
              ·
                refine ⟨9811399080946550779325657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540932720631033852883771 9811399080946550779325657)
                ·
                  refine ⟨7358549310709913084494243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811399080946550779325657 7358549310709913084494243)
                  ·
                    refine ⟨11037823966064869626741365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358549310709913084494243 11037823966064869626741365)
                    ·
                      refine ⟨1034795996818581527507003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11037823966064869626741365 1034795996818581527507003)
                      ·
                        rfl

theorem cell23_2015258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2015258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015258 prefixEnd_2015258 := by exact prefixLift 2015258
  have htrace : WordTrace (prefixWord ++ tailWord_2015258) baseStart_2015258 baseEnd_2015258 := by
    simpa [prefixWord, tailWord_2015258, baseEnd_2015258] using wordTrace_append hprefix tailTrace_2015258
  have hstable : (prefixWord ++ tailWord_2015258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015258).length < 2 ^ (prefixWord ++ tailWord_2015258).sum := by decide
  have hdescent : baseEnd_2015258 < baseStart_2015258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015291 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 7]
def baseStart_2015291 : Nat := 118140960795 + 2015291 * 2 ^ 59
def prefixEnd_2015291 : Nat := 4983230072969 + 3 ^ 40 * 2015291 * 2
def baseEnd_2015291 : Nat := 344937647226726632798117

theorem tailTrace_2015291 : CollatzResearch.WordTrace tailWord_2015291 prefixEnd_2015291 344937647226726632798117 := by
  unfold tailWord_2015291
  simp only [CollatzResearch.WordTrace]
  refine ⟨73503701341952366145997727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49002467561301577430665151 73503701341952366145997727)
  ·
    refine ⟨110255552012928549218996591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73503701341952366145997727 110255552012928549218996591)
    ·
      refine ⟨165383328019392823828494887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110255552012928549218996591 165383328019392823828494887)
      ·
        refine ⟨248074992029089235742742331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165383328019392823828494887 248074992029089235742742331)
        ·
          refine ⟨372112488043633853614113497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248074992029089235742742331 372112488043633853614113497)
          ·
            refine ⟨279084366032725390210585123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372112488043633853614113497 279084366032725390210585123)
            ·
              refine ⟨418626549049088085315877685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279084366032725390210585123 418626549049088085315877685)
              ·
                refine ⟨39246238973352007998363533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418626549049088085315877685 39246238973352007998363533)
                ·
                  refine ⟨14717339615007002999386325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39246238973352007998363533 14717339615007002999386325)
                  ·
                    refine ⟨344937647226726632798117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14717339615007002999386325 344937647226726632798117)
                    ·
                      rfl

theorem cell23_2015291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_2015291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015291 prefixEnd_2015291 := by exact prefixLift 2015291
  have htrace : WordTrace (prefixWord ++ tailWord_2015291) baseStart_2015291 baseEnd_2015291 := by
    simpa [prefixWord, tailWord_2015291, baseEnd_2015291] using wordTrace_append hprefix tailTrace_2015291
  have hstable : (prefixWord ++ tailWord_2015291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015291).length < 2 ^ (prefixWord ++ tailWord_2015291).sum := by decide
  have hdescent : baseEnd_2015291 < baseStart_2015291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015345 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_2015345 : Nat := 118140960795 + 2015345 * 2 ^ 59
def prefixEnd_2015345 : Nat := 4983230072969 + 3 ^ 40 * 2015345 * 2
def baseEnd_2015345 : Nat := 1034840669635522687119103

theorem tailTrace_2015345 : CollatzResearch.WordTrace tailWord_2015345 prefixEnd_2015345 1034840669635522687119103 := by
  unfold tailWord_2015345
  simp only [CollatzResearch.WordTrace]
  refine ⟨73505670883756733368463489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49003780589171155578975659 73505670883756733368463489)
  ·
    refine ⟨55129253162817550026347617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73505670883756733368463489 55129253162817550026347617)
    ·
      refine ⟨41346939872113162519760713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55129253162817550026347617 41346939872113162519760713)
      ·
        refine ⟨31010204904084871889820535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41346939872113162519760713 31010204904084871889820535)
        ·
          refine ⟨46515307356127307834730803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31010204904084871889820535 46515307356127307834730803)
          ·
            refine ⟨69772961034190961752096205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46515307356127307834730803 69772961034190961752096205)
            ·
              refine ⟨26164860387821610657036077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69772961034190961752096205 26164860387821610657036077)
              ·
                refine ⟨9811822645433103996388529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26164860387821610657036077 9811822645433103996388529)
                ·
                  refine ⟨7358866984074827997291397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811822645433103996388529 7358866984074827997291397)
                  ·
                    refine ⟨1379787559514030249492137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358866984074827997291397 1379787559514030249492137)
                    ·
                      refine ⟨1034840669635522687119103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379787559514030249492137 1034840669635522687119103)
                      ·
                        rfl

theorem cell23_2015345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_2015345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015345 prefixEnd_2015345 := by exact prefixLift 2015345
  have htrace : WordTrace (prefixWord ++ tailWord_2015345) baseStart_2015345 baseEnd_2015345 := by
    simpa [prefixWord, tailWord_2015345, baseEnd_2015345] using wordTrace_append hprefix tailTrace_2015345
  have hstable : (prefixWord ++ tailWord_2015345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015345).length < 2 ^ (prefixWord ++ tailWord_2015345).sum := by decide
  have hdescent : baseEnd_2015345 < baseStart_2015345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015365 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_2015365 : Nat := 118140960795 + 2015365 * 2 ^ 59
def prefixEnd_2015365 : Nat := 4983230072969 + 3 ^ 40 * 2015365 * 2
def baseEnd_2015365 : Nat := 1034850939248612608869011

theorem tailTrace_2015365 : CollatzResearch.WordTrace tailWord_2015365 prefixEnd_2015365 1034850939248612608869011 := by
  unfold tailWord_2015365
  simp only [CollatzResearch.WordTrace]
  refine ⟨73506400343684276784191549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49004266895789517856127699 73506400343684276784191549)
  ·
    refine ⟨27564900128881603794071831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73506400343684276784191549 27564900128881603794071831)
    ·
      refine ⟨41347350193322405691107747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27564900128881603794071831 41347350193322405691107747)
      ·
        refine ⟨62021025289983608536661621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41347350193322405691107747 62021025289983608536661621)
        ·
          refine ⟨5814471120935963300312027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62021025289983608536661621 5814471120935963300312027)
          ·
            refine ⟨8721706681403944950468041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814471120935963300312027 8721706681403944950468041)
            ·
              refine ⟨6541280011052958712851031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8721706681403944950468041 6541280011052958712851031)
              ·
                refine ⟨9811920016579438069276547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541280011052958712851031 9811920016579438069276547)
                ·
                  refine ⟨14717880024869157103914821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811920016579438069276547 14717880024869157103914821)
                  ·
                    refine ⟨2759602504662966956984029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14717880024869157103914821 2759602504662966956984029)
                    ·
                      refine ⟨1034850939248612608869011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2759602504662966956984029 1034850939248612608869011)
                      ·
                        rfl

theorem cell23_2015365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_2015365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015365 prefixEnd_2015365 := by exact prefixLift 2015365
  have htrace : WordTrace (prefixWord ++ tailWord_2015365) baseStart_2015365 baseEnd_2015365 := by
    simpa [prefixWord, tailWord_2015365, baseEnd_2015365] using wordTrace_append hprefix tailTrace_2015365
  have hstable : (prefixWord ++ tailWord_2015365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015365).length < 2 ^ (prefixWord ++ tailWord_2015365).sum := by decide
  have hdescent : baseEnd_2015365 < baseStart_2015365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015415 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 3, 5]
def baseStart_2015415 : Nat := 118140960795 + 2015415 * 2 ^ 59
def prefixEnd_2015415 : Nat := 4983230072969 + 3 ^ 40 * 2015415 * 2
def baseEnd_2015415 : Nat := 344958871093779137747927

theorem tailTrace_2015415 : CollatzResearch.WordTrace tailWord_2015415 prefixEnd_2015415 344958871093779137747927 := by
  unfold tailWord_2015415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73508223993503135323511699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49005482662335423549007799 73508223993503135323511699)
  ·
    refine ⟨110262335990254702985267549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73508223993503135323511699 110262335990254702985267549)
    ·
      refine ⟨41348375996345513619475331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110262335990254702985267549 41348375996345513619475331)
      ·
        refine ⟨62022563994518270429212997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41348375996345513619475331 62022563994518270429212997)
        ·
          refine ⟨11629230748972175705477437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62022563994518270429212997 11629230748972175705477437)
          ·
            refine ⟨4360961530864565889554039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11629230748972175705477437 4360961530864565889554039)
            ·
              refine ⟨6541442296296848834331059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360961530864565889554039 6541442296296848834331059)
              ·
                refine ⟨9812163444445273251496589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541442296296848834331059 9812163444445273251496589)
                ·
                  refine ⟨3679561291666977469311221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9812163444445273251496589 3679561291666977469311221)
                  ·
                    refine ⟨344958871093779137747927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3679561291666977469311221 344958871093779137747927)
                    ·
                      rfl

theorem cell23_2015415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_2015415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015415 prefixEnd_2015415 := by exact prefixLift 2015415
  have htrace : WordTrace (prefixWord ++ tailWord_2015415) baseStart_2015415 baseEnd_2015415 := by
    simpa [prefixWord, tailWord_2015415, baseEnd_2015415] using wordTrace_append hprefix tailTrace_2015415
  have hstable : (prefixWord ++ tailWord_2015415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015415).length < 2 ^ (prefixWord ++ tailWord_2015415).sum := by decide
  have hdescent : baseEnd_2015415 < baseStart_2015415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015475 : List Nat := [1, 1, 1, 2, 2, 4, 5, 7]
def baseStart_2015475 : Nat := 118140960795 + 2015475 * 2 ^ 59
def prefixEnd_2015475 : Nat := 4983230072969 + 3 ^ 40 * 2015475 * 2
def baseEnd_2015475 : Nat := 38329904522985451055315

theorem tailTrace_2015475 : CollatzResearch.WordTrace tailWord_2015475 prefixEnd_2015475 38329904522985451055315 := by
  unfold tailWord_2015475
  simp only [CollatzResearch.WordTrace]
  refine ⟨73510412373285765570695879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49006941582190510380463919 73510412373285765570695879)
  ·
    refine ⟨110265618559928648356043819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73510412373285765570695879 110265618559928648356043819)
    ·
      refine ⟨165398427839892972534065729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110265618559928648356043819 165398427839892972534065729)
      ·
        refine ⟨124048820879919729400549297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165398427839892972534065729 124048820879919729400549297)
        ·
          refine ⟨93036615659939797050411973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124048820879919729400549297 93036615659939797050411973)
          ·
            refine ⟨17444365436238711946952245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93036615659939797050411973 17444365436238711946952245)
            ·
              refine ⟨1635409259647379245026773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17444365436238711946952245 1635409259647379245026773)
              ·
                refine ⟨38329904522985451055315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1635409259647379245026773 38329904522985451055315)
                ·
                  rfl

theorem cell23_2015475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 7].length) (baseStart_2015475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015475 prefixEnd_2015475 := by exact prefixLift 2015475
  have htrace : WordTrace (prefixWord ++ tailWord_2015475) baseStart_2015475 baseEnd_2015475 := by
    simpa [prefixWord, tailWord_2015475, baseEnd_2015475] using wordTrace_append hprefix tailTrace_2015475
  have hstable : (prefixWord ++ tailWord_2015475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015475).length < 2 ^ (prefixWord ++ tailWord_2015475).sum := by decide
  have hdescent : baseEnd_2015475 < baseStart_2015475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015519 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_2015519 : Nat := 118140960795 + 2015519 * 2 ^ 59
def prefixEnd_2015519 : Nat := 4983230072969 + 3 ^ 40 * 2015519 * 2
def baseEnd_2015519 : Nat := 1034930015269405006343303

theorem tailTrace_2015519 : CollatzResearch.WordTrace tailWord_2015519 prefixEnd_2015519 1034930015269405006343303 := by
  unfold tailWord_2015519
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512017185126361085297611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49008011456750907390198407 73512017185126361085297611)
  ·
    refine ⟨110268025777689541627946417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73512017185126361085297611 110268025777689541627946417)
    ·
      refine ⟨82701019333267156220959813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110268025777689541627946417 82701019333267156220959813)
      ·
        refine ⟨15506441124987591791429965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82701019333267156220959813 15506441124987591791429965)
        ·
          refine ⟨5814915421870346921786237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15506441124987591791429965 5814915421870346921786237)
          ·
            refine ⟨2180593283201380095669839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5814915421870346921786237 2180593283201380095669839)
            ·
              refine ⟨3270889924802070143504759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180593283201380095669839 3270889924802070143504759)
              ·
                refine ⟨4906334887203105215257139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270889924802070143504759 4906334887203105215257139)
                ·
                  refine ⟨7359502330804657822885709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906334887203105215257139 7359502330804657822885709)
                  ·
                    refine ⟨2759813374051746683582141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7359502330804657822885709 2759813374051746683582141)
                    ·
                      refine ⟨1034930015269405006343303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2759813374051746683582141 1034930015269405006343303)
                      ·
                        rfl

theorem cell23_2015519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_2015519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015519 prefixEnd_2015519 := by exact prefixLift 2015519
  have htrace : WordTrace (prefixWord ++ tailWord_2015519) baseStart_2015519 baseEnd_2015519 := by
    simpa [prefixWord, tailWord_2015519, baseEnd_2015519] using wordTrace_append hprefix tailTrace_2015519
  have hstable : (prefixWord ++ tailWord_2015519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015519).length < 2 ^ (prefixWord ++ tailWord_2015519).sum := by decide
  have hdescent : baseEnd_2015519 < baseStart_2015519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015555 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_2015555 : Nat := 118140960795 + 2015555 * 2 ^ 59
def prefixEnd_2015555 : Nat := 4983230072969 + 3 ^ 40 * 2015555 * 2
def baseEnd_2015555 : Nat := 1034948500572966865493137

theorem tailTrace_2015555 : CollatzResearch.WordTrace tailWord_2015555 prefixEnd_2015555 1034948500572966865493137 := by
  unfold tailWord_2015555
  simp only [CollatzResearch.WordTrace]
  refine ⟨73513330212995939233608119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49008886808663959489072079 73513330212995939233608119)
  ·
    refine ⟨110269995319493908850412179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73513330212995939233608119 110269995319493908850412179)
    ·
      refine ⟨165404992979240863275618269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110269995319493908850412179 165404992979240863275618269)
      ·
        refine ⟨62026872367215323728356851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165404992979240863275618269 62026872367215323728356851)
        ·
          refine ⟨93040308550822985592535277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62026872367215323728356851 93040308550822985592535277)
          ·
            refine ⟨34890115706558619597200729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93040308550822985592535277 34890115706558619597200729)
            ·
              refine ⟨26167586779918964697900547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34890115706558619597200729 26167586779918964697900547)
              ·
                refine ⟨39251380169878447046850821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26167586779918964697900547 39251380169878447046850821)
                ·
                  refine ⟨7359633781852208821284529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39251380169878447046850821 7359633781852208821284529)
                  ·
                    refine ⟨5519725336389156615963397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359633781852208821284529 5519725336389156615963397)
                    ·
                      refine ⟨1034948500572966865493137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5519725336389156615963397 1034948500572966865493137)
                      ·
                        rfl

theorem cell23_2015555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_2015555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015555 prefixEnd_2015555 := by exact prefixLift 2015555
  have htrace : WordTrace (prefixWord ++ tailWord_2015555) baseStart_2015555 baseEnd_2015555 := by
    simpa [prefixWord, tailWord_2015555, baseEnd_2015555] using wordTrace_append hprefix tailTrace_2015555
  have hstable : (prefixWord ++ tailWord_2015555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015555).length < 2 ^ (prefixWord ++ tailWord_2015555).sum := by decide
  have hdescent : baseEnd_2015555 < baseStart_2015555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015559 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_2015559 : Nat := 118140960795 + 2015559 * 2 ^ 59
def prefixEnd_2015559 : Nat := 4983230072969 + 3 ^ 40 * 2015559 * 2
def baseEnd_2015559 : Nat := 1034950554495584849843119

theorem tailTrace_2015559 : CollatzResearch.WordTrace tailWord_2015559 prefixEnd_2015559 1034950554495584849843119 := by
  unfold tailWord_2015559
  simp only [CollatzResearch.WordTrace]
  refine ⟨73513476104981447916753731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49008984069987631944502487 73513476104981447916753731)
  ·
    refine ⟨110270214157472171875130597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73513476104981447916753731 110270214157472171875130597)
    ·
      refine ⟨20675665154526032226586987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110270214157472171875130597 20675665154526032226586987)
      ·
        refine ⟨31013497731789048339880481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20675665154526032226586987 31013497731789048339880481)
        ·
          refine ⟨23260123298841786254910361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31013497731789048339880481 23260123298841786254910361)
          ·
            refine ⟨17445092474131339691182771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23260123298841786254910361 17445092474131339691182771)
            ·
              refine ⟨26167638711197009536774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17445092474131339691182771 26167638711197009536774157)
              ·
                refine ⟨9812864516698878576290309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26167638711197009536774157 9812864516698878576290309)
                ·
                  refine ⟨1839912096881039733054433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9812864516698878576290309 1839912096881039733054433)
                  ·
                    refine ⟨1379934072660779799790825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1839912096881039733054433 1379934072660779799790825)
                    ·
                      refine ⟨1034950554495584849843119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379934072660779799790825 1034950554495584849843119)
                      ·
                        rfl

theorem cell23_2015559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_2015559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015559 prefixEnd_2015559 := by exact prefixLift 2015559
  have htrace : WordTrace (prefixWord ++ tailWord_2015559) baseStart_2015559 baseEnd_2015559 := by
    simpa [prefixWord, tailWord_2015559, baseEnd_2015559] using wordTrace_append hprefix tailTrace_2015559
  have hstable : (prefixWord ++ tailWord_2015559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015559).length < 2 ^ (prefixWord ++ tailWord_2015559).sum := by decide
  have hdescent : baseEnd_2015559 < baseStart_2015559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015580 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2015580 : Nat := 118140960795 + 2015580 * 2 ^ 59
def prefixEnd_2015580 : Nat := 4983230072969 + 3 ^ 40 * 2015580 * 2
def baseEnd_2015580 : Nat := 1034961337589329267680523

theorem tailTrace_2015580 : CollatzResearch.WordTrace tailWord_2015580 prefixEnd_2015580 1034961337589329267680523 := by
  unfold tailWord_2015580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36757121018952684251634097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49009494691936912335512129 36757121018952684251634097)
  ·
    refine ⟨27567840764214513188725573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36757121018952684251634097 27567840764214513188725573)
    ·
      refine ⟨5168970143290221222886045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27567840764214513188725573 5168970143290221222886045)
      ·
        refine ⟨1938363803733832958582267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5168970143290221222886045 1938363803733832958582267)
        ·
          refine ⟨2907545705600749437873401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938363803733832958582267 2907545705600749437873401)
          ·
            refine ⟨2180659279200562078405051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907545705600749437873401 2180659279200562078405051)
            ·
              refine ⟨3270988918800843117607577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180659279200562078405051 3270988918800843117607577)
              ·
                refine ⟨2453241689100632338205683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270988918800843117607577 2453241689100632338205683)
                ·
                  refine ⟨3679862533650948507308525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453241689100632338205683 3679862533650948507308525)
                  ·
                    refine ⟨1379948450119105690240697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679862533650948507308525 1379948450119105690240697)
                    ·
                      refine ⟨1034961337589329267680523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1379948450119105690240697 1034961337589329267680523)
                      ·
                        rfl

theorem cell23_2015580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2015580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015580 prefixEnd_2015580 := by exact prefixLift 2015580
  have htrace : WordTrace (prefixWord ++ tailWord_2015580) baseStart_2015580 baseEnd_2015580 := by
    simpa [prefixWord, tailWord_2015580, baseEnd_2015580] using wordTrace_append hprefix tailTrace_2015580
  have hstable : (prefixWord ++ tailWord_2015580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015580).length < 2 ^ (prefixWord ++ tailWord_2015580).sum := by decide
  have hdescent : baseEnd_2015580 < baseStart_2015580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015595 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 6, 5]
def baseStart_2015595 : Nat := 118140960795 + 2015595 * 2 ^ 59
def prefixEnd_2015595 : Nat := 4983230072969 + 3 ^ 40 * 2015595 * 2
def baseEnd_2015595 : Nat := 344989679933048902997651

theorem tailTrace_2015595 : CollatzResearch.WordTrace tailWord_2015595 prefixEnd_2015595 344989679933048902997651 := by
  unfold tailWord_2015595
  simp only [CollatzResearch.WordTrace]
  refine ⟨73514789132851026065064239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49009859421900684043376159 73514789132851026065064239)
  ·
    refine ⟨110272183699276539097596359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73514789132851026065064239 110272183699276539097596359)
    ·
      refine ⟨165408275548914808646394539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110272183699276539097596359 165408275548914808646394539)
      ·
        refine ⟨248112413323372212969591809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165408275548914808646394539 248112413323372212969591809)
        ·
          refine ⟨186084309992529159727193857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248112413323372212969591809 186084309992529159727193857)
          ·
            refine ⟨139563232494396869795395393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186084309992529159727193857 139563232494396869795395393)
            ·
              refine ⟨104672424370797652346546545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139563232494396869795395393 104672424370797652346546545)
              ·
                refine ⟨78504318278098239259909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104672424370797652346546545 78504318278098239259909909)
                ·
                  refine ⟨3679889919285854965308277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78504318278098239259909909 3679889919285854965308277)
                  ·
                    refine ⟨344989679933048902997651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3679889919285854965308277 344989679933048902997651)
                    ·
                      rfl

theorem cell23_2015595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 5].length) (baseStart_2015595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015595 prefixEnd_2015595 := by exact prefixLift 2015595
  have htrace : WordTrace (prefixWord ++ tailWord_2015595) baseStart_2015595 baseEnd_2015595 := by
    simpa [prefixWord, tailWord_2015595, baseEnd_2015595] using wordTrace_append hprefix tailTrace_2015595
  have hstable : (prefixWord ++ tailWord_2015595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015595).length < 2 ^ (prefixWord ++ tailWord_2015595).sum := by decide
  have hdescent : baseEnd_2015595 < baseStart_2015595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015626 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2015626 : Nat := 118140960795 + 2015626 * 2 ^ 59
def prefixEnd_2015626 : Nat := 4983230072969 + 3 ^ 40 * 2015626 * 2
def baseEnd_2015626 : Nat := 1034984957699436087705311

theorem tailTrace_2015626 : CollatzResearch.WordTrace tailWord_2015626 prefixEnd_2015626 1034984957699436087705311 := by
  unfold tailWord_2015626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378979948934679589860683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49010613197159145572961821 18378979948934679589860683)
  ·
    refine ⟨27568469923402019384791025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378979948934679589860683 27568469923402019384791025)
    ·
      refine ⟨20676352442551514538593269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27568469923402019384791025 20676352442551514538593269)
      ·
        refine ⟨1938408041489204487993119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20676352442551514538593269 1938408041489204487993119)
        ·
          refine ⟨2907612062233806731989679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938408041489204487993119 2907612062233806731989679)
          ·
            refine ⟨4361418093350710097984519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907612062233806731989679 4361418093350710097984519)
            ·
              refine ⟨6542127140026065146976779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361418093350710097984519 6542127140026065146976779)
              ·
                refine ⟨9813190710039097720465169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6542127140026065146976779 9813190710039097720465169)
                ·
                  refine ⟨7359893032529323290348877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9813190710039097720465169 7359893032529323290348877)
                  ·
                    refine ⟨2759959887198496233880829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7359893032529323290348877 2759959887198496233880829)
                    ·
                      refine ⟨1034984957699436087705311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2759959887198496233880829 1034984957699436087705311)
                      ·
                        rfl

theorem cell23_2015626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2015626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015626 prefixEnd_2015626 := by exact prefixLift 2015626
  have htrace : WordTrace (prefixWord ++ tailWord_2015626) baseStart_2015626 baseEnd_2015626 := by
    simpa [prefixWord, tailWord_2015626, baseEnd_2015626] using wordTrace_append hprefix tailTrace_2015626
  have hstable : (prefixWord ++ tailWord_2015626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015626).length < 2 ^ (prefixWord ++ tailWord_2015626).sum := by decide
  have hdescent : baseEnd_2015626 < baseStart_2015626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015646 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2015646 : Nat := 118140960795 + 2015646 * 2 ^ 59
def prefixEnd_2015646 : Nat := 4983230072969 + 3 ^ 40 * 2015646 * 2
def baseEnd_2015646 : Nat := 344998409104175336485073

theorem tailTrace_2015646 : CollatzResearch.WordTrace tailWord_2015646 prefixEnd_2015646 344998409104175336485073 := by
  unfold tailWord_2015646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189581156958282721896349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49011099503777507850113861 9189581156958282721896349)
  ·
    refine ⟨3446092933859356020711131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9189581156958282721896349 3446092933859356020711131)
    ·
      refine ⟨5169139400789034031066697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446092933859356020711131 5169139400789034031066697)
      ·
        refine ⟨3876854550591775523300023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5169139400789034031066697 3876854550591775523300023)
        ·
          refine ⟨5815281825887663284950035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876854550591775523300023 5815281825887663284950035)
          ·
            refine ⟨8722922738831494927425053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815281825887663284950035 8722922738831494927425053)
            ·
              refine ⟨3271096027061810597784395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8722922738831494927425053 3271096027061810597784395)
              ·
                refine ⟨4906644040592715896676593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271096027061810597784395 4906644040592715896676593)
                ·
                  refine ⟨3679983030444536922507445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4906644040592715896676593 3679983030444536922507445)
                  ·
                    refine ⟨344998409104175336485073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3679983030444536922507445 344998409104175336485073)
                    ·
                      rfl

theorem cell23_2015646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2015646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015646 prefixEnd_2015646 := by exact prefixLift 2015646
  have htrace : WordTrace (prefixWord ++ tailWord_2015646) baseStart_2015646 baseEnd_2015646 := by
    simpa [prefixWord, tailWord_2015646, baseEnd_2015646] using wordTrace_append hprefix tailTrace_2015646
  have hstable : (prefixWord ++ tailWord_2015646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015646).length < 2 ^ (prefixWord ++ tailWord_2015646).sum := by decide
  have hdescent : baseEnd_2015646 < baseStart_2015646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015676 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_2015676 : Nat := 118140960795 + 2015676 * 2 ^ 59
def prefixEnd_2015676 : Nat := 4983230072969 + 3 ^ 40 * 2015676 * 2
def baseEnd_2015676 : Nat := 345003543910720297360027

theorem tailTrace_2015676 : CollatzResearch.WordTrace tailWord_2015676 prefixEnd_2015676 345003543910720297360027 := by
  unfold tailWord_2015676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36758871722778788449381441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49011828963705051265841921 36758871722778788449381441)
  ·
    refine ⟨27569153792084091337036081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36758871722778788449381441 27569153792084091337036081)
    ·
      refine ⟨20676865344063068502777061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27569153792084091337036081 20676865344063068502777061)
      ·
        refine ⟨3876912252011825344270699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20676865344063068502777061 3876912252011825344270699)
        ·
          refine ⟨5815368378017738016406049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876912252011825344270699 5815368378017738016406049)
          ·
            refine ⟨4361526283513303512304537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5815368378017738016406049 4361526283513303512304537)
            ·
              refine ⟨3271144712634977634228403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361526283513303512304537 3271144712634977634228403)
              ·
                refine ⟨4906717068952466451342605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271144712634977634228403 4906717068952466451342605)
                ·
                  refine ⟨1840018900857174919253477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4906717068952466451342605 1840018900857174919253477)
                  ·
                    refine ⟨345003543910720297360027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1840018900857174919253477 345003543910720297360027)
                    ·
                      rfl

theorem cell23_2015676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_2015676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015676 prefixEnd_2015676 := by exact prefixLift 2015676
  have htrace : WordTrace (prefixWord ++ tailWord_2015676) baseStart_2015676 baseEnd_2015676 := by
    simpa [prefixWord, tailWord_2015676, baseEnd_2015676] using wordTrace_append hprefix tailTrace_2015676
  have hstable : (prefixWord ++ tailWord_2015676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015676).length < 2 ^ (prefixWord ++ tailWord_2015676).sum := by decide
  have hdescent : baseEnd_2015676 < baseStart_2015676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015719 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2015719 : Nat := 118140960795 + 2015719 * 2 ^ 59
def prefixEnd_2015719 : Nat := 4983230072969 + 3 ^ 40 * 2015719 * 2
def baseEnd_2015719 : Nat := 345010903800101407947461

theorem tailTrace_2015719 : CollatzResearch.WordTrace tailWord_2015719 prefixEnd_2015719 345010903800101407947461 := by
  unfold tailWord_2015719
  simp only [CollatzResearch.WordTrace]
  refine ⟨73519311784401795242578211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49012874522934530161718807 73519311784401795242578211)
  ·
    refine ⟨110278967676602692863867317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73519311784401795242578211 110278967676602692863867317)
    ·
      refine ⟨10338653219681502455987561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110278967676602692863867317 10338653219681502455987561)
      ·
        refine ⟨7753989914761126841990671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10338653219681502455987561 7753989914761126841990671)
        ·
          refine ⟨11630984872141690262986007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753989914761126841990671 11630984872141690262986007)
          ·
            refine ⟨17446477308212535394479011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630984872141690262986007 17446477308212535394479011)
            ·
              refine ⟨26169715962318803091718517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446477308212535394479011 26169715962318803091718517)
              ·
                refine ⟨2453410871467387789848611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26169715962318803091718517 2453410871467387789848611)
                ·
                  refine ⟨3680116307201081684772917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453410871467387789848611 3680116307201081684772917)
                  ·
                    refine ⟨345010903800101407947461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3680116307201081684772917 345010903800101407947461)
                    ·
                      rfl

theorem cell23_2015719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2015719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015719 prefixEnd_2015719 := by exact prefixLift 2015719
  have htrace : WordTrace (prefixWord ++ tailWord_2015719) baseStart_2015719 baseEnd_2015719 := by
    simpa [prefixWord, tailWord_2015719, baseEnd_2015719] using wordTrace_append hprefix tailTrace_2015719
  have hstable : (prefixWord ++ tailWord_2015719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015719).length < 2 ^ (prefixWord ++ tailWord_2015719).sum := by decide
  have hdescent : baseEnd_2015719 < baseStart_2015719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015726 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_2015726 : Nat := 118140960795 + 2015726 * 2 ^ 59
def prefixEnd_2015726 : Nat := 4983230072969 + 3 ^ 40 * 2015726 * 2
def baseEnd_2015726 : Nat := 1035036305764885696454851

theorem tailTrace_2015726 : CollatzResearch.WordTrace tailWord_2015726 prefixEnd_2015726 1035036305764885696454851 := by
  unfold tailWord_2015726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189945886922054429760379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49013044730250956958722021 9189945886922054429760379)
  ·
    refine ⟨13784918830383081644640569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9189945886922054429760379 13784918830383081644640569)
    ·
      refine ⟨10338689122787311233480427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13784918830383081644640569 10338689122787311233480427)
      ·
        refine ⟨15508033684180966850220641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338689122787311233480427 15508033684180966850220641)
        ·
          refine ⟨11631025263135725137665481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15508033684180966850220641 11631025263135725137665481)
          ·
            refine ⟨8723268947351793853249111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631025263135725137665481 8723268947351793853249111)
            ·
              refine ⟨13084903421027690779873667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723268947351793853249111 13084903421027690779873667)
              ·
                refine ⟨19627355131541536169810501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13084903421027690779873667 19627355131541536169810501)
                ·
                  refine ⟨3680129087164038031839469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19627355131541536169810501 3680129087164038031839469)
                  ·
                    refine ⟨1380048407686514261939801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3680129087164038031839469 1380048407686514261939801)
                    ·
                      refine ⟨1035036305764885696454851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380048407686514261939801 1035036305764885696454851)
                      ·
                        rfl

theorem cell23_2015726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_2015726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015726 prefixEnd_2015726 := by exact prefixLift 2015726
  have htrace : WordTrace (prefixWord ++ tailWord_2015726) baseStart_2015726 baseEnd_2015726 := by
    simpa [prefixWord, tailWord_2015726, baseEnd_2015726] using wordTrace_append hprefix tailTrace_2015726
  have hstable : (prefixWord ++ tailWord_2015726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015726).length < 2 ^ (prefixWord ++ tailWord_2015726).sum := by decide
  have hdescent : baseEnd_2015726 < baseStart_2015726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015756 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_2015756 : Nat := 118140960795 + 2015756 * 2 ^ 59
def prefixEnd_2015756 : Nat := 4983230072969 + 3 ^ 40 * 2015756 * 2
def baseEnd_2015756 : Nat := 1035051710184520579079713

theorem tailTrace_2015756 : CollatzResearch.WordTrace tailWord_2015756 prefixEnd_2015756 1035051710184520579079713 := by
  unfold tailWord_2015756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760330642633875280837561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49013774190178500374450081 36760330642633875280837561)
  ·
    refine ⟨27570247981975406460628171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36760330642633875280837561 27570247981975406460628171)
    ·
      refine ⟨41355371972963109690942257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27570247981975406460628171 41355371972963109690942257)
      ·
        refine ⟨31016528979722332268206693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41355371972963109690942257 31016528979722332268206693)
        ·
          refine ⟨5815599183697937300288755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31016528979722332268206693 5815599183697937300288755)
          ·
            refine ⟨8723398775546905950433133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815599183697937300288755 8723398775546905950433133)
            ·
              refine ⟨3271274540830089731412425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8723398775546905950433133 3271274540830089731412425)
              ·
                refine ⟨2453455905622567298559319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271274540830089731412425 2453455905622567298559319)
                ·
                  refine ⟨3680183858433850947838979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453455905622567298559319 3680183858433850947838979)
                  ·
                    refine ⟨5520275787650776421758469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3680183858433850947838979 5520275787650776421758469)
                    ·
                      refine ⟨1035051710184520579079713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5520275787650776421758469 1035051710184520579079713)
                      ·
                        rfl

theorem cell23_2015756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_2015756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015756 prefixEnd_2015756 := by exact prefixLift 2015756
  have htrace : WordTrace (prefixWord ++ tailWord_2015756) baseStart_2015756 baseEnd_2015756 := by
    simpa [prefixWord, tailWord_2015756, baseEnd_2015756] using wordTrace_append hprefix tailTrace_2015756
  have hstable : (prefixWord ++ tailWord_2015756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015756).length < 2 ^ (prefixWord ++ tailWord_2015756).sum := by decide
  have hdescent : baseEnd_2015756 < baseStart_2015756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015773 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2015773 : Nat := 118140960795 + 2015773 * 2 ^ 59
def prefixEnd_2015773 : Nat := 4983230072969 + 3 ^ 40 * 2015773 * 2
def baseEnd_2015773 : Nat := 1035060439355647012567135

theorem tailTrace_2015773 : CollatzResearch.WordTrace tailWord_2015773 prefixEnd_2015773 1035060439355647012567135 := by
  unfold tailWord_2015773
  simp only [CollatzResearch.WordTrace]
  refine ⟨73521281326206162465043973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49014187550804108310029315 73521281326206162465043973)
  ·
    refine ⟨13785240248663655462195745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73521281326206162465043973 13785240248663655462195745)
    ·
      refine ⟨10338930186497741596646809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13785240248663655462195745 10338930186497741596646809)
      ·
        refine ⟨7754197639873306197485107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10338930186497741596646809 7754197639873306197485107)
        ·
          refine ⟨11631296459809959296227661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754197639873306197485107 11631296459809959296227661)
          ·
            refine ⟨4361736172428734736085373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11631296459809959296227661 4361736172428734736085373)
            ·
              refine ⟨1635651064660775526032015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4361736172428734736085373 1635651064660775526032015)
              ·
                refine ⟨2453476596991163289048023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635651064660775526032015 2453476596991163289048023)
                ·
                  refine ⟨3680214895486744933572035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453476596991163289048023 3680214895486744933572035)
                  ·
                    refine ⟨5520322343230117400358053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3680214895486744933572035 5520322343230117400358053)
                    ·
                      refine ⟨1035060439355647012567135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5520322343230117400358053 1035060439355647012567135)
                      ·
                        rfl

theorem cell23_2015773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2015773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015773 prefixEnd_2015773 := by exact prefixLift 2015773
  have htrace : WordTrace (prefixWord ++ tailWord_2015773) baseStart_2015773 baseEnd_2015773 := by
    simpa [prefixWord, tailWord_2015773, baseEnd_2015773] using wordTrace_append hprefix tailTrace_2015773
  have hstable : (prefixWord ++ tailWord_2015773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015773).length < 2 ^ (prefixWord ++ tailWord_2015773).sum := by decide
  have hdescent : baseEnd_2015773 < baseStart_2015773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015792 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_2015792 : Nat := 118140960795 + 2015792 * 2 ^ 59
def prefixEnd_2015792 : Nat := 4983230072969 + 3 ^ 40 * 2015792 * 2
def baseEnd_2015792 : Nat := 345023398496027479409849

theorem tailTrace_2015792 : CollatzResearch.WordTrace tailWord_2015792 prefixEnd_2015792 345023398496027479409849 := by
  unfold tailWord_2015792
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760987156568664354992815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49014649542091552473323753 36760987156568664354992815)
  ·
    refine ⟨55141480734852996532489223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36760987156568664354992815 55141480734852996532489223)
    ·
      refine ⟨82712221102279494798733835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55141480734852996532489223 82712221102279494798733835)
      ·
        refine ⟨124068331653419242198100753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82712221102279494798733835 124068331653419242198100753)
        ·
          refine ⟨93051248740064431648575565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124068331653419242198100753 93051248740064431648575565)
          ·
            refine ⟨34894218277524161868215837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93051248740064431648575565 34894218277524161868215837)
            ·
              refine ⟨13085331854071560700580939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34894218277524161868215837 13085331854071560700580939)
              ·
                refine ⟨19627997781107341050871409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085331854071560700580939 19627997781107341050871409)
                ·
                  refine ⟨14720998335830505788153557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19627997781107341050871409 14720998335830505788153557)
                  ·
                    refine ⟨345023398496027479409849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14720998335830505788153557 345023398496027479409849)
                    ·
                      rfl

theorem cell23_2015792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_2015792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015792 prefixEnd_2015792 := by exact prefixLift 2015792
  have htrace : WordTrace (prefixWord ++ tailWord_2015792) baseStart_2015792 baseEnd_2015792 := by
    simpa [prefixWord, tailWord_2015792, baseEnd_2015792] using wordTrace_append hprefix tailTrace_2015792
  have hstable : (prefixWord ++ tailWord_2015792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015792).length < 2 ^ (prefixWord ++ tailWord_2015792).sum := by decide
  have hdescent : baseEnd_2015792 < baseStart_2015792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015863 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_2015863 : Nat := 118140960795 + 2015863 * 2 ^ 59
def prefixEnd_2015863 : Nat := 4983230072969 + 3 ^ 40 * 2015863 * 2
def baseEnd_2015863 : Nat := 1035106652614551660441721

theorem tailTrace_2015863 : CollatzResearch.WordTrace tailWord_2015863 prefixEnd_2015863 1035106652614551660441721 := by
  unfold tailWord_2015863
  simp only [CollatzResearch.WordTrace]
  refine ⟨73524563895880107835820243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49016375930586738557213495 73524563895880107835820243)
  ·
    refine ⟨110286845843820161753730365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73524563895880107835820243 110286845843820161753730365)
    ·
      refine ⟨41357567191432560657648887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110286845843820161753730365 41357567191432560657648887)
      ·
        refine ⟨62036350787148840986473331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41357567191432560657648887 62036350787148840986473331)
        ·
          refine ⟨93054526180723261479709997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62036350787148840986473331 93054526180723261479709997)
          ·
            refine ⟨34895447317771223054891249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93054526180723261479709997 34895447317771223054891249)
            ·
              refine ⟨26171585488328417291168437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34895447317771223054891249 26171585488328417291168437)
              ·
                refine ⟨2453586139530789121047041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26171585488328417291168437 2453586139530789121047041)
                ·
                  refine ⟨1840189604648091840785281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453586139530789121047041 1840189604648091840785281)
                  ·
                    refine ⟨1380142203486068880588961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840189604648091840785281 1380142203486068880588961)
                    ·
                      refine ⟨1035106652614551660441721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380142203486068880588961 1035106652614551660441721)
                      ·
                        rfl

theorem cell23_2015863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_2015863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015863 prefixEnd_2015863 := by exact prefixLift 2015863
  have htrace : WordTrace (prefixWord ++ tailWord_2015863) baseStart_2015863 baseEnd_2015863 := by
    simpa [prefixWord, tailWord_2015863, baseEnd_2015863] using wordTrace_append hprefix tailTrace_2015863
  have hstable : (prefixWord ++ tailWord_2015863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015863).length < 2 ^ (prefixWord ++ tailWord_2015863).sum := by decide
  have hdescent : baseEnd_2015863 < baseStart_2015863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015914 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2015914 : Nat := 118140960795 + 2015914 * 2 ^ 59
def prefixEnd_2015914 : Nat := 4983230072969 + 3 ^ 40 * 2015914 * 2
def baseEnd_2015914 : Nat := 1035132840127930960903987

theorem tailTrace_2015914 : CollatzResearch.WordTrace tailWord_2015914 prefixEnd_2015914 1035132840127930960903987 := by
  unfold tailWord_2015914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381606004673835886481699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49017616012463562363951197 18381606004673835886481699)
  ·
    refine ⟨27572409007010753829722549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381606004673835886481699 27572409007010753829722549)
    ·
      refine ⟨2584913344407258171536489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27572409007010753829722549 2584913344407258171536489)
      ·
        refine ⟨1938685008305443628652367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2584913344407258171536489 1938685008305443628652367)
        ·
          refine ⟨2908027512458165442978551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938685008305443628652367 2908027512458165442978551)
          ·
            refine ⟨4362041268687248164467827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908027512458165442978551 4362041268687248164467827)
            ·
              refine ⟨6543061903030872246701741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362041268687248164467827 6543061903030872246701741)
              ·
                refine ⟨2453648213636577092513153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6543061903030872246701741 2453648213636577092513153)
                ·
                  refine ⟨1840236160227432819384865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453648213636577092513153 1840236160227432819384865)
                  ·
                    refine ⟨1380177120170574614538649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840236160227432819384865 1380177120170574614538649)
                    ·
                      refine ⟨1035132840127930960903987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380177120170574614538649 1035132840127930960903987)
                      ·
                        rfl

theorem cell23_2015914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2015914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015914 prefixEnd_2015914 := by exact prefixLift 2015914
  have htrace : WordTrace (prefixWord ++ tailWord_2015914) baseStart_2015914 baseEnd_2015914 := by
    simpa [prefixWord, tailWord_2015914, baseEnd_2015914] using wordTrace_append hprefix tailTrace_2015914
  have hstable : (prefixWord ++ tailWord_2015914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015914).length < 2 ^ (prefixWord ++ tailWord_2015914).sum := by decide
  have hdescent : baseEnd_2015914 < baseStart_2015914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
