import V185TrunkScan21Chunk157

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1924701 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 4]
def baseStart_1924701 : Nat := 118140960795 + 1924701 * 2 ^ 59
def prefixEnd_1924701 : Nat := 4983230072969 + 3 ^ 40 * 1924701 * 2
def baseEnd_1924701 : Nat := 439242990750835258749319

theorem tailTrace_1924701 : CollatzResearch.WordTrace tailWord_1924701 prefixEnd_1924701 439242990750835258749319 := by
  unfold tailWord_1924701
  simp only [CollatzResearch.WordTrace]
  refine ⟨70199612600144464605749957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46799741733429643070499971 70199612600144464605749957)
  ·
    refine ⟨13162427362527087113578117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70199612600144464605749957 13162427362527087113578117)
    ·
      refine ⟨2467955130473828833795897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13162427362527087113578117 2467955130473828833795897)
      ·
        refine ⟨1850966347855371625346923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2467955130473828833795897 1850966347855371625346923)
        ·
          refine ⟨2776449521783057438020385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850966347855371625346923 2776449521783057438020385)
          ·
            refine ⟨2082337141337293078515289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776449521783057438020385 2082337141337293078515289)
            ·
              refine ⟨1561752856002969808886467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082337141337293078515289 1561752856002969808886467)
              ·
                refine ⟨2342629284004454713329701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561752856002969808886467 2342629284004454713329701)
                ·
                  refine ⟨439242990750835258749319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342629284004454713329701 439242990750835258749319)
                  ·
                    rfl

theorem cell21_1924701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_1924701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924701 prefixEnd_1924701 := by exact prefixLift 1924701
  have htrace : WordTrace (prefixWord ++ tailWord_1924701) baseStart_1924701 baseEnd_1924701 := by
    simpa [prefixWord, tailWord_1924701, baseEnd_1924701] using wordTrace_append hprefix tailTrace_1924701
  have hstable : (prefixWord ++ tailWord_1924701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924701).length < 2 ^ (prefixWord ++ tailWord_1924701).sum := by decide
  have hdescent : baseEnd_1924701 < baseStart_1924701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924740 : List Nat := [2, 3, 2, 1, 5, 8]
def baseStart_1924740 : Nat := 118140960795 + 1924740 * 2 ^ 59
def prefixEnd_1924740 : Nat := 4983230072969 + 3 ^ 40 * 1924740 * 2
def baseEnd_1924740 : Nat := 16268588558599253985157

theorem tailTrace_1924740 : CollatzResearch.WordTrace tailWord_1924740 prefixEnd_1924740 16268588558599253985157 := by
  unfold tailWord_1924740
  simp only [CollatzResearch.WordTrace]
  refine ⟨35100517523501587133209837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46800690031335449510946449 35100517523501587133209837)
  ·
    refine ⟨13162694071313095174953689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35100517523501587133209837 13162694071313095174953689)
    ·
      refine ⟨9872020553484821381215267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13162694071313095174953689 9872020553484821381215267)
      ·
        refine ⟨14808030830227232071822901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9872020553484821381215267 14808030830227232071822901)
        ·
          refine ⟨1388252890333803006733397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14808030830227232071822901 1388252890333803006733397)
          ·
            refine ⟨16268588558599253985157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1388252890333803006733397 16268588558599253985157)
            ·
              rfl

theorem cell21_1924740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 8].length) (baseStart_1924740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924740 prefixEnd_1924740 := by exact prefixLift 1924740
  have htrace : WordTrace (prefixWord ++ tailWord_1924740) baseStart_1924740 baseEnd_1924740 := by
    simpa [prefixWord, tailWord_1924740, baseEnd_1924740] using wordTrace_append hprefix tailTrace_1924740
  have hstable : (prefixWord ++ tailWord_1924740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924740).length < 2 ^ (prefixWord ++ tailWord_1924740).sum := by decide
  have hdescent : baseEnd_1924740 < baseStart_1924740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924833 : List Nat := [1, 2, 3, 1, 5, 2, 2, 5]
def baseStart_1924833 : Nat := 118140960795 + 1924833 * 2 ^ 59
def prefixEnd_1924833 : Nat := 4983230072969 + 3 ^ 40 * 1924833 * 2
def baseEnd_1924833 : Nat := 146424371649744120849683

theorem tailTrace_1924833 : CollatzResearch.WordTrace tailWord_1924833 prefixEnd_1924833 146424371649744120849683 := by
  unfold tailWord_1924833
  simp only [CollatzResearch.WordTrace]
  refine ⟨70204427035666251149555153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46802951357110834099703435 70204427035666251149555153)
  ·
    refine ⟨52653320276749688362166365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70204427035666251149555153 52653320276749688362166365)
    ·
      refine ⟨19744995103781133135812387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52653320276749688362166365 19744995103781133135812387)
      ·
        refine ⟨29617492655671699703718581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19744995103781133135812387 29617492655671699703718581)
        ·
          refine ⟨2776639936469221847223617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29617492655671699703718581 2776639936469221847223617)
          ·
            refine ⟨2082479952351916385417713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776639936469221847223617 2082479952351916385417713)
            ·
              refine ⟨1561859964263937289063285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082479952351916385417713 1561859964263937289063285)
              ·
                refine ⟨146424371649744120849683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1561859964263937289063285 146424371649744120849683)
                ·
                  rfl

theorem cell21_1924833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 5].length) (baseStart_1924833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924833 prefixEnd_1924833 := by exact prefixLift 1924833
  have htrace : WordTrace (prefixWord ++ tailWord_1924833) baseStart_1924833 baseEnd_1924833 := by
    simpa [prefixWord, tailWord_1924833, baseEnd_1924833] using wordTrace_append hprefix tailTrace_1924833
  have hstable : (prefixWord ++ tailWord_1924833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924833).length < 2 ^ (prefixWord ++ tailWord_1924833).sum := by decide
  have hdescent : baseEnd_1924833 < baseStart_1924833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924844 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1924844 : Nat := 118140960795 + 1924844 * 2 ^ 59
def prefixEnd_1924844 : Nat := 4983230072969 + 3 ^ 40 * 1924844 * 2
def baseEnd_1924844 : Nat := 439275625299098787865693

theorem tailTrace_1924844 : CollatzResearch.WordTrace tailWord_1924844 prefixEnd_1924844 439275625299098787865693 := by
  unfold tailWord_1924844
  simp only [CollatzResearch.WordTrace]
  refine ⟨35102414119313200014102793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46803218825750933352137057 35102414119313200014102793)
  ·
    refine ⟨26326810589484900010577095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35102414119313200014102793 26326810589484900010577095)
    ·
      refine ⟨39490215884227350015865643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326810589484900010577095 39490215884227350015865643)
      ·
        refine ⟨59235323826341025023798465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39490215884227350015865643 59235323826341025023798465)
        ·
          refine ⟨44426492869755768767848849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59235323826341025023798465 44426492869755768767848849)
          ·
            refine ⟨33319869652316826575886637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44426492869755768767848849 33319869652316826575886637)
            ·
              refine ⟨12494951119618809965957489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33319869652316826575886637 12494951119618809965957489)
              ·
                refine ⟨9371213339714107474468117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12494951119618809965957489 9371213339714107474468117)
                ·
                  refine ⟨439275625299098787865693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9371213339714107474468117 439275625299098787865693)
                  ·
                    rfl

theorem cell21_1924844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1924844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924844 prefixEnd_1924844 := by exact prefixLift 1924844
  have htrace : WordTrace (prefixWord ++ tailWord_1924844) baseStart_1924844 baseEnd_1924844 := by
    simpa [prefixWord, tailWord_1924844, baseEnd_1924844] using wordTrace_append hprefix tailTrace_1924844
  have hstable : (prefixWord ++ tailWord_1924844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924844).length < 2 ^ (prefixWord ++ tailWord_1924844).sum := by decide
  have hdescent : baseEnd_1924844 < baseStart_1924844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924870 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1924870 : Nat := 118140960795 + 1924870 * 2 ^ 59
def prefixEnd_1924870 : Nat := 4983230072969 + 3 ^ 40 * 1924870 * 2
def baseEnd_1924870 : Nat := 439281558853328520432307

theorem tailTrace_1924870 : CollatzResearch.WordTrace tailWord_1924870 prefixEnd_1924870 439281558853328520432307 := by
  unfold tailWord_1924870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193930516766631452145377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46803851024354804312434709 2193930516766631452145377)
  ·
    refine ⟨1645447887574973589109033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2193930516766631452145377 1645447887574973589109033)
    ·
      refine ⟨1234085915681230191831775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1645447887574973589109033 1234085915681230191831775)
      ·
        refine ⟨1851128873521845287747663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234085915681230191831775 1851128873521845287747663)
        ·
          refine ⟨2776693310282767931621495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851128873521845287747663 2776693310282767931621495)
          ·
            refine ⟨4165039965424151897432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776693310282767931621495 4165039965424151897432243)
            ·
              refine ⟨6247559948136227846148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4165039965424151897432243 6247559948136227846148365)
              ·
                refine ⟨2342834980551085442305637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6247559948136227846148365 2342834980551085442305637)
                ·
                  refine ⟨439281558853328520432307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342834980551085442305637 439281558853328520432307)
                  ·
                    rfl

theorem cell21_1924870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1924870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924870 prefixEnd_1924870 := by exact prefixLift 1924870
  have htrace : WordTrace (prefixWord ++ tailWord_1924870) baseStart_1924870 baseEnd_1924870 := by
    simpa [prefixWord, tailWord_1924870, baseEnd_1924870] using wordTrace_append hprefix tailTrace_1924870
  have hstable : (prefixWord ++ tailWord_1924870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924870).length < 2 ^ (prefixWord ++ tailWord_1924870).sum := by decide
  have hdescent : baseEnd_1924870 < baseStart_1924870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924878 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1924878 : Nat := 118140960795 + 1924878 * 2 ^ 59
def prefixEnd_1924878 : Nat := 4983230072969 + 3 ^ 40 * 1924878 * 2
def baseEnd_1924878 : Nat := 439283384562322284298957

theorem tailTrace_1924878 : CollatzResearch.WordTrace tailWord_1924878 prefixEnd_1924878 439283384562322284298957 := by
  unfold tailWord_1924878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775758540062902979367911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46804045547002149223295525 8775758540062902979367911)
  ·
    refine ⟨13163637810094354469051867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775758540062902979367911 13163637810094354469051867)
    ·
      refine ⟨19745456715141531703577801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13163637810094354469051867 19745456715141531703577801)
      ·
        refine ⟨14809092536356148777683351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19745456715141531703577801 14809092536356148777683351)
        ·
          refine ⟨22213638804534223166525027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14809092536356148777683351 22213638804534223166525027)
          ·
            refine ⟨33320458206801334749787541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22213638804534223166525027 33320458206801334749787541)
            ·
              refine ⟨1561896478443812566396291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33320458206801334749787541 1561896478443812566396291)
              ·
                refine ⟨2342844717665718849594437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561896478443812566396291 2342844717665718849594437)
                ·
                  refine ⟨439283384562322284298957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342844717665718849594437 439283384562322284298957)
                  ·
                    rfl

theorem cell21_1924878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1924878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924878 prefixEnd_1924878 := by exact prefixLift 1924878
  have htrace : WordTrace (prefixWord ++ tailWord_1924878) baseStart_1924878 baseEnd_1924878 := by
    simpa [prefixWord, tailWord_1924878, baseEnd_1924878] using wordTrace_append hprefix tailTrace_1924878
  have hstable : (prefixWord ++ tailWord_1924878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924878).length < 2 ^ (prefixWord ++ tailWord_1924878).sum := by decide
  have hdescent : baseEnd_1924878 < baseStart_1924878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924965 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_1924965 : Nat := 118140960795 + 1924965 * 2 ^ 59
def prefixEnd_1924965 : Nat := 4983230072969 + 3 ^ 40 * 1924965 * 2
def baseEnd_1924965 : Nat := 439303239147629466348779

theorem tailTrace_1924965 : CollatzResearch.WordTrace tailWord_1924965 prefixEnd_1924965 439303239147629466348779 := by
  unfold tailWord_1924965
  simp only [CollatzResearch.WordTrace]
  refine ⟨70209241471188037693360349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46806160980792025128906899 70209241471188037693360349)
  ·
    refine ⟨26328465551695514135010131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70209241471188037693360349 26328465551695514135010131)
    ·
      refine ⟨39492698327543271202515197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26328465551695514135010131 39492698327543271202515197)
      ·
        refine ⟨14809761872828726700943199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39492698327543271202515197 14809761872828726700943199)
        ·
          refine ⟨22214642809243090051414799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14809761872828726700943199 22214642809243090051414799)
          ·
            refine ⟨33321964213864635077122199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22214642809243090051414799 33321964213864635077122199)
            ·
              refine ⟨49982946320796952615683299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33321964213864635077122199 49982946320796952615683299)
              ·
                refine ⟨74974419481195428923524949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49982946320796952615683299 74974419481195428923524949)
                ·
                  refine ⟨439303239147629466348779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74974419481195428923524949 439303239147629466348779)
                  ·
                    rfl

theorem cell21_1924965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_1924965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924965 prefixEnd_1924965 := by exact prefixLift 1924965
  have htrace : WordTrace (prefixWord ++ tailWord_1924965) baseStart_1924965 baseEnd_1924965 := by
    simpa [prefixWord, tailWord_1924965, baseEnd_1924965] using wordTrace_append hprefix tailTrace_1924965
  have hstable : (prefixWord ++ tailWord_1924965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924965).length < 2 ^ (prefixWord ++ tailWord_1924965).sum := by decide
  have hdescent : baseEnd_1924965 < baseStart_1924965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925002 : List Nat := [3, 1, 2, 4, 3, 1, 2, 5]
def baseStart_1925002 : Nat := 118140960795 + 1925002 * 2 ^ 59
def prefixEnd_1925002 : Nat := 4983230072969 + 3 ^ 40 * 1925002 * 2
def baseEnd_1925002 : Nat := 146437227683908541410679

theorem tailTrace_1925002 : CollatzResearch.WordTrace tailWord_1925002 prefixEnd_1925002 146437227683908541410679 := by
  unfold tailWord_1925002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552647743013498253114315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46807060648035995341638173 17552647743013498253114315)
  ·
    refine ⟨26328971614520247379671473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17552647743013498253114315 26328971614520247379671473)
    ·
      refine ⟨19746728710890185534753605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26328971614520247379671473 19746728710890185534753605)
      ·
        refine ⟨3702511633291909787766301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19746728710890185534753605 3702511633291909787766301)
        ·
          refine ⟨1388441862484466170412363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3702511633291909787766301 1388441862484466170412363)
          ·
            refine ⟨2082662793726699255618545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388441862484466170412363 2082662793726699255618545)
            ·
              refine ⟨1561997095295024441713909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082662793726699255618545 1561997095295024441713909)
              ·
                refine ⟨146437227683908541410679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1561997095295024441713909 146437227683908541410679)
                ·
                  rfl

theorem cell21_1925002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_1925002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925002 prefixEnd_1925002 := by exact prefixLift 1925002
  have htrace : WordTrace (prefixWord ++ tailWord_1925002) baseStart_1925002 baseEnd_1925002 := by
    simpa [prefixWord, tailWord_1925002, baseEnd_1925002] using wordTrace_append hprefix tailTrace_1925002
  have hstable : (prefixWord ++ tailWord_1925002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925002).length < 2 ^ (prefixWord ++ tailWord_1925002).sum := by decide
  have hdescent : baseEnd_1925002 < baseStart_1925002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925084 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_1925084 : Nat := 118140960795 + 1925084 * 2 ^ 59
def prefixEnd_1925084 : Nat := 4983230072969 + 3 ^ 40 * 1925084 * 2
def baseEnd_1925084 : Nat := 439330396568911703865203

theorem tailTrace_1925084 : CollatzResearch.WordTrace tailWord_1925084 prefixEnd_1925084 439330396568911703865203 := by
  unfold tailWord_1925084
  simp only [CollatzResearch.WordTrace]
  refine ⟨35106790878878460508471153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46809054505171280677961537 35106790878878460508471153)
  ·
    refine ⟨26330093159158845381353365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35106790878878460508471153 26330093159158845381353365)
    ·
      refine ⟨1234223116835570877250939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26330093159158845381353365 1234223116835570877250939)
      ·
        refine ⟨1851334675253356315876409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234223116835570877250939 1851334675253356315876409)
        ·
          refine ⟨1388501006440017236907307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851334675253356315876409 1388501006440017236907307)
          ·
            refine ⟨2082751509660025855360961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388501006440017236907307 2082751509660025855360961)
            ·
              refine ⟨1562063632245019391520721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082751509660025855360961 1562063632245019391520721)
              ·
                refine ⟨1171547724183764543640541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562063632245019391520721 1171547724183764543640541)
                ·
                  refine ⟨439330396568911703865203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171547724183764543640541 439330396568911703865203)
                  ·
                    rfl

theorem cell21_1925084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_1925084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925084 prefixEnd_1925084 := by exact prefixLift 1925084
  have htrace : WordTrace (prefixWord ++ tailWord_1925084) baseStart_1925084 baseEnd_1925084 := by
    simpa [prefixWord, tailWord_1925084, baseEnd_1925084] using wordTrace_append hprefix tailTrace_1925084
  have hstable : (prefixWord ++ tailWord_1925084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925084).length < 2 ^ (prefixWord ++ tailWord_1925084).sum := by decide
  have hdescent : baseEnd_1925084 < baseStart_1925084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925117 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1925117 : Nat := 118140960795 + 1925117 * 2 ^ 59
def prefixEnd_1925117 : Nat := 4983230072969 + 3 ^ 40 * 1925117 * 2
def baseEnd_1925117 : Nat := 439337927618510979815135

theorem tailTrace_1925117 : CollatzResearch.WordTrace tailWord_1925117 prefixEnd_1925117 439337927618510979815135 := by
  unfold tailWord_1925117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70214785366637367652893605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46809856911091578435262403 70214785366637367652893605)
  ·
    refine ⟨13165272256244506434917551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70214785366637367652893605 13165272256244506434917551)
    ·
      refine ⟨19747908384366759652376327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13165272256244506434917551 19747908384366759652376327)
      ·
        refine ⟨29621862576550139478564491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19747908384366759652376327 29621862576550139478564491)
        ·
          refine ⟨44432793864825209217846737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29621862576550139478564491 44432793864825209217846737)
          ·
            refine ⟨33324595398618906913385053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44432793864825209217846737 33324595398618906913385053)
            ·
              refine ⟨12496723274482090092519395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33324595398618906913385053 12496723274482090092519395)
              ·
                refine ⟨18745084911723135138779093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12496723274482090092519395 18745084911723135138779093)
                ·
                  refine ⟨439337927618510979815135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18745084911723135138779093 439337927618510979815135)
                  ·
                    rfl

theorem cell21_1925117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1925117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925117 prefixEnd_1925117 := by exact prefixLift 1925117
  have htrace : WordTrace (prefixWord ++ tailWord_1925117) baseStart_1925117 baseEnd_1925117 := by
    simpa [prefixWord, tailWord_1925117, baseEnd_1925117] using wordTrace_append hprefix tailTrace_1925117
  have hstable : (prefixWord ++ tailWord_1925117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925117).length < 2 ^ (prefixWord ++ tailWord_1925117).sum := by decide
  have hdescent : baseEnd_1925117 < baseStart_1925117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925140 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1925140 : Nat := 118140960795 + 1925140 * 2 ^ 59
def prefixEnd_1925140 : Nat := 4983230072969 + 3 ^ 40 * 1925140 * 2
def baseEnd_1925140 : Nat := 439343176531868050931755

theorem tailTrace_1925140 : CollatzResearch.WordTrace tailWord_1925140 prefixEnd_1925140 439343176531868050931755 := by
  unfold tailWord_1925140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35107812122777021290490437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46810416163702695053987249 35107812122777021290490437)
  ·
    refine ⟨6582714773020691491966957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35107812122777021290490437 6582714773020691491966957)
    ·
      refine ⟨2468518039882759309487609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6582714773020691491966957 2468518039882759309487609)
      ·
        refine ⟨1851388529912069482115707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2468518039882759309487609 1851388529912069482115707)
        ·
          refine ⟨2777082794868104223173561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851388529912069482115707 2777082794868104223173561)
          ·
            refine ⟨2082812096151078167380171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777082794868104223173561 2082812096151078167380171)
            ·
              refine ⟨3124218144226617251070257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082812096151078167380171 3124218144226617251070257)
              ·
                refine ⟨2343163608169962938302693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3124218144226617251070257 2343163608169962938302693)
                ·
                  refine ⟨439343176531868050931755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2343163608169962938302693 439343176531868050931755)
                  ·
                    rfl

theorem cell21_1925140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1925140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925140 prefixEnd_1925140 := by exact prefixLift 1925140
  have htrace : WordTrace (prefixWord ++ tailWord_1925140) baseStart_1925140 baseEnd_1925140 := by
    simpa [prefixWord, tailWord_1925140, baseEnd_1925140] using wordTrace_append hprefix tailTrace_1925140
  have hstable : (prefixWord ++ tailWord_1925140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925140).length < 2 ^ (prefixWord ++ tailWord_1925140).sum := by decide
  have hdescent : baseEnd_1925140 < baseStart_1925140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925269 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_1925269 : Nat := 118140960795 + 1925269 * 2 ^ 59
def prefixEnd_1925269 : Nat := 4983230072969 + 3 ^ 40 * 1925269 * 2
def baseEnd_1925269 : Nat := 439372616089392493281491

theorem tailTrace_1925269 : CollatzResearch.WordTrace tailWord_1925269 prefixEnd_1925269 439372616089392493281491 := by
  unfold tailWord_1925269
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220329262086697612426861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46813552841391131741617907 70220329262086697612426861)
  ·
    refine ⟨26332623473282511604660073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70220329262086697612426861 26332623473282511604660073)
    ·
      refine ⟨19749467604961883703495055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26332623473282511604660073 19749467604961883703495055)
      ·
        refine ⟨29624201407442825555242583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19749467604961883703495055 29624201407442825555242583)
        ·
          refine ⟨44436302111164238332863875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29624201407442825555242583 44436302111164238332863875)
          ·
            refine ⟨66654453166746357499295813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44436302111164238332863875 66654453166746357499295813)
            ·
              refine ⟨12497709968764942031117965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66654453166746357499295813 12497709968764942031117965)
              ·
                refine ⟨4686641238286853261669237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12497709968764942031117965 4686641238286853261669237)
                ·
                  refine ⟨439372616089392493281491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686641238286853261669237 439372616089392493281491)
                  ·
                    rfl

theorem cell21_1925269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_1925269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925269 prefixEnd_1925269 := by exact prefixLift 1925269
  have htrace : WordTrace (prefixWord ++ tailWord_1925269) baseStart_1925269 baseEnd_1925269 := by
    simpa [prefixWord, tailWord_1925269, baseEnd_1925269] using wordTrace_append hprefix tailTrace_1925269
  have hstable : (prefixWord ++ tailWord_1925269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925269).length < 2 ^ (prefixWord ++ tailWord_1925269).sum := by decide
  have hdescent : baseEnd_1925269 < baseStart_1925269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925272 : List Nat := [2, 1, 2, 4, 3, 2, 1, 6]
def baseStart_1925272 : Nat := 118140960795 + 1925272 * 2 ^ 59
def prefixEnd_1925272 : Nat := 4983230072969 + 3 ^ 40 * 1925272 * 2
def baseEnd_1925272 : Nat := 146457766910088384910495

theorem tailTrace_1925272 : CollatzResearch.WordTrace tailWord_1925272 prefixEnd_1925272 146457766910088384910495 := by
  unfold tailWord_1925272
  simp only [CollatzResearch.WordTrace]
  refine ⟨35110219340537914562393035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46813625787383886083190713 35110219340537914562393035)
  ·
    refine ⟨52665329010806871843589553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35110219340537914562393035 52665329010806871843589553)
    ·
      refine ⟨39498996758105153882692165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52665329010806871843589553 39498996758105153882692165)
      ·
        refine ⟨7406061892144716353004781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39498996758105153882692165 7406061892144716353004781)
        ·
          refine ⟨2777273209554268632376793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7406061892144716353004781 2777273209554268632376793)
          ·
            refine ⟨2082954907165701474282595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2777273209554268632376793 2082954907165701474282595)
            ·
              refine ⟨3124432360748552211423893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082954907165701474282595 3124432360748552211423893)
              ·
                refine ⟨146457766910088384910495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3124432360748552211423893 146457766910088384910495)
                ·
                  rfl

theorem cell21_1925272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_1925272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925272 prefixEnd_1925272 := by exact prefixLift 1925272
  have htrace : WordTrace (prefixWord ++ tailWord_1925272) baseStart_1925272 baseEnd_1925272 := by
    simpa [prefixWord, tailWord_1925272, baseEnd_1925272] using wordTrace_append hprefix tailTrace_1925272
  have hstable : (prefixWord ++ tailWord_1925272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925272).length < 2 ^ (prefixWord ++ tailWord_1925272).sum := by decide
  have hdescent : baseEnd_1925272 < baseStart_1925272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925283 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_1925283 : Nat := 118140960795 + 1925283 * 2 ^ 59
def prefixEnd_1925283 : Nat := 4983230072969 + 3 ^ 40 * 1925283 * 2
def baseEnd_1925283 : Nat := 439375811080131580048129

theorem tailTrace_1925283 : CollatzResearch.WordTrace tailWord_1925283 prefixEnd_1925283 439375811080131580048129 := by
  unfold tailWord_1925283
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220839884035978003436503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46813893256023985335624335 70220839884035978003436503)
  ·
    refine ⟨105331259826053967005154755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70220839884035978003436503 105331259826053967005154755)
    ·
      refine ⟨157996889739080950507732133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105331259826053967005154755 157996889739080950507732133)
      ·
        refine ⟨29624416826077678220199775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157996889739080950507732133 29624416826077678220199775)
        ·
          refine ⟨44436625239116517330299663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29624416826077678220199775 44436625239116517330299663)
          ·
            refine ⟨66654937858674775995449495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44436625239116517330299663 66654937858674775995449495)
            ·
              refine ⟨99982406788012163993174243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66654937858674775995449495 99982406788012163993174243)
              ·
                refine ⟨149973610182018245989761365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99982406788012163993174243 149973610182018245989761365)
                ·
                  refine ⟨439375811080131580048129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149973610182018245989761365 439375811080131580048129)
                  ·
                    rfl

theorem cell21_1925283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_1925283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925283 prefixEnd_1925283 := by exact prefixLift 1925283
  have htrace : WordTrace (prefixWord ++ tailWord_1925283) baseStart_1925283 baseEnd_1925283 := by
    simpa [prefixWord, tailWord_1925283, baseEnd_1925283] using wordTrace_append hprefix tailTrace_1925283
  have hstable : (prefixWord ++ tailWord_1925283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925283).length < 2 ^ (prefixWord ++ tailWord_1925283).sum := by decide
  have hdescent : baseEnd_1925283 < baseStart_1925283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925303 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 3]
def baseStart_1925303 : Nat := 118140960795 + 1925303 * 2 ^ 59
def prefixEnd_1925303 : Nat := 4983230072969 + 3 ^ 40 * 1925303 * 2
def baseEnd_1925303 : Nat := 439380375352615989714755

theorem tailTrace_1925303 : CollatzResearch.WordTrace tailWord_1925303 prefixEnd_1925303 439380375352615989714755 := by
  unfold tailWord_1925303
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221569343963521419164563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46814379562642347612776375 70221569343963521419164563)
  ·
    refine ⟨105332354015945282128746845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70221569343963521419164563 105332354015945282128746845)
    ·
      refine ⟨39499632755979480798280067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105332354015945282128746845 39499632755979480798280067)
      ·
        refine ⟨59249449133969221197420101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39499632755979480798280067 59249449133969221197420101)
        ·
          refine ⟨11109271712619228974516269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59249449133969221197420101 11109271712619228974516269)
          ·
            refine ⟨4165976892232210865443601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11109271712619228974516269 4165976892232210865443601)
            ·
              refine ⟨3124482669174158149082701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4165976892232210865443601 3124482669174158149082701)
              ·
                refine ⟨1171681000940309305906013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124482669174158149082701 1171681000940309305906013)
                ·
                  refine ⟨439380375352615989714755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171681000940309305906013 439380375352615989714755)
                  ·
                    rfl

theorem cell21_1925303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3].length) (baseStart_1925303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925303 prefixEnd_1925303 := by exact prefixLift 1925303
  have htrace : WordTrace (prefixWord ++ tailWord_1925303) baseStart_1925303 baseEnd_1925303 := by
    simpa [prefixWord, tailWord_1925303, baseEnd_1925303] using wordTrace_append hprefix tailTrace_1925303
  have hstable : (prefixWord ++ tailWord_1925303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925303).length < 2 ^ (prefixWord ++ tailWord_1925303).sum := by decide
  have hdescent : baseEnd_1925303 < baseStart_1925303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925345 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_1925345 : Nat := 118140960795 + 1925345 * 2 ^ 59
def prefixEnd_1925345 : Nat := 4983230072969 + 3 ^ 40 * 1925345 * 2
def baseEnd_1925345 : Nat := 439389960324833250014669

theorem tailTrace_1925345 : CollatzResearch.WordTrace tailWord_1925345 prefixEnd_1925345 439389960324833250014669 := by
  unfold tailWord_1925345
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223101209811362592193489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46815400806540908394795659 70223101209811362592193489)
  ·
    refine ⟨52667325907358521944145117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70223101209811362592193489 52667325907358521944145117)
    ·
      refine ⟨19750247215259445729054419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52667325907358521944145117 19750247215259445729054419)
      ·
        refine ⟨29625370822889168593581629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750247215259445729054419 29625370822889168593581629)
        ·
          refine ⟨11109514058583438222593111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29625370822889168593581629 11109514058583438222593111)
          ·
            refine ⟨16664271087875157333889667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109514058583438222593111 16664271087875157333889667)
            ·
              refine ⟨24996406631812736000834501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16664271087875157333889667 24996406631812736000834501)
              ·
                refine ⟨4686826243464888000156469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24996406631812736000834501 4686826243464888000156469)
                ·
                  refine ⟨439389960324833250014669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686826243464888000156469 439389960324833250014669)
                  ·
                    rfl

theorem cell21_1925345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_1925345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925345 prefixEnd_1925345 := by exact prefixLift 1925345
  have htrace : WordTrace (prefixWord ++ tailWord_1925345) baseStart_1925345 baseEnd_1925345 := by
    simpa [prefixWord, tailWord_1925345, baseEnd_1925345] using wordTrace_append hprefix tailTrace_1925345
  have hstable : (prefixWord ++ tailWord_1925345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925345).length < 2 ^ (prefixWord ++ tailWord_1925345).sum := by decide
  have hdescent : baseEnd_1925345 < baseStart_1925345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925379 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 3]
def baseStart_1925379 : Nat := 118140960795 + 1925379 * 2 ^ 59
def prefixEnd_1925379 : Nat := 4983230072969 + 3 ^ 40 * 1925379 * 2
def baseEnd_1925379 : Nat := 439397719588056746447933

theorem tailTrace_1925379 : CollatzResearch.WordTrace tailWord_1925379 prefixEnd_1925379 439397719588056746447933 := by
  unfold tailWord_1925379
  simp only [CollatzResearch.WordTrace]
  refine ⟨70224341291688186398931191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46816227527792124265954127 70224341291688186398931191)
  ·
    refine ⟨105336511937532279598396787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70224341291688186398931191 105336511937532279598396787)
    ·
      refine ⟨158004767906298419397595181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105336511937532279598396787 158004767906298419397595181)
      ·
        refine ⟨59251787964861907274098193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158004767906298419397595181 59251787964861907274098193)
        ·
          refine ⟨44438840973646430455573645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59251787964861907274098193 44438840973646430455573645)
          ·
            refine ⟨16664565365117411420840117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44438840973646430455573645 16664565365117411420840117)
            ·
              refine ⟨1562303002979757320703761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16664565365117411420840117 1562303002979757320703761)
              ·
                refine ⟨1171727252234817990527821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562303002979757320703761 1171727252234817990527821)
                ·
                  refine ⟨439397719588056746447933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171727252234817990527821 439397719588056746447933)
                  ·
                    rfl

theorem cell21_1925379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3].length) (baseStart_1925379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925379 prefixEnd_1925379 := by exact prefixLift 1925379
  have htrace : WordTrace (prefixWord ++ tailWord_1925379) baseStart_1925379 baseEnd_1925379 := by
    simpa [prefixWord, tailWord_1925379, baseEnd_1925379] using wordTrace_append hprefix tailTrace_1925379
  have hstable : (prefixWord ++ tailWord_1925379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925379).length < 2 ^ (prefixWord ++ tailWord_1925379).sum := by decide
  have hdescent : baseEnd_1925379 < baseStart_1925379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925393 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 4]
def baseStart_1925393 : Nat := 118140960795 + 1925393 * 2 ^ 59
def prefixEnd_1925393 : Nat := 4983230072969 + 3 ^ 40 * 1925393 * 2
def baseEnd_1925393 : Nat := 439400914578795833214571

theorem tailTrace_1925393 : CollatzResearch.WordTrace tailWord_1925393 prefixEnd_1925393 439400914578795833214571 := by
  unfold tailWord_1925393
  simp only [CollatzResearch.WordTrace]
  refine ⟨70224851913637466789940833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46816567942424977859960555 70224851913637466789940833)
  ·
    refine ⟨52668638935228100092455625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70224851913637466789940833 52668638935228100092455625)
    ·
      refine ⟨39501479201421075069341719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52668638935228100092455625 39501479201421075069341719)
      ·
        refine ⟨59252218802131612604012579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39501479201421075069341719 59252218802131612604012579)
        ·
          refine ⟨88878328203197418906018869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59252218802131612604012579 88878328203197418906018869)
          ·
            refine ⟨8332343269049758022439269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88878328203197418906018869 8332343269049758022439269)
            ·
              refine ⟨1562314362946829629207363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8332343269049758022439269 1562314362946829629207363)
              ·
                refine ⟨2343471544420244443811045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562314362946829629207363 2343471544420244443811045)
                ·
                  refine ⟨439400914578795833214571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2343471544420244443811045 439400914578795833214571)
                  ·
                    rfl

theorem cell21_1925393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_1925393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925393 prefixEnd_1925393 := by exact prefixLift 1925393
  have htrace : WordTrace (prefixWord ++ tailWord_1925393) baseStart_1925393 baseEnd_1925393 := by
    simpa [prefixWord, tailWord_1925393, baseEnd_1925393] using wordTrace_append hprefix tailTrace_1925393
  have hstable : (prefixWord ++ tailWord_1925393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925393).length < 2 ^ (prefixWord ++ tailWord_1925393).sum := by decide
  have hdescent : baseEnd_1925393 < baseStart_1925393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925441 : List Nat := [1, 2, 5, 2, 3, 1, 1, 6]
def baseStart_1925441 : Nat := 118140960795 + 1925441 * 2 ^ 59
def prefixEnd_1925441 : Nat := 4983230072969 + 3 ^ 40 * 1925441 * 2
def baseEnd_1925441 : Nat := 146470622944252805471491

theorem tailTrace_1925441 : CollatzResearch.WordTrace tailWord_1925441 prefixEnd_1925441 146470622944252805471491 := by
  unfold tailWord_1925441
  simp only [CollatzResearch.WordTrace]
  refine ⟨70226602617463570987688177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46817735078309047325125451 70226602617463570987688177)
  ·
    refine ⟨52669951963097678240766133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70226602617463570987688177 52669951963097678240766133)
    ·
      refine ⟨4937807996540407335071825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52669951963097678240766133 4937807996540407335071825)
      ·
        refine ⟨3703355997405305501303869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4937807996540407335071825 3703355997405305501303869)
        ·
          refine ⟨1388758499026989562988951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3703355997405305501303869 1388758499026989562988951)
          ·
            refine ⟨2083137748540484344483427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388758499026989562988951 2083137748540484344483427)
            ·
              refine ⟨3124706622810726516725141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083137748540484344483427 3124706622810726516725141)
              ·
                refine ⟨146470622944252805471491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3124706622810726516725141 146470622944252805471491)
                ·
                  rfl

theorem cell21_1925441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 6].length) (baseStart_1925441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925441 prefixEnd_1925441 := by exact prefixLift 1925441
  have htrace : WordTrace (prefixWord ++ tailWord_1925441) baseStart_1925441 baseEnd_1925441 := by
    simpa [prefixWord, tailWord_1925441, baseEnd_1925441] using wordTrace_append hprefix tailTrace_1925441
  have hstable : (prefixWord ++ tailWord_1925441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925441).length < 2 ^ (prefixWord ++ tailWord_1925441).sum := by decide
  have hdescent : baseEnd_1925441 < baseStart_1925441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925452 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_1925452 : Nat := 118140960795 + 1925452 * 2 ^ 59
def prefixEnd_1925452 : Nat := 4983230072969 + 3 ^ 40 * 1925452 * 2
def baseEnd_1925452 : Nat := 439414379182624841731117

theorem tailTrace_1925452 : CollatzResearch.WordTrace tailWord_1925452 prefixEnd_1925452 439414379182624841731117 := by
  unfold tailWord_1925452
  simp only [CollatzResearch.WordTrace]
  refine ⟨35113501910211859933169305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46818002546949146577559073 35113501910211859933169305)
  ·
    refine ⟨26335126432658894949876979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35113501910211859933169305 26335126432658894949876979)
    ·
      refine ⟨39502689648988342424815469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26335126432658894949876979 39502689648988342424815469)
      ·
        refine ⟨14813508618370628409305801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39502689648988342424815469 14813508618370628409305801)
        ·
          refine ⟨11110131463777971306979351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14813508618370628409305801 11110131463777971306979351)
          ·
            refine ⟨16665197195666956960469027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110131463777971306979351 16665197195666956960469027)
            ·
              refine ⟨24997795793500435440703541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665197195666956960469027 24997795793500435440703541)
              ·
                refine ⟨2343543355640665822565957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24997795793500435440703541 2343543355640665822565957)
                ·
                  refine ⟨439414379182624841731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2343543355640665822565957 439414379182624841731117)
                  ·
                    rfl

theorem cell21_1925452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_1925452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925452 prefixEnd_1925452 := by exact prefixLift 1925452
  have htrace : WordTrace (prefixWord ++ tailWord_1925452) baseStart_1925452 baseEnd_1925452 := by
    simpa [prefixWord, tailWord_1925452, baseEnd_1925452] using wordTrace_append hprefix tailTrace_1925452
  have hstable : (prefixWord ++ tailWord_1925452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925452).length < 2 ^ (prefixWord ++ tailWord_1925452).sum := by decide
  have hdescent : baseEnd_1925452 < baseStart_1925452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925528 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_1925528 : Nat := 118140960795 + 1925528 * 2 ^ 59
def prefixEnd_1925528 : Nat := 4983230072969 + 3 ^ 40 * 1925528 * 2
def baseEnd_1925528 : Nat := 439431723418065598464295

theorem tailTrace_1925528 : CollatzResearch.WordTrace tailWord_1925528 prefixEnd_1925528 439431723418065598464295 := by
  unfold tailWord_1925528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35114887884074192423052619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46819850512098923230736825 35114887884074192423052619)
  ·
    refine ⟨52672331826111288634578929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35114887884074192423052619 52672331826111288634578929)
    ·
      refine ⟨39504248869583466475934197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52672331826111288634578929 39504248869583466475934197)
      ·
        refine ⟨3703523331523449982118831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39504248869583466475934197 3703523331523449982118831)
        ·
          refine ⟨5555284997285174973178247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703523331523449982118831 5555284997285174973178247)
          ·
            refine ⟨8332927495927762459767371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555284997285174973178247 8332927495927762459767371)
            ·
              refine ⟨12499391243891643689651057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332927495927762459767371 12499391243891643689651057)
              ·
                refine ⟨9374543432918732767238293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499391243891643689651057 9374543432918732767238293)
                ·
                  refine ⟨439431723418065598464295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9374543432918732767238293 439431723418065598464295)
                  ·
                    rfl

theorem cell21_1925528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_1925528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925528 prefixEnd_1925528 := by exact prefixLift 1925528
  have htrace : WordTrace (prefixWord ++ tailWord_1925528) baseStart_1925528 baseEnd_1925528 := by
    simpa [prefixWord, tailWord_1925528, baseEnd_1925528] using wordTrace_append hprefix tailTrace_1925528
  have hstable : (prefixWord ++ tailWord_1925528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925528).length < 2 ^ (prefixWord ++ tailWord_1925528).sum := by decide
  have hdescent : baseEnd_1925528 < baseStart_1925528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925655 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 4]
def baseStart_1925655 : Nat := 118140960795 + 1925655 * 2 ^ 59
def prefixEnd_1925655 : Nat := 4983230072969 + 3 ^ 40 * 1925655 * 2
def baseEnd_1925655 : Nat := 439460706548341599847369

theorem tailTrace_1925655 : CollatzResearch.WordTrace tailWord_1925655 prefixEnd_1925655 439460706548341599847369 := by
  unfold tailWord_1925655
  simp only [CollatzResearch.WordTrace]
  refine ⟨70234407838688285535978419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46822938559125523690652279 70234407838688285535978419)
  ·
    refine ⟨105351611758032428303967629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70234407838688285535978419 105351611758032428303967629)
    ·
      refine ⟨39506854409262160613987861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105351611758032428303967629 39506854409262160613987861)
      ·
        refine ⟨1851883800434163778780681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39506854409262160613987861 1851883800434163778780681)
        ·
          refine ⟨1388912850325622834085511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851883800434163778780681 1388912850325622834085511)
          ·
            refine ⟨2083369275488434251128267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388912850325622834085511 2083369275488434251128267)
            ·
              refine ⟨3125053913232651376692401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083369275488434251128267 3125053913232651376692401)
              ·
                refine ⟨2343790434924488532519301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125053913232651376692401 2343790434924488532519301)
                ·
                  refine ⟨439460706548341599847369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2343790434924488532519301 439460706548341599847369)
                  ·
                    rfl

theorem cell21_1925655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4].length) (baseStart_1925655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925655 prefixEnd_1925655 := by exact prefixLift 1925655
  have htrace : WordTrace (prefixWord ++ tailWord_1925655) baseStart_1925655 baseEnd_1925655 := by
    simpa [prefixWord, tailWord_1925655, baseEnd_1925655] using wordTrace_append hprefix tailTrace_1925655
  have hstable : (prefixWord ++ tailWord_1925655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925655).length < 2 ^ (prefixWord ++ tailWord_1925655).sum := by decide
  have hdescent : baseEnd_1925655 < baseStart_1925655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925770 : List Nat := [3, 1, 2, 3, 3, 9]
def baseStart_1925770 : Nat := 118140960795 + 1925770 * 2 ^ 59
def prefixEnd_1925770 : Nat := 4983230072969 + 3 ^ 40 * 1925770 * 2
def baseEnd_1925770 : Nat := 16277294485745442793721

theorem tailTrace_1925770 : CollatzResearch.WordTrace tailWord_1925770 prefixEnd_1925770 16277294485745442793721 := by
  unfold tailWord_1925770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17559650558317915044103691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46825734822181106784276509 17559650558317915044103691)
  ·
    refine ⟨26339475837476872566155537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17559650558317915044103691 26339475837476872566155537)
    ·
      refine ⟨19754606878107654424616653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26339475837476872566155537 19754606878107654424616653)
      ·
        refine ⟨7407977579290370409231245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19754606878107654424616653 7407977579290370409231245)
        ·
          refine ⟨2777991592233888903461717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7407977579290370409231245 2777991592233888903461717)
          ·
            refine ⟨16277294485745442793721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2777991592233888903461717 16277294485745442793721)
            ·
              rfl

theorem cell21_1925770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 9].length) (baseStart_1925770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925770 prefixEnd_1925770 := by exact prefixLift 1925770
  have htrace : WordTrace (prefixWord ++ tailWord_1925770) baseStart_1925770 baseEnd_1925770 := by
    simpa [prefixWord, tailWord_1925770, baseEnd_1925770] using wordTrace_append hprefix tailTrace_1925770
  have hstable : (prefixWord ++ tailWord_1925770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925770).length < 2 ^ (prefixWord ++ tailWord_1925770).sum := by decide
  have hdescent : baseEnd_1925770 < baseStart_1925770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925818 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_1925818 : Nat := 118140960795 + 1925818 * 2 ^ 59
def prefixEnd_1925818 : Nat := 4983230072969 + 3 ^ 40 * 1925818 * 2
def baseEnd_1925818 : Nat := 439497905369089538630369

theorem tailTrace_1925818 : CollatzResearch.WordTrace tailWord_1925818 prefixEnd_1925818 439497905369089538630369 := by
  unfold tailWord_1925818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560088234274441093540527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46826901958065176249441405 17560088234274441093540527)
  ·
    refine ⟨26340132351411661640310791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17560088234274441093540527 26340132351411661640310791)
    ·
      refine ⟨39510198527117492460466187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26340132351411661640310791 39510198527117492460466187)
      ·
        refine ⟨59265297790676238690699281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510198527117492460466187 59265297790676238690699281)
        ·
          refine ⟨44448973343007179018024461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59265297790676238690699281 44448973343007179018024461)
          ·
            refine ⟨16668365003627692131759173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44448973343007179018024461 16668365003627692131759173)
            ·
              refine ⟨3125318438180192274704845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16668365003627692131759173 3125318438180192274704845)
              ·
                refine ⟨1171994414317572103014317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125318438180192274704845 1171994414317572103014317)
                ·
                  refine ⟨439497905369089538630369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171994414317572103014317 439497905369089538630369)
                  ·
                    rfl

theorem cell21_1925818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_1925818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925818 prefixEnd_1925818 := by exact prefixLift 1925818
  have htrace : WordTrace (prefixWord ++ tailWord_1925818) baseStart_1925818 baseEnd_1925818 := by
    simpa [prefixWord, tailWord_1925818, baseEnd_1925818] using wordTrace_append hprefix tailTrace_1925818
  have hstable : (prefixWord ++ tailWord_1925818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925818).length < 2 ^ (prefixWord ++ tailWord_1925818).sum := by decide
  have hdescent : baseEnd_1925818 < baseStart_1925818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925832 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_1925832 : Nat := 118140960795 + 1925832 * 2 ^ 59
def prefixEnd_1925832 : Nat := 4983230072969 + 3 ^ 40 * 1925832 * 2
def baseEnd_1925832 : Nat := 439501100359828625397007

theorem tailTrace_1925832 : CollatzResearch.WordTrace tailWord_1925832 prefixEnd_1925832 439501100359828625397007 := by
  unfold tailWord_1925832
  simp only [CollatzResearch.WordTrace]
  refine ⟨35120431779523522382585875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46827242372698029843447833 35120431779523522382585875)
  ·
    refine ⟨52680647669285283573878813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35120431779523522382585875 52680647669285283573878813)
    ·
      refine ⟨19755242875981981340204555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52680647669285283573878813 19755242875981981340204555)
      ·
        refine ⟨29632864313972972010306833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19755242875981981340204555 29632864313972972010306833)
        ·
          refine ⟨22224648235479729007730125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29632864313972972010306833 22224648235479729007730125)
          ·
            refine ⟨8334243088304898377898797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22224648235479729007730125 8334243088304898377898797)
            ·
              refine ⟨3125341158114336891712049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8334243088304898377898797 3125341158114336891712049)
              ·
                refine ⟨2344005868585752668784037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125341158114336891712049 2344005868585752668784037)
                ·
                  refine ⟨439501100359828625397007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344005868585752668784037 439501100359828625397007)
                  ·
                    rfl

theorem cell21_1925832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_1925832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925832 prefixEnd_1925832 := by exact prefixLift 1925832
  have htrace : WordTrace (prefixWord ++ tailWord_1925832) baseStart_1925832 baseEnd_1925832 := by
    simpa [prefixWord, tailWord_1925832, baseEnd_1925832] using wordTrace_append hprefix tailTrace_1925832
  have hstable : (prefixWord ++ tailWord_1925832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925832).length < 2 ^ (prefixWord ++ tailWord_1925832).sum := by decide
  have hdescent : baseEnd_1925832 < baseStart_1925832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925891 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_1925891 : Nat := 118140960795 + 1925891 * 2 ^ 59
def prefixEnd_1925891 : Nat := 4983230072969 + 3 ^ 40 * 1925891 * 2
def baseEnd_1925891 : Nat := 439514564963657633913553

theorem tailTrace_1925891 : CollatzResearch.WordTrace tailWord_1925891 prefixEnd_1925891 439514564963657633913553 := by
  unfold tailWord_1925891
  simp only [CollatzResearch.WordTrace]
  refine ⟨70243015465833297841569527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46828676977222198561046351 70243015465833297841569527)
  ·
    refine ⟨105364523198749946762354291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70243015465833297841569527 105364523198749946762354291)
    ·
      refine ⟨158046784798124920143531437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105364523198749946762354291 158046784798124920143531437)
      ·
        refine ⟨59267544299296845053824289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158046784798124920143531437 59267544299296845053824289)
        ·
          refine ⟨44450658224472633790368217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59267544299296845053824289 44450658224472633790368217)
          ·
            refine ⟨33337993668354475342776163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44450658224472633790368217 33337993668354475342776163)
            ·
              refine ⟨50006990502531713014164245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33337993668354475342776163 50006990502531713014164245)
              ·
                refine ⟨2344077679806174047538949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50006990502531713014164245 2344077679806174047538949)
                ·
                  refine ⟨439514564963657633913553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344077679806174047538949 439514564963657633913553)
                  ·
                    rfl

theorem cell21_1925891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_1925891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925891 prefixEnd_1925891 := by exact prefixLift 1925891
  have htrace : WordTrace (prefixWord ++ tailWord_1925891) baseStart_1925891 baseEnd_1925891 := by
    simpa [prefixWord, tailWord_1925891, baseEnd_1925891] using wordTrace_append hprefix tailTrace_1925891
  have hstable : (prefixWord ++ tailWord_1925891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925891).length < 2 ^ (prefixWord ++ tailWord_1925891).sum := by decide
  have hdescent : baseEnd_1925891 < baseStart_1925891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925905 : List Nat := [1, 2, 2, 1, 1, 3, 3, 8]
def baseStart_1925905 : Nat := 118140960795 + 1925905 * 2 ^ 59
def prefixEnd_1925905 : Nat := 4983230072969 + 3 ^ 40 * 1925905 * 2
def baseEnd_1925905 : Nat := 146505919984798906893397

theorem tailTrace_1925905 : CollatzResearch.WordTrace tailWord_1925905 prefixEnd_1925905 146505919984798906893397 := by
  unfold tailWord_1925905
  simp only [CollatzResearch.WordTrace]
  refine ⟨70243526087782578232579169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46829017391855052155052779 70243526087782578232579169)
  ·
    refine ⟨52682644565836933674434377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70243526087782578232579169 52682644565836933674434377)
    ·
      refine ⟨39511983424377700255825783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52682644565836933674434377 39511983424377700255825783)
      ·
        refine ⟨59267975136566550383738675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39511983424377700255825783 59267975136566550383738675)
        ·
          refine ⟨88901962704849825575608013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59267975136566550383738675 88901962704849825575608013)
          ·
            refine ⟨33338236014318684590853005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88901962704849825575608013 33338236014318684590853005)
            ·
              refine ⟨12501838505369506721569877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33338236014318684590853005 12501838505369506721569877)
              ·
                refine ⟨146505919984798906893397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12501838505369506721569877 146505919984798906893397)
                ·
                  rfl

theorem cell21_1925905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_1925905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925905 prefixEnd_1925905 := by exact prefixLift 1925905
  have htrace : WordTrace (prefixWord ++ tailWord_1925905) baseStart_1925905 baseEnd_1925905 := by
    simpa [prefixWord, tailWord_1925905, baseEnd_1925905] using wordTrace_append hprefix tailTrace_1925905
  have hstable : (prefixWord ++ tailWord_1925905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925905).length < 2 ^ (prefixWord ++ tailWord_1925905).sum := by decide
  have hdescent : baseEnd_1925905 < baseStart_1925905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925922 : List Nat := [3, 3, 1, 1, 2, 2, 2, 7]
def baseStart_1925922 : Nat := 118140960795 + 1925922 * 2 ^ 59
def prefixEnd_1925922 : Nat := 4983230072969 + 3 ^ 40 * 1925922 * 2
def baseEnd_1925922 : Nat := 146507213195336156298941

theorem tailTrace_1925922 : CollatzResearch.WordTrace tailWord_1925922 prefixEnd_1925922 146507213195336156298941 := by
  unfold tailWord_1925922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561036532180247533987005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46829430752480660090632013 17561036532180247533987005)
  ·
    refine ⟨6585388699567592825245127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17561036532180247533987005 6585388699567592825245127)
    ·
      refine ⟨9878083049351389237867691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585388699567592825245127 9878083049351389237867691)
      ·
        refine ⟨14817124574027083856801537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878083049351389237867691 14817124574027083856801537)
        ·
          refine ⟨11112843430520312892601153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14817124574027083856801537 11112843430520312892601153)
          ·
            refine ⟨8334632572890234669450865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11112843430520312892601153 8334632572890234669450865)
            ·
              refine ⟨6250974429667676002088149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334632572890234669450865 6250974429667676002088149)
              ·
                refine ⟨146507213195336156298941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6250974429667676002088149 146507213195336156298941)
                ·
                  rfl

theorem cell21_1925922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_1925922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925922 prefixEnd_1925922 := by exact prefixLift 1925922
  have htrace : WordTrace (prefixWord ++ tailWord_1925922) baseStart_1925922 baseEnd_1925922 := by
    simpa [prefixWord, tailWord_1925922, baseEnd_1925922] using wordTrace_append hprefix tailTrace_1925922
  have hstable : (prefixWord ++ tailWord_1925922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925922).length < 2 ^ (prefixWord ++ tailWord_1925922).sum := by decide
  have hdescent : baseEnd_1925922 < baseStart_1925922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1925942 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1925942 : Nat := 118140960795 + 1925942 * 2 ^ 59
def prefixEnd_1925942 : Nat := 4983230072969 + 3 ^ 40 * 1925942 * 2
def baseEnd_1925942 : Nat := 439526203858492878563449

theorem tailTrace_1925942 : CollatzResearch.WordTrace tailWord_1925942 prefixEnd_1925942 439526203858492878563449 := by
  unfold tailWord_1925942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390304724290533346979755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46829917059099022367784053 4390304724290533346979755)
  ·
    refine ⟨6585457086435800020469633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390304724290533346979755 6585457086435800020469633)
    ·
      refine ⟨4939092814826850015352225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585457086435800020469633 4939092814826850015352225)
      ·
        refine ⟨3704319611120137511514169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4939092814826850015352225 3704319611120137511514169)
        ·
          refine ⟨2778239708340103133635627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3704319611120137511514169 2778239708340103133635627)
          ·
            refine ⟨4167359562510154700453441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778239708340103133635627 4167359562510154700453441)
            ·
              refine ⟨3125519671882616025340081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167359562510154700453441 3125519671882616025340081)
              ·
                refine ⟨2344139753911962019005061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125519671882616025340081 2344139753911962019005061)
                ·
                  refine ⟨439526203858492878563449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344139753911962019005061 439526203858492878563449)
                  ·
                    rfl

theorem cell21_1925942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1925942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1925942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1925942 prefixEnd_1925942 := by exact prefixLift 1925942
  have htrace : WordTrace (prefixWord ++ tailWord_1925942) baseStart_1925942 baseEnd_1925942 := by
    simpa [prefixWord, tailWord_1925942, baseEnd_1925942] using wordTrace_append hprefix tailTrace_1925942
  have hstable : (prefixWord ++ tailWord_1925942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1925942).length < 2 ^ (prefixWord ++ tailWord_1925942).sum := by decide
  have hdescent : baseEnd_1925942 < baseStart_1925942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1925942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926122 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1926122 : Nat := 118140960795 + 1926122 * 2 ^ 59
def prefixEnd_1926122 : Nat := 4983230072969 + 3 ^ 40 * 1926122 * 2
def baseEnd_1926122 : Nat := 439567282310852565563081

theorem tailTrace_1926122 : CollatzResearch.WordTrace tailWord_1926122 prefixEnd_1926122 439567282310852565563081 := by
  unfold tailWord_1926122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562860181999106073307155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46834293818664282862152413 17562860181999106073307155)
  ·
    refine ⟨26344290272998659109960733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17562860181999106073307155 26344290272998659109960733)
    ·
      refine ⟨9879108852374497166235275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26344290272998659109960733 9879108852374497166235275)
      ·
        refine ⟨14818663278561745749352913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879108852374497166235275 14818663278561745749352913)
        ·
          refine ⟨11113997458921309312014685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14818663278561745749352913 11113997458921309312014685)
          ·
            refine ⟨4167749047095490992005507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11113997458921309312014685 4167749047095490992005507)
            ·
              refine ⟨6251623570643236488008261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167749047095490992005507 6251623570643236488008261)
              ·
                refine ⟨1172179419495606841501549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6251623570643236488008261 1172179419495606841501549)
                ·
                  refine ⟨439567282310852565563081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172179419495606841501549 439567282310852565563081)
                  ·
                    rfl

theorem cell21_1926122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1926122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926122 prefixEnd_1926122 := by exact prefixLift 1926122
  have htrace : WordTrace (prefixWord ++ tailWord_1926122) baseStart_1926122 baseEnd_1926122 := by
    simpa [prefixWord, tailWord_1926122, baseEnd_1926122] using wordTrace_append hprefix tailTrace_1926122
  have hstable : (prefixWord ++ tailWord_1926122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926122).length < 2 ^ (prefixWord ++ tailWord_1926122).sum := by decide
  have hdescent : baseEnd_1926122 < baseStart_1926122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926181 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 3]
def baseStart_1926181 : Nat := 118140960795 + 1926181 * 2 ^ 59
def prefixEnd_1926181 : Nat := 4983230072969 + 3 ^ 40 * 1926181 * 2
def baseEnd_1926181 : Nat := 439580746914681574079627

theorem tailTrace_1926181 : CollatzResearch.WordTrace tailWord_1926181 prefixEnd_1926181 439580746914681574079627 := by
  unfold tailWord_1926181
  simp only [CollatzResearch.WordTrace]
  refine ⟨70253592634782677369626397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46835728423188451579750931 70253592634782677369626397)
  ·
    refine ⟨26345097238043504013609899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70253592634782677369626397 26345097238043504013609899)
    ·
      refine ⟨39517645857065256020414849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26345097238043504013609899 39517645857065256020414849)
      ·
        refine ⟨29638234392798942015311137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39517645857065256020414849 29638234392798942015311137)
        ·
          refine ⟨22228675794599206511483353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29638234392798942015311137 22228675794599206511483353)
          ·
            refine ⟨16671506845949404883612515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22228675794599206511483353 16671506845949404883612515)
            ·
              refine ⟨25007260268924107325418773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16671506845949404883612515 25007260268924107325418773)
              ·
                refine ⟨1172215325105817530879005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25007260268924107325418773 1172215325105817530879005)
                ·
                  refine ⟨439580746914681574079627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172215325105817530879005 439580746914681574079627)
                  ·
                    rfl

theorem cell21_1926181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_1926181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926181 prefixEnd_1926181 := by exact prefixLift 1926181
  have htrace : WordTrace (prefixWord ++ tailWord_1926181) baseStart_1926181 baseEnd_1926181 := by
    simpa [prefixWord, tailWord_1926181, baseEnd_1926181] using wordTrace_append hprefix tailTrace_1926181
  have hstable : (prefixWord ++ tailWord_1926181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926181).length < 2 ^ (prefixWord ++ tailWord_1926181).sum := by decide
  have hdescent : baseEnd_1926181 < baseStart_1926181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926226 : List Nat := [3, 2, 2, 1, 3, 3, 7]
def baseStart_1926226 : Nat := 118140960795 + 1926226 * 2 ^ 59
def prefixEnd_1926226 : Nat := 4983230072969 + 3 ^ 40 * 1926226 * 2
def baseEnd_1926226 : Nat := 48843446280863499536615

theorem tailTrace_1926226 : CollatzResearch.WordTrace tailWord_1926226 prefixEnd_1926226 48843446280863499536615 := by
  unfold tailWord_1926226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563808479904912513753633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46836822613079766703343021 17563808479904912513753633)
  ·
    refine ⟨13172856359928684385315225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17563808479904912513753633 13172856359928684385315225)
    ·
      refine ⟨9879642269946513288986419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13172856359928684385315225 9879642269946513288986419)
      ·
        refine ⟨14819463404919769933479629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879642269946513288986419 14819463404919769933479629)
        ·
          refine ⟨5557298776844913725054861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14819463404919769933479629 5557298776844913725054861)
          ·
            refine ⟨2083987041316842646895573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5557298776844913725054861 2083987041316842646895573)
            ·
              refine ⟨48843446280863499536615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2083987041316842646895573 48843446280863499536615)
              ·
                rfl

theorem cell21_1926226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 7].length) (baseStart_1926226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926226 prefixEnd_1926226 := by exact prefixLift 1926226
  have htrace : WordTrace (prefixWord ++ tailWord_1926226) baseStart_1926226 baseEnd_1926226 := by
    simpa [prefixWord, tailWord_1926226, baseEnd_1926226] using wordTrace_append hprefix tailTrace_1926226
  have hstable : (prefixWord ++ tailWord_1926226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926226).length < 2 ^ (prefixWord ++ tailWord_1926226).sum := by decide
  have hdescent : baseEnd_1926226 < baseStart_1926226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926330 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1926330 : Nat := 118140960795 + 1926330 * 2 ^ 59
def prefixEnd_1926330 : Nat := 4983230072969 + 3 ^ 40 * 1926330 * 2
def baseEnd_1926330 : Nat := 439614750744690426095989

theorem tailTrace_1926330 : CollatzResearch.WordTrace tailWord_1926330 prefixEnd_1926330 439614750744690426095989 := by
  unfold tailWord_1926330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564756777810718954200111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46839351407495250544533629 17564756777810718954200111)
  ·
    refine ⟨26347135166716078431300167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564756777810718954200111 26347135166716078431300167)
    ·
      refine ⟨39520702750074117646950251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26347135166716078431300167 39520702750074117646950251)
      ·
        refine ⟨59281054125111176470425377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39520702750074117646950251 59281054125111176470425377)
        ·
          refine ⟨44460790593833382352819033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59281054125111176470425377 44460790593833382352819033)
          ·
            refine ⟨33345592945375036764614275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44460790593833382352819033 33345592945375036764614275)
            ·
              refine ⟨50018389418062555146921413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33345592945375036764614275 50018389418062555146921413)
              ·
                refine ⟨9378448015886729090047765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50018389418062555146921413 9378448015886729090047765)
                ·
                  refine ⟨439614750744690426095989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9378448015886729090047765 439614750744690426095989)
                  ·
                    rfl

theorem cell21_1926330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1926330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926330 prefixEnd_1926330 := by exact prefixLift 1926330
  have htrace : WordTrace (prefixWord ++ tailWord_1926330) baseStart_1926330 baseEnd_1926330 := by
    simpa [prefixWord, tailWord_1926330, baseEnd_1926330] using wordTrace_append hprefix tailTrace_1926330
  have hstable : (prefixWord ++ tailWord_1926330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926330).length < 2 ^ (prefixWord ++ tailWord_1926330).sum := by decide
  have hdescent : baseEnd_1926330 < baseStart_1926330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926333 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 3]
def baseStart_1926333 : Nat := 118140960795 + 1926333 * 2 ^ 59
def prefixEnd_1926333 : Nat := 4983230072969 + 3 ^ 40 * 1926333 * 2
def baseEnd_1926333 : Nat := 439615435385563087545983

theorem tailTrace_1926333 : CollatzResearch.WordTrace tailWord_1926333 prefixEnd_1926333 439615435385563087545983 := by
  unfold tailWord_1926333
  simp only [CollatzResearch.WordTrace]
  refine ⟨70259136530232007329159653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46839424353488004886106435 70259136530232007329159653)
  ·
    refine ⟨13173588099418501374217435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70259136530232007329159653 13173588099418501374217435)
    ·
      refine ⟨19760382149127752061326153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13173588099418501374217435 19760382149127752061326153)
      ·
        refine ⟨14820286611845814045994615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19760382149127752061326153 14820286611845814045994615)
        ·
          refine ⟨22230429917768721068991923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820286611845814045994615 22230429917768721068991923)
          ·
            refine ⟨33345644876653081603487885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22230429917768721068991923 33345644876653081603487885)
            ·
              refine ⟨12504616828744905601307957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33345644876653081603487885 12504616828744905601307957)
              ·
                refine ⟨1172307827694834900122621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12504616828744905601307957 1172307827694834900122621)
                ·
                  refine ⟨439615435385563087545983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172307827694834900122621 439615435385563087545983)
                  ·
                    rfl

theorem cell21_1926333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_1926333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926333 prefixEnd_1926333 := by exact prefixLift 1926333
  have htrace : WordTrace (prefixWord ++ tailWord_1926333) baseStart_1926333 baseEnd_1926333 := by
    simpa [prefixWord, tailWord_1926333, baseEnd_1926333] using wordTrace_append hprefix tailTrace_1926333
  have hstable : (prefixWord ++ tailWord_1926333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926333).length < 2 ^ (prefixWord ++ tailWord_1926333).sum := by decide
  have hdescent : baseEnd_1926333 < baseStart_1926333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926378 : List Nat := [3, 1, 3, 1, 1, 3, 4, 5]
def baseStart_1926378 : Nat := 118140960795 + 1926378 * 2 ^ 59
def prefixEnd_1926378 : Nat := 4983230072969 + 3 ^ 40 * 1926378 * 2
def baseEnd_1926378 : Nat := 146541901666217669765297

theorem tailTrace_1926378 : CollatzResearch.WordTrace tailWord_1926378 prefixEnd_1926378 146541901666217669765297 := by
  unfold tailWord_1926378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565194453767245003636947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46840518543379320009698525 17565194453767245003636947)
  ·
    refine ⟨26347791680650867505455421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565194453767245003636947 26347791680650867505455421)
    ·
      refine ⟨9880421880244075314545783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26347791680650867505455421 9880421880244075314545783)
      ·
        refine ⟨14820632820366112971818675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880421880244075314545783 14820632820366112971818675)
        ·
          refine ⟨22230949230549169457728013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820632820366112971818675 22230949230549169457728013)
          ·
            refine ⟨8336605961455938546648005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22230949230549169457728013 8336605961455938546648005)
            ·
              refine ⟨1563113617772988477496501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8336605961455938546648005 1563113617772988477496501)
              ·
                refine ⟨146541901666217669765297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563113617772988477496501 146541901666217669765297)
                ·
                  rfl

theorem cell21_1926378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_1926378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926378 prefixEnd_1926378 := by exact prefixLift 1926378
  have htrace : WordTrace (prefixWord ++ tailWord_1926378) baseStart_1926378 baseEnd_1926378 := by
    simpa [prefixWord, tailWord_1926378, baseEnd_1926378] using wordTrace_append hprefix tailTrace_1926378
  have hstable : (prefixWord ++ tailWord_1926378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926378).length < 2 ^ (prefixWord ++ tailWord_1926378).sum := by decide
  have hdescent : baseEnd_1926378 < baseStart_1926378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926423 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_1926423 : Nat := 118140960795 + 1926423 * 2 ^ 59
def prefixEnd_1926423 : Nat := 4983230072969 + 3 ^ 40 * 1926423 * 2
def baseEnd_1926423 : Nat := 439635974611742931045799

theorem tailTrace_1926423 : CollatzResearch.WordTrace tailWord_1926423 prefixEnd_1926423 439635974611742931045799 := by
  unfold tailWord_1926423
  simp only [CollatzResearch.WordTrace]
  refine ⟨70262419099905952699935923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46841612733270635133290615 70262419099905952699935923)
  ·
    refine ⟨105393628649858929049903885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70262419099905952699935923 105393628649858929049903885)
    ·
      refine ⟨39522610743697098393713957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105393628649858929049903885 39522610743697098393713957)
      ·
        refine ⟨7410489514443205948821367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39522610743697098393713957 7410489514443205948821367)
        ·
          refine ⟨11115734271664808923232051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410489514443205948821367 11115734271664808923232051)
          ·
            refine ⟨16673601407497213384848077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115734271664808923232051 16673601407497213384848077)
            ·
              refine ⟨6252600527811455019318029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16673601407497213384848077 6252600527811455019318029)
              ·
                refine ⟨2344725197929295632244261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252600527811455019318029 2344725197929295632244261)
                ·
                  refine ⟨439635974611742931045799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344725197929295632244261 439635974611742931045799)
                  ·
                    rfl

theorem cell21_1926423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_1926423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926423 prefixEnd_1926423 := by exact prefixLift 1926423
  have htrace : WordTrace (prefixWord ++ tailWord_1926423) baseStart_1926423 baseEnd_1926423 := by
    simpa [prefixWord, tailWord_1926423, baseEnd_1926423] using wordTrace_append hprefix tailTrace_1926423
  have hstable : (prefixWord ++ tailWord_1926423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926423).length < 2 ^ (prefixWord ++ tailWord_1926423).sum := by decide
  have hdescent : baseEnd_1926423 < baseStart_1926423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926437 : List Nat := [1, 3, 1, 2, 4, 1, 2, 7]
def baseStart_1926437 : Nat := 118140960795 + 1926437 * 2 ^ 59
def prefixEnd_1926437 : Nat := 4983230072969 + 3 ^ 40 * 1926437 * 2
def baseEnd_1926437 : Nat := 146546389867494005937479

theorem tailTrace_1926437 : CollatzResearch.WordTrace tailWord_1926437 prefixEnd_1926437 146546389867494005937479 := by
  unfold tailWord_1926437
  simp only [CollatzResearch.WordTrace]
  refine ⟨70262929721855233090945565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46841953147903488727297043 70262929721855233090945565)
  ·
    refine ⟨26348598645695712409104587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70262929721855233090945565 26348598645695712409104587)
    ·
      refine ⟨39522897968543568613656881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26348598645695712409104587 39522897968543568613656881)
      ·
        refine ⟨29642173476407676460242661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39522897968543568613656881 29642173476407676460242661)
        ·
          refine ⟨5557907526826439336295499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29642173476407676460242661 5557907526826439336295499)
          ·
            refine ⟨8336861290239659004443249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557907526826439336295499 8336861290239659004443249)
            ·
              refine ⟨6252645967679744253332437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336861290239659004443249 6252645967679744253332437)
              ·
                refine ⟨146546389867494005937479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6252645967679744253332437 146546389867494005937479)
                ·
                  rfl

theorem cell21_1926437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_1926437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926437 prefixEnd_1926437 := by exact prefixLift 1926437
  have htrace : WordTrace (prefixWord ++ tailWord_1926437) baseStart_1926437 baseEnd_1926437 := by
    simpa [prefixWord, tailWord_1926437, baseEnd_1926437] using wordTrace_append hprefix tailTrace_1926437
  have hstable : (prefixWord ++ tailWord_1926437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926437).length < 2 ^ (prefixWord ++ tailWord_1926437).sum := by decide
  have hdescent : baseEnd_1926437 < baseStart_1926437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926454 : List Nat := [5, 1, 2, 3, 10]
def baseStart_1926454 : Nat := 118140960795 + 1926454 * 2 ^ 59
def prefixEnd_1926454 : Nat := 4983230072969 + 3 ^ 40 * 1926454 * 2
def baseEnd_1926454 : Nat := 5427691965853009457149

theorem tailTrace_1926454 : CollatzResearch.WordTrace tailWord_1926454 prefixEnd_1926454 5427691965853009457149 := by
  unfold tailWord_1926454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391471860174602812144651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46842366508529096662876277 4391471860174602812144651)
  ·
    refine ⟨6587207790261904218216977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4391471860174602812144651 6587207790261904218216977)
    ·
      refine ⟨4940405842696428163662733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6587207790261904218216977 4940405842696428163662733)
      ·
        refine ⟨1852652191011160561373525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4940405842696428163662733 1852652191011160561373525)
        ·
          refine ⟨5427691965853009457149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1852652191011160561373525 5427691965853009457149)
          ·
            rfl

theorem cell21_1926454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 10].length) (baseStart_1926454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926454 prefixEnd_1926454 := by exact prefixLift 1926454
  have htrace : WordTrace (prefixWord ++ tailWord_1926454) baseStart_1926454 baseEnd_1926454 := by
    simpa [prefixWord, tailWord_1926454, baseEnd_1926454] using wordTrace_append hprefix tailTrace_1926454
  have hstable : (prefixWord ++ tailWord_1926454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926454).length < 2 ^ (prefixWord ++ tailWord_1926454).sum := by decide
  have hdescent : baseEnd_1926454 < baseStart_1926454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926482 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1926482 : Nat := 118140960795 + 1926482 * 2 ^ 59
def prefixEnd_1926482 : Nat := 4983230072969 + 3 ^ 40 * 1926482 * 2
def baseEnd_1926482 : Nat := 439649439215571939562345

theorem tailTrace_1926482 : CollatzResearch.WordTrace tailWord_1926482 prefixEnd_1926482 439649439215571939562345 := by
  unfold tailWord_1926482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17566142751673051444083425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46843047337794803850889133 17566142751673051444083425)
  ·
    refine ⟨13174607063754788583062569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17566142751673051444083425 13174607063754788583062569)
    ·
      refine ⟨9880955297816091437296927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13174607063754788583062569 9880955297816091437296927)
      ·
        refine ⟨14821432946724137155945391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9880955297816091437296927 14821432946724137155945391)
        ·
          refine ⟨22232149420086205733918087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14821432946724137155945391 22232149420086205733918087)
          ·
            refine ⟨33348224130129308600877131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22232149420086205733918087 33348224130129308600877131)
            ·
              refine ⟨50022336195193962901315697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33348224130129308600877131 50022336195193962901315697)
              ·
                refine ⟨37516752146395472175986773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50022336195193962901315697 37516752146395472175986773)
                ·
                  refine ⟨439649439215571939562345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37516752146395472175986773 439649439215571939562345)
                  ·
                    rfl

theorem cell21_1926482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1926482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926482 prefixEnd_1926482 := by exact prefixLift 1926482
  have htrace : WordTrace (prefixWord ++ tailWord_1926482) baseStart_1926482 baseEnd_1926482 := by
    simpa [prefixWord, tailWord_1926482, baseEnd_1926482] using wordTrace_append hprefix tailTrace_1926482
  have hstable : (prefixWord ++ tailWord_1926482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926482).length < 2 ^ (prefixWord ++ tailWord_1926482).sum := by decide
  have hdescent : baseEnd_1926482 < baseStart_1926482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926572 : List Nat := [2, 2, 1, 1, 1, 1, 13]
def baseStart_1926572 : Nat := 118140960795 + 1926572 * 2 ^ 59
def prefixEnd_1926572 : Nat := 4983230072969 + 3 ^ 40 * 1926572 * 2
def baseEnd_1926572 : Nat := 48852219826861309229129

theorem tailTrace_1926572 : CollatzResearch.WordTrace tailWord_1926572 prefixEnd_1926572 48852219826861309229129 := by
  unfold tailWord_1926572
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133926788183075573554985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46845235717577434098073313 35133926788183075573554985)
  ·
    refine ⟨26350445091137306680166239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35133926788183075573554985 26350445091137306680166239)
    ·
      refine ⟨39525667636705960020249359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26350445091137306680166239 39525667636705960020249359)
      ·
        refine ⟨59288501455058940030374039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39525667636705960020249359 59288501455058940030374039)
        ·
          refine ⟨88932752182588410045561059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59288501455058940030374039 88932752182588410045561059)
          ·
            refine ⟨133399128273882615068341589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88932752182588410045561059 133399128273882615068341589)
            ·
              refine ⟨48852219826861309229129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 133399128273882615068341589 48852219826861309229129)
              ·
                rfl

theorem cell21_1926572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 13].length) (baseStart_1926572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926572 prefixEnd_1926572 := by exact prefixLift 1926572
  have htrace : WordTrace (prefixWord ++ tailWord_1926572) baseStart_1926572 baseEnd_1926572 := by
    simpa [prefixWord, tailWord_1926572, baseEnd_1926572] using wordTrace_append hprefix tailTrace_1926572
  have hstable : (prefixWord ++ tailWord_1926572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926572).length < 2 ^ (prefixWord ++ tailWord_1926572).sum := by decide
  have hdescent : baseEnd_1926572 < baseStart_1926572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926589 : List Nat := [1, 4, 1, 2, 2, 1, 4, 6]
def baseStart_1926589 : Nat := 118140960795 + 1926589 * 2 ^ 59
def prefixEnd_1926589 : Nat := 4983230072969 + 3 ^ 40 * 1926589 * 2
def baseEnd_1926589 : Nat := 146557952691121177092931

theorem tailTrace_1926589 : CollatzResearch.WordTrace tailWord_1926589 prefixEnd_1926589 146557952691121177092931 := by
  unfold tailWord_1926589
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268473617304563050478821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46845649078203042033652547 70268473617304563050478821)
  ·
    refine ⟨13175338803244605571964779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70268473617304563050478821 13175338803244605571964779)
    ·
      refine ⟨19763008204866908357947169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175338803244605571964779 19763008204866908357947169)
      ·
        refine ⟨14822256153650181268460377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19763008204866908357947169 14822256153650181268460377)
        ·
          refine ⟨11116692115237635951345283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14822256153650181268460377 11116692115237635951345283)
          ·
            refine ⟨16675038172856453927017925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11116692115237635951345283 16675038172856453927017925)
            ·
              refine ⟨3126569657410585111315861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16675038172856453927017925 3126569657410585111315861)
              ·
                refine ⟨146557952691121177092931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3126569657410585111315861 146557952691121177092931)
                ·
                  rfl

theorem cell21_1926589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_1926589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926589 prefixEnd_1926589 := by exact prefixLift 1926589
  have htrace : WordTrace (prefixWord ++ tailWord_1926589) baseStart_1926589 baseEnd_1926589 := by
    simpa [prefixWord, tailWord_1926589, baseEnd_1926589] using wordTrace_append hprefix tailTrace_1926589
  have hstable : (prefixWord ++ tailWord_1926589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926589).length < 2 ^ (prefixWord ++ tailWord_1926589).sum := by decide
  have hdescent : baseEnd_1926589 < baseStart_1926589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926603 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_1926603 : Nat := 118140960795 + 1926603 * 2 ^ 59
def prefixEnd_1926603 : Nat := 4983230072969 + 3 ^ 40 * 1926603 * 2
def baseEnd_1926603 : Nat := 439677053064102618045431

theorem tailTrace_1926603 : CollatzResearch.WordTrace tailWord_1926603 prefixEnd_1926603 439677053064102618045431 := by
  unfold tailWord_1926603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268984239253843441488463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46845989492835895627658975 70268984239253843441488463)
  ·
    refine ⟨105403476358880765162232695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70268984239253843441488463 105403476358880765162232695)
    ·
      refine ⟨158105214538321147743349043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105403476358880765162232695 158105214538321147743349043)
      ·
        refine ⟨237157821807481721615023565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158105214538321147743349043 237157821807481721615023565)
        ·
          refine ⟨88934183177805645605633837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237157821807481721615023565 88934183177805645605633837)
          ·
            refine ⟨33350318691677117102112689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88934183177805645605633837 33350318691677117102112689)
            ·
              refine ⟨25012739018757837826584517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33350318691677117102112689 25012739018757837826584517)
              ·
                refine ⟨4689888566017094592484597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25012739018757837826584517 4689888566017094592484597)
                ·
                  refine ⟨439677053064102618045431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689888566017094592484597 439677053064102618045431)
                  ·
                    rfl

theorem cell21_1926603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_1926603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926603 prefixEnd_1926603 := by exact prefixLift 1926603
  have htrace : WordTrace (prefixWord ++ tailWord_1926603) baseStart_1926603 baseEnd_1926603 := by
    simpa [prefixWord, tailWord_1926603, baseEnd_1926603] using wordTrace_append hprefix tailTrace_1926603
  have hstable : (prefixWord ++ tailWord_1926603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926603).length < 2 ^ (prefixWord ++ tailWord_1926603).sum := by decide
  have hdescent : baseEnd_1926603 < baseStart_1926603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926654 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1926654 : Nat := 118140960795 + 1926654 * 2 ^ 59
def prefixEnd_1926654 : Nat := 4983230072969 + 3 ^ 40 * 1926654 * 2
def baseEnd_1926654 : Nat := 439688691958937862695327

theorem tailTrace_1926654 : CollatzResearch.WordTrace tailWord_1926654 prefixEnd_1926654 439688691958937862695327 := by
  unfold tailWord_1926654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783855545258634893949377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46847229574712719434396677 8783855545258634893949377)
  ·
    refine ⟨6587891658943976170462033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8783855545258634893949377 6587891658943976170462033)
    ·
      refine ⟨4940918744207982127846525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6587891658943976170462033 4940918744207982127846525)
      ·
        refine ⟨1852844529077993297942447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4940918744207982127846525 1852844529077993297942447)
        ·
          refine ⟨2779266793616989946913671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852844529077993297942447 2779266793616989946913671)
          ·
            refine ⟨4168900190425484920370507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779266793616989946913671 4168900190425484920370507)
            ·
              refine ⟨6253350285638227380555761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4168900190425484920370507 6253350285638227380555761)
              ·
                refine ⟨4690012714228670535416821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253350285638227380555761 4690012714228670535416821)
                ·
                  refine ⟨439688691958937862695327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690012714228670535416821 439688691958937862695327)
                  ·
                    rfl

theorem cell21_1926654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1926654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926654 prefixEnd_1926654 := by exact prefixLift 1926654
  have htrace : WordTrace (prefixWord ++ tailWord_1926654) baseStart_1926654 baseEnd_1926654 := by
    simpa [prefixWord, tailWord_1926654, baseEnd_1926654] using wordTrace_append hprefix tailTrace_1926654
  have hstable : (prefixWord ++ tailWord_1926654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926654).length < 2 ^ (prefixWord ++ tailWord_1926654).sum := by decide
  have hdescent : baseEnd_1926654 < baseStart_1926654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926665 : List Nat := [1, 2, 1, 1, 3, 1, 7, 5]
def baseStart_1926665 : Nat := 118140960795 + 1926665 * 2 ^ 59
def prefixEnd_1926665 : Nat := 4983230072969 + 3 ^ 40 * 1926665 * 2
def baseEnd_1926665 : Nat := 146563734102934762670657

theorem tailTrace_1926665 : CollatzResearch.WordTrace tailWord_1926665 prefixEnd_1926665 146563734102934762670657 := by
  unfold tailWord_1926665
  simp only [CollatzResearch.WordTrace]
  refine ⟨70271245565029228030245449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46847497043352818686830299 70271245565029228030245449)
  ·
    refine ⟨52703434173771921022684087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70271245565029228030245449 52703434173771921022684087)
    ·
      refine ⟨79055151260657881534026131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52703434173771921022684087 79055151260657881534026131)
      ·
        refine ⟨118582726890986822301039197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79055151260657881534026131 118582726890986822301039197)
        ·
          refine ⟨44468522584120058362889699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118582726890986822301039197 44468522584120058362889699)
          ·
            refine ⟨66702783876180087544334549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44468522584120058362889699 66702783876180087544334549)
            ·
              refine ⟨1563346497097970801820341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66702783876180087544334549 1563346497097970801820341)
              ·
                refine ⟨146563734102934762670657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1563346497097970801820341 146563734102934762670657)
                ·
                  rfl

theorem cell21_1926665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 5].length) (baseStart_1926665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926665 prefixEnd_1926665 := by exact prefixLift 1926665
  have htrace : WordTrace (prefixWord ++ tailWord_1926665) baseStart_1926665 baseEnd_1926665 := by
    simpa [prefixWord, tailWord_1926665, baseEnd_1926665] using wordTrace_append hprefix tailTrace_1926665
  have hstable : (prefixWord ++ tailWord_1926665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926665).length < 2 ^ (prefixWord ++ tailWord_1926665).sum := by decide
  have hdescent : baseEnd_1926665 < baseStart_1926665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926817 : List Nat := [1, 2, 3, 3, 2, 1, 3, 6]
def baseStart_1926817 : Nat := 118140960795 + 1926817 * 2 ^ 59
def prefixEnd_1926817 : Nat := 4983230072969 + 3 ^ 40 * 1926817 * 2
def baseEnd_1926817 : Nat := 146575296926561933826109

theorem tailTrace_1926817 : CollatzResearch.WordTrace tailWord_1926817 prefixEnd_1926817 146575296926561933826109 := by
  unfold tailWord_1926817
  simp only [CollatzResearch.WordTrace]
  refine ⟨70276789460478557989778705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46851192973652371993185803 70276789460478557989778705)
  ·
    refine ⟨52707592095358918492334029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70276789460478557989778705 52707592095358918492334029)
    ·
      refine ⟨19765347035759594434625261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52707592095358918492334029 19765347035759594434625261)
      ·
        refine ⟨7412005138409847912984473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19765347035759594434625261 7412005138409847912984473)
        ·
          refine ⟨5559003853807385934738355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7412005138409847912984473 5559003853807385934738355)
          ·
            refine ⟨8338505780711078902107533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559003853807385934738355 8338505780711078902107533)
            ·
              refine ⟨3126939667766654588290325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8338505780711078902107533 3126939667766654588290325)
              ·
                refine ⟨146575296926561933826109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3126939667766654588290325 146575296926561933826109)
                ·
                  rfl

theorem cell21_1926817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_1926817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926817 prefixEnd_1926817 := by exact prefixLift 1926817
  have htrace : WordTrace (prefixWord ++ tailWord_1926817) baseStart_1926817 baseEnd_1926817 := by
    simpa [prefixWord, tailWord_1926817, baseEnd_1926817] using wordTrace_append hprefix tailTrace_1926817
  have hstable : (prefixWord ++ tailWord_1926817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926817).length < 2 ^ (prefixWord ++ tailWord_1926817).sum := by decide
  have hdescent : baseEnd_1926817 < baseStart_1926817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926831 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_1926831 : Nat := 118140960795 + 1926831 * 2 ^ 59
def prefixEnd_1926831 : Nat := 4983230072969 + 3 ^ 40 * 1926831 * 2
def baseEnd_1926831 : Nat := 439729085770424888244965

theorem tailTrace_1926831 : CollatzResearch.WordTrace tailWord_1926831 prefixEnd_1926831 439729085770424888244965 := by
  unfold tailWord_1926831
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277300082427838380788347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46851533388285225587192231 70277300082427838380788347)
  ·
    refine ⟨105415950123641757571182521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70277300082427838380788347 105415950123641757571182521)
    ·
      refine ⟨79061962592731318178386891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105415950123641757571182521 79061962592731318178386891)
      ·
        refine ⟨118592943889096977267580337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79061962592731318178386891 118592943889096977267580337)
        ·
          refine ⟨88944707916822732950685253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118592943889096977267580337 88944707916822732950685253)
          ·
            refine ⟨16677132734404262428253485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88944707916822732950685253 16677132734404262428253485)
            ·
              refine ⟨6253924775401598410595057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16677132734404262428253485 6253924775401598410595057)
              ·
                refine ⟨4690443581551198807946293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253924775401598410595057 4690443581551198807946293)
                ·
                  refine ⟨439729085770424888244965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690443581551198807946293 439729085770424888244965)
                  ·
                    rfl

theorem cell21_1926831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_1926831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926831 prefixEnd_1926831 := by exact prefixLift 1926831
  have htrace : WordTrace (prefixWord ++ tailWord_1926831) baseStart_1926831 baseEnd_1926831 := by
    simpa [prefixWord, tailWord_1926831, baseEnd_1926831] using wordTrace_append hprefix tailTrace_1926831
  have hstable : (prefixWord ++ tailWord_1926831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926831).length < 2 ^ (prefixWord ++ tailWord_1926831).sum := by decide
  have hdescent : baseEnd_1926831 < baseStart_1926831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926854 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1926854 : Nat := 118140960795 + 1926854 * 2 ^ 59
def prefixEnd_1926854 : Nat := 4983230072969 + 3 ^ 40 * 1926854 * 2
def baseEnd_1926854 : Nat := 439734334683781959361585

theorem tailTrace_1926854 : CollatzResearch.WordTrace tailWord_1926854 prefixEnd_1926854 439734334683781959361585 := by
  unfold tailWord_1926854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196191842542016040902363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46852092640896342205917077 2196191842542016040902363)
  ·
    refine ⟨3294287763813024061353545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196191842542016040902363 3294287763813024061353545)
    ·
      refine ⟨2470715822859768046015159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294287763813024061353545 2470715822859768046015159)
      ·
        refine ⟨3706073734289652069022739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470715822859768046015159 3706073734289652069022739)
        ·
          refine ⟨5559110601434478103534109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706073734289652069022739 5559110601434478103534109)
          ·
            refine ⟨2084666475537929288825291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5559110601434478103534109 2084666475537929288825291)
            ·
              refine ⟨3126999713306893933237937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084666475537929288825291 3126999713306893933237937)
              ·
                refine ⟨2345249784980170449928453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126999713306893933237937 2345249784980170449928453)
                ·
                  refine ⟨439734334683781959361585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345249784980170449928453 439734334683781959361585)
                  ·
                    rfl

theorem cell21_1926854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1926854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926854 prefixEnd_1926854 := by exact prefixLift 1926854
  have htrace : WordTrace (prefixWord ++ tailWord_1926854) baseStart_1926854 baseEnd_1926854 := by
    simpa [prefixWord, tailWord_1926854, baseEnd_1926854] using wordTrace_append hprefix tailTrace_1926854
  have hstable : (prefixWord ++ tailWord_1926854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926854).length < 2 ^ (prefixWord ++ tailWord_1926854).sum := by decide
  have hdescent : baseEnd_1926854 < baseStart_1926854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926862 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1926862 : Nat := 118140960795 + 1926862 * 2 ^ 59
def prefixEnd_1926862 : Nat := 4983230072969 + 3 ^ 40 * 1926862 * 2
def baseEnd_1926862 : Nat := 439736160392775723228235

theorem tailTrace_1926862 : CollatzResearch.WordTrace tailWord_1926862 prefixEnd_1926862 439736160392775723228235 := by
  unfold tailWord_1926862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784803843164441334395855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46852287163543687116777893 8784803843164441334395855)
  ·
    refine ⟨13177205764746662001593783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8784803843164441334395855 13177205764746662001593783)
    ·
      refine ⟨19765808647119993002390675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13177205764746662001593783 19765808647119993002390675)
      ·
        refine ⟨29648712970679989503586013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19765808647119993002390675 29648712970679989503586013)
        ·
          refine ⟨11118267364004996063844755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29648712970679989503586013 11118267364004996063844755)
          ·
            refine ⟨16677401046007494095767133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118267364004996063844755 16677401046007494095767133)
            ·
              refine ⟨6254025392252810285912675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16677401046007494095767133 6254025392252810285912675)
              ·
                refine ⟨9381038088379215428869013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254025392252810285912675 9381038088379215428869013)
                ·
                  refine ⟨439736160392775723228235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9381038088379215428869013 439736160392775723228235)
                  ·
                    rfl

theorem cell21_1926862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1926862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926862 prefixEnd_1926862 := by exact prefixLift 1926862
  have htrace : WordTrace (prefixWord ++ tailWord_1926862) baseStart_1926862 baseEnd_1926862 := by
    simpa [prefixWord, tailWord_1926862, baseEnd_1926862] using wordTrace_append hprefix tailTrace_1926862
  have hstable : (prefixWord ++ tailWord_1926862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926862).length < 2 ^ (prefixWord ++ tailWord_1926862).sum := by decide
  have hdescent : baseEnd_1926862 < baseStart_1926862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926879 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 4]
def baseStart_1926879 : Nat := 118140960795 + 1926879 * 2 ^ 59
def prefixEnd_1926879 : Nat := 4983230072969 + 3 ^ 40 * 1926879 * 2
def baseEnd_1926879 : Nat := 439740040024387471444867

theorem tailTrace_1926879 : CollatzResearch.WordTrace tailWord_1926879 prefixEnd_1926879 439740040024387471444867 := by
  unfold tailWord_1926879
  simp only [CollatzResearch.WordTrace]
  refine ⟨70279050786253942578535691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46852700524169295052357127 70279050786253942578535691)
  ·
    refine ⟨105418576179380913867803537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70279050786253942578535691 105418576179380913867803537)
    ·
      refine ⟨79063932134535685400852653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105418576179380913867803537 79063932134535685400852653)
      ·
        refine ⟨29648974550450882025319745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79063932134535685400852653 29648974550450882025319745)
        ·
          refine ⟨22236730912838161518989809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29648974550450882025319745 22236730912838161518989809)
          ·
            refine ⟨16677548184628621139242357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22236730912838161518989809 16677548184628621139242357)
            ·
              refine ⟨1563520142308933231803971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16677548184628621139242357 1563520142308933231803971)
              ·
                refine ⟨2345280213463399847705957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563520142308933231803971 2345280213463399847705957)
                ·
                  refine ⟨439740040024387471444867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345280213463399847705957 439740040024387471444867)
                  ·
                    rfl

theorem cell21_1926879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4].length) (baseStart_1926879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926879 prefixEnd_1926879 := by exact prefixLift 1926879
  have htrace : WordTrace (prefixWord ++ tailWord_1926879) baseStart_1926879 baseEnd_1926879 := by
    simpa [prefixWord, tailWord_1926879, baseEnd_1926879] using wordTrace_append hprefix tailTrace_1926879
  have hstable : (prefixWord ++ tailWord_1926879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926879).length < 2 ^ (prefixWord ++ tailWord_1926879).sum := by decide
  have hdescent : baseEnd_1926879 < baseStart_1926879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926893 : List Nat := [1, 5, 1, 2, 1, 3, 1, 7]
def baseStart_1926893 : Nat := 118140960795 + 1926893 * 2 ^ 59
def prefixEnd_1926893 : Nat := 4983230072969 + 3 ^ 40 * 1926893 * 2
def baseEnd_1926893 : Nat := 146581078338375519403835

theorem tailTrace_1926893 : CollatzResearch.WordTrace tailWord_1926893 prefixEnd_1926893 146581078338375519403835 := by
  unfold tailWord_1926893
  simp only [CollatzResearch.WordTrace]
  refine ⟨70279561408203222969545333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46853040938802148646363555 70279561408203222969545333)
  ·
    refine ⟨6588708882019052153394875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70279561408203222969545333 6588708882019052153394875)
    ·
      refine ⟨9883063323028578230092313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6588708882019052153394875 9883063323028578230092313)
      ·
        refine ⟨7412297492271433672569235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9883063323028578230092313 7412297492271433672569235)
        ·
          refine ⟨11118446238407150508853853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412297492271433672569235 11118446238407150508853853)
          ·
            refine ⟨4169417339402681440820195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11118446238407150508853853 4169417339402681440820195)
            ·
              refine ⟨6254126009104022161230293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169417339402681440820195 6254126009104022161230293)
              ·
                refine ⟨146581078338375519403835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6254126009104022161230293 146581078338375519403835)
                ·
                  rfl

theorem cell21_1926893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_1926893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926893 prefixEnd_1926893 := by exact prefixLift 1926893
  have htrace : WordTrace (prefixWord ++ tailWord_1926893) baseStart_1926893 baseEnd_1926893 := by
    simpa [prefixWord, tailWord_1926893, baseEnd_1926893] using wordTrace_append hprefix tailTrace_1926893
  have hstable : (prefixWord ++ tailWord_1926893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926893).length < 2 ^ (prefixWord ++ tailWord_1926893).sum := by decide
  have hdescent : baseEnd_1926893 < baseStart_1926893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926910 : List Nat := [4, 2, 2, 1, 3, 2, 7]
def baseStart_1926910 : Nat := 118140960795 + 1926910 * 2 ^ 59
def prefixEnd_1926910 : Nat := 4983230072969 + 3 ^ 40 * 1926910 * 2
def baseEnd_1926910 : Nat := 48860790516304256269793

theorem tailTrace_1926910 : CollatzResearch.WordTrace tailWord_1926910 prefixEnd_1926910 48860790516304256269793 := by
  unfold tailWord_1926910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785022681142704359114273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46853454299427756581942789 8785022681142704359114273)
  ·
    refine ⟨6588767010857028269335705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8785022681142704359114273 6588767010857028269335705)
    ·
      refine ⟨4941575258142771202001779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6588767010857028269335705 4941575258142771202001779)
      ·
        refine ⟨7412362887214156803002669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941575258142771202001779 7412362887214156803002669)
        ·
          refine ⟨2779636082705308801126001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7412362887214156803002669 2779636082705308801126001)
          ·
            refine ⟨2084727062028981600844501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2779636082705308801126001 2084727062028981600844501)
            ·
              refine ⟨48860790516304256269793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2084727062028981600844501 48860790516304256269793)
              ·
                rfl

theorem cell21_1926910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 7].length) (baseStart_1926910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926910 prefixEnd_1926910 := by exact prefixLift 1926910
  have htrace : WordTrace (prefixWord ++ tailWord_1926910) baseStart_1926910 baseEnd_1926910 := by
    simpa [prefixWord, tailWord_1926910, baseEnd_1926910] using wordTrace_append hprefix tailTrace_1926910
  have hstable : (prefixWord ++ tailWord_1926910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926910).length < 2 ^ (prefixWord ++ tailWord_1926910).sum := by decide
  have hdescent : baseEnd_1926910 < baseStart_1926910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926924 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_1926924 : Nat := 118140960795 + 1926924 * 2 ^ 59
def prefixEnd_1926924 : Nat := 4983230072969 + 3 ^ 40 * 1926924 * 2
def baseEnd_1926924 : Nat := 439750309637477393194775

theorem tailTrace_1926924 : CollatzResearch.WordTrace tailWord_1926924 prefixEnd_1926924 439750309637477393194775 := by
  unfold tailWord_1926924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140346035545457631961913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46853794714060610175949217 35140346035545457631961913)
  ·
    refine ⟨26355259526659093223971435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35140346035545457631961913 26355259526659093223971435)
    ·
      refine ⟨39532889289988639835957153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26355259526659093223971435 39532889289988639835957153)
      ·
        refine ⟨29649666967491479876967865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39532889289988639835957153 29649666967491479876967865)
        ·
          refine ⟨22237250225618609907725899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29649666967491479876967865 22237250225618609907725899)
          ·
            refine ⟨33355875338427914861588849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22237250225618609907725899 33355875338427914861588849)
            ·
              refine ⟨25016906503820936146191637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33355875338427914861588849 25016906503820936146191637)
              ·
                refine ⟨1172667492366606381852733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25016906503820936146191637 1172667492366606381852733)
                ·
                  refine ⟨439750309637477393194775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172667492366606381852733 439750309637477393194775)
                  ·
                    rfl

theorem cell21_1926924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_1926924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926924 prefixEnd_1926924 := by exact prefixLift 1926924
  have htrace : WordTrace (prefixWord ++ tailWord_1926924) baseStart_1926924 baseEnd_1926924 := by
    simpa [prefixWord, tailWord_1926924, baseEnd_1926924] using wordTrace_append hprefix tailTrace_1926924
  have hstable : (prefixWord ++ tailWord_1926924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926924).length < 2 ^ (prefixWord ++ tailWord_1926924).sum := by decide
  have hdescent : baseEnd_1926924 < baseStart_1926924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926969 : List Nat := [1, 2, 1, 7, 1, 9]
def baseStart_1926969 : Nat := 118140960795 + 1926969 * 2 ^ 59
def prefixEnd_1926969 : Nat := 4983230072969 + 3 ^ 40 * 1926969 * 2
def baseEnd_1926969 : Nat := 16287428861132122775729

theorem tailTrace_1926969 : CollatzResearch.WordTrace tailWord_1926969 prefixEnd_1926969 16287428861132122775729 := by
  unfold tailWord_1926969
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282333355927887949311961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46854888903951925299541307 70282333355927887949311961)
  ·
    refine ⟨52711750016945915961983971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70282333355927887949311961 52711750016945915961983971)
    ·
      refine ⟨79067625025418873942975957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52711750016945915961983971 79067625025418873942975957)
      ·
        refine ⟨1853147461533254858038499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79067625025418873942975957 1853147461533254858038499)
        ·
          refine ⟨2779721192299882287057749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853147461533254858038499 2779721192299882287057749)
          ·
            refine ⟨16287428861132122775729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2779721192299882287057749 16287428861132122775729)
            ·
              rfl

theorem cell21_1926969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 9].length) (baseStart_1926969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926969 prefixEnd_1926969 := by exact prefixLift 1926969
  have htrace : WordTrace (prefixWord ++ tailWord_1926969) baseStart_1926969 baseEnd_1926969 := by
    simpa [prefixWord, tailWord_1926969, baseEnd_1926969] using wordTrace_append hprefix tailTrace_1926969
  have hstable : (prefixWord ++ tailWord_1926969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926969).length < 2 ^ (prefixWord ++ tailWord_1926969).sum := by decide
  have hdescent : baseEnd_1926969 < baseStart_1926969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1926975 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 3]
def baseStart_1926975 : Nat := 118140960795 + 1926975 * 2 ^ 59
def prefixEnd_1926975 : Nat := 4983230072969 + 3 ^ 40 * 1926975 * 2
def baseEnd_1926975 : Nat := 439761948532312637844671

theorem tailTrace_1926975 : CollatzResearch.WordTrace tailWord_1926975 prefixEnd_1926975 439761948532312637844671 := by
  unfold tailWord_1926975
  simp only [CollatzResearch.WordTrace]
  refine ⟨70282552193906150974030379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46855034795937433982686919 70282552193906150974030379)
  ·
    refine ⟨105423828290859226461045569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70282552193906150974030379 105423828290859226461045569)
    ·
      refine ⟨79067871218144419845784177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105423828290859226461045569 79067871218144419845784177)
      ·
        refine ⟨59300903413608314884338133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79067871218144419845784177 59300903413608314884338133)
        ·
          refine ⟨1389864923756444880101675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59300903413608314884338133 1389864923756444880101675)
          ·
            refine ⟨2084797385634667320152513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389864923756444880101675 2084797385634667320152513)
            ·
              refine ⟨1563598039226000490114385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2084797385634667320152513 1563598039226000490114385)
              ·
                refine ⟨1172698529419500367585789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563598039226000490114385 1172698529419500367585789)
                ·
                  refine ⟨439761948532312637844671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172698529419500367585789 439761948532312637844671)
                  ·
                    rfl

theorem cell21_1926975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3].length) (baseStart_1926975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1926975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1926975 prefixEnd_1926975 := by exact prefixLift 1926975
  have htrace : WordTrace (prefixWord ++ tailWord_1926975) baseStart_1926975 baseEnd_1926975 := by
    simpa [prefixWord, tailWord_1926975, baseEnd_1926975] using wordTrace_append hprefix tailTrace_1926975
  have hstable : (prefixWord ++ tailWord_1926975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1926975).length < 2 ^ (prefixWord ++ tailWord_1926975).sum := by decide
  have hdescent : baseEnd_1926975 < baseStart_1926975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1926975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927048 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_1927048 : Nat := 118140960795 + 1927048 * 2 ^ 59
def prefixEnd_1927048 : Nat := 4983230072969 + 3 ^ 40 * 1927048 * 2
def baseEnd_1927048 : Nat := 439778608126880733127855

theorem tailTrace_1927048 : CollatzResearch.WordTrace tailWord_1927048 prefixEnd_1927048 439778608126880733127855 := by
  unfold tailWord_1927048
  simp only [CollatzResearch.WordTrace]
  refine ⟨35142607361320842220718899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46856809815094456294291865 35142607361320842220718899)
  ·
    refine ⟨52713911041981263331078349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35142607361320842220718899 52713911041981263331078349)
    ·
      refine ⟨19767716640742973749154381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52713911041981263331078349 19767716640742973749154381)
      ·
        refine ⟨7412893740278615155932893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19767716640742973749154381 7412893740278615155932893)
        ·
          refine ⟨2779835152604480683474835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7412893740278615155932893 2779835152604480683474835)
          ·
            refine ⟨4169752728906721025212253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779835152604480683474835 4169752728906721025212253)
            ·
              refine ⟨1563657273340020384454595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4169752728906721025212253 1563657273340020384454595)
              ·
                refine ⟨2345485910010030576681893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563657273340020384454595 2345485910010030576681893)
                ·
                  refine ⟨439778608126880733127855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2345485910010030576681893 439778608126880733127855)
                  ·
                    rfl

theorem cell21_1927048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_1927048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927048 prefixEnd_1927048 := by exact prefixLift 1927048
  have htrace : WordTrace (prefixWord ++ tailWord_1927048) baseStart_1927048 baseEnd_1927048 := by
    simpa [prefixWord, tailWord_1927048, baseEnd_1927048] using wordTrace_append hprefix tailTrace_1927048
  have hstable : (prefixWord ++ tailWord_1927048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927048).length < 2 ^ (prefixWord ++ tailWord_1927048).sum := by decide
  have hdescent : baseEnd_1927048 < baseStart_1927048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927104 : List Nat := [2, 1, 1, 2, 3, 2, 4, 6]
def baseStart_1927104 : Nat := 118140960795 + 1927104 * 2 ^ 59
def prefixEnd_1927104 : Nat := 4983230072969 + 3 ^ 40 * 1927104 * 2
def baseEnd_1927104 : Nat := 146597129363279026731469

theorem tailTrace_1927104 : CollatzResearch.WordTrace tailWord_1927104 prefixEnd_1927104 146597129363279026731469 := by
  unfold tailWord_1927104
  simp only [CollatzResearch.WordTrace]
  refine ⟨35143628605219403002738183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46858171473625870670317577 35143628605219403002738183)
  ·
    refine ⟨52715442907829104504107275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35143628605219403002738183 52715442907829104504107275)
    ·
      refine ⟨79073164361743656756160913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52715442907829104504107275 79073164361743656756160913)
      ·
        refine ⟨59304873271307742567120685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79073164361743656756160913 59304873271307742567120685)
        ·
          refine ⟨22239327476740403462670257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59304873271307742567120685 22239327476740403462670257)
          ·
            refine ⟨16679495607555302597002693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22239327476740403462670257 16679495607555302597002693)
            ·
              refine ⟨3127405426416619236938005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16679495607555302597002693 3127405426416619236938005)
              ·
                refine ⟨146597129363279026731469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3127405426416619236938005 146597129363279026731469)
                ·
                  rfl

theorem cell21_1927104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_1927104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927104 prefixEnd_1927104 := by exact prefixLift 1927104
  have htrace : WordTrace (prefixWord ++ tailWord_1927104) baseStart_1927104 baseEnd_1927104 := by
    simpa [prefixWord, tailWord_1927104, baseEnd_1927104] using wordTrace_append hprefix tailTrace_1927104
  have hstable : (prefixWord ++ tailWord_1927104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927104).length < 2 ^ (prefixWord ++ tailWord_1927104).sum := by decide
  have hdescent : baseEnd_1927104 < baseStart_1927104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927138 : List Nat := [3, 3, 3, 1, 3, 8]
def baseStart_1927138 : Nat := 118140960795 + 1927138 * 2 ^ 59
def prefixEnd_1927138 : Nat := 4983230072969 + 3 ^ 40 * 1927138 * 2
def baseEnd_1927138 : Nat := 16288857309372613949173

theorem tailTrace_1927138 : CollatzResearch.WordTrace tailWord_1927138 prefixEnd_1927138 16288857309372613949173 := by
  unfold tailWord_1927138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17572124323078907453053517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46858998194877086541476045 17572124323078907453053517)
  ·
    refine ⟨6589546621154590294895069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17572124323078907453053517 6589546621154590294895069)
    ·
      refine ⟨2471079982932971360585651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6589546621154590294895069 2471079982932971360585651)
      ·
        refine ⟨3706619974399457040878477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471079982932971360585651 3706619974399457040878477)
        ·
          refine ⟨1389982490399796390329429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3706619974399457040878477 1389982490399796390329429)
          ·
            refine ⟨16288857309372613949173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1389982490399796390329429 16288857309372613949173)
            ·
              rfl

theorem cell21_1927138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 8].length) (baseStart_1927138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927138 prefixEnd_1927138 := by exact prefixLift 1927138
  have htrace : WordTrace (prefixWord ++ tailWord_1927138) baseStart_1927138 baseEnd_1927138 := by
    simpa [prefixWord, tailWord_1927138, baseEnd_1927138] using wordTrace_append hprefix tailTrace_1927138
  have hstable : (prefixWord ++ tailWord_1927138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927138).length < 2 ^ (prefixWord ++ tailWord_1927138).sum := by decide
  have hdescent : baseEnd_1927138 < baseStart_1927138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927256 : List Nat := [2, 1, 2, 2, 1, 6, 7]
def baseStart_1927256 : Nat := 118140960795 + 1927256 * 2 ^ 59
def prefixEnd_1927256 : Nat := 4983230072969 + 3 ^ 40 * 1927256 * 2
def baseEnd_1927256 : Nat := 48869564062302065962307

theorem tailTrace_1927256 : CollatzResearch.WordTrace tailWord_1927256 prefixEnd_1927256 48869564062302065962307 := by
  unfold tailWord_1927256
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146400552944067982504811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46861867403925423976673081 35146400552944067982504811)
  ·
    refine ⟨52719600829416101973757217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35146400552944067982504811 52719600829416101973757217)
    ·
      refine ⟨39539700622062076480317913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52719600829416101973757217 39539700622062076480317913)
      ·
        refine ⟨29654775466546557360238435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39539700622062076480317913 29654775466546557360238435)
        ·
          refine ⟨44482163199819836040357653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29654775466546557360238435 44482163199819836040357653)
          ·
            refine ⟨2085101399991554814391765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44482163199819836040357653 2085101399991554814391765)
            ·
              refine ⟨48869564062302065962307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2085101399991554814391765 48869564062302065962307)
              ·
                rfl

theorem cell21_1927256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 7].length) (baseStart_1927256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927256 prefixEnd_1927256 := by exact prefixLift 1927256
  have htrace : WordTrace (prefixWord ++ tailWord_1927256) baseStart_1927256 baseEnd_1927256 := by
    simpa [prefixWord, tailWord_1927256, baseEnd_1927256] using wordTrace_append hprefix tailTrace_1927256
  have hstable : (prefixWord ++ tailWord_1927256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927256).length < 2 ^ (prefixWord ++ tailWord_1927256).sum := by decide
  have hdescent : baseEnd_1927256 < baseStart_1927256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927391 : List Nat := [1, 1, 2, 3, 2, 1, 1, 10]
def baseStart_1927391 : Nat := 118140960795 + 1927391 * 2 ^ 59
def prefixEnd_1927391 : Nat := 4983230072969 + 3 ^ 40 * 1927391 * 2
def baseEnd_1927391 : Nat := 146618961799996119636829

theorem tailTrace_1927391 : CollatzResearch.WordTrace tailWord_1927391 prefixEnd_1927391 146618961799996119636829 := by
  unfold tailWord_1927391
  simp only [CollatzResearch.WordTrace]
  refine ⟨70297724960399054021174027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46865149973599369347449351 70297724960399054021174027)
  ·
    refine ⟨105446587440598581031761041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70297724960399054021174027 105446587440598581031761041)
    ·
      refine ⟨79084940580448935773820781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105446587440598581031761041 79084940580448935773820781)
      ·
        refine ⟨29656852717668350915182793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79084940580448935773820781 29656852717668350915182793)
        ·
          refine ⟨22242639538251263186387095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29656852717668350915182793 22242639538251263186387095)
          ·
            refine ⟨33363959307376894779580643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22242639538251263186387095 33363959307376894779580643)
            ·
              refine ⟨50045938961065342169370965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33363959307376894779580643 50045938961065342169370965)
              ·
                refine ⟨146618961799996119636829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50045938961065342169370965 146618961799996119636829)
                ·
                  rfl

theorem cell21_1927391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_1927391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927391 prefixEnd_1927391 := by exact prefixLift 1927391
  have htrace : WordTrace (prefixWord ++ tailWord_1927391) baseStart_1927391 baseEnd_1927391 := by
    simpa [prefixWord, tailWord_1927391, baseEnd_1927391] using wordTrace_append hprefix tailTrace_1927391
  have hstable : (prefixWord ++ tailWord_1927391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927391).length < 2 ^ (prefixWord ++ tailWord_1927391).sum := by decide
  have hdescent : baseEnd_1927391 < baseStart_1927391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927439 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 3]
def baseStart_1927439 : Nat := 118140960795 + 1927439 * 2 ^ 59
def prefixEnd_1927439 : Nat := 4983230072969 + 3 ^ 40 * 1927439 * 2
def baseEnd_1927439 : Nat := 439867839653950942110389

theorem tailTrace_1927439 : CollatzResearch.WordTrace tailWord_1927439 prefixEnd_1927439 439867839653950942110389 := by
  unfold tailWord_1927439
  simp only [CollatzResearch.WordTrace]
  refine ⟨70299475664225158218921371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46866317109483438812614247 70299475664225158218921371)
  ·
    refine ⟨105449213496337737328382057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70299475664225158218921371 105449213496337737328382057)
    ·
      refine ⟨79086910122253302996286543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105449213496337737328382057 79086910122253302996286543)
      ·
        refine ⟨118630365183379954494429815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79086910122253302996286543 118630365183379954494429815)
        ·
          refine ⟨177945547775069931741644723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118630365183379954494429815 177945547775069931741644723)
          ·
            refine ⟨266918321662604897612467085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177945547775069931741644723 266918321662604897612467085)
            ·
              refine ⟨100094370623476836604675157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266918321662604897612467085 100094370623476836604675157)
              ·
                refine ⟨1172980905743869178961037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 100094370623476836604675157 1172980905743869178961037)
                ·
                  refine ⟨439867839653950942110389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172980905743869178961037 439867839653950942110389)
                  ·
                    rfl

theorem cell21_1927439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3].length) (baseStart_1927439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927439 prefixEnd_1927439 := by exact prefixLift 1927439
  have htrace : WordTrace (prefixWord ++ tailWord_1927439) baseStart_1927439 baseEnd_1927439 := by
    simpa [prefixWord, tailWord_1927439, baseEnd_1927439] using wordTrace_append hprefix tailTrace_1927439
  have hstable : (prefixWord ++ tailWord_1927439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927439).length < 2 ^ (prefixWord ++ tailWord_1927439).sum := by decide
  have hdescent : baseEnd_1927439 < baseStart_1927439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927636 : List Nat := [2, 4, 1, 2, 2, 1, 2, 7]
def baseStart_1927636 : Nat := 118140960795 + 1927636 * 2 ^ 59
def prefixEnd_1927636 : Nat := 4983230072969 + 3 ^ 40 * 1927636 * 2
def baseEnd_1927636 : Nat := 146637599245974125775551

theorem tailTrace_1927636 : CollatzResearch.WordTrace tailWord_1927636 prefixEnd_1927636 146637599245974125775551 := by
  unfold tailWord_1927636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35153330422255730431921381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46871107229674307242561841 35153330422255730431921381)
  ·
    refine ⟨6591249454172949455985259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35153330422255730431921381 6591249454172949455985259)
    ·
      refine ⟨9886874181259424183977889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6591249454172949455985259 9886874181259424183977889)
      ·
        refine ⟨7415155635944568137983417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9886874181259424183977889 7415155635944568137983417)
        ·
          refine ⟨5561366726958426103487563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7415155635944568137983417 5561366726958426103487563)
          ·
            refine ⟨8342050090437639155231345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561366726958426103487563 8342050090437639155231345)
            ·
              refine ⟨6256537567828229366423509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342050090437639155231345 6256537567828229366423509)
              ·
                refine ⟨146637599245974125775551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6256537567828229366423509 146637599245974125775551)
                ·
                  rfl

theorem cell21_1927636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_1927636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927636 prefixEnd_1927636 := by exact prefixLift 1927636
  have htrace : WordTrace (prefixWord ++ tailWord_1927636) baseStart_1927636 baseEnd_1927636 := by
    simpa [prefixWord, tailWord_1927636, baseEnd_1927636] using wordTrace_append hprefix tailTrace_1927636
  have hstable : (prefixWord ++ tailWord_1927636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927636).length < 2 ^ (prefixWord ++ tailWord_1927636).sum := by decide
  have hdescent : baseEnd_1927636 < baseStart_1927636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927667 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 3]
def baseStart_1927667 : Nat := 118140960795 + 1927667 * 2 ^ 59
def prefixEnd_1927667 : Nat := 4983230072969 + 3 ^ 40 * 1927667 * 2
def baseEnd_1927667 : Nat := 439919872360273212309923

theorem tailTrace_1927667 : CollatzResearch.WordTrace tailWord_1927667 prefixEnd_1927667 439919872360273212309923 := by
  unfold tailWord_1927667
  simp only [CollatzResearch.WordTrace]
  refine ⟨70307791507399153158221255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46871861004932768772147503 70307791507399153158221255)
  ·
    refine ⟨105461687261098729737331883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70307791507399153158221255 105461687261098729737331883)
    ·
      refine ⟨158192530891648094605997825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105461687261098729737331883 158192530891648094605997825)
      ·
        refine ⟨118644398168736070954498369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158192530891648094605997825 118644398168736070954498369)
        ·
          refine ⟨88983298626552053215873777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118644398168736070954498369 88983298626552053215873777)
          ·
            refine ⟨66737473969914039911905333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88983298626552053215873777 66737473969914039911905333)
            ·
              refine ⟨6256638184679441241741125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66737473969914039911905333 6256638184679441241741125)
              ·
                refine ⟨1173119659627395232826461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6256638184679441241741125 1173119659627395232826461)
                ·
                  refine ⟨439919872360273212309923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173119659627395232826461 439919872360273212309923)
                  ·
                    rfl

theorem cell21_1927667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3].length) (baseStart_1927667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927667 prefixEnd_1927667 := by exact prefixLift 1927667
  have htrace : WordTrace (prefixWord ++ tailWord_1927667) baseStart_1927667 baseEnd_1927667 := by
    simpa [prefixWord, tailWord_1927667, baseEnd_1927667] using wordTrace_append hprefix tailTrace_1927667
  have hstable : (prefixWord ++ tailWord_1927667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927667).length < 2 ^ (prefixWord ++ tailWord_1927667).sum := by decide
  have hdescent : baseEnd_1927667 < baseStart_1927667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927712 : List Nat := [2, 1, 1, 6, 2, 1, 8]
def baseStart_1927712 : Nat := 118140960795 + 1927712 * 2 ^ 59
def prefixEnd_1927712 : Nat := 4983230072969 + 3 ^ 40 * 1927712 * 2
def baseEnd_1927712 : Nat := 48881126885929237117759

theorem tailTrace_1927712 : CollatzResearch.WordTrace tailWord_1927712 prefixEnd_1927712 48881126885929237117759 := by
  unfold tailWord_1927712
  simp only [CollatzResearch.WordTrace]
  refine ⟨35154716396118062921804695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46872955194824083895739593 35154716396118062921804695)
  ·
    refine ⟨52732074594177094382707043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35154716396118062921804695 52732074594177094382707043)
    ·
      refine ⟨79098111891265641574060565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52732074594177094382707043 79098111891265641574060565)
      ·
        refine ⟨3707723994903076948784089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79098111891265641574060565 3707723994903076948784089)
        ·
          refine ⟨2780792996177307711588067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3707723994903076948784089 2780792996177307711588067)
          ·
            refine ⟨4171189494265961567382101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780792996177307711588067 4171189494265961567382101)
            ·
              refine ⟨48881126885929237117759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4171189494265961567382101 48881126885929237117759)
              ·
                rfl

theorem cell21_1927712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 8].length) (baseStart_1927712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927712 prefixEnd_1927712 := by exact prefixLift 1927712
  have htrace : WordTrace (prefixWord ++ tailWord_1927712) baseStart_1927712 baseEnd_1927712 := by
    simpa [prefixWord, tailWord_1927712, baseEnd_1927712] using wordTrace_append hprefix tailTrace_1927712
  have hstable : (prefixWord ++ tailWord_1927712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927712).length < 2 ^ (prefixWord ++ tailWord_1927712).sum := by decide
  have hdescent : baseEnd_1927712 < baseStart_1927712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927833 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_1927833 : Nat := 118140960795 + 1927833 * 2 ^ 59
def prefixEnd_1927833 : Nat := 4983230072969 + 3 ^ 40 * 1927833 * 2
def baseEnd_1927833 : Nat := 439957755821893812542917

theorem tailTrace_1927833 : CollatzResearch.WordTrace tailWord_1927833 prefixEnd_1927833 439957755821893812542917 := by
  unfold tailWord_1927833
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313846024797763508764153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46875897349865175672509435 70313846024797763508764153)
  ·
    refine ⟨52735384518598322631573115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70313846024797763508764153 52735384518598322631573115)
    ·
      refine ⟨79103076777897483947359673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52735384518598322631573115 79103076777897483947359673)
      ·
        refine ⟨59327307583423112960519755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79103076777897483947359673 59327307583423112960519755)
        ·
          refine ⟨88990961375134669440779633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59327307583423112960519755 88990961375134669440779633)
          ·
            refine ⟨66743221031351002080584725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88990961375134669440779633 66743221031351002080584725)
            ·
              refine ⟨3128588485844578222527409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66743221031351002080584725 3128588485844578222527409)
              ·
                refine ⟨2346441364383433666895557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128588485844578222527409 2346441364383433666895557)
                ·
                  refine ⟨439957755821893812542917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346441364383433666895557 439957755821893812542917)
                  ·
                    rfl

theorem cell21_1927833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_1927833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927833 prefixEnd_1927833 := by exact prefixLift 1927833
  have htrace : WordTrace (prefixWord ++ tailWord_1927833) baseStart_1927833 baseEnd_1927833 := by
    simpa [prefixWord, tailWord_1927833, baseEnd_1927833] using wordTrace_append hprefix tailTrace_1927833
  have hstable : (prefixWord ++ tailWord_1927833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927833).length < 2 ^ (prefixWord ++ tailWord_1927833).sum := by decide
  have hdescent : baseEnd_1927833 < baseStart_1927833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927836 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_1927836 : Nat := 118140960795 + 1927836 * 2 ^ 59
def prefixEnd_1927836 : Nat := 4983230072969 + 3 ^ 40 * 1927836 * 2
def baseEnd_1927836 : Nat := 439958440462766473992911

theorem tailTrace_1927836 : CollatzResearch.WordTrace tailWord_1927836 prefixEnd_1927836 439958440462766473992911 := by
  unfold tailWord_1927836
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156977721893447510561681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46875970295857930014082241 35156977721893447510561681)
  ·
    refine ⟨26367733291420085632921261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35156977721893447510561681 26367733291420085632921261)
    ·
      refine ⟨9887899984282532112345473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26367733291420085632921261 9887899984282532112345473)
      ·
        refine ⟨7415924988211899084259105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9887899984282532112345473 7415924988211899084259105)
        ·
          refine ⟨5561943741158924313194329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7415924988211899084259105 5561943741158924313194329)
          ·
            refine ⟨4171457805869193234895747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561943741158924313194329 4171457805869193234895747)
            ·
              refine ⟨6257186708803789852343621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171457805869193234895747 6257186708803789852343621)
              ·
                refine ⟨1173222507900710597314429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6257186708803789852343621 1173222507900710597314429)
                ·
                  refine ⟨439958440462766473992911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173222507900710597314429 439958440462766473992911)
                  ·
                    rfl

theorem cell21_1927836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_1927836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927836 prefixEnd_1927836 := by exact prefixLift 1927836
  have htrace : WordTrace (prefixWord ++ tailWord_1927836) baseStart_1927836 baseEnd_1927836 := by
    simpa [prefixWord, tailWord_1927836, baseEnd_1927836] using wordTrace_append hprefix tailTrace_1927836
  have hstable : (prefixWord ++ tailWord_1927836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927836).length < 2 ^ (prefixWord ++ tailWord_1927836).sum := by decide
  have hdescent : baseEnd_1927836 < baseStart_1927836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1927895 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 3]
def baseStart_1927895 : Nat := 118140960795 + 1927895 * 2 ^ 59
def prefixEnd_1927895 : Nat := 4983230072969 + 3 ^ 40 * 1927895 * 2
def baseEnd_1927895 : Nat := 439971905066595482509457

theorem tailTrace_1927895 : CollatzResearch.WordTrace tailWord_1927895 prefixEnd_1927895 439971905066595482509457 := by
  unfold tailWord_1927895
  simp only [CollatzResearch.WordTrace]
  refine ⟨70316107350573148097521139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46877404900382098731680759 70316107350573148097521139)
  ·
    refine ⟨105474161025859722146281709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70316107350573148097521139 105474161025859722146281709)
    ·
      refine ⟨39552810384697395804855641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105474161025859722146281709 39552810384697395804855641)
      ·
        refine ⟨29664607788523046853641731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39552810384697395804855641 29664607788523046853641731)
        ·
          refine ⟨44496911682784570280462597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29664607788523046853641731 44496911682784570280462597)
          ·
            refine ⟨8343170940522106927586737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44496911682784570280462597 8343170940522106927586737)
            ·
              refine ⟨6257378205391580195690053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8343170940522106927586737 6257378205391580195690053)
              ·
                refine ⟨1173258413510921286691885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6257378205391580195690053 1173258413510921286691885)
                ·
                  refine ⟨439971905066595482509457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173258413510921286691885 439971905066595482509457)
                  ·
                    rfl

theorem cell21_1927895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3].length) (baseStart_1927895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1927895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1927895 prefixEnd_1927895 := by exact prefixLift 1927895
  have htrace : WordTrace (prefixWord ++ tailWord_1927895) baseStart_1927895 baseEnd_1927895 := by
    simpa [prefixWord, tailWord_1927895, baseEnd_1927895] using wordTrace_append hprefix tailTrace_1927895
  have hstable : (prefixWord ++ tailWord_1927895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1927895).length < 2 ^ (prefixWord ++ tailWord_1927895).sum := by decide
  have hdescent : baseEnd_1927895 < baseStart_1927895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1927895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928044 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1928044 : Nat := 118140960795 + 1928044 * 2 ^ 59
def prefixEnd_1928044 : Nat := 4983230072969 + 3 ^ 40 * 1928044 * 2
def baseEnd_1928044 : Nat := 440005908896604334525819

theorem tailTrace_1928044 : CollatzResearch.WordTrace tailWord_1928044 prefixEnd_1928044 440005908896604334525819 := by
  unfold tailWord_1928044
  simp only [CollatzResearch.WordTrace]
  refine ⟨35160770913516673272347593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46881027884688897696463457 35160770913516673272347593)
  ·
    refine ⟨26370578185137504954260695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35160770913516673272347593 26370578185137504954260695)
    ·
      refine ⟨39555867277706257431391043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26370578185137504954260695 39555867277706257431391043)
      ·
        refine ⟨59333800916559386147086565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39555867277706257431391043 59333800916559386147086565)
        ·
          refine ⟨11125087671854884902578731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59333800916559386147086565 11125087671854884902578731)
          ·
            refine ⟨16687631507782327353868097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125087671854884902578731 16687631507782327353868097)
            ·
              refine ⟨12515723630836745515401073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16687631507782327353868097 12515723630836745515401073)
              ·
                refine ⟨9386792723127559136550805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12515723630836745515401073 9386792723127559136550805)
                ·
                  refine ⟨440005908896604334525819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9386792723127559136550805 440005908896604334525819)
                  ·
                    rfl

theorem cell21_1928044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1928044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928044 prefixEnd_1928044 := by exact prefixLift 1928044
  have htrace : WordTrace (prefixWord ++ tailWord_1928044) baseStart_1928044 baseEnd_1928044 := by
    simpa [prefixWord, tailWord_1928044, baseEnd_1928044] using wordTrace_append hprefix tailTrace_1928044
  have hstable : (prefixWord ++ tailWord_1928044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928044).length < 2 ^ (prefixWord ++ tailWord_1928044).sum := by decide
  have hdescent : baseEnd_1928044 < baseStart_1928044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928061 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1928061 : Nat := 118140960795 + 1928061 * 2 ^ 59
def prefixEnd_1928061 : Nat := 4983230072969 + 3 ^ 40 * 1928061 * 2
def baseEnd_1928061 : Nat := 440009788528216082742451

theorem tailTrace_1928061 : CollatzResearch.WordTrace tailWord_1928061 prefixEnd_1928061 440009788528216082742451 := by
  unfold tailWord_1928061
  simp only [CollatzResearch.WordTrace]
  refine ⟨70322161867971758448064037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46881441245314505632042691 70322161867971758448064037)
  ·
    refine ⟨13185405350244704709012007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70322161867971758448064037 13185405350244704709012007)
    ·
      refine ⟨19778108025367057063518011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13185405350244704709012007 19778108025367057063518011)
      ·
        refine ⟨29667162038050585595277017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778108025367057063518011 29667162038050585595277017)
        ·
          refine ⟨22250371528537939196457763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29667162038050585595277017 22250371528537939196457763)
          ·
            refine ⟨33375557292806908794686645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22250371528537939196457763 33375557292806908794686645)
            ·
              refine ⟨3128958496200647699501873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33375557292806908794686645 3128958496200647699501873)
              ·
                refine ⟨2346718872150485774626405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128958496200647699501873 2346718872150485774626405)
                ·
                  refine ⟨440009788528216082742451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2346718872150485774626405 440009788528216082742451)
                  ·
                    rfl

theorem cell21_1928061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1928061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928061 prefixEnd_1928061 := by exact prefixLift 1928061
  have htrace : WordTrace (prefixWord ++ tailWord_1928061) baseStart_1928061 baseEnd_1928061 := by
    simpa [prefixWord, tailWord_1928061, baseEnd_1928061] using wordTrace_append hprefix tailTrace_1928061
  have hstable : (prefixWord ++ tailWord_1928061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928061).length < 2 ^ (prefixWord ++ tailWord_1928061).sum := by decide
  have hdescent : baseEnd_1928061 < baseStart_1928061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928092 : List Nat := [2, 2, 3, 3, 2, 1, 1, 7]
def baseStart_1928092 : Nat := 118140960795 + 1928092 * 2 ^ 59
def prefixEnd_1928092 : Nat := 4983230072969 + 3 ^ 40 * 1928092 * 2
def baseEnd_1928092 : Nat := 146672287716855639241907

theorem tailTrace_1928092 : CollatzResearch.WordTrace tailWord_1928092 prefixEnd_1928092 146672287716855639241907 := by
  unfold tailWord_1928092
  simp only [CollatzResearch.WordTrace]
  refine ⟨35161646265429725371221265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46882195020572967161628353 35161646265429725371221265)
  ·
    refine ⟨26371234699072294028415949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35161646265429725371221265 26371234699072294028415949)
    ·
      refine ⟨9889213012152110260655981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26371234699072294028415949 9889213012152110260655981)
      ·
        refine ⟨3708454879557041347745993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9889213012152110260655981 3708454879557041347745993)
        ·
          refine ⟨2781341159667781010809495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3708454879557041347745993 2781341159667781010809495)
          ·
            refine ⟨4172011739501671516214243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781341159667781010809495 4172011739501671516214243)
            ·
              refine ⟨6258017609252507274321365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172011739501671516214243 6258017609252507274321365)
              ·
                refine ⟨146672287716855639241907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6258017609252507274321365 146672287716855639241907)
                ·
                  rfl

theorem cell21_1928092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_1928092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928092 prefixEnd_1928092 := by exact prefixLift 1928092
  have htrace : WordTrace (prefixWord ++ tailWord_1928092) baseStart_1928092 baseEnd_1928092 := by
    simpa [prefixWord, tailWord_1928092, baseEnd_1928092] using wordTrace_append hprefix tailTrace_1928092
  have hstable : (prefixWord ++ tailWord_1928092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928092).length < 2 ^ (prefixWord ++ tailWord_1928092).sum := by decide
  have hdescent : baseEnd_1928092 < baseStart_1928092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928109 : List Nat := [1, 5, 2, 3, 1, 2, 7]
def baseStart_1928109 : Nat := 118140960795 + 1928109 * 2 ^ 59
def prefixEnd_1928109 : Nat := 4983230072969 + 3 ^ 40 * 1928109 * 2
def baseEnd_1928109 : Nat := 48891193642464296215817

theorem tailTrace_1928109 : CollatzResearch.WordTrace tailWord_1928109 prefixEnd_1928109 48891193642464296215817 := by
  unfold tailWord_1928109
  simp only [CollatzResearch.WordTrace]
  refine ⟨70323912571797862645811381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46882608381198575097207587 70323912571797862645811381)
  ·
    refine ⟨6592866803606049623044817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70323912571797862645811381 6592866803606049623044817)
    ·
      refine ⟨4944650102704537217283613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592866803606049623044817 4944650102704537217283613)
      ·
        refine ⟨1854243788514201456481355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4944650102704537217283613 1854243788514201456481355)
        ·
          refine ⟨2781365682771302184722033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854243788514201456481355 2781365682771302184722033)
          ·
            refine ⟨2086024262078476638541525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781365682771302184722033 2086024262078476638541525)
            ·
              refine ⟨48891193642464296215817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2086024262078476638541525 48891193642464296215817)
              ·
                rfl

theorem cell21_1928109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 7].length) (baseStart_1928109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928109 prefixEnd_1928109 := by exact prefixLift 1928109
  have htrace : WordTrace (prefixWord ++ tailWord_1928109) baseStart_1928109 baseEnd_1928109 := by
    simpa [prefixWord, tailWord_1928109, baseEnd_1928109] using wordTrace_append hprefix tailTrace_1928109
  have hstable : (prefixWord ++ tailWord_1928109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928109).length < 2 ^ (prefixWord ++ tailWord_1928109).sum := by decide
  have hdescent : baseEnd_1928109 < baseStart_1928109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928120 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1928120 : Nat := 118140960795 + 1928120 * 2 ^ 59
def prefixEnd_1928120 : Nat := 4983230072969 + 3 ^ 40 * 1928120 * 2
def baseEnd_1928120 : Nat := 440023253132045091258997

theorem tailTrace_1928120 : CollatzResearch.WordTrace tailWord_1928120 prefixEnd_1928120 440023253132045091258997 := by
  unfold tailWord_1928120
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162156887379005762230907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46882875849838674349641209 35162156887379005762230907)
  ·
    refine ⟨52743235331068508643346361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35162156887379005762230907 52743235331068508643346361)
    ·
      refine ⟨39557426498301381482509771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52743235331068508643346361 39557426498301381482509771)
      ·
        refine ⟨59336139747452072223764657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39557426498301381482509771 59336139747452072223764657)
        ·
          refine ⟨44502104810589054167823493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59336139747452072223764657 44502104810589054167823493)
          ·
            refine ⟨8344144651985447656466905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44502104810589054167823493 8344144651985447656466905)
            ·
              refine ⟨6258108488989085742350179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344144651985447656466905 6258108488989085742350179)
              ·
                refine ⟨9387162733483628613525269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258108488989085742350179 9387162733483628613525269)
                ·
                  refine ⟨440023253132045091258997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9387162733483628613525269 440023253132045091258997)
                  ·
                    rfl

theorem cell21_1928120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1928120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928120 prefixEnd_1928120 := by exact prefixLift 1928120
  have htrace : WordTrace (prefixWord ++ tailWord_1928120) baseStart_1928120 baseEnd_1928120 := by
    simpa [prefixWord, tailWord_1928120, baseEnd_1928120] using wordTrace_append hprefix tailTrace_1928120
  have hstable : (prefixWord ++ tailWord_1928120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928120).length < 2 ^ (prefixWord ++ tailWord_1928120).sum := by decide
  have hdescent : baseEnd_1928120 < baseStart_1928120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928174 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_1928174 : Nat := 118140960795 + 1928174 * 2 ^ 59
def prefixEnd_1928174 : Nat := 4983230072969 + 3 ^ 40 * 1928174 * 2
def baseEnd_1928174 : Nat := 440035576667752997358887

theorem tailTrace_1928174 : CollatzResearch.WordTrace tailWord_1928174 prefixEnd_1928174 440035576667752997358887 := by
  unfold tailWord_1928174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790785414570297343365947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46884188877708252497951717 8790785414570297343365947)
  ·
    refine ⟨13186178121855446015048921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8790785414570297343365947 13186178121855446015048921)
    ·
      refine ⟨9889633591391584511286691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13186178121855446015048921 9889633591391584511286691)
      ·
        refine ⟨14834450387087376766930037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889633591391584511286691 14834450387087376766930037)
        ·
          refine ⟨1390729723789441571899691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14834450387087376766930037 1390729723789441571899691)
          ·
            refine ⟨2086094585684162357849537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390729723789441571899691 2086094585684162357849537)
            ·
              refine ⟨1564570939263121768387153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2086094585684162357849537 1564570939263121768387153)
              ·
                refine ⟨1173428204447341326290365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564570939263121768387153 1173428204447341326290365)
                ·
                  refine ⟨440035576667752997358887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173428204447341326290365 440035576667752997358887)
                  ·
                    rfl

theorem cell21_1928174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_1928174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928174 prefixEnd_1928174 := by exact prefixLift 1928174
  have htrace : WordTrace (prefixWord ++ tailWord_1928174) baseStart_1928174 baseEnd_1928174 := by
    simpa [prefixWord, tailWord_1928174, baseEnd_1928174] using wordTrace_append hprefix tailTrace_1928174
  have hstable : (prefixWord ++ tailWord_1928174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928174).length < 2 ^ (prefixWord ++ tailWord_1928174).sum := by decide
  have hdescent : baseEnd_1928174 < baseStart_1928174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928278 : List Nat := [5, 2, 2, 1, 3, 1, 7]
def baseStart_1928278 : Nat := 118140960795 + 1928278 * 2 ^ 59
def prefixEnd_1928278 : Nat := 4983230072969 + 3 ^ 40 * 1928278 * 2
def baseEnd_1928278 : Nat := 48895478987185769736149

theorem tailTrace_1928278 : CollatzResearch.WordTrace tailWord_1928278 prefixEnd_1928278 48895478987185769736149 := by
  unfold tailWord_1928278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395629781761600281794593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46886717672123736339142325 4395629781761600281794593)
  ·
    refine ⟨3296722336321200211345945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4395629781761600281794593 3296722336321200211345945)
    ·
      refine ⟨2472541752240900158509459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296722336321200211345945 2472541752240900158509459)
      ·
        refine ⟨3708812628361350237764189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472541752240900158509459 3708812628361350237764189)
        ·
          refine ⟨1390804735635506339161571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3708812628361350237764189 1390804735635506339161571)
          ·
            refine ⟨2086207103453259508742357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390804735635506339161571 2086207103453259508742357)
            ·
              refine ⟨48895478987185769736149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2086207103453259508742357 48895478987185769736149)
              ·
                rfl

theorem cell21_1928278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 7].length) (baseStart_1928278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928278 prefixEnd_1928278 := by exact prefixLift 1928278
  have htrace : WordTrace (prefixWord ++ tailWord_1928278) baseStart_1928278 baseEnd_1928278 := by
    simpa [prefixWord, tailWord_1928278, baseEnd_1928278] using wordTrace_append hprefix tailTrace_1928278
  have hstable : (prefixWord ++ tailWord_1928278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928278).length < 2 ^ (prefixWord ++ tailWord_1928278).sum := by decide
  have hdescent : baseEnd_1928278 < baseStart_1928278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928317 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1928317 : Nat := 118140960795 + 1928317 * 2 ^ 59
def prefixEnd_1928317 : Nat := 4983230072969 + 3 ^ 40 * 1928317 * 2
def baseEnd_1928317 : Nat := 440068211216016526475261

theorem tailTrace_1928317 : CollatzResearch.WordTrace tailWord_1928317 prefixEnd_1928317 440068211216016526475261 := by
  unfold tailWord_1928317
  simp only [CollatzResearch.WordTrace]
  refine ⟨70331498955044314169383205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46887665970029542779588803 70331498955044314169383205)
  ·
    refine ⟨13187156054070808906759351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70331498955044314169383205 13187156054070808906759351)
    ·
      refine ⟨19780734081106213360139027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13187156054070808906759351 19780734081106213360139027)
      ·
        refine ⟨29671101121659320040208541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19780734081106213360139027 29671101121659320040208541)
        ·
          refine ⟨11126662920622245015078203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29671101121659320040208541 11126662920622245015078203)
          ·
            refine ⟨16689994380933367522617305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126662920622245015078203 16689994380933367522617305)
            ·
              refine ⟨12517495785700025641962979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16689994380933367522617305 12517495785700025641962979)
              ·
                refine ⟨18776243678550038462944469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12517495785700025641962979 18776243678550038462944469)
                ·
                  refine ⟨440068211216016526475261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18776243678550038462944469 440068211216016526475261)
                  ·
                    rfl

theorem cell21_1928317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1928317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928317 prefixEnd_1928317 := by exact prefixLift 1928317
  have htrace : WordTrace (prefixWord ++ tailWord_1928317) baseStart_1928317 baseEnd_1928317 := by
    simpa [prefixWord, tailWord_1928317, baseEnd_1928317] using wordTrace_append hprefix tailTrace_1928317
  have hstable : (prefixWord ++ tailWord_1928317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928317).length < 2 ^ (prefixWord ++ tailWord_1928317).sum := by decide
  have hdescent : baseEnd_1928317 < baseStart_1928317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928331 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_1928331 : Nat := 118140960795 + 1928331 * 2 ^ 59
def prefixEnd_1928331 : Nat := 4983230072969 + 3 ^ 40 * 1928331 * 2
def baseEnd_1928331 : Nat := 440071406206755613241899

theorem tailTrace_1928331 : CollatzResearch.WordTrace tailWord_1928331 prefixEnd_1928331 440071406206755613241899 := by
  unfold tailWord_1928331
  simp only [CollatzResearch.WordTrace]
  refine ⟨70332009576993594560392847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46888006384662396373595231 70332009576993594560392847)
  ·
    refine ⟨105498014365490391840589271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70332009576993594560392847 105498014365490391840589271)
    ·
      refine ⟨158247021548235587760883907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105498014365490391840589271 158247021548235587760883907)
      ·
        refine ⟨237370532322353381641325861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158247021548235587760883907 237370532322353381641325861)
        ·
          refine ⟨44506974810441259057748599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237370532322353381641325861 44506974810441259057748599)
          ·
            refine ⟨66760462215661888586622899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44506974810441259057748599 66760462215661888586622899)
            ·
              refine ⟨100140693323492832879934349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66760462215661888586622899 100140693323492832879934349)
              ·
                refine ⟨37552759996309812329975381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100140693323492832879934349 37552759996309812329975381)
                ·
                  refine ⟨440071406206755613241899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37552759996309812329975381 440071406206755613241899)
                  ·
                    rfl

theorem cell21_1928331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_1928331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928331 prefixEnd_1928331 := by exact prefixLift 1928331
  have htrace : WordTrace (prefixWord ++ tailWord_1928331) baseStart_1928331 baseEnd_1928331 := by
    simpa [prefixWord, tailWord_1928331, baseEnd_1928331] using wordTrace_append hprefix tailTrace_1928331
  have hstable : (prefixWord ++ tailWord_1928331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928331).length < 2 ^ (prefixWord ++ tailWord_1928331).sum := by decide
  have hdescent : baseEnd_1928331 < baseStart_1928331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928444 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_1928444 : Nat := 118140960795 + 1928444 * 2 ^ 59
def prefixEnd_1928444 : Nat := 4983230072969 + 3 ^ 40 * 1928444 * 2
def baseEnd_1928444 : Nat := 440097194346292527858335

theorem tailTrace_1928444 : CollatzResearch.WordTrace tailWord_1928444 prefixEnd_1928444 440097194346292527858335 := by
  unfold tailWord_1928444
  simp only [CollatzResearch.WordTrace]
  refine ⟨35168065512792107429628193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46890754017056143239504257 35168065512792107429628193)
  ·
    refine ⟨26376049134594080572221145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35168065512792107429628193 26376049134594080572221145)
    ·
      refine ⟨19782036850945560429165859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26376049134594080572221145 19782036850945560429165859)
      ·
        refine ⟨29673055276418340643748789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19782036850945560429165859 29673055276418340643748789)
        ·
          refine ⟨2781848932164219435351449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29673055276418340643748789 2781848932164219435351449)
          ·
            refine ⟨2086386699123164576513587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781848932164219435351449 2086386699123164576513587)
            ·
              refine ⟨3129580048684746864770381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086386699123164576513587 3129580048684746864770381)
              ·
                refine ⟨1173592518256780074288893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129580048684746864770381 1173592518256780074288893)
                ·
                  refine ⟨440097194346292527858335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173592518256780074288893 440097194346292527858335)
                  ·
                    rfl

theorem cell21_1928444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_1928444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928444 prefixEnd_1928444 := by exact prefixLift 1928444
  have htrace : WordTrace (prefixWord ++ tailWord_1928444) baseStart_1928444 baseEnd_1928444 := by
    simpa [prefixWord, tailWord_1928444, baseEnd_1928444] using wordTrace_append hprefix tailTrace_1928444
  have hstable : (prefixWord ++ tailWord_1928444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928444).length < 2 ^ (prefixWord ++ tailWord_1928444).sum := by decide
  have hdescent : baseEnd_1928444 < baseStart_1928444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928559 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_1928559 : Nat := 118140960795 + 1928559 * 2 ^ 59
def prefixEnd_1928559 : Nat := 4983230072969 + 3 ^ 40 * 1928559 * 2
def baseEnd_1928559 : Nat := 440123438913077883441433

theorem tailTrace_1928559 : CollatzResearch.WordTrace tailWord_1928559 prefixEnd_1928559 440123438913077883441433 := by
  unfold tailWord_1928559
  simp only [CollatzResearch.WordTrace]
  refine ⟨70340325420167589499692731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46893550280111726333128487 70340325420167589499692731)
  ·
    refine ⟨105510488130251384249539097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70340325420167589499692731 105510488130251384249539097)
    ·
      refine ⟨79132866097688538187154323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105510488130251384249539097 79132866097688538187154323)
      ·
        refine ⟨118699299146532807280731485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79132866097688538187154323 118699299146532807280731485)
        ·
          refine ⟨44512237179949802730274307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118699299146532807280731485 44512237179949802730274307)
          ·
            refine ⟨66768355769924704095411461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44512237179949802730274307 66768355769924704095411461)
            ·
              refine ⟨12519066706860882017889649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66768355769924704095411461 12519066706860882017889649)
              ·
                refine ⟨9389300030145661513417237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12519066706860882017889649 9389300030145661513417237)
                ·
                  refine ⟨440123438913077883441433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9389300030145661513417237 440123438913077883441433)
                  ·
                    rfl

theorem cell21_1928559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_1928559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928559 prefixEnd_1928559 := by exact prefixLift 1928559
  have htrace : WordTrace (prefixWord ++ tailWord_1928559) baseStart_1928559 baseEnd_1928559 := by
    simpa [prefixWord, tailWord_1928559, baseEnd_1928559] using wordTrace_append hprefix tailTrace_1928559
  have hstable : (prefixWord ++ tailWord_1928559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928559).length < 2 ^ (prefixWord ++ tailWord_1928559).sum := by decide
  have hdescent : baseEnd_1928559 < baseStart_1928559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928607 : List Nat := [1, 1, 2, 5, 1, 2, 4, 5]
def baseStart_1928607 : Nat := 118140960795 + 1928607 * 2 ^ 59
def prefixEnd_1928607 : Nat := 4983230072969 + 3 ^ 40 * 1928607 * 2
def baseEnd_1928607 : Nat := 146711464389013488880445

theorem tailTrace_1928607 : CollatzResearch.WordTrace tailWord_1928607 prefixEnd_1928607 146711464389013488880445 := by
  unfold tailWord_1928607
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342076123993693697440075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46894717415995795798293383 70342076123993693697440075)
  ·
    refine ⟨105513114185990540546160113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70342076123993693697440075 105513114185990540546160113)
    ·
      refine ⟨79134835639492905409620085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105513114185990540546160113 79134835639492905409620085)
      ·
        refine ⟨7418890841202459882151883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79134835639492905409620085 7418890841202459882151883)
        ·
          refine ⟨11128336261803689823227825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418890841202459882151883 11128336261803689823227825)
          ·
            refine ⟨8346252196352767367420869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11128336261803689823227825 8346252196352767367420869)
            ·
              refine ⟨1564922286816143881391413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8346252196352767367420869 1564922286816143881391413)
              ·
                refine ⟨146711464389013488880445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564922286816143881391413 146711464389013488880445)
                ·
                  rfl

theorem cell21_1928607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 5].length) (baseStart_1928607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928607 prefixEnd_1928607 := by exact prefixLift 1928607
  have htrace : WordTrace (prefixWord ++ tailWord_1928607) baseStart_1928607 baseEnd_1928607 := by
    simpa [prefixWord, tailWord_1928607, baseEnd_1928607] using wordTrace_append hprefix tailTrace_1928607
  have hstable : (prefixWord ++ tailWord_1928607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928607).length < 2 ^ (prefixWord ++ tailWord_1928607).sum := by decide
  have hdescent : baseEnd_1928607 < baseStart_1928607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928666 : List Nat := [3, 1, 1, 2, 3, 2, 2, 7]
def baseStart_1928666 : Nat := 118140960795 + 1928666 * 2 ^ 59
def prefixEnd_1928666 : Nat := 4983230072969 + 3 ^ 40 * 1928666 * 2
def baseEnd_1928666 : Nat := 146715952590289825052627

theorem tailTrace_1928666 : CollatzResearch.WordTrace tailWord_1928666 prefixEnd_1928666 146715952590289825052627 := by
  unfold tailWord_1928666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586057007694986693459463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46896152020519964515891901 17586057007694986693459463)
  ·
    refine ⟨26379085511542480040189195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17586057007694986693459463 26379085511542480040189195)
    ·
      refine ⟨39568628267313720060283793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26379085511542480040189195 39568628267313720060283793)
      ·
        refine ⟨29676471200485290045212845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39568628267313720060283793 29676471200485290045212845)
        ·
          refine ⟨11128676700181983766954817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29676471200485290045212845 11128676700181983766954817)
          ·
            refine ⟨8346507525136487825216113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11128676700181983766954817 8346507525136487825216113)
            ·
              refine ⟨6259880643852365868912085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346507525136487825216113 6259880643852365868912085)
              ·
                refine ⟨146715952590289825052627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6259880643852365868912085 146715952590289825052627)
                ·
                  rfl

theorem cell21_1928666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_1928666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928666 prefixEnd_1928666 := by exact prefixLift 1928666
  have htrace : WordTrace (prefixWord ++ tailWord_1928666) baseStart_1928666 baseEnd_1928666 := by
    simpa [prefixWord, tailWord_1928666, baseEnd_1928666] using wordTrace_append hprefix tailTrace_1928666
  have hstable : (prefixWord ++ tailWord_1928666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928666).length < 2 ^ (prefixWord ++ tailWord_1928666).sum := by decide
  have hdescent : baseEnd_1928666 < baseStart_1928666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928818 : List Nat := [3, 2, 1, 2, 3, 1, 1, 8]
def baseStart_1928818 : Nat := 118140960795 + 1928818 * 2 ^ 59
def prefixEnd_1928818 : Nat := 4983230072969 + 3 ^ 40 * 1928818 * 2
def baseEnd_1928818 : Nat := 146727515413916996208079

theorem tailTrace_1928818 : CollatzResearch.WordTrace tailWord_1928818 prefixEnd_1928818 146727515413916996208079 := by
  unfold tailWord_1928818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587442981557319183342777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46899847950819517822247405 17587442981557319183342777)
  ·
    refine ⟨13190582236167989387507083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17587442981557319183342777 13190582236167989387507083)
    ·
      refine ⟨19785873354251984081260625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13190582236167989387507083 19785873354251984081260625)
      ·
        refine ⟨14839405015688988060945469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19785873354251984081260625 14839405015688988060945469)
        ·
          refine ⟨5564776880883370522854551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14839405015688988060945469 5564776880883370522854551)
          ·
            refine ⟨8347165321325055784281827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564776880883370522854551 8347165321325055784281827)
            ·
              refine ⟨12520747981987583676422741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347165321325055784281827 12520747981987583676422741)
              ·
                refine ⟨146727515413916996208079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12520747981987583676422741 146727515413916996208079)
                ·
                  rfl

theorem cell21_1928818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_1928818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928818 prefixEnd_1928818 := by exact prefixLift 1928818
  have htrace : WordTrace (prefixWord ++ tailWord_1928818) baseStart_1928818 baseEnd_1928818 := by
    simpa [prefixWord, tailWord_1928818, baseEnd_1928818] using wordTrace_append hprefix tailTrace_1928818
  have hstable : (prefixWord ++ tailWord_1928818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928818).length < 2 ^ (prefixWord ++ tailWord_1928818).sum := by decide
  have hdescent : baseEnd_1928818 < baseStart_1928818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928821 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_1928821 : Nat := 118140960795 + 1928821 * 2 ^ 59
def prefixEnd_1928821 : Nat := 4983230072969 + 3 ^ 40 * 1928821 * 2
def baseEnd_1928821 : Nat := 440183230882623650074231

theorem tailTrace_1928821 : CollatzResearch.WordTrace tailWord_1928821 prefixEnd_1928821 440183230882623650074231 := by
  unfold tailWord_1928821
  simp only [CollatzResearch.WordTrace]
  refine ⟨70349881345218408245730317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46899920896812272163820211 70349881345218408245730317)
  ·
    refine ⟨26381205504456903092148869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70349881345218408245730317 26381205504456903092148869)
    ·
      refine ⟨4946476032085669329777913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26381205504456903092148869 4946476032085669329777913)
      ·
        refine ⟨3709857024064251997333435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4946476032085669329777913 3709857024064251997333435)
        ·
          refine ⟨5564785536096377996000153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709857024064251997333435 5564785536096377996000153)
          ·
            refine ⟨4173589152072283497000115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564785536096377996000153 4173589152072283497000115)
            ·
              refine ⟨6260383728108425245500173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173589152072283497000115 6260383728108425245500173)
              ·
                refine ⟨2347643898040659467062565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6260383728108425245500173 2347643898040659467062565)
                ·
                  refine ⟨440183230882623650074231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347643898040659467062565 440183230882623650074231)
                  ·
                    rfl

theorem cell21_1928821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_1928821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928821 prefixEnd_1928821 := by exact prefixLift 1928821
  have htrace : WordTrace (prefixWord ++ tailWord_1928821) baseStart_1928821 baseEnd_1928821 := by
    simpa [prefixWord, tailWord_1928821, baseEnd_1928821] using wordTrace_append hprefix tailTrace_1928821
  have hstable : (prefixWord ++ tailWord_1928821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928821).length < 2 ^ (prefixWord ++ tailWord_1928821).sum := by decide
  have hdescent : baseEnd_1928821 < baseStart_1928821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928832 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1928832 : Nat := 118140960795 + 1928832 * 2 ^ 59
def prefixEnd_1928832 : Nat := 4983230072969 + 3 ^ 40 * 1928832 * 2
def baseEnd_1928832 : Nat := 440185741232490075390875

theorem tailTrace_1928832 : CollatzResearch.WordTrace tailWord_1928832 prefixEnd_1928832 440185741232490075390875 := by
  unfold tailWord_1928832
  simp only [CollatzResearch.WordTrace]
  refine ⟨35175141274089278562190375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46900188365452371416253833 35175141274089278562190375)
  ·
    refine ⟨52762711911133917843285563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35175141274089278562190375 52762711911133917843285563)
    ·
      refine ⟨79144067866700876764928345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52762711911133917843285563 79144067866700876764928345)
      ·
        refine ⟨59358050900025657573696259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79144067866700876764928345 59358050900025657573696259)
        ·
          refine ⟨89037076350038486360544389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59358050900025657573696259 89037076350038486360544389)
          ·
            refine ⟨16694451815632216192602073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89037076350038486360544389 16694451815632216192602073)
            ·
              refine ⟨12520838861724162144451555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16694451815632216192602073 12520838861724162144451555)
              ·
                refine ⟨18781258292586243216677333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12520838861724162144451555 18781258292586243216677333)
                ·
                  refine ⟨440185741232490075390875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18781258292586243216677333 440185741232490075390875)
                  ·
                    rfl

theorem cell21_1928832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1928832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928832 prefixEnd_1928832 := by exact prefixLift 1928832
  have htrace : WordTrace (prefixWord ++ tailWord_1928832) baseStart_1928832 baseEnd_1928832 := by
    simpa [prefixWord, tailWord_1928832, baseEnd_1928832] using wordTrace_append hprefix tailTrace_1928832
  have hstable : (prefixWord ++ tailWord_1928832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928832).length < 2 ^ (prefixWord ++ tailWord_1928832).sum := by decide
  have hdescent : baseEnd_1928832 < baseStart_1928832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928939 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_1928939 : Nat := 118140960795 + 1928939 * 2 ^ 59
def prefixEnd_1928939 : Nat := 4983230072969 + 3 ^ 40 * 1928939 * 2
def baseEnd_1928939 : Nat := 440210160090281667107323

theorem tailTrace_1928939 : CollatzResearch.WordTrace tailWord_1928939 prefixEnd_1928939 440210160090281667107323 := by
  unfold tailWord_1928939
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354185158790914398525871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46902790105860609599017247 70354185158790914398525871)
  ·
    refine ⟨105531277738186371597788807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70354185158790914398525871 105531277738186371597788807)
    ·
      refine ⟨158296916607279557396683211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105531277738186371597788807 158296916607279557396683211)
      ·
        refine ⟨237445374910919336095024817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158296916607279557396683211 237445374910919336095024817)
        ·
          refine ⟨178084031183189502071268613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237445374910919336095024817 178084031183189502071268613)
          ·
            refine ⟨33390755846848031638362865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178084031183189502071268613 33390755846848031638362865)
            ·
              refine ⟨25043066885136023728772149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33390755846848031638362865 25043066885136023728772149)
              ·
                refine ⟨2347787520481502224572389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25043066885136023728772149 2347787520481502224572389)
                ·
                  refine ⟨440210160090281667107323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347787520481502224572389 440210160090281667107323)
                  ·
                    rfl

theorem cell21_1928939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_1928939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928939 prefixEnd_1928939 := by exact prefixLift 1928939
  have htrace : WordTrace (prefixWord ++ tailWord_1928939) baseStart_1928939 baseEnd_1928939 := by
    simpa [prefixWord, tailWord_1928939, baseEnd_1928939] using wordTrace_append hprefix tailTrace_1928939
  have hstable : (prefixWord ++ tailWord_1928939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928939).length < 2 ^ (prefixWord ++ tailWord_1928939).sum := by decide
  have hdescent : baseEnd_1928939 < baseStart_1928939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1928970 : List Nat := [3, 1, 2, 2, 1, 5, 7]
def baseStart_1928970 : Nat := 118140960795 + 1928970 * 2 ^ 59
def prefixEnd_1928970 : Nat := 4983230072969 + 3 ^ 40 * 1928970 * 2
def baseEnd_1928970 : Nat := 48913026079181389121177

theorem tailTrace_1928970 : CollatzResearch.WordTrace tailWord_1928970 prefixEnd_1928970 48913026079181389121177 := by
  unfold tailWord_1928970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17588828955419651673226091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46903543881119071128602909 17588828955419651673226091)
  ·
    refine ⟨26383243433129477509839137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17588828955419651673226091 26383243433129477509839137)
    ·
      refine ⟨19787432574847108132379353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26383243433129477509839137 19787432574847108132379353)
      ·
        refine ⟨14840574431135331099284515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19787432574847108132379353 14840574431135331099284515)
        ·
          refine ⟨22260861646702996648926773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14840574431135331099284515 22260861646702996648926773)
          ·
            refine ⟨2086955779378405935836885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22260861646702996648926773 2086955779378405935836885)
            ·
              refine ⟨48913026079181389121177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2086955779378405935836885 48913026079181389121177)
              ·
                rfl

theorem cell21_1928970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 7].length) (baseStart_1928970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1928970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1928970 prefixEnd_1928970 := by exact prefixLift 1928970
  have htrace : WordTrace (prefixWord ++ tailWord_1928970) baseStart_1928970 baseEnd_1928970 := by
    simpa [prefixWord, tailWord_1928970, baseEnd_1928970] using wordTrace_append hprefix tailTrace_1928970
  have hstable : (prefixWord ++ tailWord_1928970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1928970).length < 2 ^ (prefixWord ++ tailWord_1928970).sum := by decide
  have hdescent : baseEnd_1928970 < baseStart_1928970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1928970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929032 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_1929032 : Nat := 118140960795 + 1929032 * 2 ^ 59
def prefixEnd_1929032 : Nat := 4983230072969 + 3 ^ 40 * 1929032 * 2
def baseEnd_1929032 : Nat := 440231383957334172057133

theorem tailTrace_1929032 : CollatzResearch.WordTrace tailWord_1929032 prefixEnd_1929032 440231383957334172057133 := by
  unfold tailWord_1929032
  simp only [CollatzResearch.WordTrace]
  refine ⟨35178788573726995640830675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46905051431635994187774233 35178788573726995640830675)
  ·
    refine ⟨52768182860590493461246013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35178788573726995640830675 52768182860590493461246013)
    ·
      refine ⟨19788068572721435047967255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52768182860590493461246013 19788068572721435047967255)
      ·
        refine ⟨29682102859082152571950883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19788068572721435047967255 29682102859082152571950883)
        ·
          refine ⟨44523154288623228857926325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29682102859082152571950883 44523154288623228857926325)
          ·
            refine ⟨4174045714558427705430593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44523154288623228857926325 4174045714558427705430593)
            ·
              refine ⟨3130534285918820779072945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174045714558427705430593 3130534285918820779072945)
              ·
                refine ⟨2347900714439115584304709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130534285918820779072945 2347900714439115584304709)
                ·
                  refine ⟨440231383957334172057133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2347900714439115584304709 440231383957334172057133)
                  ·
                    rfl

theorem cell21_1929032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_1929032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929032 prefixEnd_1929032 := by exact prefixLift 1929032
  have htrace : WordTrace (prefixWord ++ tailWord_1929032) baseStart_1929032 baseEnd_1929032 := by
    simpa [prefixWord, tailWord_1929032, baseEnd_1929032] using wordTrace_append hprefix tailTrace_1929032
  have hstable : (prefixWord ++ tailWord_1929032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929032).length < 2 ^ (prefixWord ++ tailWord_1929032).sum := by decide
  have hdescent : baseEnd_1929032 < baseStart_1929032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929091 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_1929091 : Nat := 118140960795 + 1929091 * 2 ^ 59
def prefixEnd_1929091 : Nat := 4983230072969 + 3 ^ 40 * 1929091 * 2
def baseEnd_1929091 : Nat := 440244848561163180573679

theorem tailTrace_1929091 : CollatzResearch.WordTrace tailWord_1929091 prefixEnd_1929091 440244848561163180573679 := by
  unfold tailWord_1929091
  simp only [CollatzResearch.WordTrace]
  refine ⟨70359729054240244358059127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46906486036160162905372751 70359729054240244358059127)
  ·
    refine ⟨105539593581360366537088691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70359729054240244358059127 105539593581360366537088691)
    ·
      refine ⟨158309390372040549805633037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105539593581360366537088691 158309390372040549805633037)
      ·
        refine ⟨59366021389515206177112389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158309390372040549805633037 59366021389515206177112389)
        ·
          refine ⟨11131129010534101158208573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59366021389515206177112389 11131129010534101158208573)
          ·
            refine ⟨4174173378950287934328215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11131129010534101158208573 4174173378950287934328215)
            ·
              refine ⟨6261260068425431901492323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174173378950287934328215 6261260068425431901492323)
              ·
                refine ⟨9391890102638147852238485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261260068425431901492323 9391890102638147852238485)
                ·
                  refine ⟨440244848561163180573679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9391890102638147852238485 440244848561163180573679)
                  ·
                    rfl

theorem cell21_1929091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_1929091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929091 prefixEnd_1929091 := by exact prefixLift 1929091
  have htrace : WordTrace (prefixWord ++ tailWord_1929091) baseStart_1929091 baseEnd_1929091 := by
    simpa [prefixWord, tailWord_1929091, baseEnd_1929091] using wordTrace_append hprefix tailTrace_1929091
  have hstable : (prefixWord ++ tailWord_1929091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929091).length < 2 ^ (prefixWord ++ tailWord_1929091).sum := by decide
  have hdescent : baseEnd_1929091 < baseStart_1929091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929167 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_1929167 : Nat := 118140960795 + 1929167 * 2 ^ 59
def prefixEnd_1929167 : Nat := 4983230072969 + 3 ^ 40 * 1929167 * 2
def baseEnd_1929167 : Nat := 440262192796603937306857

theorem tailTrace_1929167 : CollatzResearch.WordTrace tailWord_1929167 prefixEnd_1929167 440262192796603937306857 := by
  unfold tailWord_1929167
  simp only [CollatzResearch.WordTrace]
  refine ⟨70362501001964909337825755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46908334001309939558550503 70362501001964909337825755)
  ·
    refine ⟨105543751502947364006738633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70362501001964909337825755 105543751502947364006738633)
    ·
      refine ⟨79157813627210523005053975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105543751502947364006738633 79157813627210523005053975)
      ·
        refine ⟨118736720440815784507580963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79157813627210523005053975 118736720440815784507580963)
        ·
          refine ⟨178105080661223676761371445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118736720440815784507580963 178105080661223676761371445)
          ·
            refine ⟨16697351311989719696378573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178105080661223676761371445 16697351311989719696378573)
            ·
              refine ⟨6261506741996144886141965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16697351311989719696378573 6261506741996144886141965)
              ·
                refine ⟨2348065028248554332303237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6261506741996144886141965 2348065028248554332303237)
                ·
                  refine ⟨440262192796603937306857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348065028248554332303237 440262192796603937306857)
                  ·
                    rfl

theorem cell21_1929167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_1929167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929167 prefixEnd_1929167 := by exact prefixLift 1929167
  have htrace : WordTrace (prefixWord ++ tailWord_1929167) baseStart_1929167 baseEnd_1929167 := by
    simpa [prefixWord, tailWord_1929167, baseEnd_1929167] using wordTrace_append hprefix tailTrace_1929167
  have hstable : (prefixWord ++ tailWord_1929167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929167).length < 2 ^ (prefixWord ++ tailWord_1929167).sum := by decide
  have hdescent : baseEnd_1929167 < baseStart_1929167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929212 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1929212 : Nat := 118140960795 + 1929212 * 2 ^ 59
def prefixEnd_1929212 : Nat := 4983230072969 + 3 ^ 40 * 1929212 * 2
def baseEnd_1929212 : Nat := 440272462409693859056765

theorem tailTrace_1929212 : CollatzResearch.WordTrace tailWord_1929212 prefixEnd_1929212 440272462409693859056765 := by
  unfold tailWord_1929212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35182071143400941011606945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46909428191201254682142593 35182071143400941011606945)
  ·
    refine ⟨26386553357550705758705209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35182071143400941011606945 26386553357550705758705209)
    ·
      refine ⟨19789915018163029319028907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26386553357550705758705209 19789915018163029319028907)
      ·
        refine ⟨29684872527244543978543361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789915018163029319028907 29684872527244543978543361)
        ·
          refine ⟨22263654395433407983907521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29684872527244543978543361 22263654395433407983907521)
          ·
            refine ⟨16697740796575055987930641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22263654395433407983907521 16697740796575055987930641)
            ·
              refine ⟨12523305597431291990947981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16697740796575055987930641 12523305597431291990947981)
              ·
                refine ⟨4696239599036734496605493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12523305597431291990947981 4696239599036734496605493)
                ·
                  refine ⟨440272462409693859056765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696239599036734496605493 440272462409693859056765)
                  ·
                    rfl

theorem cell21_1929212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1929212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929212 prefixEnd_1929212 := by exact prefixLift 1929212
  have htrace : WordTrace (prefixWord ++ tailWord_1929212) baseStart_1929212 baseEnd_1929212 := by
    simpa [prefixWord, tailWord_1929212, baseEnd_1929212] using wordTrace_append hprefix tailTrace_1929212
  have hstable : (prefixWord ++ tailWord_1929212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929212).length < 2 ^ (prefixWord ++ tailWord_1929212).sum := by decide
  have hdescent : baseEnd_1929212 < baseStart_1929212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929319 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_1929319 : Nat := 118140960795 + 1929319 * 2 ^ 59
def prefixEnd_1929319 : Nat := 4983230072969 + 3 ^ 40 * 1929319 * 2
def baseEnd_1929319 : Nat := 440296881267485450773213

theorem tailTrace_1929319 : CollatzResearch.WordTrace tailWord_1929319 prefixEnd_1929319 440296881267485450773213 := by
  unfold tailWord_1929319
  simp only [CollatzResearch.WordTrace]
  refine ⟨70368044897414239297359011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46912029931609492864906007 70368044897414239297359011)
  ·
    refine ⟨105552067346121358946038517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70368044897414239297359011 105552067346121358946038517)
    ·
      refine ⟨9895506313698877401191111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105552067346121358946038517 9895506313698877401191111)
      ·
        refine ⟨14843259470548316101786667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895506313698877401191111 14843259470548316101786667)
        ·
          refine ⟨22264889205822474152680001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14843259470548316101786667 22264889205822474152680001)
          ·
            refine ⟨16698666904366855614510001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22264889205822474152680001 16698666904366855614510001)
            ·
              refine ⟨12524000178275141710882501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16698666904366855614510001 12524000178275141710882501)
              ·
                refine ⟨2348250033426589070790469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12524000178275141710882501 2348250033426589070790469)
                ·
                  refine ⟨440296881267485450773213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348250033426589070790469 440296881267485450773213)
                  ·
                    rfl

theorem cell21_1929319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_1929319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929319 prefixEnd_1929319 := by exact prefixLift 1929319
  have htrace : WordTrace (prefixWord ++ tailWord_1929319) baseStart_1929319 baseEnd_1929319 := by
    simpa [prefixWord, tailWord_1929319, baseEnd_1929319] using wordTrace_append hprefix tailTrace_1929319
  have hstable : (prefixWord ++ tailWord_1929319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929319).length < 2 ^ (prefixWord ++ tailWord_1929319).sum := by decide
  have hdescent : baseEnd_1929319 < baseStart_1929319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929322 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_1929322 : Nat := 118140960795 + 1929322 * 2 ^ 59
def prefixEnd_1929322 : Nat := 4983230072969 + 3 ^ 40 * 1929322 * 2
def baseEnd_1929322 : Nat := 440297565908358112223207

theorem tailTrace_1929322 : CollatzResearch.WordTrace tailWord_1929322 prefixEnd_1929322 440297565908358112223207 := by
  unfold tailWord_1929322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17592038579100842702429555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46912102877602247206478813 17592038579100842702429555)
  ·
    refine ⟨26388057868651264053644333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17592038579100842702429555 26388057868651264053644333)
    ·
      refine ⟨9895521700744224020116625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26388057868651264053644333 9895521700744224020116625)
      ·
        refine ⟨7421641275558168015087469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9895521700744224020116625 7421641275558168015087469)
        ·
          refine ⟨2783115478334313005657801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7421641275558168015087469 2783115478334313005657801)
          ·
            refine ⟨2087336608750734754243351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783115478334313005657801 2087336608750734754243351)
            ·
              refine ⟨3131004913126102131365027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087336608750734754243351 3131004913126102131365027)
              ·
                refine ⟨4696507369689153197047541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131004913126102131365027 4696507369689153197047541)
                ·
                  refine ⟨440297565908358112223207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696507369689153197047541 440297565908358112223207)
                  ·
                    rfl

theorem cell21_1929322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_1929322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929322 prefixEnd_1929322 := by exact prefixLift 1929322
  have htrace : WordTrace (prefixWord ++ tailWord_1929322) baseStart_1929322 baseEnd_1929322 := by
    simpa [prefixWord, tailWord_1929322, baseEnd_1929322] using wordTrace_append hprefix tailTrace_1929322
  have hstable : (prefixWord ++ tailWord_1929322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929322).length < 2 ^ (prefixWord ++ tailWord_1929322).sum := by decide
  have hdescent : baseEnd_1929322 < baseStart_1929322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929381 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 3]
def baseStart_1929381 : Nat := 118140960795 + 1929381 * 2 ^ 59
def prefixEnd_1929381 : Nat := 4983230072969 + 3 ^ 40 * 1929381 * 2
def baseEnd_1929381 : Nat := 440311030512187120739753

theorem tailTrace_1929381 : CollatzResearch.WordTrace tailWord_1929381 prefixEnd_1929381 440311030512187120739753 := by
  unfold tailWord_1929381
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370306223189623886115997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46913537482126415924077331 70370306223189623886115997)
  ·
    refine ⟨26388864833696108957293499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70370306223189623886115997 26388864833696108957293499)
    ·
      refine ⟨39583297250544163435940249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26388864833696108957293499 39583297250544163435940249)
      ·
        refine ⟨29687472937908122576955187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39583297250544163435940249 29687472937908122576955187)
        ·
          refine ⟨44531209406862183865432781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29687472937908122576955187 44531209406862183865432781)
          ·
            refine ⟨16699203527573318949537293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44531209406862183865432781 16699203527573318949537293)
            ·
              refine ⟨6262201322839994606076485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16699203527573318949537293 6262201322839994606076485)
              ·
                refine ⟨1174162748032498988639341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6262201322839994606076485 1174162748032498988639341)
                ·
                  refine ⟨440311030512187120739753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174162748032498988639341 440311030512187120739753)
                  ·
                    rfl

theorem cell21_1929381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_1929381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929381 prefixEnd_1929381 := by exact prefixLift 1929381
  have htrace : WordTrace (prefixWord ++ tailWord_1929381) baseStart_1929381 baseEnd_1929381 := by
    simpa [prefixWord, tailWord_1929381, baseEnd_1929381] using wordTrace_append hprefix tailTrace_1929381
  have hstable : (prefixWord ++ tailWord_1929381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929381).length < 2 ^ (prefixWord ++ tailWord_1929381).sum := by decide
  have hdescent : baseEnd_1929381 < baseStart_1929381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929423 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_1929423 : Nat := 118140960795 + 1929423 * 2 ^ 59
def prefixEnd_1929423 : Nat := 4983230072969 + 3 ^ 40 * 1929423 * 2
def baseEnd_1929423 : Nat := 440320615484404381039667

theorem tailTrace_1929423 : CollatzResearch.WordTrace tailWord_1929423 prefixEnd_1929423 440320615484404381039667 := by
  unfold tailWord_1929423
  simp only [CollatzResearch.WordTrace]
  refine ⟨70371838089037465059144923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46914558726024976706096615 70371838089037465059144923)
  ·
    refine ⟨105557757133556197588717385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70371838089037465059144923 105557757133556197588717385)
    ·
      refine ⟨79168317850167148191538039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105557757133556197588717385 79168317850167148191538039)
      ·
        refine ⟨118752476775250722287307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79168317850167148191538039 118752476775250722287307059)
        ·
          refine ⟨178128715162876083430960589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118752476775250722287307059 178128715162876083430960589)
          ·
            refine ⟨66798268186078531286610221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178128715162876083430960589 66798268186078531286610221)
            ·
              refine ⟨25049350569779449232478833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66798268186078531286610221 25049350569779449232478833)
              ·
                refine ⟨18787012927334586924359125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25049350569779449232478833 18787012927334586924359125)
                ·
                  refine ⟨440320615484404381039667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18787012927334586924359125 440320615484404381039667)
                  ·
                    rfl

theorem cell21_1929423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_1929423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929423 prefixEnd_1929423 := by exact prefixLift 1929423
  have htrace : WordTrace (prefixWord ++ tailWord_1929423) baseStart_1929423 baseEnd_1929423 := by
    simpa [prefixWord, tailWord_1929423, baseEnd_1929423] using wordTrace_append hprefix tailTrace_1929423
  have hstable : (prefixWord ++ tailWord_1929423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929423).length < 2 ^ (prefixWord ++ tailWord_1929423).sum := by decide
  have hdescent : baseEnd_1929423 < baseStart_1929423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929429 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 4]
def baseStart_1929429 : Nat := 118140960795 + 1929429 * 2 ^ 59
def prefixEnd_1929429 : Nat := 4983230072969 + 3 ^ 40 * 1929429 * 2
def baseEnd_1929429 : Nat := 440321984766149703939655

theorem tailTrace_1929429 : CollatzResearch.WordTrace tailWord_1929429 prefixEnd_1929429 440321984766149703939655 := by
  unfold tailWord_1929429
  simp only [CollatzResearch.WordTrace]
  refine ⟨70372056927015728083863341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46914704618010485389242227 70372056927015728083863341)
  ·
    refine ⟨26389521347630898031448753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70372056927015728083863341 26389521347630898031448753)
    ·
      refine ⟨19792141010723173523586565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26389521347630898031448753 19792141010723173523586565)
      ·
        refine ⟨3711026439510595035672481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19792141010723173523586565 3711026439510595035672481)
        ·
          refine ⟨2783269829632946276754361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711026439510595035672481 2783269829632946276754361)
          ·
            refine ⟨2087452372224709707565771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2783269829632946276754361 2087452372224709707565771)
            ·
              refine ⟨3131178558337064561348657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087452372224709707565771 3131178558337064561348657)
              ·
                refine ⟨2348383918752798421011493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131178558337064561348657 2348383918752798421011493)
                ·
                  refine ⟨440321984766149703939655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2348383918752798421011493 440321984766149703939655)
                  ·
                    rfl

theorem cell21_1929429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_1929429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929429 prefixEnd_1929429 := by exact prefixLift 1929429
  have htrace : WordTrace (prefixWord ++ tailWord_1929429) baseStart_1929429 baseEnd_1929429 := by
    simpa [prefixWord, tailWord_1929429, baseEnd_1929429] using wordTrace_append hprefix tailTrace_1929429
  have hstable : (prefixWord ++ tailWord_1929429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929429).length < 2 ^ (prefixWord ++ tailWord_1929429).sum := by decide
  have hdescent : baseEnd_1929429 < baseStart_1929429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929440 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_1929440 : Nat := 118140960795 + 1929440 * 2 ^ 59
def prefixEnd_1929440 : Nat := 4983230072969 + 3 ^ 40 * 1929440 * 2
def baseEnd_1929440 : Nat := 440324495116016129256299

theorem tailTrace_1929440 : CollatzResearch.WordTrace tailWord_1929440 prefixEnd_1929440 440324495116016129256299 := by
  unfold tailWord_1929440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35186229064987938481256887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46914972086650584641675849 35186229064987938481256887)
  ·
    refine ⟨52779343597481907721885331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35186229064987938481256887 52779343597481907721885331)
    ·
      refine ⟨79169015396222861582827997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52779343597481907721885331 79169015396222861582827997)
      ·
        refine ⟨29688380773583573093560499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79169015396222861582827997 29688380773583573093560499)
        ·
          refine ⟨44532571160375359640340749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29688380773583573093560499 44532571160375359640340749)
          ·
            refine ⟨16699714185140759865127781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44532571160375359640340749 16699714185140759865127781)
            ·
              refine ⟨3131196409713892474711459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16699714185140759865127781 3131196409713892474711459)
              ·
                refine ⟨4696794614570838712067189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131196409713892474711459 4696794614570838712067189)
                ·
                  refine ⟨440324495116016129256299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696794614570838712067189 440324495116016129256299)
                  ·
                    rfl

theorem cell21_1929440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_1929440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929440 prefixEnd_1929440 := by exact prefixLift 1929440
  have htrace : WordTrace (prefixWord ++ tailWord_1929440) baseStart_1929440 baseEnd_1929440 := by
    simpa [prefixWord, tailWord_1929440, baseEnd_1929440] using wordTrace_append hprefix tailTrace_1929440
  have hstable : (prefixWord ++ tailWord_1929440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929440).length < 2 ^ (prefixWord ++ tailWord_1929440).sum := by decide
  have hdescent : baseEnd_1929440 < baseStart_1929440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929609 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 3]
def baseStart_1929609 : Nat := 118140960795 + 1929609 * 2 ^ 59
def prefixEnd_1929609 : Nat := 4983230072969 + 3 ^ 40 * 1929609 * 2
def baseEnd_1929609 : Nat := 440363063218509390939287

theorem tailTrace_1929609 : CollatzResearch.WordTrace tailWord_1929609 prefixEnd_1929609 440363063218509390939287 := by
  unfold tailWord_1929609
  simp only [CollatzResearch.WordTrace]
  refine ⟨70378622066363618825415881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46919081377575745883610587 70378622066363618825415881)
  ·
    refine ⟨52783966549772714119061911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70378622066363618825415881 52783966549772714119061911)
    ·
      refine ⟨79175949824659071178592867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52783966549772714119061911 79175949824659071178592867)
      ·
        refine ⟨118763924736988606767889301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79175949824659071178592867 118763924736988606767889301)
        ·
          refine ⟨5567058972046340942244811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118763924736988606767889301 5567058972046340942244811)
          ·
            refine ⟨8350588458069511413367217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567058972046340942244811 8350588458069511413367217)
            ·
              refine ⟨6262941343552133560025413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8350588458069511413367217 6262941343552133560025413)
              ·
                refine ⟨1174301501916025042504765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6262941343552133560025413 1174301501916025042504765)
                ·
                  refine ⟨440363063218509390939287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174301501916025042504765 440363063218509390939287)
                  ·
                    rfl

theorem cell21_1929609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_1929609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929609 prefixEnd_1929609 := by exact prefixLift 1929609
  have htrace : WordTrace (prefixWord ++ tailWord_1929609) baseStart_1929609 baseEnd_1929609 := by
    simpa [prefixWord, tailWord_1929609, baseEnd_1929609] using wordTrace_append hprefix tailTrace_1929609
  have hstable : (prefixWord ++ tailWord_1929609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929609).length < 2 ^ (prefixWord ++ tailWord_1929609).sum := by decide
  have hdescent : baseEnd_1929609 < baseStart_1929609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929696 : List Nat := [2, 1, 1, 3, 1, 1, 3, 9]
def baseStart_1929696 : Nat := 118140960795 + 1929696 * 2 ^ 59
def prefixEnd_1929696 : Nat := 4983230072969 + 3 ^ 40 * 1929696 * 2
def baseEnd_1929696 : Nat := 146794305934605524329703

theorem tailTrace_1929696 : CollatzResearch.WordTrace tailWord_1929696 prefixEnd_1929696 146794305934605524329703 := by
  unfold tailWord_1929696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190897608524216341916471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46921196811365621789221961 35190897608524216341916471)
  ·
    refine ⟨52786346412786324512874707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35190897608524216341916471 52786346412786324512874707)
    ·
      refine ⟨79179519619179486769312061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52786346412786324512874707 79179519619179486769312061)
      ·
        refine ⟨29692319857192307538492023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79179519619179486769312061 29692319857192307538492023)
        ·
          refine ⟨44538479785788461307738035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29692319857192307538492023 44538479785788461307738035)
          ·
            refine ⟨66807719678682691961607053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44538479785788461307738035 66807719678682691961607053)
            ·
              refine ⟨25052894879506009485602645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66807719678682691961607053 25052894879506009485602645)
              ·
                refine ⟨146794305934605524329703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25052894879506009485602645 146794305934605524329703)
                ·
                  rfl

theorem cell21_1929696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_1929696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929696 prefixEnd_1929696 := by exact prefixLift 1929696
  have htrace : WordTrace (prefixWord ++ tailWord_1929696) baseStart_1929696 baseEnd_1929696 := by
    simpa [prefixWord, tailWord_1929696, baseEnd_1929696] using wordTrace_append hprefix tailTrace_1929696
  have hstable : (prefixWord ++ tailWord_1929696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929696).length < 2 ^ (prefixWord ++ tailWord_1929696).sum := by decide
  have hdescent : baseEnd_1929696 < baseStart_1929696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929727 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_1929727 : Nat := 118140960795 + 1929727 * 2 ^ 59
def prefixEnd_1929727 : Nat := 4983230072969 + 3 ^ 40 * 1929727 * 2
def baseEnd_1929727 : Nat := 440389992426167407972379

theorem tailTrace_1929727 : CollatzResearch.WordTrace tailWord_1929727 prefixEnd_1929727 440389992426167407972379 := by
  unfold tailWord_1929727
  simp only [CollatzResearch.WordTrace]
  refine ⟨70382925879936124978211435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46921950586624083318807623 70382925879936124978211435)
  ·
    refine ⟨105574388819904187467317153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70382925879936124978211435 105574388819904187467317153)
    ·
      refine ⟨79180791614928140600487865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105574388819904187467317153 79180791614928140600487865)
      ·
        refine ⟨59385593711196105450365899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79180791614928140600487865 59385593711196105450365899)
        ·
          refine ⟨89078390566794158175548849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59385593711196105450365899 89078390566794158175548849)
          ·
            refine ⟨66808792925095618631661637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89078390566794158175548849 66808792925095618631661637)
            ·
              refine ⟨12526648673455428493436557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66808792925095618631661637 12526648673455428493436557)
              ·
                refine ⟨4697493252545785685038709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12526648673455428493436557 4697493252545785685038709)
                ·
                  refine ⟨440389992426167407972379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4697493252545785685038709 440389992426167407972379)
                  ·
                    rfl

theorem cell21_1929727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_1929727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929727 prefixEnd_1929727 := by exact prefixLift 1929727
  have htrace : WordTrace (prefixWord ++ tailWord_1929727) baseStart_1929727 baseEnd_1929727 := by
    simpa [prefixWord, tailWord_1929727, baseEnd_1929727] using wordTrace_append hprefix tailTrace_1929727
  have hstable : (prefixWord ++ tailWord_1929727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929727).length < 2 ^ (prefixWord ++ tailWord_1929727).sum := by decide
  have hdescent : baseEnd_1929727 < baseStart_1929727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929761 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 3]
def baseStart_1929761 : Nat := 118140960795 + 1929761 * 2 ^ 59
def prefixEnd_1929761 : Nat := 4983230072969 + 3 ^ 40 * 1929761 * 2
def baseEnd_1929761 : Nat := 440397751689390904405643

theorem tailTrace_1929761 : CollatzResearch.WordTrace tailWord_1929761 prefixEnd_1929761 440397751689390904405643 := by
  unfold tailWord_1929761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384165961812948784949137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46922777307875299189966091 70384165961812948784949137)
  ·
    refine ⟨52788124471359711588711853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70384165961812948784949137 52788124471359711588711853)
    ·
      refine ⟨19795546676759891845766945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52788124471359711588711853 19795546676759891845766945)
      ·
        refine ⟨14846660007569918884325209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19795546676759891845766945 14846660007569918884325209)
        ·
          refine ⟨11134995005677439163243907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14846660007569918884325209 11134995005677439163243907)
          ·
            refine ⟨16702492508516158744865861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134995005677439163243907 16702492508516158744865861)
            ·
              refine ⟨3131717345346779764662349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16702492508516158744865861 3131717345346779764662349)
              ·
                refine ⟨1174394004505042411748381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3131717345346779764662349 1174394004505042411748381)
                ·
                  refine ⟨440397751689390904405643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174394004505042411748381 440397751689390904405643)
                  ·
                    rfl

theorem cell21_1929761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_1929761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929761 prefixEnd_1929761 := by exact prefixLift 1929761
  have htrace : WordTrace (prefixWord ++ tailWord_1929761) baseStart_1929761 baseEnd_1929761 := by
    simpa [prefixWord, tailWord_1929761, baseEnd_1929761] using wordTrace_append hprefix tailTrace_1929761
  have hstable : (prefixWord ++ tailWord_1929761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929761).length < 2 ^ (prefixWord ++ tailWord_1929761).sum := by decide
  have hdescent : baseEnd_1929761 < baseStart_1929761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929803 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_1929803 : Nat := 118140960795 + 1929803 * 2 ^ 59
def prefixEnd_1929803 : Nat := 4983230072969 + 3 ^ 40 * 1929803 * 2
def baseEnd_1929803 : Nat := 440407336661608164705557

theorem tailTrace_1929803 : CollatzResearch.WordTrace tailWord_1929803 prefixEnd_1929803 440407336661608164705557 := by
  unfold tailWord_1929803
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385697827660789957978063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46923798551773859971985375 70385697827660789957978063)
  ·
    refine ⟨105578546741491184936967095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70385697827660789957978063 105578546741491184936967095)
    ·
      refine ⟨158367820112236777405450643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105578546741491184936967095 158367820112236777405450643)
      ·
        refine ⟨237551730168355166108175965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158367820112236777405450643 237551730168355166108175965)
        ·
          refine ⟨89081898813133187290565987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237551730168355166108175965 89081898813133187290565987)
          ·
            refine ⟨133622848219699780935848981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89081898813133187290565987 133622848219699780935848981)
            ·
              refine ⟨6263571010298427231367921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133622848219699780935848981 6263571010298427231367921)
              ·
                refine ⟨4697678257723820423525941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263571010298427231367921 4697678257723820423525941)
                ·
                  refine ⟨440407336661608164705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4697678257723820423525941 440407336661608164705557)
                  ·
                    rfl

theorem cell21_1929803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_1929803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929803 prefixEnd_1929803 := by exact prefixLift 1929803
  have htrace : WordTrace (prefixWord ++ tailWord_1929803) baseStart_1929803 baseEnd_1929803 := by
    simpa [prefixWord, tailWord_1929803, baseEnd_1929803] using wordTrace_append hprefix tailTrace_1929803
  have hstable : (prefixWord ++ tailWord_1929803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929803).length < 2 ^ (prefixWord ++ tailWord_1929803).sum := by decide
  have hdescent : baseEnd_1929803 < baseStart_1929803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929834 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1929834 : Nat := 118140960795 + 1929834 * 2 ^ 59
def prefixEnd_1929834 : Nat := 4983230072969 + 3 ^ 40 * 1929834 * 2
def baseEnd_1929834 : Nat := 440414411283958999688827

theorem tailTrace_1929834 : CollatzResearch.WordTrace tailWord_1929834 prefixEnd_1929834 440414411283958999688827 := by
  unfold tailWord_1929834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17596707122637120563089139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46924552327032321501571037 17596707122637120563089139)
  ·
    refine ⟨26395060683955680844633709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17596707122637120563089139 26395060683955680844633709)
    ·
      refine ⟨9898147756483380316737641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26395060683955680844633709 9898147756483380316737641)
      ·
        refine ⟨7423610817362535237553231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9898147756483380316737641 7423610817362535237553231)
        ·
          refine ⟨11135416226043802856329847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423610817362535237553231 11135416226043802856329847)
          ·
            refine ⟨16703124339065704284494771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135416226043802856329847 16703124339065704284494771)
            ·
              refine ⟨25054686508598556426742157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16703124339065704284494771 25054686508598556426742157)
              ·
                refine ⟨9395507440724458660028309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25054686508598556426742157 9395507440724458660028309)
                ·
                  refine ⟨440414411283958999688827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9395507440724458660028309 440414411283958999688827)
                  ·
                    rfl

theorem cell21_1929834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1929834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929834 prefixEnd_1929834 := by exact prefixLift 1929834
  have htrace : WordTrace (prefixWord ++ tailWord_1929834) baseStart_1929834 baseEnd_1929834 := by
    simpa [prefixWord, tailWord_1929834, baseEnd_1929834] using wordTrace_append hprefix tailTrace_1929834
  have hstable : (prefixWord ++ tailWord_1929834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929834).length < 2 ^ (prefixWord ++ tailWord_1929834).sum := by decide
  have hdescent : baseEnd_1929834 < baseStart_1929834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929837 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1929837 : Nat := 118140960795 + 1929837 * 2 ^ 59
def prefixEnd_1929837 : Nat := 4983230072969 + 3 ^ 40 * 1929837 * 2
def baseEnd_1929837 : Nat := 440415095924831661138821

theorem tailTrace_1929837 : CollatzResearch.WordTrace tailWord_1929837 prefixEnd_1929837 440415095924831661138821 := by
  unfold tailWord_1929837
  simp only [CollatzResearch.WordTrace]
  refine ⟨70386937909537613764715765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46924625273025075843143843 70386937909537613764715765)
  ·
    refine ⟨6598775429019151290442103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70386937909537613764715765 6598775429019151290442103)
    ·
      refine ⟨9898163143528726935663155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6598775429019151290442103 9898163143528726935663155)
      ·
        refine ⟨14847244715293090403494733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9898163143528726935663155 14847244715293090403494733)
        ·
          refine ⟨5567716768234908901310525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14847244715293090403494733 5567716768234908901310525)
          ·
            refine ⟨2087893788088090837991447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5567716768234908901310525 2087893788088090837991447)
            ·
              refine ⟨3131840682132136256987171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087893788088090837991447 3131840682132136256987171)
              ·
                refine ⟨4697761023198204385480757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131840682132136256987171 4697761023198204385480757)
                ·
                  refine ⟨440415095924831661138821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4697761023198204385480757 440415095924831661138821)
                  ·
                    rfl

theorem cell21_1929837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1929837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929837 prefixEnd_1929837 := by exact prefixLift 1929837
  have htrace : WordTrace (prefixWord ++ tailWord_1929837) baseStart_1929837 baseEnd_1929837 := by
    simpa [prefixWord, tailWord_1929837, baseEnd_1929837] using wordTrace_append hprefix tailTrace_1929837
  have hstable : (prefixWord ++ tailWord_1929837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929837).length < 2 ^ (prefixWord ++ tailWord_1929837).sum := by decide
  have hdescent : baseEnd_1929837 < baseStart_1929837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1929882 : List Nat := [3, 1, 1, 6, 2, 8]
def baseStart_1929882 : Nat := 118140960795 + 1929882 * 2 ^ 59
def prefixEnd_1929882 : Nat := 4983230072969 + 3 ^ 40 * 1929882 * 2
def baseEnd_1929882 : Nat := 16312050575478577144027

theorem tailTrace_1929882 : CollatzResearch.WordTrace tailWord_1929882 prefixEnd_1929882 16312050575478577144027 := by
  unfold tailWord_1929882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17597144798593646612525975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46925719462916390966735933 17597144798593646612525975)
  ·
    refine ⟨26395717197890469918788963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17597144798593646612525975 26395717197890469918788963)
    ·
      refine ⟨39593575796835704878183445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26395717197890469918788963 39593575796835704878183445)
      ·
        refine ⟨1855948865476673666164849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39593575796835704878183445 1855948865476673666164849)
        ·
          refine ⟨1391961649107505249623637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855948865476673666164849 1391961649107505249623637)
          ·
            refine ⟨16312050575478577144027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1391961649107505249623637 16312050575478577144027)
            ·
              rfl

theorem cell21_1929882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 8].length) (baseStart_1929882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1929882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1929882 prefixEnd_1929882 := by exact prefixLift 1929882
  have htrace : WordTrace (prefixWord ++ tailWord_1929882) baseStart_1929882 baseEnd_1929882 := by
    simpa [prefixWord, tailWord_1929882, baseEnd_1929882] using wordTrace_append hprefix tailTrace_1929882
  have hstable : (prefixWord ++ tailWord_1929882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1929882).length < 2 ^ (prefixWord ++ tailWord_1929882).sum := by decide
  have hdescent : baseEnd_1929882 < baseStart_1929882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1929882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930065 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 3]
def baseStart_1930065 : Nat := 118140960795 + 1930065 * 2 ^ 59
def prefixEnd_1930065 : Nat := 4983230072969 + 3 ^ 40 * 1930065 * 2
def baseEnd_1930065 : Nat := 440467128631153931338355

theorem tailTrace_1930065 : CollatzResearch.WordTrace tailWord_1930065 prefixEnd_1930065 440467128631153931338355 := by
  unfold tailWord_1930065
  simp only [CollatzResearch.WordTrace]
  refine ⟨70395253752711608704015649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46930169168474405802677099 70395253752711608704015649)
  ·
    refine ⟨52796440314533706528011737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70395253752711608704015649 52796440314533706528011737)
    ·
      refine ⟨39597330235900279896008803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52796440314533706528011737 39597330235900279896008803)
      ·
        refine ⟨59395995353850419844013205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39597330235900279896008803 59395995353850419844013205)
        ·
          refine ⟨2784187282211738430188119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59395995353850419844013205 2784187282211738430188119)
          ·
            refine ⟨4176280923317607645282179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784187282211738430188119 4176280923317607645282179)
            ·
              refine ⟨6264421384976411467923269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176280923317607645282179 6264421384976411467923269)
              ·
                refine ⟨1174579009683077150235613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6264421384976411467923269 1174579009683077150235613)
                ·
                  refine ⟨440467128631153931338355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174579009683077150235613 440467128631153931338355)
                  ·
                    rfl

theorem cell21_1930065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_1930065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930065 prefixEnd_1930065 := by exact prefixLift 1930065
  have htrace : WordTrace (prefixWord ++ tailWord_1930065) baseStart_1930065 baseEnd_1930065 := by
    simpa [prefixWord, tailWord_1930065, baseEnd_1930065] using wordTrace_append hprefix tailTrace_1930065
  have hstable : (prefixWord ++ tailWord_1930065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930065).length < 2 ^ (prefixWord ++ tailWord_1930065).sum := by decide
  have hdescent : baseEnd_1930065 < baseStart_1930065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930110 : List Nat := [4, 2, 3, 1, 2, 1, 8]
def baseStart_1930110 : Nat := 118140960795 + 1930110 * 2 ^ 59
def prefixEnd_1930110 : Nat := 4983230072969 + 3 ^ 40 * 1930110 * 2
def baseEnd_1930110 : Nat := 48941933138249317009807

theorem tailTrace_1930110 : CollatzResearch.WordTrace tailWord_1930110 prefixEnd_1930110 48941933138249317009807 := by
  unfold tailWord_1930110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799611879693572673675473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46931263358365720926269189 8799611879693572673675473)
  ·
    refine ⟨6599708909770179505256605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8799611879693572673675473 6599708909770179505256605)
    ·
      refine ⟨2474890841163817314471227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6599708909770179505256605 2474890841163817314471227)
      ·
        refine ⟨3712336261745725971706841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474890841163817314471227 3712336261745725971706841)
        ·
          refine ⟨2784252196309294478780131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3712336261745725971706841 2784252196309294478780131)
          ·
            refine ⟨4176378294463941718170197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784252196309294478780131 4176378294463941718170197)
            ·
              refine ⟨48941933138249317009807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4176378294463941718170197 48941933138249317009807)
              ·
                rfl

theorem cell21_1930110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 8].length) (baseStart_1930110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930110 prefixEnd_1930110 := by exact prefixLift 1930110
  have htrace : WordTrace (prefixWord ++ tailWord_1930110) baseStart_1930110 baseEnd_1930110 := by
    simpa [prefixWord, tailWord_1930110, baseEnd_1930110] using wordTrace_append hprefix tailTrace_1930110
  have hstable : (prefixWord ++ tailWord_1930110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930110).length < 2 ^ (prefixWord ++ tailWord_1930110).sum := by decide
  have hdescent : baseEnd_1930110 < baseStart_1930110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930124 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_1930124 : Nat := 118140960795 + 1930124 * 2 ^ 59
def prefixEnd_1930124 : Nat := 4983230072969 + 3 ^ 40 * 1930124 * 2
def baseEnd_1930124 : Nat := 440480593234982939854901

theorem tailTrace_1930124 : CollatzResearch.WordTrace tailWord_1930124 prefixEnd_1930124 440480593234982939854901 := by
  unfold tailWord_1930124
  simp only [CollatzResearch.WordTrace]
  refine ⟨35198702829748930890206713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46931603772998574520275617 35198702829748930890206713)
  ·
    refine ⟨26399027122311698167655035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35198702829748930890206713 26399027122311698167655035)
    ·
      refine ⟨39598540683467547251482553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26399027122311698167655035 39598540683467547251482553)
      ·
        refine ⟨29698905512600660438611915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39598540683467547251482553 29698905512600660438611915)
        ·
          refine ⟨44548358268900990657917873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29698905512600660438611915 44548358268900990657917873)
          ·
            refine ⟨33411268701675742993438405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44548358268900990657917873 33411268701675742993438405)
            ·
              refine ⟨6264612881564201811269701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33411268701675742993438405 6264612881564201811269701)
              ·
                refine ⟨1174614915293287839613069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6264612881564201811269701 1174614915293287839613069)
                ·
                  refine ⟨440480593234982939854901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174614915293287839613069 440480593234982939854901)
                  ·
                    rfl

theorem cell21_1930124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_1930124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930124 prefixEnd_1930124 := by exact prefixLift 1930124
  have htrace : WordTrace (prefixWord ++ tailWord_1930124) baseStart_1930124 baseEnd_1930124 := by
    simpa [prefixWord, tailWord_1930124, baseEnd_1930124] using wordTrace_append hprefix tailTrace_1930124
  have hstable : (prefixWord ++ tailWord_1930124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930124).length < 2 ^ (prefixWord ++ tailWord_1930124).sum := by decide
  have hdescent : baseEnd_1930124 < baseStart_1930124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930183 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_1930183 : Nat := 118140960795 + 1930183 * 2 ^ 59
def prefixEnd_1930183 : Nat := 4983230072969 + 3 ^ 40 * 1930183 * 2
def baseEnd_1930183 : Nat := 440494057838811948371447

theorem tailTrace_1930183 : CollatzResearch.WordTrace tailWord_1930183 prefixEnd_1930183 440494057838811948371447 := by
  unfold tailWord_1930183
  simp only [CollatzResearch.WordTrace]
  refine ⟨70399557566284114856811203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46933038377522743237874135 70399557566284114856811203)
  ·
    refine ⟨105599336349426172285216805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70399557566284114856811203 105599336349426172285216805)
    ·
      refine ⟨19799875565517407303478151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105599336349426172285216805 19799875565517407303478151)
      ·
        refine ⟨29699813348276110955217227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19799875565517407303478151 29699813348276110955217227)
        ·
          refine ⟨44549720022414166432825841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29699813348276110955217227 44549720022414166432825841)
          ·
            refine ⟨33412290016810624824619381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44549720022414166432825841 33412290016810624824619381)
            ·
              refine ⟨3132402189075996077308067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33412290016810624824619381 3132402189075996077308067)
              ·
                refine ⟨4698603283613994115962101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132402189075996077308067 4698603283613994115962101)
                ·
                  refine ⟨440494057838811948371447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4698603283613994115962101 440494057838811948371447)
                  ·
                    rfl

theorem cell21_1930183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_1930183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930183 prefixEnd_1930183 := by exact prefixLift 1930183
  have htrace : WordTrace (prefixWord ++ tailWord_1930183) baseStart_1930183 baseEnd_1930183 := by
    simpa [prefixWord, tailWord_1930183, baseEnd_1930183] using wordTrace_append hprefix tailTrace_1930183
  have hstable : (prefixWord ++ tailWord_1930183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930183).length < 2 ^ (prefixWord ++ tailWord_1930183).sum := by decide
  have hdescent : baseEnd_1930183 < baseStart_1930183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930439 : List Nat := [1, 1, 4, 1, 1, 1, 1, 11]
def baseStart_1930439 : Nat := 118140960795 + 1930439 * 2 ^ 59
def prefixEnd_1930439 : Nat := 4983230072969 + 3 ^ 40 * 1930439 * 2
def baseEnd_1930439 : Nat := 146850826842204130701419

theorem tailTrace_1930439 : CollatzResearch.WordTrace tailWord_1930439 prefixEnd_1930439 146850826842204130701419 := by
  unfold tailWord_1930439
  simp only [CollatzResearch.WordTrace]
  refine ⟨70408894653356670578130371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46939263102237780385420247 70408894653356670578130371)
  ·
    refine ⟨105613341980035005867195557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70408894653356670578130371 105613341980035005867195557)
    ·
      refine ⟨19802501621256563600099167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105613341980035005867195557 19802501621256563600099167)
      ·
        refine ⟨29703752431884845400148751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802501621256563600099167 29703752431884845400148751)
        ·
          refine ⟨44555628647827268100223127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29703752431884845400148751 44555628647827268100223127)
          ·
            refine ⟨66833442971740902150334691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44555628647827268100223127 66833442971740902150334691)
            ·
              refine ⟨100250164457611353225502037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66833442971740902150334691 100250164457611353225502037)
              ·
                refine ⟨146850826842204130701419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 100250164457611353225502037 146850826842204130701419)
                ·
                  rfl

theorem cell21_1930439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_1930439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930439 prefixEnd_1930439 := by exact prefixLift 1930439
  have htrace : WordTrace (prefixWord ++ tailWord_1930439) baseStart_1930439 baseEnd_1930439 := by
    simpa [prefixWord, tailWord_1930439, baseEnd_1930439] using wordTrace_append hprefix tailTrace_1930439
  have hstable : (prefixWord ++ tailWord_1930439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930439).length < 2 ^ (prefixWord ++ tailWord_1930439).sum := by decide
  have hdescent : baseEnd_1930439 < baseStart_1930439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930456 : List Nat := [2, 1, 2, 2, 5, 1, 8]
def baseStart_1930456 : Nat := 118140960795 + 1930456 * 2 ^ 59
def prefixEnd_1930456 : Nat := 4983230072969 + 3 ^ 40 * 1930456 * 2
def baseEnd_1930456 : Nat := 48950706684247126702321

theorem tailTrace_1930456 : CollatzResearch.WordTrace tailWord_1930456 prefixEnd_1930456 48950706684247126702321 := by
  unfold tailWord_1930456
  simp only [CollatzResearch.WordTrace]
  refine ⟨35204757347147541240749611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46939676462863388320999481 35204757347147541240749611)
  ·
    refine ⟨52807136020721311861124417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35204757347147541240749611 52807136020721311861124417)
    ·
      refine ⟨39605352015540983895843313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52807136020721311861124417 39605352015540983895843313)
      ·
        refine ⟨29704014011655737921882485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39605352015540983895843313 29704014011655737921882485)
        ·
          refine ⟨2784751313592725430176483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29704014011655737921882485 2784751313592725430176483)
          ·
            refine ⟨4177126970389088145264725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784751313592725430176483 4177126970389088145264725)
            ·
              refine ⟨48950706684247126702321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4177126970389088145264725 48950706684247126702321)
              ·
                rfl

theorem cell21_1930456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 8].length) (baseStart_1930456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930456 prefixEnd_1930456 := by exact prefixLift 1930456
  have htrace : WordTrace (prefixWord ++ tailWord_1930456) baseStart_1930456 baseEnd_1930456 := by
    simpa [prefixWord, tailWord_1930456, baseEnd_1930456] using wordTrace_append hprefix tailTrace_1930456
  have hstable : (prefixWord ++ tailWord_1930456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930456).length < 2 ^ (prefixWord ++ tailWord_1930456).sum := by decide
  have hdescent : baseEnd_1930456 < baseStart_1930456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930532 : List Nat := [2, 3, 1, 3, 1, 1, 4, 6]
def baseStart_1930532 : Nat := 118140960795 + 1930532 * 2 ^ 59
def prefixEnd_1930532 : Nat := 4983230072969 + 3 ^ 40 * 1930532 * 2
def baseEnd_1930532 : Nat := 146857901464554965684689

theorem tailTrace_1930532 : CollatzResearch.WordTrace tailWord_1930532 prefixEnd_1930532 146857901464554965684689 := by
  unfold tailWord_1930532
  simp only [CollatzResearch.WordTrace]
  refine ⟨35206143321009873730632925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46941524428013164974177233 35206143321009873730632925)
  ·
    refine ⟨13202303745378702648987347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35206143321009873730632925 13202303745378702648987347)
    ·
      refine ⟨19803455618068053973481021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13202303745378702648987347 19803455618068053973481021)
      ·
        refine ⟨7426295856775520240055383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19803455618068053973481021 7426295856775520240055383)
        ·
          refine ⟨11139443785163280360083075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426295856775520240055383 11139443785163280360083075)
          ·
            refine ⟨16709165677744920540124613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139443785163280360083075 16709165677744920540124613)
            ·
              refine ⟨3132968564577172601273365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16709165677744920540124613 3132968564577172601273365)
              ·
                refine ⟨146857901464554965684689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3132968564577172601273365 146857901464554965684689)
                ·
                  rfl

theorem cell21_1930532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_1930532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930532 prefixEnd_1930532 := by exact prefixLift 1930532
  have htrace : WordTrace (prefixWord ++ tailWord_1930532) baseStart_1930532 baseEnd_1930532 := by
    simpa [prefixWord, tailWord_1930532, baseEnd_1930532] using wordTrace_append hprefix tailTrace_1930532
  have hstable : (prefixWord ++ tailWord_1930532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930532).length < 2 ^ (prefixWord ++ tailWord_1930532).sum := by decide
  have hdescent : baseEnd_1930532 < baseStart_1930532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930563 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 3]
def baseStart_1930563 : Nat := 118140960795 + 1930563 * 2 ^ 59
def prefixEnd_1930563 : Nat := 4983230072969 + 3 ^ 40 * 1930563 * 2
def baseEnd_1930563 : Nat := 440580779016015732037337

theorem tailTrace_1930563 : CollatzResearch.WordTrace tailWord_1930563 prefixEnd_1930563 440580779016015732037337 := by
  unfold tailWord_1930563
  simp only [CollatzResearch.WordTrace]
  refine ⟨70413417304907439755644343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46942278203271626503762895 70413417304907439755644343)
  ·
    refine ⟨105620125957361159633466515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70413417304907439755644343 105620125957361159633466515)
    ·
      refine ⟨158430188936041739450199773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105620125957361159633466515 158430188936041739450199773)
      ·
        refine ⟨59411320851015652293824915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158430188936041739450199773 59411320851015652293824915)
        ·
          refine ⟨89116981276523478440737373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59411320851015652293824915 89116981276523478440737373)
          ·
            refine ⟨33418867978696304415276515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89116981276523478440737373 33418867978696304415276515)
            ·
              refine ⟨50128301968044456622914773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33418867978696304415276515 50128301968044456622914773)
              ·
                refine ⟨1174882077376041952099565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50128301968044456622914773 1174882077376041952099565)
                ·
                  refine ⟨440580779016015732037337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174882077376041952099565 440580779016015732037337)
                  ·
                    rfl

theorem cell21_1930563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 3].length) (baseStart_1930563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930563 prefixEnd_1930563 := by exact prefixLift 1930563
  have htrace : WordTrace (prefixWord ++ tailWord_1930563) baseStart_1930563 baseEnd_1930563 := by
    simpa [prefixWord, tailWord_1930563, baseEnd_1930563] using wordTrace_append hprefix tailTrace_1930563
  have hstable : (prefixWord ++ tailWord_1930563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930563).length < 2 ^ (prefixWord ++ tailWord_1930563).sum := by decide
  have hdescent : baseEnd_1930563 < baseStart_1930563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930566 : List Nat := [6, 1, 1, 3, 1, 9]
def baseStart_1930566 : Nat := 118140960795 + 1930566 * 2 ^ 59
def prefixEnd_1930566 : Nat := 4983230072969 + 3 ^ 40 * 1930566 * 2
def baseEnd_1930566 : Nat := 16317831987292162721753

theorem tailTrace_1930566 : CollatzResearch.WordTrace tailWord_1930566 prefixEnd_1930566 16317831987292162721753 := by
  unfold tailWord_1930566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200422710121767852125111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46942351149264380845335701 2200422710121767852125111)
  ·
    refine ⟨3300634065182651778187667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2200422710121767852125111 3300634065182651778187667)
    ·
      refine ⟨4950951097773977667281501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3300634065182651778187667 4950951097773977667281501)
      ·
        refine ⟨1856606661665241625230563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4950951097773977667281501 1856606661665241625230563)
        ·
          refine ⟨2784909992497862437845845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856606661665241625230563 2784909992497862437845845)
          ·
            refine ⟨16317831987292162721753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2784909992497862437845845 16317831987292162721753)
            ·
              rfl

theorem cell21_1930566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 9].length) (baseStart_1930566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930566 prefixEnd_1930566 := by exact prefixLift 1930566
  have htrace : WordTrace (prefixWord ++ tailWord_1930566) baseStart_1930566 baseEnd_1930566 := by
    simpa [prefixWord, tailWord_1930566, baseEnd_1930566] using wordTrace_append hprefix tailTrace_1930566
  have hstable : (prefixWord ++ tailWord_1930566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930566).length < 2 ^ (prefixWord ++ tailWord_1930566).sum := by decide
  have hdescent : baseEnd_1930566 < baseStart_1930566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930580 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1930580 : Nat := 118140960795 + 1930580 * 2 ^ 59
def prefixEnd_1930580 : Nat := 4983230072969 + 3 ^ 40 * 1930580 * 2
def baseEnd_1930580 : Nat := 440584658647627480253969

theorem tailTrace_1930580 : CollatzResearch.WordTrace tailWord_1930580 prefixEnd_1930580 440584658647627480253969 := by
  unfold tailWord_1930580
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207018672922925829506597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46942691563897234439342129 35207018672922925829506597)
  ·
    refine ⟨6601316001173048593032487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35207018672922925829506597 6601316001173048593032487)
    ·
      refine ⟨9901974001759572889548731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601316001173048593032487 9901974001759572889548731)
      ·
        refine ⟨14852961002639359334323097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9901974001759572889548731 14852961002639359334323097)
        ·
          refine ⟨11139720751979519500742323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14852961002639359334323097 11139720751979519500742323)
          ·
            refine ⟨16709581127969279251113485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139720751979519500742323 16709581127969279251113485)
            ·
              refine ⟨6266092922988479719167557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16709581127969279251113485 6266092922988479719167557)
              ·
                refine ⟨1174892423060339947343917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6266092922988479719167557 1174892423060339947343917)
                ·
                  refine ⟨440584658647627480253969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174892423060339947343917 440584658647627480253969)
                  ·
                    rfl

theorem cell21_1930580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1930580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930580 prefixEnd_1930580 := by exact prefixLift 1930580
  have htrace : WordTrace (prefixWord ++ tailWord_1930580) baseStart_1930580 baseEnd_1930580 := by
    simpa [prefixWord, tailWord_1930580, baseEnd_1930580] using wordTrace_append hprefix tailTrace_1930580
  have hstable : (prefixWord ++ tailWord_1930580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930580).length < 2 ^ (prefixWord ++ tailWord_1930580).sum := by decide
  have hdescent : baseEnd_1930580 < baseStart_1930580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930594 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1930594 : Nat := 118140960795 + 1930594 * 2 ^ 59
def prefixEnd_1930594 : Nat := 4983230072969 + 3 ^ 40 * 1930594 * 2
def baseEnd_1930594 : Nat := 440587853638366567020607

theorem tailTrace_1930594 : CollatzResearch.WordTrace tailWord_1930594 prefixEnd_1930594 440587853638366567020607 := by
  unfold tailWord_1930594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603636991948783012505709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46943031978530088033348557 17603636991948783012505709)
  ·
    refine ⟨6601363871980793629689641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17603636991948783012505709 6601363871980793629689641)
    ·
      refine ⟨4951022903985595222267231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6601363871980793629689641 4951022903985595222267231)
      ·
        refine ⟨7426534355978392833400847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4951022903985595222267231 7426534355978392833400847)
        ·
          refine ⟨11139801533967589250101271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7426534355978392833400847 11139801533967589250101271)
          ·
            refine ⟨16709702300951383875151907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139801533967589250101271 16709702300951383875151907)
            ·
              refine ⟨25064553451427075812727861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16709702300951383875151907 25064553451427075812727861)
              ·
                refine ⟨2349801886071288357443237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25064553451427075812727861 2349801886071288357443237)
                ·
                  refine ⟨440587853638366567020607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2349801886071288357443237 440587853638366567020607)
                  ·
                    rfl

theorem cell21_1930594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1930594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930594 prefixEnd_1930594 := by exact prefixLift 1930594
  have htrace : WordTrace (prefixWord ++ tailWord_1930594) baseStart_1930594 baseEnd_1930594 := by
    simpa [prefixWord, tailWord_1930594, baseEnd_1930594] using wordTrace_append hprefix tailTrace_1930594
  have hstable : (prefixWord ++ tailWord_1930594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930594).length < 2 ^ (prefixWord ++ tailWord_1930594).sum := by decide
  have hdescent : baseEnd_1930594 < baseStart_1930594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930608 : List Nat := [2, 1, 1, 1, 4, 2, 5, 5]
def baseStart_1930608 : Nat := 118140960795 + 1930608 * 2 ^ 59
def prefixEnd_1930608 : Nat := 4983230072969 + 3 ^ 40 * 1930608 * 2
def baseEnd_1930608 : Nat := 146863682876368551262415

theorem tailTrace_1930608 : CollatzResearch.WordTrace tailWord_1930608 prefixEnd_1930608 146863682876368551262415 := by
  unfold tailWord_1930608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207529294872206220516239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46943372393162941627354985 35207529294872206220516239)
  ·
    refine ⟨52811293942308309330774359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35207529294872206220516239 52811293942308309330774359)
    ·
      refine ⟨79216940913462463996161539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52811293942308309330774359 79216940913462463996161539)
      ·
        refine ⟨118825411370193695994242309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79216940913462463996161539 118825411370193695994242309)
        ·
          refine ⟨22279764631911317998920433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118825411370193695994242309 22279764631911317998920433)
          ·
            refine ⟨16709823473933488499190325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22279764631911317998920433 16709823473933488499190325)
            ·
              refine ⟨1566545950681264546799093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16709823473933488499190325 1566545950681264546799093)
              ·
                refine ⟨146863682876368551262415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1566545950681264546799093 146863682876368551262415)
                ·
                  rfl

theorem cell21_1930608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_1930608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930608 prefixEnd_1930608 := by exact prefixLift 1930608
  have htrace : WordTrace (prefixWord ++ tailWord_1930608) baseStart_1930608 baseEnd_1930608 := by
    simpa [prefixWord, tailWord_1930608, baseEnd_1930608] using wordTrace_append hprefix tailTrace_1930608
  have hstable : (prefixWord ++ tailWord_1930608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930608).length < 2 ^ (prefixWord ++ tailWord_1930608).sum := by decide
  have hdescent : baseEnd_1930608 < baseStart_1930608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930749 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 3]
def baseStart_1930749 : Nat := 118140960795 + 1930749 * 2 ^ 59
def prefixEnd_1930749 : Nat := 4983230072969 + 3 ^ 40 * 1930749 * 2
def baseEnd_1930749 : Nat := 440623226750120741936957

theorem tailTrace_1930749 : CollatzResearch.WordTrace tailWord_1930749 prefixEnd_1930749 440623226750120741936957 := by
  unfold tailWord_1930749
  simp only [CollatzResearch.WordTrace]
  refine ⟨70420201282233593521915301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46946800854822395681276867 70420201282233593521915301)
  ·
    refine ⟨13203787740418798785359119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70420201282233593521915301 13203787740418798785359119)
    ·
      refine ⟨19805681610628198178038679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203787740418798785359119 19805681610628198178038679)
      ·
        refine ⟨29708522415942297267058019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19805681610628198178038679 29708522415942297267058019)
        ·
          refine ⟨44562783623913445900587029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29708522415942297267058019 44562783623913445900587029)
          ·
            refine ⟨2088880482370942776590017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44562783623913445900587029 2088880482370942776590017)
            ·
              refine ⟨1566660361778207082442513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2088880482370942776590017 1566660361778207082442513)
              ·
                refine ⟨1174995271333655311831885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566660361778207082442513 1174995271333655311831885)
                ·
                  refine ⟨440623226750120741936957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1174995271333655311831885 440623226750120741936957)
                  ·
                    rfl

theorem cell21_1930749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_1930749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930749 prefixEnd_1930749 := by exact prefixLift 1930749
  have htrace : WordTrace (prefixWord ++ tailWord_1930749) baseStart_1930749 baseEnd_1930749 := by
    simpa [prefixWord, tailWord_1930749, baseEnd_1930749] using wordTrace_append hprefix tailTrace_1930749
  have hstable : (prefixWord ++ tailWord_1930749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930749).length < 2 ^ (prefixWord ++ tailWord_1930749).sum := by decide
  have hdescent : baseEnd_1930749 < baseStart_1930749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1930805 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_1930805 : Nat := 118140960795 + 1930805 * 2 ^ 59
def prefixEnd_1930805 : Nat := 4983230072969 + 3 ^ 40 * 1930805 * 2
def baseEnd_1930805 : Nat := 440636006713077089003509

theorem tailTrace_1930805 : CollatzResearch.WordTrace tailWord_1930805 prefixEnd_1930805 440636006713077089003509 := by
  unfold tailWord_1930805
  simp only [CollatzResearch.WordTrace]
  refine ⟨70422243770030715085953869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46948162513353810057302579 70422243770030715085953869)
  ·
    refine ⟨26408341413761518157232701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70422243770030715085953869 26408341413761518157232701)
    ·
      refine ⟨9903128030160569308962263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26408341413761518157232701 9903128030160569308962263)
      ·
        refine ⟨14854692045240853963443395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9903128030160569308962263 14854692045240853963443395)
        ·
          refine ⟨22282038067861280945165093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14854692045240853963443395 22282038067861280945165093)
          ·
            refine ⟨4177882137723990177218455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22282038067861280945165093 4177882137723990177218455)
            ·
              refine ⟨6266823206585985265827683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177882137723990177218455 6266823206585985265827683)
              ·
                refine ⟨9400234809878977898741525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6266823206585985265827683 9400234809878977898741525)
                ·
                  refine ⟨440636006713077089003509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9400234809878977898741525 440636006713077089003509)
                  ·
                    rfl

theorem cell21_1930805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_1930805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1930805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1930805 prefixEnd_1930805 := by exact prefixLift 1930805
  have htrace : WordTrace (prefixWord ++ tailWord_1930805) baseStart_1930805 baseEnd_1930805 := by
    simpa [prefixWord, tailWord_1930805, baseEnd_1930805] using wordTrace_append hprefix tailTrace_1930805
  have hstable : (prefixWord ++ tailWord_1930805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1930805).length < 2 ^ (prefixWord ++ tailWord_1930805).sum := by decide
  have hdescent : baseEnd_1930805 < baseStart_1930805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1930805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931016 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1931016 : Nat := 118140960795 + 1931016 * 2 ^ 59
def prefixEnd_1931016 : Nat := 4983230072969 + 3 ^ 40 * 1931016 * 2
def baseEnd_1931016 : Nat := 440684159787787610986411

theorem tailTrace_1931016 : CollatzResearch.WordTrace tailWord_1931016 prefixEnd_1931016 440684159787787610986411 := by
  unfold tailWord_1931016
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214969786133149060942451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46953293048177532081256601 35214969786133149060942451)
  ·
    refine ⟨52822454679199723591413677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35214969786133149060942451 52822454679199723591413677)
    ·
      refine ⟨19808420504699896346780129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52822454679199723591413677 19808420504699896346780129)
      ·
        refine ⟨14856315378524922260085097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19808420504699896346780129 14856315378524922260085097)
        ·
          refine ⟨11142236533893691695063823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14856315378524922260085097 11142236533893691695063823)
          ·
            refine ⟨16713354800840537542595735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11142236533893691695063823 16713354800840537542595735)
            ·
              refine ⟨25070032201260806313893603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16713354800840537542595735 25070032201260806313893603)
              ·
                refine ⟨37605048301891209470840405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25070032201260806313893603 37605048301891209470840405)
                ·
                  refine ⟨440684159787787610986411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37605048301891209470840405 440684159787787610986411)
                  ·
                    rfl

theorem cell21_1931016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1931016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931016 prefixEnd_1931016 := by exact prefixLift 1931016
  have htrace : WordTrace (prefixWord ++ tailWord_1931016) baseStart_1931016 baseEnd_1931016 := by
    simpa [prefixWord, tailWord_1931016, baseEnd_1931016] using wordTrace_append hprefix tailTrace_1931016
  have hstable : (prefixWord ++ tailWord_1931016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931016).length < 2 ^ (prefixWord ++ tailWord_1931016).sum := by decide
  have hdescent : baseEnd_1931016 < baseStart_1931016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931019 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 3]
def baseStart_1931019 : Nat := 118140960795 + 1931019 * 2 ^ 59
def prefixEnd_1931019 : Nat := 4983230072969 + 3 ^ 40 * 1931019 * 2
def baseEnd_1931019 : Nat := 440684844428660272436405

theorem tailTrace_1931019 : CollatzResearch.WordTrace tailWord_1931019 prefixEnd_1931019 440684844428660272436405 := by
  unfold tailWord_1931019
  simp only [CollatzResearch.WordTrace]
  refine ⟨70430048991255429634244111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46953365994170286422829407 70430048991255429634244111)
  ·
    refine ⟨105645073486883144451366167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70430048991255429634244111 105645073486883144451366167)
    ·
      refine ⟨158467610230324716677049251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105645073486883144451366167 158467610230324716677049251)
      ·
        refine ⟨237701415345487075015573877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158467610230324716677049251 237701415345487075015573877)
        ·
          refine ⟨22284507688639413282710051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237701415345487075015573877 22284507688639413282710051)
          ·
            refine ⟨33426761532959119924065077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22284507688639413282710051 33426761532959119924065077)
            ·
              refine ⟨3133758893714917492881101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33426761532959119924065077 3133758893714917492881101)
              ·
                refine ⟨1175159585143094059830413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133758893714917492881101 1175159585143094059830413)
                ·
                  refine ⟨440684844428660272436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175159585143094059830413 440684844428660272436405)
                  ·
                    rfl

theorem cell21_1931019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3].length) (baseStart_1931019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931019 prefixEnd_1931019 := by exact prefixLift 1931019
  have htrace : WordTrace (prefixWord ++ tailWord_1931019) baseStart_1931019 baseEnd_1931019 := by
    simpa [prefixWord, tailWord_1931019, baseEnd_1931019] using wordTrace_append hprefix tailTrace_1931019
  have hstable : (prefixWord ++ tailWord_1931019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931019).length < 2 ^ (prefixWord ++ tailWord_1931019).sum := by decide
  have hdescent : baseEnd_1931019 < baseStart_1931019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931036 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_1931036 : Nat := 118140960795 + 1931036 * 2 ^ 59
def prefixEnd_1931036 : Nat := 4983230072969 + 3 ^ 40 * 1931036 * 2
def baseEnd_1931036 : Nat := 440688724060272020653037

theorem tailTrace_1931036 : CollatzResearch.WordTrace tailWord_1931036 prefixEnd_1931036 440688724060272020653037 := by
  unfold tailWord_1931036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35215334516096920768806481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46953779354795894358408641 35215334516096920768806481)
  ·
    refine ⟨26411500887072690576604861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35215334516096920768806481 26411500887072690576604861)
    ·
      refine ⟨9904312832652258966226823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26411500887072690576604861 9904312832652258966226823)
      ·
        refine ⟨14856469248978388449340235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9904312832652258966226823 14856469248978388449340235)
        ·
          refine ⟨22284703873467582674010353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14856469248978388449340235 22284703873467582674010353)
          ·
            refine ⟨16713527905100687005507765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22284703873467582674010353 16713527905100687005507765)
            ·
              refine ⟨1566893241103189406766353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16713527905100687005507765 1566893241103189406766353)
              ·
                refine ⟨1175169930827392055074765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566893241103189406766353 1175169930827392055074765)
                ·
                  refine ⟨440688724060272020653037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175169930827392055074765 440688724060272020653037)
                  ·
                    rfl

theorem cell21_1931036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_1931036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931036 prefixEnd_1931036 := by exact prefixLift 1931036
  have htrace : WordTrace (prefixWord ++ tailWord_1931036) baseStart_1931036 baseEnd_1931036 := by
    simpa [prefixWord, tailWord_1931036, baseEnd_1931036] using wordTrace_append hprefix tailTrace_1931036
  have hstable : (prefixWord ++ tailWord_1931036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931036).length < 2 ^ (prefixWord ++ tailWord_1931036).sum := by decide
  have hdescent : baseEnd_1931036 < baseStart_1931036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931143 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 4]
def baseStart_1931143 : Nat := 118140960795 + 1931143 * 2 ^ 59
def prefixEnd_1931143 : Nat := 4983230072969 + 3 ^ 40 * 1931143 * 2
def baseEnd_1931143 : Nat := 440713142918063612369485

theorem tailTrace_1931143 : CollatzResearch.WordTrace tailWord_1931143 prefixEnd_1931143 440713142918063612369485 := by
  unfold tailWord_1931143
  simp only [CollatzResearch.WordTrace]
  refine ⟨70434571642806198811758083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46956381095204132541172055 70434571642806198811758083)
  ·
    refine ⟨105651857464209298217637125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70434571642806198811758083 105651857464209298217637125)
    ·
      refine ⟨19809723274539243415806961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105651857464209298217637125 19809723274539243415806961)
      ·
        refine ⟨14857292455904432561855221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19809723274539243415806961 14857292455904432561855221)
        ·
          refine ⟨1392871167741040552673927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14857292455904432561855221 1392871167741040552673927)
          ·
            refine ⟨2089306751611560829010891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392871167741040552673927 2089306751611560829010891)
            ·
              refine ⟨3133960127417341243516337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089306751611560829010891 3133960127417341243516337)
              ·
                refine ⟨2350470095563005932637253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3133960127417341243516337 2350470095563005932637253)
                ·
                  refine ⟨440713142918063612369485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350470095563005932637253 440713142918063612369485)
                  ·
                    rfl

theorem cell21_1931143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4].length) (baseStart_1931143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931143 prefixEnd_1931143 := by exact prefixLift 1931143
  have htrace : WordTrace (prefixWord ++ tailWord_1931143) baseStart_1931143 baseEnd_1931143 := by
    simpa [prefixWord, tailWord_1931143, baseEnd_1931143] using wordTrace_append hprefix tailTrace_1931143
  have hstable : (prefixWord ++ tailWord_1931143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931143).length < 2 ^ (prefixWord ++ tailWord_1931143).sum := by decide
  have hdescent : baseEnd_1931143 < baseStart_1931143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931292 : List Nat := [2, 2, 3, 1, 3, 2, 3, 5]
def baseStart_1931292 : Nat := 118140960795 + 1931292 * 2 ^ 59
def prefixEnd_1931292 : Nat := 4983230072969 + 3 ^ 40 * 1931292 * 2
def baseEnd_1931292 : Nat := 146915715582690821461949

theorem tailTrace_1931292 : CollatzResearch.WordTrace tailWord_1931292 prefixEnd_1931292 146915715582690821461949 := by
  unfold tailWord_1931292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220003059633198629466065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46960004079510931505954753 35220003059633198629466065)
  ·
    refine ⟨26415002294724898972099549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35220003059633198629466065 26415002294724898972099549)
    ·
      refine ⟨9905625860521837114537331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26415002294724898972099549 9905625860521837114537331)
      ·
        refine ⟨14858438790782755671805997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9905625860521837114537331 14858438790782755671805997)
        ·
          refine ⟨5571914546543533376927249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14858438790782755671805997 5571914546543533376927249)
          ·
            refine ⟨4178935909907650032695437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571914546543533376927249 4178935909907650032695437)
            ·
              refine ⟨1567100966215368762260789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4178935909907650032695437 1567100966215368762260789)
              ·
                refine ⟨146915715582690821461949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1567100966215368762260789 146915715582690821461949)
                ·
                  rfl

theorem cell21_1931292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_1931292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931292 prefixEnd_1931292 := by exact prefixLift 1931292
  have htrace : WordTrace (prefixWord ++ tailWord_1931292) baseStart_1931292 baseEnd_1931292 := by
    simpa [prefixWord, tailWord_1931292, baseEnd_1931292] using wordTrace_append hprefix tailTrace_1931292
  have hstable : (prefixWord ++ tailWord_1931292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931292).length < 2 ^ (prefixWord ++ tailWord_1931292).sum := by decide
  have hdescent : baseEnd_1931292 < baseStart_1931292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931337 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 4]
def baseStart_1931337 : Nat := 118140960795 + 1931337 * 2 ^ 59
def prefixEnd_1931337 : Nat := 4983230072969 + 3 ^ 40 * 1931337 * 2
def baseEnd_1931337 : Nat := 440757416361162386135755

theorem tailTrace_1931337 : CollatzResearch.WordTrace tailWord_1931337 prefixEnd_1931337 440757416361162386135755 := by
  unfold tailWord_1931337
  simp only [CollatzResearch.WordTrace]
  refine ⟨70441647404103369944320265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46961098269402246629546843 70441647404103369944320265)
  ·
    refine ⟨52831235553077527458240199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70441647404103369944320265 52831235553077527458240199)
    ·
      refine ⟨79246853329616291187360299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52831235553077527458240199 79246853329616291187360299)
      ·
        refine ⟨118870279994424436781040449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79246853329616291187360299 118870279994424436781040449)
        ·
          refine ⟨89152709995818327585780337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118870279994424436781040449 89152709995818327585780337)
          ·
            refine ⟨66864532496863745689335253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89152709995818327585780337 66864532496863745689335253)
            ·
              refine ⟨1567137480395244039593795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66864532496863745689335253 1567137480395244039593795)
              ·
                refine ⟨2350706220592866059390693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567137480395244039593795 2350706220592866059390693)
                ·
                  refine ⟨440757416361162386135755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350706220592866059390693 440757416361162386135755)
                  ·
                    rfl

theorem cell21_1931337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_1931337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931337 prefixEnd_1931337 := by exact prefixLift 1931337
  have htrace : WordTrace (prefixWord ++ tailWord_1931337) baseStart_1931337 baseEnd_1931337 := by
    simpa [prefixWord, tailWord_1931337, baseEnd_1931337] using wordTrace_append hprefix tailTrace_1931337
  have hstable : (prefixWord ++ tailWord_1931337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931337).length < 2 ^ (prefixWord ++ tailWord_1931337).sum := by decide
  have hdescent : baseEnd_1931337 < baseStart_1931337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931351 : List Nat := [1, 1, 3, 2, 2, 1, 6, 5]
def baseStart_1931351 : Nat := 118140960795 + 1931351 * 2 ^ 59
def prefixEnd_1931351 : Nat := 4983230072969 + 3 ^ 40 * 1931351 * 2
def baseEnd_1931351 : Nat := 146920203783967157634131

theorem tailTrace_1931351 : CollatzResearch.WordTrace tailWord_1931351 prefixEnd_1931351 146920203783967157634131 := by
  unfold tailWord_1931351
  simp only [CollatzResearch.WordTrace]
  refine ⟨70442158026052650335329907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46961438684035100223553271 70442158026052650335329907)
  ·
    refine ⟨105663237039078975502994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70442158026052650335329907 105663237039078975502994861)
    ·
      refine ⟨39623713889654615813623073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105663237039078975502994861 39623713889654615813623073)
      ·
        refine ⟨29717785417240961860217305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39623713889654615813623073 29717785417240961860217305)
        ·
          refine ⟨22288339062930721395162979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29717785417240961860217305 22288339062930721395162979)
          ·
            refine ⟨33432508594396082092744469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22288339062930721395162979 33432508594396082092744469)
            ·
              refine ⟨1567148840362316348097397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33432508594396082092744469 1567148840362316348097397)
              ·
                refine ⟨146920203783967157634131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1567148840362316348097397 146920203783967157634131)
                ·
                  rfl

theorem cell21_1931351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 5].length) (baseStart_1931351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931351 prefixEnd_1931351 := by exact prefixLift 1931351
  have htrace : WordTrace (prefixWord ++ tailWord_1931351) baseStart_1931351 baseEnd_1931351 := by
    simpa [prefixWord, tailWord_1931351, baseEnd_1931351] using wordTrace_append hprefix tailTrace_1931351
  have hstable : (prefixWord ++ tailWord_1931351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931351).length < 2 ^ (prefixWord ++ tailWord_1931351).sum := by decide
  have hdescent : baseEnd_1931351 < baseStart_1931351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931357 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 3]
def baseStart_1931357 : Nat := 118140960795 + 1931357 * 2 ^ 59
def prefixEnd_1931357 : Nat := 4983230072969 + 3 ^ 40 * 1931357 * 2
def baseEnd_1931357 : Nat := 440761980633646795802381

theorem tailTrace_1931357 : CollatzResearch.WordTrace tailWord_1931357 prefixEnd_1931357 440761980633646795802381 := by
  unfold tailWord_1931357
  simp only [CollatzResearch.WordTrace]
  refine ⟨70442376864030913360048325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46961584576020608906698883 70442376864030913360048325)
  ·
    refine ⟨13207945662005796255009061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70442376864030913360048325 13207945662005796255009061)
    ·
      refine ⟨2476489811626086797814199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13207945662005796255009061 2476489811626086797814199)
      ·
        refine ⟨3714734717439130196721299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476489811626086797814199 3714734717439130196721299)
        ·
          refine ⟨5572102076158695295081949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714734717439130196721299 5572102076158695295081949)
          ·
            refine ⟨2089538278559510735655731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5572102076158695295081949 2089538278559510735655731)
            ·
              refine ⟨3134307417839266103483597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089538278559510735655731 3134307417839266103483597)
              ·
                refine ⟨1175365281689724788806349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3134307417839266103483597 1175365281689724788806349)
                ·
                  refine ⟨440761980633646795802381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175365281689724788806349 440761980633646795802381)
                  ·
                    rfl

theorem cell21_1931357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_1931357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931357 prefixEnd_1931357 := by exact prefixLift 1931357
  have htrace : WordTrace (prefixWord ++ tailWord_1931357) baseStart_1931357 baseEnd_1931357 := by
    simpa [prefixWord, tailWord_1931357, baseEnd_1931357] using wordTrace_append hprefix tailTrace_1931357
  have hstable : (prefixWord ++ tailWord_1931357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931357).length < 2 ^ (prefixWord ++ tailWord_1931357).sum := by decide
  have hdescent : baseEnd_1931357 < baseStart_1931357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931455 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_1931455 : Nat := 118140960795 + 1931455 * 2 ^ 59
def prefixEnd_1931455 : Nat := 4983230072969 + 3 ^ 40 * 1931455 * 2
def baseEnd_1931455 : Nat := 440784345568820403168847

theorem tailTrace_1931455 : CollatzResearch.WordTrace tailWord_1931455 prefixEnd_1931455 440784345568820403168847 := by
  unfold tailWord_1931455
  simp only [CollatzResearch.WordTrace]
  refine ⟨70445951217675876097115819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46963967478450584064743879 70445951217675876097115819)
  ·
    refine ⟨105668926826513814145673729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70445951217675876097115819 105668926826513814145673729)
    ·
      refine ⟨79251695119885360609255297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105668926826513814145673729 79251695119885360609255297)
      ·
        refine ⟨59438771339914020456941473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79251695119885360609255297 59438771339914020456941473)
        ·
          refine ⟨44579078504935515342706105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59438771339914020456941473 44579078504935515342706105)
          ·
            refine ⟨33434308878701636507029579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44579078504935515342706105 33434308878701636507029579)
            ·
              refine ⟨50151463318052454760544369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33434308878701636507029579 50151463318052454760544369)
              ·
                refine ⟨37613597488539341070408277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50151463318052454760544369 37613597488539341070408277)
                ·
                  refine ⟨440784345568820403168847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37613597488539341070408277 440784345568820403168847)
                  ·
                    rfl

theorem cell21_1931455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_1931455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931455 prefixEnd_1931455 := by exact prefixLift 1931455
  have htrace : WordTrace (prefixWord ++ tailWord_1931455) baseStart_1931455 baseEnd_1931455 := by
    simpa [prefixWord, tailWord_1931455, baseEnd_1931455] using wordTrace_append hprefix tailTrace_1931455
  have hstable : (prefixWord ++ tailWord_1931455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931455).length < 2 ^ (prefixWord ++ tailWord_1931455).sum := by decide
  have hdescent : baseEnd_1931455 < baseStart_1931455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931506 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_1931506 : Nat := 118140960795 + 1931506 * 2 ^ 59
def prefixEnd_1931506 : Nat := 4983230072969 + 3 ^ 40 * 1931506 * 2
def baseEnd_1931506 : Nat := 440795984463655647818743

theorem tailTrace_1931506 : CollatzResearch.WordTrace tailWord_1931506 prefixEnd_1931506 440795984463655647818743 := by
  unfold tailWord_1931506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17611952835122777951805593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46965207560327407871481581 17611952835122777951805593)
  ·
    refine ⟨13208964626342083463854195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17611952835122777951805593 13208964626342083463854195)
    ·
      refine ⟨19813446939513125195781293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13208964626342083463854195 19813446939513125195781293)
      ·
        refine ⟨7430042602317421948417985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19813446939513125195781293 7430042602317421948417985)
        ·
          refine ⟨5572531951738066461313489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7430042602317421948417985 5572531951738066461313489)
          ·
            refine ⟨4179398963803549845985117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572531951738066461313489 4179398963803549845985117)
            ·
              refine ⟨1567274611426331192244419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4179398963803549845985117 1567274611426331192244419)
              ·
                refine ⟨2350911917139496788366629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567274611426331192244419 2350911917139496788366629)
                ·
                  refine ⟨440795984463655647818743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350911917139496788366629 440795984463655647818743)
                  ·
                    rfl

theorem cell21_1931506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_1931506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931506 prefixEnd_1931506 := by exact prefixLift 1931506
  have htrace : WordTrace (prefixWord ++ tailWord_1931506) baseStart_1931506 baseEnd_1931506 := by
    simpa [prefixWord, tailWord_1931506, baseEnd_1931506] using wordTrace_append hprefix tailTrace_1931506
  have hstable : (prefixWord ++ tailWord_1931506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931506).length < 2 ^ (prefixWord ++ tailWord_1931506).sum := by decide
  have hdescent : baseEnd_1931506 < baseStart_1931506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931531 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_1931531 : Nat := 118140960795 + 1931531 * 2 ^ 59
def prefixEnd_1931531 : Nat := 4983230072969 + 3 ^ 40 * 1931531 * 2
def baseEnd_1931531 : Nat := 440801689804261159902025

theorem tailTrace_1931531 : CollatzResearch.WordTrace tailWord_1931531 prefixEnd_1931531 440801689804261159902025 := by
  unfold tailWord_1931531
  simp only [CollatzResearch.WordTrace]
  refine ⟨70448723165400541076882447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46965815443600360717921631 70448723165400541076882447)
  ·
    refine ⟨105673084748100811615323671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70448723165400541076882447 105673084748100811615323671)
    ·
      refine ⟨158509627122151217422985507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105673084748100811615323671 158509627122151217422985507)
      ·
        refine ⟨237764440683226826134478261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158509627122151217422985507 237764440683226826134478261)
        ·
          refine ⟨22290416314052514950107337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237764440683226826134478261 22290416314052514950107337)
          ·
            refine ⟨16717812235539386212580503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22290416314052514950107337 16717812235539386212580503)
            ·
              refine ⟨25076718353309079318870755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16717812235539386212580503 25076718353309079318870755)
              ·
                refine ⟨37615077529963618978306133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25076718353309079318870755 37615077529963618978306133)
                ·
                  refine ⟨440801689804261159902025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37615077529963618978306133 440801689804261159902025)
                  ·
                    rfl

theorem cell21_1931531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_1931531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931531 prefixEnd_1931531 := by exact prefixLift 1931531
  have htrace : WordTrace (prefixWord ++ tailWord_1931531) baseStart_1931531 baseEnd_1931531 := by
    simpa [prefixWord, tailWord_1931531, baseEnd_1931531] using wordTrace_append hprefix tailTrace_1931531
  have hstable : (prefixWord ++ tailWord_1931531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931531).length < 2 ^ (prefixWord ++ tailWord_1931531).sum := by decide
  have hdescent : baseEnd_1931531 < baseStart_1931531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931548 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_1931548 : Nat := 118140960795 + 1931548 * 2 ^ 59
def prefixEnd_1931548 : Nat := 4983230072969 + 3 ^ 40 * 1931548 * 2
def baseEnd_1931548 : Nat := 440805569435872908118657

theorem tailTrace_1931548 : CollatzResearch.WordTrace tailWord_1931548 prefixEnd_1931548 440805569435872908118657 := by
  unfold tailWord_1931548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35224671603169476490125649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46966228804225968653500865 35224671603169476490125649)
  ·
    refine ⟨26418503702377107367594237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35224671603169476490125649 26418503702377107367594237)
    ·
      refine ⟨9906938888391415262847839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26418503702377107367594237 9906938888391415262847839)
      ·
        refine ⟨14860408332587122894271759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9906938888391415262847839 14860408332587122894271759)
        ·
          refine ⟨22290612498880684341407639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860408332587122894271759 22290612498880684341407639)
          ·
            refine ⟨33435918748321026512111459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290612498880684341407639 33435918748321026512111459)
            ·
              refine ⟨50153878122481539768167189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33435918748321026512111459 50153878122481539768167189)
              ·
                refine ⟨2350963036991322176632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50153878122481539768167189 2350963036991322176632837)
                ·
                  refine ⟨440805569435872908118657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2350963036991322176632837 440805569435872908118657)
                  ·
                    rfl

theorem cell21_1931548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_1931548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931548 prefixEnd_1931548 := by exact prefixLift 1931548
  have htrace : WordTrace (prefixWord ++ tailWord_1931548) baseStart_1931548 baseEnd_1931548 := by
    simpa [prefixWord, tailWord_1931548, baseEnd_1931548] using wordTrace_append hprefix tailTrace_1931548
  have hstable : (prefixWord ++ tailWord_1931548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931548).length < 2 ^ (prefixWord ++ tailWord_1931548).sum := by decide
  have hdescent : baseEnd_1931548 < baseStart_1931548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931703 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 3]
def baseStart_1931703 : Nat := 118140960795 + 1931703 * 2 ^ 59
def prefixEnd_1931703 : Nat := 4983230072969 + 3 ^ 40 * 1931703 * 2
def baseEnd_1931703 : Nat := 440840942547627083035007

theorem tailTrace_1931703 : CollatzResearch.WordTrace tailWord_1931703 prefixEnd_1931703 440840942547627083035007 := by
  unfold tailWord_1931703
  simp only [CollatzResearch.WordTrace]
  refine ⟨70454996520777414452143763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46969997680518276301429175 70454996520777414452143763)
  ·
    refine ⟨105682494781166121678215645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70454996520777414452143763 105682494781166121678215645)
    ·
      refine ⟨39630935542937295629330867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105682494781166121678215645 39630935542937295629330867)
      ·
        refine ⟨59446403314405943443996301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39630935542937295629330867 59446403314405943443996301)
        ·
          refine ⟨22292401242902228791498613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59446403314405943443996301 22292401242902228791498613)
          ·
            refine ⟨2089912616522083949202995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22292401242902228791498613 2089912616522083949202995)
            ·
              refine ⟨3134868924783125923804493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089912616522083949202995 3134868924783125923804493)
              ·
                refine ⟨1175575846793672221426685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3134868924783125923804493 1175575846793672221426685)
                ·
                  refine ⟨440840942547627083035007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1175575846793672221426685 440840942547627083035007)
                  ·
                    rfl

theorem cell21_1931703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3].length) (baseStart_1931703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931703 prefixEnd_1931703 := by exact prefixLift 1931703
  have htrace : WordTrace (prefixWord ++ tailWord_1931703) baseStart_1931703 baseEnd_1931703 := by
    simpa [prefixWord, tailWord_1931703, baseEnd_1931703] using wordTrace_append hprefix tailTrace_1931703
  have hstable : (prefixWord ++ tailWord_1931703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931703).length < 2 ^ (prefixWord ++ tailWord_1931703).sum := by decide
  have hdescent : baseEnd_1931703 < baseStart_1931703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931782 : List Nat := [6, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1931782 : Nat := 118140960795 + 1931782 * 2 ^ 59
def prefixEnd_1931782 : Nat := 4983230072969 + 3 ^ 40 * 1931782 * 2
def baseEnd_1931782 : Nat := 146952990474646833739393

theorem tailTrace_1931782 : CollatzResearch.WordTrace tailWord_1931782 prefixEnd_1931782 146952990474646833739393 := by
  unfold tailWord_1931782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201808683984100342008425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46971918591660807296179733 2201808683984100342008425)
  ·
    refine ⟨1651356512988075256506319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2201808683984100342008425 1651356512988075256506319)
    ·
      refine ⟨2477034769482112884759479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651356512988075256506319 2477034769482112884759479)
      ·
        refine ⟨3715552154223169327139219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477034769482112884759479 3715552154223169327139219)
        ·
          refine ⟨5573328231334753990708829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715552154223169327139219 5573328231334753990708829)
          ·
            refine ⟨2089998086750532746515811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5573328231334753990708829 2089998086750532746515811)
            ·
              refine ⟨3134997130125799119773717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089998086750532746515811 3134997130125799119773717)
              ·
                refine ⟨146952990474646833739393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3134997130125799119773717 146952990474646833739393)
                ·
                  rfl

theorem cell21_1931782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1931782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931782 prefixEnd_1931782 := by exact prefixLift 1931782
  have htrace : WordTrace (prefixWord ++ tailWord_1931782) baseStart_1931782 baseEnd_1931782 := by
    simpa [prefixWord, tailWord_1931782, baseEnd_1931782] using wordTrace_append hprefix tailTrace_1931782
  have hstable : (prefixWord ++ tailWord_1931782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931782).length < 2 ^ (prefixWord ++ tailWord_1931782).sum := by decide
  have hdescent : baseEnd_1931782 < baseStart_1931782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931844 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1931844 : Nat := 118140960795 + 1931844 * 2 ^ 59
def prefixEnd_1931844 : Nat := 4983230072969 + 3 ^ 40 * 1931844 * 2
def baseEnd_1931844 : Nat := 440873120668642171184719

theorem tailTrace_1931844 : CollatzResearch.WordTrace tailWord_1931844 prefixEnd_1931844 440873120668642171184719 := by
  unfold tailWord_1931844
  simp only [CollatzResearch.WordTrace]
  refine ⟨35230069606633297766513293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46973426142177730355351057 35230069606633297766513293)
  ·
    refine ⟨13211276102487486662442485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35230069606633297766513293 13211276102487486662442485)
    ·
      refine ⟨1238557134608201874603983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13211276102487486662442485 1238557134608201874603983)
      ·
        refine ⟨1857835701912302811905975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238557134608201874603983 1857835701912302811905975)
        ·
          refine ⟨2786753552868454217858963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857835701912302811905975 2786753552868454217858963)
          ·
            refine ⟨4180130329302681326788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786753552868454217858963 4180130329302681326788445)
            ·
              refine ⟨1567548873488505497545667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180130329302681326788445 1567548873488505497545667)
              ·
                refine ⟨2351323310232758246318501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567548873488505497545667 2351323310232758246318501)
                ·
                  refine ⟨440873120668642171184719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351323310232758246318501 440873120668642171184719)
                  ·
                    rfl

theorem cell21_1931844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1931844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931844 prefixEnd_1931844 := by exact prefixLift 1931844
  have htrace : WordTrace (prefixWord ++ tailWord_1931844) baseStart_1931844 baseEnd_1931844 := by
    simpa [prefixWord, tailWord_1931844, baseEnd_1931844] using wordTrace_append hprefix tailTrace_1931844
  have hstable : (prefixWord ++ tailWord_1931844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931844).length < 2 ^ (prefixWord ++ tailWord_1931844).sum := by decide
  have hdescent : baseEnd_1931844 < baseStart_1931844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931897 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_1931897 : Nat := 118140960795 + 1931897 * 2 ^ 59
def prefixEnd_1931897 : Nat := 4983230072969 + 3 ^ 40 * 1931897 * 2
def baseEnd_1931897 : Nat := 440885215990725856801277

theorem tailTrace_1931897 : CollatzResearch.WordTrace tailWord_1931897 prefixEnd_1931897 440885215990725856801277 := by
  unfold tailWord_1931897
  simp only [CollatzResearch.WordTrace]
  refine ⟨70462072282074585584705945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46974714854716390389803963 70462072282074585584705945)
  ·
    refine ⟨52846554211555939188529459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70462072282074585584705945 52846554211555939188529459)
    ·
      refine ⟨79269831317333908782794189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52846554211555939188529459 79269831317333908782794189)
      ·
        refine ⟨29726186744000215793547821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79269831317333908782794189 29726186744000215793547821)
        ·
          refine ⟨11147320029000080922580433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29726186744000215793547821 11147320029000080922580433)
          ·
            refine ⟨8360490021750060691935325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11147320029000080922580433 8360490021750060691935325)
            ·
              refine ⟨3135183758156272759475747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8360490021750060691935325 3135183758156272759475747)
              ·
                refine ⟨4702775637234409139213621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135183758156272759475747 4702775637234409139213621)
                ·
                  refine ⟨440885215990725856801277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4702775637234409139213621 440885215990725856801277)
                  ·
                    rfl

theorem cell21_1931897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_1931897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931897 prefixEnd_1931897 := by exact prefixLift 1931897
  have htrace : WordTrace (prefixWord ++ tailWord_1931897) baseStart_1931897 baseEnd_1931897 := by
    simpa [prefixWord, tailWord_1931897, baseEnd_1931897] using wordTrace_append hprefix tailTrace_1931897
  have hstable : (prefixWord ++ tailWord_1931897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931897).length < 2 ^ (prefixWord ++ tailWord_1931897).sum := by decide
  have hdescent : baseEnd_1931897 < baseStart_1931897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1931959 : List Nat := [1, 1, 3, 1, 6, 2, 1, 6]
def baseStart_1931959 : Nat := 118140960795 + 1931959 * 2 ^ 59
def prefixEnd_1931959 : Nat := 4983230072969 + 3 ^ 40 * 1931959 * 2
def baseEnd_1931959 : Nat := 146966455078475842255939

theorem tailTrace_1931959 : CollatzResearch.WordTrace tailWord_1931959 prefixEnd_1931959 146966455078475842255939 := by
  unfold tailWord_1931959
  simp only [CollatzResearch.WordTrace]
  refine ⟨70464333607849970173462931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46976222405233313448975287 70464333607849970173462931)
  ·
    refine ⟨105696500411774955260194397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70464333607849970173462931 105696500411774955260194397)
    ·
      refine ⟨39636187654415608222572899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105696500411774955260194397 39636187654415608222572899)
      ·
        refine ⟨59454281481623412333859349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39636187654415608222572899 59454281481623412333859349)
        ·
          refine ⟨2786919444451097453149657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59454281481623412333859349 2786919444451097453149657)
          ·
            refine ⟨2090189583338323089862243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786919444451097453149657 2090189583338323089862243)
            ·
              refine ⟨3135284375007484634793365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090189583338323089862243 3135284375007484634793365)
              ·
                refine ⟨146966455078475842255939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3135284375007484634793365 146966455078475842255939)
                ·
                  rfl

theorem cell21_1931959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 6].length) (baseStart_1931959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1931959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1931959 prefixEnd_1931959 := by exact prefixLift 1931959
  have htrace : WordTrace (prefixWord ++ tailWord_1931959) baseStart_1931959 baseEnd_1931959 := by
    simpa [prefixWord, tailWord_1931959, baseEnd_1931959] using wordTrace_append hprefix tailTrace_1931959
  have hstable : (prefixWord ++ tailWord_1931959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1931959).length < 2 ^ (prefixWord ++ tailWord_1931959).sum := by decide
  have hdescent : baseEnd_1931959 < baseStart_1931959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1931959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932004 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_1932004 : Nat := 118140960795 + 1932004 * 2 ^ 59
def prefixEnd_1932004 : Nat := 4983230072969 + 3 ^ 40 * 1932004 * 2
def baseEnd_1932004 : Nat := 440909634848517448517725

theorem tailTrace_1932004 : CollatzResearch.WordTrace tailWord_1932004 prefixEnd_1932004 440909634848517448517725 := by
  unfold tailWord_1932004
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232987446343471429425533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46977316595124628572567377 35232987446343471429425533)
  ·
    refine ⟨13212370292378801786034575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35232987446343471429425533 13212370292378801786034575)
    ·
      refine ⟨19818555438568202679051863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13212370292378801786034575 19818555438568202679051863)
      ·
        refine ⟨29727833157852304018577795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19818555438568202679051863 29727833157852304018577795)
        ·
          refine ⟨44591749736778456027866693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29727833157852304018577795 44591749736778456027866693)
          ·
            refine ⟨8360953075645960505225005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44591749736778456027866693 8360953075645960505225005)
            ·
              refine ⟨3135357403367235189459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8360953075645960505225005 3135357403367235189459377)
              ·
                refine ⟨2351518052525426392094533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135357403367235189459377 2351518052525426392094533)
                ·
                  refine ⟨440909634848517448517725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351518052525426392094533 440909634848517448517725)
                  ·
                    rfl

theorem cell21_1932004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_1932004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932004 prefixEnd_1932004 := by exact prefixLift 1932004
  have htrace : WordTrace (prefixWord ++ tailWord_1932004) baseStart_1932004 baseEnd_1932004 := by
    simpa [prefixWord, tailWord_1932004, baseEnd_1932004] using wordTrace_append hprefix tailTrace_1932004
  have hstable : (prefixWord ++ tailWord_1932004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932004).length < 2 ^ (prefixWord ++ tailWord_1932004).sum := by decide
  have hdescent : baseEnd_1932004 < baseStart_1932004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932063 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_1932063 : Nat := 118140960795 + 1932063 * 2 ^ 59
def prefixEnd_1932063 : Nat := 4983230072969 + 3 ^ 40 * 1932063 * 2
def baseEnd_1932063 : Nat := 440923099452346457034271

theorem tailTrace_1932063 : CollatzResearch.WordTrace tailWord_1932063 prefixEnd_1932063 440923099452346457034271 := by
  unfold tailWord_1932063
  simp only [CollatzResearch.WordTrace]
  refine ⟨70468126799473195935248843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46978751199648797290165895 70468126799473195935248843)
  ·
    refine ⟨105702190199209793902873265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70468126799473195935248843 105702190199209793902873265)
    ·
      refine ⟨79276642649407345427154949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105702190199209793902873265 79276642649407345427154949)
      ·
        refine ⟨14864370496763877267591553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79276642649407345427154949 14864370496763877267591553)
        ·
          refine ⟨11148277872572907950693665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14864370496763877267591553 11148277872572907950693665)
          ·
            refine ⟨8361208404429680963020249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11148277872572907950693665 8361208404429680963020249)
            ·
              refine ⟨6270906303322260722265187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8361208404429680963020249 6270906303322260722265187)
              ·
                refine ⟨9406359454983391083397781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6270906303322260722265187 9406359454983391083397781)
                ·
                  refine ⟨440923099452346457034271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9406359454983391083397781 440923099452346457034271)
                  ·
                    rfl

theorem cell21_1932063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_1932063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932063 prefixEnd_1932063 := by exact prefixLift 1932063
  have htrace : WordTrace (prefixWord ++ tailWord_1932063) baseStart_1932063 baseEnd_1932063 := by
    simpa [prefixWord, tailWord_1932063, baseEnd_1932063] using wordTrace_append hprefix tailTrace_1932063
  have hstable : (prefixWord ++ tailWord_1932063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932063).length < 2 ^ (prefixWord ++ tailWord_1932063).sum := by decide
  have hdescent : baseEnd_1932063 < baseStart_1932063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932066 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1932066 : Nat := 118140960795 + 1932066 * 2 ^ 59
def prefixEnd_1932066 : Nat := 4983230072969 + 3 ^ 40 * 1932066 * 2
def baseEnd_1932066 : Nat := 440923784093219118484265

theorem tailTrace_1932066 : CollatzResearch.WordTrace tailWord_1932066 prefixEnd_1932066 440923784093219118484265 := by
  unfold tailWord_1932066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17617059054615581861902013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46978824145641551631738701 17617059054615581861902013)
  ·
    refine ⟨6606397145480843198213255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17617059054615581861902013 6606397145480843198213255)
    ·
      refine ⟨9909595718221264797319883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606397145480843198213255 9909595718221264797319883)
      ·
        refine ⟨14864393577331897195979825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909595718221264797319883 14864393577331897195979825)
        ·
          refine ⟨11148295182998922896984869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14864393577331897195979825 11148295182998922896984869)
          ·
            refine ⟨2090305346812298043184663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11148295182998922896984869 2090305346812298043184663)
            ·
              refine ⟨3135458020218447064776995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090305346812298043184663 3135458020218447064776995)
              ·
                refine ⟨4703187030327670597165493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135458020218447064776995 4703187030327670597165493)
                ·
                  refine ⟨440923784093219118484265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4703187030327670597165493 440923784093219118484265)
                  ·
                    rfl

theorem cell21_1932066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1932066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932066 prefixEnd_1932066 := by exact prefixLift 1932066
  have htrace : WordTrace (prefixWord ++ tailWord_1932066) baseStart_1932066 baseEnd_1932066 := by
    simpa [prefixWord, tailWord_1932066, baseEnd_1932066] using wordTrace_append hprefix tailTrace_1932066
  have hstable : (prefixWord ++ tailWord_1932066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932066).length < 2 ^ (prefixWord ++ tailWord_1932066).sum := by decide
  have hdescent : baseEnd_1932066 < baseStart_1932066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932139 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_1932139 : Nat := 118140960795 + 1932139 * 2 ^ 59
def prefixEnd_1932139 : Nat := 4983230072969 + 3 ^ 40 * 1932139 * 2
def baseEnd_1932139 : Nat := 440940443687787213767449

theorem tailTrace_1932139 : CollatzResearch.WordTrace tailWord_1932139 prefixEnd_1932139 440940443687787213767449 := by
  unfold tailWord_1932139
  simp only [CollatzResearch.WordTrace]
  refine ⟨70470898747197860915015471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46980599164798573943343647 70470898747197860915015471)
  ·
    refine ⟨105706348120796791372523207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70470898747197860915015471 105706348120796791372523207)
    ·
      refine ⟨158559522181195187058784811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105706348120796791372523207 158559522181195187058784811)
      ·
        refine ⟨237839283271792780588177217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158559522181195187058784811 237839283271792780588177217)
        ·
          refine ⟨178379462453844585441132913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237839283271792780588177217 178379462453844585441132913)
          ·
            refine ⟨133784596840383439080849685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178379462453844585441132913 133784596840383439080849685)
            ·
              refine ⟨6271152976892973706914829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133784596840383439080849685 6271152976892973706914829)
              ·
                refine ⟨2351682366334865140093061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6271152976892973706914829 2351682366334865140093061)
                ·
                  refine ⟨440940443687787213767449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351682366334865140093061 440940443687787213767449)
                  ·
                    rfl

theorem cell21_1932139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_1932139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932139 prefixEnd_1932139 := by exact prefixLift 1932139
  have htrace : WordTrace (prefixWord ++ tailWord_1932139) baseStart_1932139 baseEnd_1932139 := by
    simpa [prefixWord, tailWord_1932139, baseEnd_1932139] using wordTrace_append hprefix tailTrace_1932139
  have hstable : (prefixWord ++ tailWord_1932139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932139).length < 2 ^ (prefixWord ++ tailWord_1932139).sum := by decide
  have hdescent : baseEnd_1932139 < baseStart_1932139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932142 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1932142 : Nat := 118140960795 + 1932142 * 2 ^ 59
def prefixEnd_1932142 : Nat := 4983230072969 + 3 ^ 40 * 1932142 * 2
def baseEnd_1932142 : Nat := 440941128328659875217443

theorem tailTrace_1932142 : CollatzResearch.WordTrace tailWord_1932142 prefixEnd_1932142 440941128328659875217443 := by
  unfold tailWord_1932142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808876020773374053421835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46980672110791328284916453 8808876020773374053421835)
  ·
    refine ⟨13213314031160061080132753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8808876020773374053421835 13213314031160061080132753)
    ·
      refine ⟨9909985523370045810099565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13213314031160061080132753 9909985523370045810099565)
      ·
        refine ⟨3716244571263767178787337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9909985523370045810099565 3716244571263767178787337)
        ·
          refine ⟨2787183428447825384090503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716244571263767178787337 2787183428447825384090503)
          ·
            refine ⟨4180775142671738076135755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787183428447825384090503 4180775142671738076135755)
            ·
              refine ⟨6271162714007607114203633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180775142671738076135755 6271162714007607114203633)
              ·
                refine ⟨4703372035505705335652725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6271162714007607114203633 4703372035505705335652725)
                ·
                  refine ⟨440941128328659875217443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4703372035505705335652725 440941128328659875217443)
                  ·
                    rfl

theorem cell21_1932142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1932142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932142 prefixEnd_1932142 := by exact prefixLift 1932142
  have htrace : WordTrace (prefixWord ++ tailWord_1932142) baseStart_1932142 baseEnd_1932142 := by
    simpa [prefixWord, tailWord_1932142, baseEnd_1932142] using wordTrace_append hprefix tailTrace_1932142
  have hstable : (prefixWord ++ tailWord_1932142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932142).length < 2 ^ (prefixWord ++ tailWord_1932142).sum := by decide
  have hdescent : baseEnd_1932142 < baseStart_1932142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932170 : List Nat := [3, 1, 2, 4, 1, 2, 8]
def baseStart_1932170 : Nat := 118140960795 + 1932170 * 2 ^ 59
def prefixEnd_1932170 : Nat := 4983230072969 + 3 ^ 40 * 1932170 * 2
def baseEnd_1932170 : Nat := 48994168701126449861191

theorem tailTrace_1932170 : CollatzResearch.WordTrace tailWord_1932170 prefixEnd_1932170 48994168701126449861191 := by
  unfold tailWord_1932170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618007352521388302348491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46981352940057035472929309 17618007352521388302348491)
  ·
    refine ⟨26427011028782082453522737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17618007352521388302348491 26427011028782082453522737)
    ·
      refine ⟨19820258271586561840142053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26427011028782082453522737 19820258271586561840142053)
      ·
        refine ⟨3716298425922480345026635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19820258271586561840142053 3716298425922480345026635)
        ·
          refine ⟨5574447638883720517539953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716298425922480345026635 5574447638883720517539953)
          ·
            refine ⟨4180835729162790388154965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5574447638883720517539953 4180835729162790388154965)
            ·
              refine ⟨48994168701126449861191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4180835729162790388154965 48994168701126449861191)
              ·
                rfl

theorem cell21_1932170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 8].length) (baseStart_1932170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932170 prefixEnd_1932170 := by exact prefixLift 1932170
  have htrace : WordTrace (prefixWord ++ tailWord_1932170) baseStart_1932170 baseEnd_1932170 := by
    simpa [prefixWord, tailWord_1932170, baseEnd_1932170] using wordTrace_append hprefix tailTrace_1932170
  have hstable : (prefixWord ++ tailWord_1932170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932170).length < 2 ^ (prefixWord ++ tailWord_1932170).sum := by decide
  have hdescent : baseEnd_1932170 < baseStart_1932170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932249 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 4]
def baseStart_1932249 : Nat := 118140960795 + 1932249 * 2 ^ 59
def prefixEnd_1932249 : Nat := 4983230072969 + 3 ^ 40 * 1932249 * 2
def baseEnd_1932249 : Nat := 440965547186451466933891

theorem tailTrace_1932249 : CollatzResearch.WordTrace tailWord_1932249 prefixEnd_1932249 440965547186451466933891 := by
  unfold tailWord_1932249
  simp only [CollatzResearch.WordTrace]
  refine ⟨70474910776799349701519801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46983273851199566467679867 70474910776799349701519801)
  ·
    refine ⟨52856183082599512276139851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70474910776799349701519801 52856183082599512276139851)
    ·
      refine ⟨79284274623899268414209777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52856183082599512276139851 79284274623899268414209777)
      ·
        refine ⟨59463205967924451310657333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79284274623899268414209777 59463205967924451310657333)
        ·
          refine ⟨5574675559492917310374125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59463205967924451310657333 5574675559492917310374125)
          ·
            refine ⟨2090503334809843991390297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5574675559492917310374125 2090503334809843991390297)
            ·
              refine ⟨1567877501107382993542723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090503334809843991390297 1567877501107382993542723)
              ·
                refine ⟨2351816251661074490314085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567877501107382993542723 2351816251661074490314085)
                ·
                  refine ⟨440965547186451466933891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2351816251661074490314085 440965547186451466933891)
                  ·
                    rfl

theorem cell21_1932249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_1932249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932249 prefixEnd_1932249 := by exact prefixLift 1932249
  have htrace : WordTrace (prefixWord ++ tailWord_1932249) baseStart_1932249 baseEnd_1932249 := by
    simpa [prefixWord, tailWord_1932249, baseEnd_1932249] using wordTrace_append hprefix tailTrace_1932249
  have hstable : (prefixWord ++ tailWord_1932249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932249).length < 2 ^ (prefixWord ++ tailWord_1932249).sum := by decide
  have hdescent : baseEnd_1932249 < baseStart_1932249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932398 : List Nat := [4, 1, 2, 2, 1, 4, 7]
def baseStart_1932398 : Nat := 118140960795 + 1932398 * 2 ^ 59
def prefixEnd_1932398 : Nat := 4983230072969 + 3 ^ 40 * 1932398 * 2
def baseEnd_1932398 : Nat := 48999950112940035438917

theorem tailTrace_1932398 : CollatzResearch.WordTrace tailWord_1932398 prefixEnd_1932398 48999950112940035438917 := by
  unfold tailWord_1932398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810043156657443518586731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46986896835506365432462565 8810043156657443518586731)
  ·
    refine ⟨13215064734986165277880097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810043156657443518586731 13215064734986165277880097)
    ·
      refine ⟨9911298551239623958410073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13215064734986165277880097 9911298551239623958410073)
      ·
        refine ⟨7433473913429717968807555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9911298551239623958410073 7433473913429717968807555)
        ·
          refine ⟨11150210870144576953211333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7433473913429717968807555 11150210870144576953211333)
          ·
            refine ⟨2090664538152108178727125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11150210870144576953211333 2090664538152108178727125)
            ·
              refine ⟨48999950112940035438917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2090664538152108178727125 48999950112940035438917)
              ·
                rfl

theorem cell21_1932398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 7].length) (baseStart_1932398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932398 prefixEnd_1932398 := by exact prefixLift 1932398
  have htrace : WordTrace (prefixWord ++ tailWord_1932398) baseStart_1932398 baseEnd_1932398 := by
    simpa [prefixWord, tailWord_1932398, baseEnd_1932398] using wordTrace_append hprefix tailTrace_1932398
  have hstable : (prefixWord ++ tailWord_1932398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932398).length < 2 ^ (prefixWord ++ tailWord_1932398).sum := by decide
  have hdescent : baseEnd_1932398 < baseStart_1932398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932581 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 5]
def baseStart_1932581 : Nat := 118140960795 + 1932581 * 2 ^ 59
def prefixEnd_1932581 : Nat := 4983230072969 + 3 ^ 40 * 1932581 * 2
def baseEnd_1932581 : Nat := 441041314109692667399879

theorem tailTrace_1932581 : CollatzResearch.WordTrace tailWord_1932581 prefixEnd_1932581 441041314109692667399879 := by
  unfold tailWord_1932581
  simp only [CollatzResearch.WordTrace]
  refine ⟨70487019811596570402605597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46991346541064380268403731 70487019811596570402605597)
  ·
    refine ⟨26432632429348713900977099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70487019811596570402605597 26432632429348713900977099)
    ·
      refine ⟨39648948644023070851465649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26432632429348713900977099 39648948644023070851465649)
      ·
        refine ⟨29736711483017303138599237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39648948644023070851465649 29736711483017303138599237)
        ·
          refine ⟨5575633403065744338487357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29736711483017303138599237 5575633403065744338487357)
          ·
            refine ⟨2090862526149654126932759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5575633403065744338487357 2090862526149654126932759)
            ·
              refine ⟨3136293789224481190399139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090862526149654126932759 3136293789224481190399139)
              ·
                refine ⟨4704440683836721785598709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136293789224481190399139 4704440683836721785598709)
                ·
                  refine ⟨441041314109692667399879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4704440683836721785598709 441041314109692667399879)
                  ·
                    rfl

theorem cell21_1932581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_1932581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932581 prefixEnd_1932581 := by exact prefixLift 1932581
  have htrace : WordTrace (prefixWord ++ tailWord_1932581) baseStart_1932581 baseEnd_1932581 := by
    simpa [prefixWord, tailWord_1932581, baseEnd_1932581] using wordTrace_append hprefix tailTrace_1932581
  have hstable : (prefixWord ++ tailWord_1932581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932581).length < 2 ^ (prefixWord ++ tailWord_1932581).sum := by decide
  have hdescent : baseEnd_1932581 < baseStart_1932581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932595 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_1932595 : Nat := 118140960795 + 1932595 * 2 ^ 59
def prefixEnd_1932595 : Nat := 4983230072969 + 3 ^ 40 * 1932595 * 2
def baseEnd_1932595 : Nat := 441044509100431754166517

theorem tailTrace_1932595 : CollatzResearch.WordTrace tailWord_1932595 prefixEnd_1932595 441044509100431754166517 := by
  unfold tailWord_1932595
  simp only [CollatzResearch.WordTrace]
  refine ⟨70487530433545850793615239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46991686955697233862410159 70487530433545850793615239)
  ·
    refine ⟨105731295650318776190422859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70487530433545850793615239 105731295650318776190422859)
    ·
      refine ⟨158596943475478164285634289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105731295650318776190422859 158596943475478164285634289)
      ·
        refine ⟨118947707606608623214225717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158596943475478164285634289 118947707606608623214225717)
        ·
          refine ⟨11151347588119558426333661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118947707606608623214225717 11151347588119558426333661)
          ·
            refine ⟨4181755345544834409875123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11151347588119558426333661 4181755345544834409875123)
            ·
              refine ⟨6272633018317251614812685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181755345544834409875123 6272633018317251614812685)
              ·
                refine ⟨2352237381868969355554757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6272633018317251614812685 2352237381868969355554757)
                ·
                  refine ⟨441044509100431754166517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352237381868969355554757 441044509100431754166517)
                  ·
                    rfl

theorem cell21_1932595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_1932595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932595 prefixEnd_1932595 := by exact prefixLift 1932595
  have htrace : WordTrace (prefixWord ++ tailWord_1932595) baseStart_1932595 baseEnd_1932595 := by
    simpa [prefixWord, tailWord_1932595, baseEnd_1932595] using wordTrace_append hprefix tailTrace_1932595
  have hstable : (prefixWord ++ tailWord_1932595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932595).length < 2 ^ (prefixWord ++ tailWord_1932595).sum := by decide
  have hdescent : baseEnd_1932595 < baseStart_1932595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932761 : List Nat := [1, 2, 1, 2, 4, 3, 2, 6]
def baseStart_1932761 : Nat := 118140960795 + 1932761 * 2 ^ 59
def prefixEnd_1932761 : Nat := 4983230072969 + 3 ^ 40 * 1932761 * 2
def baseEnd_1932761 : Nat := 147027464187350784799837

theorem tailTrace_1932761 : CollatzResearch.WordTrace tailWord_1932761 prefixEnd_1932761 147027464187350784799837 := by
  unfold tailWord_1932761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70493584950944461144158137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46995723300629640762772091 70493584950944461144158137)
  ·
    refine ⟨52870188713208345858118603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70493584950944461144158137 52870188713208345858118603)
    ·
      refine ⟨79305283069812518787177905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52870188713208345858118603 79305283069812518787177905)
      ·
        refine ⟨59478962302359389090383429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79305283069812518787177905 59478962302359389090383429)
        ·
          refine ⟨11152305431692385454446893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59478962302359389090383429 11152305431692385454446893)
          ·
            refine ⟨4182114536884644545417585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11152305431692385454446893 4182114536884644545417585)
            ·
              refine ⟨3136585902663483409063189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182114536884644545417585 3136585902663483409063189)
              ·
                refine ⟨147027464187350784799837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3136585902663483409063189 147027464187350784799837)
                ·
                  rfl

theorem cell21_1932761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_1932761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932761 prefixEnd_1932761 := by exact prefixLift 1932761
  have htrace : WordTrace (prefixWord ++ tailWord_1932761) baseStart_1932761 baseEnd_1932761 := by
    simpa [prefixWord, tailWord_1932761, baseEnd_1932761] using wordTrace_append hprefix tailTrace_1932761
  have hstable : (prefixWord ++ tailWord_1932761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932761).length < 2 ^ (prefixWord ++ tailWord_1932761).sum := by decide
  have hdescent : baseEnd_1932761 < baseStart_1932761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932854 : List Nat := [5, 1, 2, 1, 3, 1, 8]
def baseStart_1932854 : Nat := 118140960795 + 1932854 * 2 ^ 59
def prefixEnd_1932854 : Nat := 4983230072969 + 3 ^ 40 * 1932854 * 2
def baseEnd_1932854 : Nat := 49011512936567206594369

theorem tailTrace_1932854 : CollatzResearch.WordTrace tailWord_1932854 prefixEnd_1932854 49011512936567206594369 := by
  unfold tailWord_1932854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406061058725471126705851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46997984626405025351529077 4406061058725471126705851)
  ·
    refine ⟨6609091588088206690058777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406061058725471126705851 6609091588088206690058777)
    ·
      refine ⟨4956818691066155017544083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6609091588088206690058777 4956818691066155017544083)
      ·
        refine ⟨7435228036599232526316125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956818691066155017544083 7435228036599232526316125)
        ·
          refine ⟨2788210513724712197368547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7435228036599232526316125 2788210513724712197368547)
          ·
            refine ⟨4182315770587068296052821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788210513724712197368547 4182315770587068296052821)
            ·
              refine ⟨49011512936567206594369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4182315770587068296052821 49011512936567206594369)
              ·
                rfl

theorem cell21_1932854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 8].length) (baseStart_1932854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1932854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1932854 prefixEnd_1932854 := by exact prefixLift 1932854
  have htrace : WordTrace (prefixWord ++ tailWord_1932854) baseStart_1932854 baseEnd_1932854 := by
    simpa [prefixWord, tailWord_1932854, baseEnd_1932854] using wordTrace_append hprefix tailTrace_1932854
  have hstable : (prefixWord ++ tailWord_1932854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932854).length < 2 ^ (prefixWord ++ tailWord_1932854).sum := by decide
  have hdescent : baseEnd_1932854 < baseStart_1932854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933037 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1933037 : Nat := 118140960795 + 1933037 * 2 ^ 59
def prefixEnd_1933037 : Nat := 4983230072969 + 3 ^ 40 * 1933037 * 2
def baseEnd_1933037 : Nat := 441145379522337207798947

theorem tailTrace_1933037 : CollatzResearch.WordTrace tailWord_1933037 prefixEnd_1933037 441145379522337207798947 := by
  unfold tailWord_1933037
  simp only [CollatzResearch.WordTrace]
  refine ⟨70503651497944560281205365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47002434331963040187470243 70503651497944560281205365)
  ·
    refine ⟨6609717327932302526363003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70503651497944560281205365 6609717327932302526363003)
    ·
      refine ⟨9914575991898453789544505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609717327932302526363003 9914575991898453789544505)
      ·
        refine ⟨7435931993923840342158379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9914575991898453789544505 7435931993923840342158379)
        ·
          refine ⟨11153897990885760513237569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435931993923840342158379 11153897990885760513237569)
          ·
            refine ⟨8365423493164320384928177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11153897990885760513237569 8365423493164320384928177)
            ·
              refine ⟨6274067619873240288696133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8365423493164320384928177 6274067619873240288696133)
              ·
                refine ⟨1176387678726232554130525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6274067619873240288696133 1176387678726232554130525)
                ·
                  refine ⟨441145379522337207798947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176387678726232554130525 441145379522337207798947)
                  ·
                    rfl

theorem cell21_1933037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1933037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933037 prefixEnd_1933037 := by exact prefixLift 1933037
  have htrace : WordTrace (prefixWord ++ tailWord_1933037) baseStart_1933037 baseEnd_1933037 := by
    simpa [prefixWord, tailWord_1933037, baseEnd_1933037] using wordTrace_append hprefix tailTrace_1933037
  have hstable : (prefixWord ++ tailWord_1933037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933037).length < 2 ^ (prefixWord ++ tailWord_1933037).sum := by decide
  have hdescent : baseEnd_1933037 < baseStart_1933037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933096 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_1933096 : Nat := 118140960795 + 1933096 * 2 ^ 59
def prefixEnd_1933096 : Nat := 4983230072969 + 3 ^ 40 * 1933096 * 2
def baseEnd_1933096 : Nat := 441158844126166216315493

theorem tailTrace_1933096 : CollatzResearch.WordTrace tailWord_1933096 prefixEnd_1933096 441158844126166216315493 := by
  unfold tailWord_1933096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35252901702365406678801571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47003868936487208905068761 35252901702365406678801571)
  ·
    refine ⟨52879352553548110018202357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35252901702365406678801571 52879352553548110018202357)
    ·
      refine ⟨4957439301895135314206471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52879352553548110018202357 4957439301895135314206471)
      ·
        refine ⟨7436158952842702971309707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957439301895135314206471 7436158952842702971309707)
        ·
          refine ⟨11154238429264054456964561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436158952842702971309707 11154238429264054456964561)
          ·
            refine ⟨8365678821948040842723421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11154238429264054456964561 8365678821948040842723421)
            ·
              refine ⟨3137129558230515316021283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8365678821948040842723421 3137129558230515316021283)
              ·
                refine ⟨4705694337345772974031925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137129558230515316021283 4705694337345772974031925)
                ·
                  refine ⟨441158844126166216315493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4705694337345772974031925 441158844126166216315493)
                  ·
                    rfl

theorem cell21_1933096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_1933096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933096 prefixEnd_1933096 := by exact prefixLift 1933096
  have htrace : WordTrace (prefixWord ++ tailWord_1933096) baseStart_1933096 baseEnd_1933096 := by
    simpa [prefixWord, tailWord_1933096, baseEnd_1933096] using wordTrace_append hprefix tailTrace_1933096
  have hstable : (prefixWord ++ tailWord_1933096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933096).length < 2 ^ (prefixWord ++ tailWord_1933096).sum := by decide
  have hdescent : baseEnd_1933096 < baseStart_1933096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933102 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_1933102 : Nat := 118140960795 + 1933102 * 2 ^ 59
def prefixEnd_1933102 : Nat := 4983230072969 + 3 ^ 40 * 1933102 * 2
def baseEnd_1933102 : Nat := 441160213407911539215481

theorem tailTrace_1933102 : CollatzResearch.WordTrace tailWord_1933102 prefixEnd_1933102 441160213407911539215481 := by
  unfold tailWord_1933102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813252780338634547790195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47004014828472717588214373 8813252780338634547790195)
  ·
    refine ⟨13219879170507951821685293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813252780338634547790195 13219879170507951821685293)
    ·
      refine ⟨4957454688940481933131985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13219879170507951821685293 4957454688940481933131985)
      ·
        refine ⟨3718091016705361449848989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4957454688940481933131985 3718091016705361449848989)
        ·
          refine ⟨1394284131264510543693371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3718091016705361449848989 1394284131264510543693371)
          ·
            refine ⟨2091426196896765815540057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394284131264510543693371 2091426196896765815540057)
            ·
              refine ⟨1568569647672574361655043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091426196896765815540057 1568569647672574361655043)
              ·
                refine ⟨2352854471508861542482565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568569647672574361655043 2352854471508861542482565)
                ·
                  refine ⟨441160213407911539215481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2352854471508861542482565 441160213407911539215481)
                  ·
                    rfl

theorem cell21_1933102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_1933102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933102 prefixEnd_1933102 := by exact prefixLift 1933102
  have htrace : WordTrace (prefixWord ++ tailWord_1933102) baseStart_1933102 baseEnd_1933102 := by
    simpa [prefixWord, tailWord_1933102, baseEnd_1933102] using wordTrace_append hprefix tailTrace_1933102
  have hstable : (prefixWord ++ tailWord_1933102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933102).length < 2 ^ (prefixWord ++ tailWord_1933102).sum := by decide
  have hdescent : baseEnd_1933102 < baseStart_1933102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933262 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1933262 : Nat := 118140960795 + 1933262 * 2 ^ 59
def prefixEnd_1933262 : Nat := 4983230072969 + 3 ^ 40 * 1933262 * 2
def baseEnd_1933262 : Nat := 441196727587786816548487

theorem tailTrace_1933262 : CollatzResearch.WordTrace tailWord_1933262 prefixEnd_1933262 441196727587786816548487 := by
  unfold tailWord_1933262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813982240266177963518255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47007905281419615805430693 8813982240266177963518255)
  ·
    refine ⟨13220973360399266945277383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813982240266177963518255 13220973360399266945277383)
    ·
      refine ⟨19831460040598900417916075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220973360399266945277383 19831460040598900417916075)
      ·
        refine ⟨29747190060898350626874113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19831460040598900417916075 29747190060898350626874113)
        ·
          refine ⟨22310392545673762970155585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29747190060898350626874113 22310392545673762970155585)
          ·
            refine ⟨16732794409255322227616689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22310392545673762970155585 16732794409255322227616689)
            ·
              refine ⟨12549595806941491670712517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16732794409255322227616689 12549595806941491670712517)
              ·
                refine ⟨2353049213801529688258597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12549595806941491670712517 2353049213801529688258597)
                ·
                  refine ⟨441196727587786816548487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353049213801529688258597 441196727587786816548487)
                  ·
                    rfl

theorem cell21_1933262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1933262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933262 prefixEnd_1933262 := by exact prefixLift 1933262
  have htrace : WordTrace (prefixWord ++ tailWord_1933262) baseStart_1933262 baseEnd_1933262 := by
    simpa [prefixWord, tailWord_1933262, baseEnd_1933262] using wordTrace_append hprefix tailTrace_1933262
  have hstable : (prefixWord ++ tailWord_1933262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933262).length < 2 ^ (prefixWord ++ tailWord_1933262).sum := by decide
  have hdescent : baseEnd_1933262 < baseStart_1933262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933279 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 4]
def baseStart_1933279 : Nat := 118140960795 + 1933279 * 2 ^ 59
def prefixEnd_1933279 : Nat := 4983230072969 + 3 ^ 40 * 1933279 * 2
def baseEnd_1933279 : Nat := 441200607219398564765119

theorem tailTrace_1933279 : CollatzResearch.WordTrace tailWord_1933279 prefixEnd_1933279 441200607219398564765119 := by
  unfold tailWord_1933279
  simp only [CollatzResearch.WordTrace]
  refine ⟨70512477963067835611514891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47008318642045223741009927 70512477963067835611514891)
  ·
    refine ⟨105768716944601753417272337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70512477963067835611514891 105768716944601753417272337)
    ·
      refine ⟨79326537708451315062954253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105768716944601753417272337 79326537708451315062954253)
      ·
        refine ⟨29747451640669243148607845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79326537708451315062954253 29747451640669243148607845)
        ·
          refine ⟨5577647182625483090363971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29747451640669243148607845 5577647182625483090363971)
          ·
            refine ⟨8366470773938224635545957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577647182625483090363971 8366470773938224635545957)
            ·
              refine ⟨1568713270113417119164867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8366470773938224635545957 1568713270113417119164867)
              ·
                refine ⟨2353069905170125678747301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568713270113417119164867 2353069905170125678747301)
                ·
                  refine ⟨441200607219398564765119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353069905170125678747301 441200607219398564765119)
                  ·
                    rfl

theorem cell21_1933279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4].length) (baseStart_1933279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933279 prefixEnd_1933279 := by exact prefixLift 1933279
  have htrace : WordTrace (prefixWord ++ tailWord_1933279) baseStart_1933279 baseEnd_1933279 := by
    simpa [prefixWord, tailWord_1933279, baseEnd_1933279] using wordTrace_append hprefix tailTrace_1933279
  have hstable : (prefixWord ++ tailWord_1933279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933279).length < 2 ^ (prefixWord ++ tailWord_1933279).sum := by decide
  have hdescent : baseEnd_1933279 < baseStart_1933279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933316 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1933316 : Nat := 118140960795 + 1933316 * 2 ^ 59
def prefixEnd_1933316 : Nat := 4983230072969 + 3 ^ 40 * 1933316 * 2
def baseEnd_1933316 : Nat := 441209051123494722648377

theorem tailTrace_1933316 : CollatzResearch.WordTrace tailWord_1933316 prefixEnd_1933316 441209051123494722648377 := by
  unfold tailWord_1933316
  simp only [CollatzResearch.WordTrace]
  refine ⟨35256913731966895465305901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47009218309289193953741201 35256913731966895465305901)
  ·
    refine ⟨13221342649487585799489713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35256913731966895465305901 13221342649487585799489713)
    ·
      refine ⟨9916006987115689349617285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13221342649487585799489713 9916006987115689349617285)
      ·
        refine ⟨1859251310084191753053241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9916006987115689349617285 1859251310084191753053241)
        ·
          refine ⟨1394438482563143814789931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859251310084191753053241 1394438482563143814789931)
          ·
            refine ⟨2091657723844715722184897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394438482563143814789931 2091657723844715722184897)
            ·
              refine ⟨1568743292883536791638673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091657723844715722184897 1568743292883536791638673)
              ·
                refine ⟨1176557469662652593729005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568743292883536791638673 1176557469662652593729005)
                ·
                  refine ⟨441209051123494722648377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176557469662652593729005 441209051123494722648377)
                  ·
                    rfl

theorem cell21_1933316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1933316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933316 prefixEnd_1933316 := by exact prefixLift 1933316
  have htrace : WordTrace (prefixWord ++ tailWord_1933316) baseStart_1933316 baseEnd_1933316 := by
    simpa [prefixWord, tailWord_1933316, baseEnd_1933316] using wordTrace_append hprefix tailTrace_1933316
  have hstable : (prefixWord ++ tailWord_1933316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933316).length < 2 ^ (prefixWord ++ tailWord_1933316).sum := by decide
  have hdescent : baseEnd_1933316 < baseStart_1933316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933324 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_1933324 : Nat := 118140960795 + 1933324 * 2 ^ 59
def prefixEnd_1933324 : Nat := 4983230072969 + 3 ^ 40 * 1933324 * 2
def baseEnd_1933324 : Nat := 441210876832488486515027

theorem tailTrace_1933324 : CollatzResearch.WordTrace tailWord_1933324 prefixEnd_1933324 441210876832488486515027 := by
  unfold tailWord_1933324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35257059623952404148451513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47009412831936538864602017 35257059623952404148451513)
  ·
    refine ⟨26442794717964303111338635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35257059623952404148451513 26442794717964303111338635)
    ·
      refine ⟨39664192076946454667007953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26442794717964303111338635 39664192076946454667007953)
      ·
        refine ⟨29748144057709841000255965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39664192076946454667007953 29748144057709841000255965)
        ·
          refine ⟨11155554021641190375095987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29748144057709841000255965 11155554021641190375095987)
          ·
            refine ⟨16733331032461785562643981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155554021641190375095987 16733331032461785562643981)
            ·
              refine ⟨6274999137173169585991493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16733331032461785562643981 6274999137173169585991493)
              ·
                refine ⟨1176562338219969297373405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6274999137173169585991493 1176562338219969297373405)
                ·
                  refine ⟨441210876832488486515027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176562338219969297373405 441210876832488486515027)
                  ·
                    rfl

theorem cell21_1933324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_1933324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933324 prefixEnd_1933324 := by exact prefixLift 1933324
  have htrace : WordTrace (prefixWord ++ tailWord_1933324) baseStart_1933324 baseEnd_1933324 := by
    simpa [prefixWord, tailWord_1933324, baseEnd_1933324] using wordTrace_append hprefix tailTrace_1933324
  have hstable : (prefixWord ++ tailWord_1933324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933324).length < 2 ^ (prefixWord ++ tailWord_1933324).sum := by decide
  have hdescent : baseEnd_1933324 < baseStart_1933324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933338 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1933338 : Nat := 118140960795 + 1933338 * 2 ^ 59
def prefixEnd_1933338 : Nat := 4983230072969 + 3 ^ 40 * 1933338 * 2
def baseEnd_1933338 : Nat := 441214071823227573281665

theorem tailTrace_1933338 : CollatzResearch.WordTrace tailWord_1933338 prefixEnd_1933338 441214071823227573281665 := by
  unfold tailWord_1933338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628657467463522171978167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47009753246569392458608445 17628657467463522171978167)
  ·
    refine ⟨26442986201195283257967251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17628657467463522171978167 26442986201195283257967251)
    ·
      refine ⟨39664479301792924886950877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26442986201195283257967251 39664479301792924886950877)
      ·
        refine ⟨14874179738172346832606579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39664479301792924886950877 14874179738172346832606579)
        ·
          refine ⟨22311269607258520248909869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874179738172346832606579 22311269607258520248909869)
          ·
            refine ⟨8366726102721945093341201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22311269607258520248909869 8366726102721945093341201)
            ·
              refine ⟨6275044577041458820005901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366726102721945093341201 6275044577041458820005901)
              ·
                refine ⟨2353141716390547057502213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6275044577041458820005901 2353141716390547057502213)
                ·
                  refine ⟨441214071823227573281665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353141716390547057502213 441214071823227573281665)
                  ·
                    rfl

theorem cell21_1933338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1933338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933338 prefixEnd_1933338 := by exact prefixLift 1933338
  have htrace : WordTrace (prefixWord ++ tailWord_1933338) baseStart_1933338 baseEnd_1933338 := by
    simpa [prefixWord, tailWord_1933338, baseEnd_1933338] using wordTrace_append hprefix tailTrace_1933338
  have hstable : (prefixWord ++ tailWord_1933338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933338).length < 2 ^ (prefixWord ++ tailWord_1933338).sum := by decide
  have hdescent : baseEnd_1933338 < baseStart_1933338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933383 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_1933383 : Nat := 118140960795 + 1933383 * 2 ^ 59
def prefixEnd_1933383 : Nat := 4983230072969 + 3 ^ 40 * 1933383 * 2
def baseEnd_1933383 : Nat := 441224341436317495031573

theorem tailTrace_1933383 : CollatzResearch.WordTrace tailWord_1933383 prefixEnd_1933383 441224341436317495031573 := by
  unfold tailWord_1933383
  simp only [CollatzResearch.WordTrace]
  refine ⟨70516271154691061373300803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47010847436460707582200535 70516271154691061373300803)
  ·
    refine ⟨105774406732036592059951205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70516271154691061373300803 105774406732036592059951205)
    ·
      refine ⟨19832701262256861011240851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105774406732036592059951205 19832701262256861011240851)
      ·
        refine ⟨29749051893385291516861277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19832701262256861011240851 29749051893385291516861277)
        ·
          refine ⟨11155894460019484318822979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29749051893385291516861277 11155894460019484318822979)
          ·
            refine ⟨16733841690029226478234469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155894460019484318822979 16733841690029226478234469)
            ·
              refine ⟨3137595316880479964668963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16733841690029226478234469 3137595316880479964668963)
              ·
                refine ⟨4706392975320719947003445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137595316880479964668963 4706392975320719947003445)
                ·
                  refine ⟨441224341436317495031573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706392975320719947003445 441224341436317495031573)
                  ·
                    rfl

theorem cell21_1933383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_1933383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933383 prefixEnd_1933383 := by exact prefixLift 1933383
  have htrace : WordTrace (prefixWord ++ tailWord_1933383) baseStart_1933383 baseEnd_1933383 := by
    simpa [prefixWord, tailWord_1933383, baseEnd_1933383] using wordTrace_append hprefix tailTrace_1933383
  have hstable : (prefixWord ++ tailWord_1933383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933383).length < 2 ^ (prefixWord ++ tailWord_1933383).sum := by decide
  have hdescent : baseEnd_1933383 < baseStart_1933383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933448 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_1933448 : Nat := 118140960795 + 1933448 * 2 ^ 59
def prefixEnd_1933448 : Nat := 4983230072969 + 3 ^ 40 * 1933448 * 2
def baseEnd_1933448 : Nat := 441239175321891826448107

theorem tailTrace_1933448 : CollatzResearch.WordTrace tailWord_1933448 prefixEnd_1933448 441239175321891826448107 := by
  unfold tailWord_1933448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259320949727788737208499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47012427932970384982944665 35259320949727788737208499)
  ·
    refine ⟨52888981424591683105812749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35259320949727788737208499 52888981424591683105812749)
    ·
      refine ⟨19833368034221881164679781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52888981424591683105812749 19833368034221881164679781)
      ·
        refine ⟨3718756506416602718377459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19833368034221881164679781 3718756506416602718377459)
        ·
          refine ⟨5578134759624904077566189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718756506416602718377459 5578134759624904077566189)
          ·
            refine ⟨2091800534859339029087321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5578134759624904077566189 2091800534859339029087321)
            ·
              refine ⟨1568850401144504271815491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091800534859339029087321 1568850401144504271815491)
              ·
                refine ⟨2353275601716756407723237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568850401144504271815491 2353275601716756407723237)
                ·
                  refine ⟨441239175321891826448107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353275601716756407723237 441239175321891826448107)
                  ·
                    rfl

theorem cell21_1933448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_1933448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933448 prefixEnd_1933448 := by exact prefixLift 1933448
  have htrace : WordTrace (prefixWord ++ tailWord_1933448) baseStart_1933448 baseEnd_1933448 := by
    simpa [prefixWord, tailWord_1933448, baseEnd_1933448] using wordTrace_append hprefix tailTrace_1933448
  have hstable : (prefixWord ++ tailWord_1933448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933448).length < 2 ^ (prefixWord ++ tailWord_1933448).sum := by decide
  have hdescent : baseEnd_1933448 < baseStart_1933448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933490 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1933490 : Nat := 118140960795 + 1933490 * 2 ^ 59
def prefixEnd_1933490 : Nat := 4983230072969 + 3 ^ 40 * 1933490 * 2
def baseEnd_1933490 : Nat := 441248760294109086748021

theorem tailTrace_1933490 : CollatzResearch.WordTrace tailWord_1933490 prefixEnd_1933490 441248760294109086748021 := by
  unfold tailWord_1933490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17630043441325854661861481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47013449176868945764963949 17630043441325854661861481)
  ·
    refine ⟨13222532580994390996396111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17630043441325854661861481 13222532580994390996396111)
    ·
      refine ⟨19833798871491586494594167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13222532580994390996396111 19833798871491586494594167)
      ·
        refine ⟨29750698307237379741891251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19833798871491586494594167 29750698307237379741891251)
        ·
          refine ⟨44626047460856069612836877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29750698307237379741891251 44626047460856069612836877)
          ·
            refine ⟨16734767797821026104813829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44626047460856069612836877 16734767797821026104813829)
            ·
              refine ⟨3137768962091442394652593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16734767797821026104813829 3137768962091442394652593)
              ·
                refine ⟨2353326721568581795989445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137768962091442394652593 2353326721568581795989445)
                ·
                  refine ⟨441248760294109086748021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353326721568581795989445 441248760294109086748021)
                  ·
                    rfl

theorem cell21_1933490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1933490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933490 prefixEnd_1933490 := by exact prefixLift 1933490
  have htrace : WordTrace (prefixWord ++ tailWord_1933490) baseStart_1933490 baseEnd_1933490 := by
    simpa [prefixWord, tailWord_1933490, baseEnd_1933490] using wordTrace_append hprefix tailTrace_1933490
  have hstable : (prefixWord ++ tailWord_1933490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933490).length < 2 ^ (prefixWord ++ tailWord_1933490).sum := by decide
  have hdescent : baseEnd_1933490 < baseStart_1933490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933504 : List Nat := [2, 1, 1, 2, 5, 1, 3, 6]
def baseStart_1933504 : Nat := 118140960795 + 1933504 * 2 ^ 59
def prefixEnd_1933504 : Nat := 4983230072969 + 3 ^ 40 * 1933504 * 2
def baseEnd_1933504 : Nat := 147083985094949391171553

theorem tailTrace_1933504 : CollatzResearch.WordTrace tailWord_1933504 prefixEnd_1933504 147083985094949391171553 := by
  unfold tailWord_1933504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260342193626349519227783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47013789591501799358970377 35260342193626349519227783)
  ·
    refine ⟨52890513290439524278841675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35260342193626349519227783 52890513290439524278841675)
    ·
      refine ⟨79335769935659286418262513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52890513290439524278841675 79335769935659286418262513)
      ·
        refine ⟨59501827451744464813696885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79335769935659286418262513 59501827451744464813696885)
        ·
          refine ⟨5578296323601043576284083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59501827451744464813696885 5578296323601043576284083)
          ·
            refine ⟨8367444485401565364426125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578296323601043576284083 8367444485401565364426125)
            ·
              refine ⟨3137791682025587011659797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8367444485401565364426125 3137791682025587011659797)
              ·
                refine ⟨147083985094949391171553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3137791682025587011659797 147083985094949391171553)
                ·
                  rfl

theorem cell21_1933504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_1933504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933504 prefixEnd_1933504 := by exact prefixLift 1933504
  have htrace : WordTrace (prefixWord ++ tailWord_1933504) baseStart_1933504 baseEnd_1933504 := by
    simpa [prefixWord, tailWord_1933504, baseEnd_1933504] using wordTrace_append hprefix tailTrace_1933504
  have hstable : (prefixWord ++ tailWord_1933504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933504).length < 2 ^ (prefixWord ++ tailWord_1933504).sum := by decide
  have hdescent : baseEnd_1933504 < baseStart_1933504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933597 : List Nat := [1, 4, 2, 3, 2, 2, 7]
def baseStart_1933597 : Nat := 118140960795 + 1933597 * 2 ^ 59
def prefixEnd_1933597 : Nat := 4983230072969 + 3 ^ 40 * 1933597 * 2
def baseEnd_1933597 : Nat := 49030353239100075384941

theorem tailTrace_1933597 : CollatzResearch.WordTrace tailWord_1933597 prefixEnd_1933597 49030353239100075384941 := by
  unfold tailWord_1933597
  simp only [CollatzResearch.WordTrace]
  refine ⟨70524076375915775921591045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47016050917277183947727363 70524076375915775921591045)
  ·
    refine ⟨13223264320484207985298321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70524076375915775921591045 13223264320484207985298321)
    ·
      refine ⟨9917448240363155988973741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13223264320484207985298321 9917448240363155988973741)
      ·
        refine ⟨3719043090136183495865153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9917448240363155988973741 3719043090136183495865153)
        ·
          refine ⟨2789282317602137621898865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3719043090136183495865153 2789282317602137621898865)
          ·
            refine ⟨2091961738201603216424149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2789282317602137621898865 2091961738201603216424149)
            ·
              refine ⟨49030353239100075384941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2091961738201603216424149 49030353239100075384941)
              ·
                rfl

theorem cell21_1933597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 7].length) (baseStart_1933597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933597 prefixEnd_1933597 := by exact prefixLift 1933597
  have htrace : WordTrace (prefixWord ++ tailWord_1933597) baseStart_1933597 baseEnd_1933597 := by
    simpa [prefixWord, tailWord_1933597, baseEnd_1933597] using wordTrace_append hprefix tailTrace_1933597
  have hstable : (prefixWord ++ tailWord_1933597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933597).length < 2 ^ (prefixWord ++ tailWord_1933597).sum := by decide
  have hdescent : baseEnd_1933597 < baseStart_1933597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933614 : List Nat := [4, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1933614 : Nat := 118140960795 + 1933614 * 2 ^ 59
def prefixEnd_1933614 : Nat := 4983230072969 + 3 ^ 40 * 1933614 * 2
def baseEnd_1933614 : Nat := 147092352927837475560367

theorem tailTrace_1933614 : CollatzResearch.WordTrace tailWord_1933614 prefixEnd_1933614 147092352927837475560367 := by
  unfold tailWord_1933614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815587052106773478119987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47016464277902791883306597 8815587052106773478119987)
  ·
    refine ⟨13223380578160160217179981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8815587052106773478119987 13223380578160160217179981)
    ·
      refine ⟨4958767716810060081442493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13223380578160160217179981 4958767716810060081442493)
      ·
        refine ⟨1859537893803772530540935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4958767716810060081442493 1859537893803772530540935)
        ·
          refine ⟨2789306840705658795811403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859537893803772530540935 2789306840705658795811403)
          ·
            refine ⟨4183960261058488193717105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789306840705658795811403 4183960261058488193717105)
            ·
              refine ⟨3137970195793866145287829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183960261058488193717105 3137970195793866145287829)
              ·
                refine ⟨147092352927837475560367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3137970195793866145287829 147092352927837475560367)
                ·
                  rfl

theorem cell21_1933614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1933614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933614 prefixEnd_1933614 := by exact prefixLift 1933614
  have htrace : WordTrace (prefixWord ++ tailWord_1933614) baseStart_1933614 baseEnd_1933614 := by
    simpa [prefixWord, tailWord_1933614, baseEnd_1933614] using wordTrace_append hprefix tailTrace_1933614
  have hstable : (prefixWord ++ tailWord_1933614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933614).length < 2 ^ (prefixWord ++ tailWord_1933614).sum := by decide
  have hdescent : baseEnd_1933614 < baseStart_1933614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933639 : List Nat := [1, 1, 4, 1, 2, 2, 1, 9]
def baseStart_1933639 : Nat := 118140960795 + 1933639 * 2 ^ 59
def prefixEnd_1933639 : Nat := 4983230072969 + 3 ^ 40 * 1933639 * 2
def baseEnd_1933639 : Nat := 147094254708039312921461

theorem tailTrace_1933639 : CollatzResearch.WordTrace tailWord_1933639 prefixEnd_1933639 147094254708039312921461 := by
  unfold tailWord_1933639
  simp only [CollatzResearch.WordTrace]
  refine ⟨70525608241763617094619971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47017072161175744729746647 70525608241763617094619971)
  ·
    refine ⟨105788412362645425641929957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70525608241763617094619971 105788412362645425641929957)
    ·
      refine ⟨19835327317996017307861867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105788412362645425641929957 19835327317996017307861867)
      ·
        refine ⟨29752990976994025961792801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19835327317996017307861867 29752990976994025961792801)
        ·
          refine ⟨22314743232745519471344601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29752990976994025961792801 22314743232745519471344601)
          ·
            refine ⟨16736057424559139603508451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22314743232745519471344601 16736057424559139603508451)
            ·
              refine ⟨25104086136838709405262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16736057424559139603508451 25104086136838709405262677)
              ·
                refine ⟨147094254708039312921461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25104086136838709405262677 147094254708039312921461)
                ·
                  rfl

theorem cell21_1933639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_1933639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933639 prefixEnd_1933639 := by exact prefixLift 1933639
  have htrace : WordTrace (prefixWord ++ tailWord_1933639) baseStart_1933639 baseEnd_1933639 := by
    simpa [prefixWord, tailWord_1933639, baseEnd_1933639] using wordTrace_append hprefix tailTrace_1933639
  have hstable : (prefixWord ++ tailWord_1933639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933639).length < 2 ^ (prefixWord ++ tailWord_1933639).sum := by decide
  have hdescent : baseEnd_1933639 < baseStart_1933639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933704 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_1933704 : Nat := 118140960795 + 1933704 * 2 ^ 59
def prefixEnd_1933704 : Nat := 4983230072969 + 3 ^ 40 * 1933704 * 2
def baseEnd_1933704 : Nat := 441297598009692270180917

theorem tailTrace_1933704 : CollatzResearch.WordTrace tailWord_1933704 prefixEnd_1933704 441297598009692270180917 := by
  unfold tailWord_1933704
  simp only [CollatzResearch.WordTrace]
  refine ⟨35263989493264066597868083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47018652657685422130490777 35263989493264066597868083)
  ·
    refine ⟨52895984239896099896802125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35263989493264066597868083 52895984239896099896802125)
    ·
      refine ⟨19835994089961037461300797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52895984239896099896802125 19835994089961037461300797)
      ·
        refine ⟨7438497783735389047987799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19835994089961037461300797 7438497783735389047987799)
        ·
          refine ⟨11157746675603083571981699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438497783735389047987799 11157746675603083571981699)
          ·
            refine ⟨16736620013404625357972549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157746675603083571981699 16736620013404625357972549)
            ·
              refine ⟨3138116252513367254619853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16736620013404625357972549 3138116252513367254619853)
              ·
                refine ⟨1176793594692512720482445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138116252513367254619853 1176793594692512720482445)
                ·
                  refine ⟨441297598009692270180917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176793594692512720482445 441297598009692270180917)
                  ·
                    rfl

theorem cell21_1933704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_1933704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933704 prefixEnd_1933704 := by exact prefixLift 1933704
  have htrace : WordTrace (prefixWord ++ tailWord_1933704) baseStart_1933704 baseEnd_1933704 := by
    simpa [prefixWord, tailWord_1933704, baseEnd_1933704] using wordTrace_append hprefix tailTrace_1933704
  have hstable : (prefixWord ++ tailWord_1933704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933704).length < 2 ^ (prefixWord ++ tailWord_1933704).sum := by decide
  have hdescent : baseEnd_1933704 < baseStart_1933704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933735 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 4]
def baseStart_1933735 : Nat := 118140960795 + 1933735 * 2 ^ 59
def prefixEnd_1933735 : Nat := 4983230072969 + 3 ^ 40 * 1933735 * 2
def baseEnd_1933735 : Nat := 441304672632043105164187

theorem tailTrace_1933735 : CollatzResearch.WordTrace tailWord_1933735 prefixEnd_1933735 441304672632043105164187 := by
  unfold tailWord_1933735
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529109649415825490114659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47019406432943883660076439 70529109649415825490114659)
  ·
    refine ⟨105793664474123738235171989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70529109649415825490114659 105793664474123738235171989)
    ·
      refine ⟨4959078022224550229773687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105793664474123738235171989 4959078022224550229773687)
      ·
        refine ⟨7438617033336825344660531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959078022224550229773687 7438617033336825344660531)
        ·
          refine ⟨11157925550005238016990797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438617033336825344660531 11157925550005238016990797)
          ·
            refine ⟨4184222081251964256371549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11157925550005238016990797 4184222081251964256371549)
            ·
              refine ⟨1569083280469486596139331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4184222081251964256371549 1569083280469486596139331)
              ·
                refine ⟨2353624920704229894208997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569083280469486596139331 2353624920704229894208997)
                ·
                  refine ⟨441304672632043105164187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2353624920704229894208997 441304672632043105164187)
                  ·
                    rfl

theorem cell21_1933735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4].length) (baseStart_1933735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933735 prefixEnd_1933735 := by exact prefixLift 1933735
  have htrace : WordTrace (prefixWord ++ tailWord_1933735) baseStart_1933735 baseEnd_1933735 := by
    simpa [prefixWord, tailWord_1933735, baseEnd_1933735] using wordTrace_append hprefix tailTrace_1933735
  have hstable : (prefixWord ++ tailWord_1933735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933735).length < 2 ^ (prefixWord ++ tailWord_1933735).sum := by decide
  have hdescent : baseEnd_1933735 < baseStart_1933735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933746 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1933746 : Nat := 118140960795 + 1933746 * 2 ^ 59
def prefixEnd_1933746 : Nat := 4983230072969 + 3 ^ 40 * 1933746 * 2
def baseEnd_1933746 : Nat := 441307182981909530480831

theorem tailTrace_1933746 : CollatzResearch.WordTrace tailWord_1933746 prefixEnd_1933746 441307182981909530480831 := by
  unfold tailWord_1933746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632377713093993592191273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47019673901583982912510061 17632377713093993592191273)
  ·
    refine ⟨13224283284820495194143455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17632377713093993592191273 13224283284820495194143455)
    ·
      refine ⟨19836424927230742791215183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13224283284820495194143455 19836424927230742791215183)
      ·
        refine ⟨29754637390846114186822775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19836424927230742791215183 29754637390846114186822775)
        ·
          refine ⟨44631956086269171280234163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29754637390846114186822775 44631956086269171280234163)
          ·
            refine ⟨66947934129403756920351245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44631956086269171280234163 66947934129403756920351245)
            ·
              refine ⟨25105475298526408845131717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66947934129403756920351245 25105475298526408845131717)
              ·
                refine ⟨4707276618473701658462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25105475298526408845131717 4707276618473701658462197)
                ·
                  refine ⟨441307182981909530480831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707276618473701658462197 441307182981909530480831)
                  ·
                    rfl

theorem cell21_1933746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1933746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933746 prefixEnd_1933746 := by exact prefixLift 1933746
  have htrace : WordTrace (prefixWord ++ tailWord_1933746) baseStart_1933746 baseEnd_1933746 := by
    simpa [prefixWord, tailWord_1933746, baseEnd_1933746] using wordTrace_append hprefix tailTrace_1933746
  have hstable : (prefixWord ++ tailWord_1933746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933746).length < 2 ^ (prefixWord ++ tailWord_1933746).sum := by decide
  have hdescent : baseEnd_1933746 < baseStart_1933746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933780 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1933780 : Nat := 118140960795 + 1933780 * 2 ^ 59
def prefixEnd_1933780 : Nat := 4983230072969 + 3 ^ 40 * 1933780 * 2
def baseEnd_1933780 : Nat := 441314942245133026914095

theorem tailTrace_1933780 : CollatzResearch.WordTrace tailWord_1933780 prefixEnd_1933780 441314942245133026914095 := by
  unfold tailWord_1933780
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265375467126399087751397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47020500622835198783668529 35265375467126399087751397)
  ·
    refine ⟨6612257900086199828953387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35265375467126399087751397 6612257900086199828953387)
    ·
      refine ⟨9918386850129299743430081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6612257900086199828953387 9918386850129299743430081)
      ·
        refine ⟨7438790137596974807572561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9918386850129299743430081 7438790137596974807572561)
        ·
          refine ⟨5579092603197731105679421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438790137596974807572561 5579092603197731105679421)
          ·
            refine ⟨2092159726199149164629783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5579092603197731105679421 2092159726199149164629783)
            ·
              refine ⟨3138239589298723746944675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092159726199149164629783 3138239589298723746944675)
              ·
                refine ⟨4707359383948085620417013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138239589298723746944675 4707359383948085620417013)
                ·
                  refine ⟨441314942245133026914095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707359383948085620417013 441314942245133026914095)
                  ·
                    rfl

theorem cell21_1933780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1933780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933780 prefixEnd_1933780 := by exact prefixLift 1933780
  have htrace : WordTrace (prefixWord ++ tailWord_1933780) baseStart_1933780 baseEnd_1933780 := by
    simpa [prefixWord, tailWord_1933780, baseEnd_1933780] using wordTrace_append hprefix tailTrace_1933780
  have hstable : (prefixWord ++ tailWord_1933780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933780).length < 2 ^ (prefixWord ++ tailWord_1933780).sum := by decide
  have hdescent : baseEnd_1933780 < baseStart_1933780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933791 : List Nat := [1, 1, 2, 3, 3, 2, 1, 8]
def baseStart_1933791 : Nat := 118140960795 + 1933791 * 2 ^ 59
def prefixEnd_1933791 : Nat := 4983230072969 + 3 ^ 40 * 1933791 * 2
def baseEnd_1933791 : Nat := 147105817531666484076913

theorem tailTrace_1933791 : CollatzResearch.WordTrace tailWord_1933791 prefixEnd_1933791 147105817531666484076913 := by
  unfold tailWord_1933791
  simp only [CollatzResearch.WordTrace]
  refine ⟨70531152137212947054153227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47020768091475298036102151 70531152137212947054153227)
  ·
    refine ⟨105796728205819420581229841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70531152137212947054153227 105796728205819420581229841)
    ·
      refine ⟨79347546154364565435922381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105796728205819420581229841 79347546154364565435922381)
      ·
        refine ⟨29755329807886712038470893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79347546154364565435922381 29755329807886712038470893)
        ·
          refine ⟨11158248677957517014426585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29755329807886712038470893 11158248677957517014426585)
          ·
            refine ⟨8368686508468137760819939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11158248677957517014426585 8368686508468137760819939)
            ·
              refine ⟨12553029762702206641229909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368686508468137760819939 12553029762702206641229909)
              ·
                refine ⟨147105817531666484076913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12553029762702206641229909 147105817531666484076913)
                ·
                  rfl

theorem cell21_1933791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_1933791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933791 prefixEnd_1933791 := by exact prefixLift 1933791
  have htrace : WordTrace (prefixWord ++ tailWord_1933791) baseStart_1933791 baseEnd_1933791 := by
    simpa [prefixWord, tailWord_1933791, baseEnd_1933791] using wordTrace_append hprefix tailTrace_1933791
  have hstable : (prefixWord ++ tailWord_1933791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933791).length < 2 ^ (prefixWord ++ tailWord_1933791).sum := by decide
  have hdescent : baseEnd_1933791 < baseStart_1933791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933898 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1933898 : Nat := 118140960795 + 1933898 * 2 ^ 59
def prefixEnd_1933898 : Nat := 4983230072969 + 3 ^ 40 * 1933898 * 2
def baseEnd_1933898 : Nat := 441341871452791043947187

theorem tailTrace_1933898 : CollatzResearch.WordTrace tailWord_1933898 prefixEnd_1933898 441341871452791043947187 := by
  unfold tailWord_1933898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17633763686956326082074587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47023369831883536218865565 17633763686956326082074587)
  ·
    refine ⟨26450645530434489123111881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17633763686956326082074587 26450645530434489123111881)
    ·
      refine ⟨19837984147825866842333911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26450645530434489123111881 19837984147825866842333911)
      ·
        refine ⟨29756976221738800263500867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19837984147825866842333911 29756976221738800263500867)
        ·
          refine ⟨44635464332608200395251301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29756976221738800263500867 44635464332608200395251301)
          ·
            refine ⟨8369149562364037574109619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44635464332608200395251301 8369149562364037574109619)
            ·
              refine ⟨12553724343546056361164429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369149562364037574109619 12553724343546056361164429)
              ·
                refine ⟨4707646628829771135436661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12553724343546056361164429 4707646628829771135436661)
                ·
                  refine ⟨441341871452791043947187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707646628829771135436661 441341871452791043947187)
                  ·
                    rfl

theorem cell21_1933898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1933898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933898 prefixEnd_1933898 := by exact prefixLift 1933898
  have htrace : WordTrace (prefixWord ++ tailWord_1933898) baseStart_1933898 baseEnd_1933898 := by
    simpa [prefixWord, tailWord_1933898, baseEnd_1933898] using wordTrace_append hprefix tailTrace_1933898
  have hstable : (prefixWord ++ tailWord_1933898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933898).length < 2 ^ (prefixWord ++ tailWord_1933898).sum := by decide
  have hdescent : baseEnd_1933898 < baseStart_1933898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933949 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 3]
def baseStart_1933949 : Nat := 118140960795 + 1933949 * 2 ^ 59
def prefixEnd_1933949 : Nat := 4983230072969 + 3 ^ 40 * 1933949 * 2
def baseEnd_1933949 : Nat := 441353510347626288597083

theorem tailTrace_1933949 : CollatzResearch.WordTrace tailWord_1933949 prefixEnd_1933949 441353510347626288597083 := by
  unfold tailWord_1933949
  simp only [CollatzResearch.WordTrace]
  refine ⟨70536914870640540038404901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47024609913760360025603267 70536914870640540038404901)
  ·
    refine ⟨13225671538245101257200919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70536914870640540038404901 13225671538245101257200919)
    ·
      refine ⟨19838507307367651885801379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13225671538245101257200919 19838507307367651885801379)
      ·
        refine ⟨29757760961051477828702069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19838507307367651885801379 29757760961051477828702069)
        ·
          refine ⟨2789790090098576046440819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29757760961051477828702069 2789790090098576046440819)
          ·
            refine ⟨4184685135147864069661229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789790090098576046440819 4184685135147864069661229)
            ·
              refine ⟨1569256925680449026122961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4184685135147864069661229 1569256925680449026122961)
              ·
                refine ⟨1176942694260336769592221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569256925680449026122961 1176942694260336769592221)
                ·
                  refine ⟨441353510347626288597083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1176942694260336769592221 441353510347626288597083)
                  ·
                    rfl

theorem cell21_1933949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_1933949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1933949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1933949 prefixEnd_1933949 := by exact prefixLift 1933949
  have htrace : WordTrace (prefixWord ++ tailWord_1933949) baseStart_1933949 baseEnd_1933949 := by
    simpa [prefixWord, tailWord_1933949, baseEnd_1933949] using wordTrace_append hprefix tailTrace_1933949
  have hstable : (prefixWord ++ tailWord_1933949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933949).length < 2 ^ (prefixWord ++ tailWord_1933949).sum := by decide
  have hdescent : baseEnd_1933949 < baseStart_1933949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934064 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_1934064 : Nat := 118140960795 + 1934064 * 2 ^ 59
def prefixEnd_1934064 : Nat := 4983230072969 + 3 ^ 40 * 1934064 * 2
def baseEnd_1934064 : Nat := 441379754914411644180181

theorem tailTrace_1934064 : CollatzResearch.WordTrace tailWord_1934064 prefixEnd_1934064 441379754914411644180181 := by
  unfold tailWord_1934064
  simp only [CollatzResearch.WordTrace]
  refine ⟨35270554632611957339420623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47027406176815943119227497 35270554632611957339420623)
  ·
    refine ⟨52905831948917936009130935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35270554632611957339420623 52905831948917936009130935)
    ·
      refine ⟨79358747923376904013696403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52905831948917936009130935 79358747923376904013696403)
      ·
        refine ⟨119038121885065356020544605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79358747923376904013696403 119038121885065356020544605)
        ·
          refine ⟨44639295706899508507704227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119038121885065356020544605 44639295706899508507704227)
          ·
            refine ⟨66958943560349262761556341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44639295706899508507704227 66958943560349262761556341)
            ·
              refine ⟨6277400958782743383895907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66958943560349262761556341 6277400958782743383895907)
              ·
                refine ⟨9416101438174115075843861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277400958782743383895907 9416101438174115075843861)
                ·
                  refine ⟨441379754914411644180181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9416101438174115075843861 441379754914411644180181)
                  ·
                    rfl

theorem cell21_1934064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_1934064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934064 prefixEnd_1934064 := by exact prefixLift 1934064
  have htrace : WordTrace (prefixWord ++ tailWord_1934064) baseStart_1934064 baseEnd_1934064 := by
    simpa [prefixWord, tailWord_1934064, baseEnd_1934064] using wordTrace_append hprefix tailTrace_1934064
  have hstable : (prefixWord ++ tailWord_1934064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934064).length < 2 ^ (prefixWord ++ tailWord_1934064).sum := by decide
  have hdescent : baseEnd_1934064 < baseStart_1934064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934132 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1934132 : Nat := 118140960795 + 1934132 * 2 ^ 59
def prefixEnd_1934132 : Nat := 4983230072969 + 3 ^ 40 * 1934132 * 2
def baseEnd_1934132 : Nat := 441395273440858637046709

theorem tailTrace_1934132 : CollatzResearch.WordTrace tailWord_1934132 prefixEnd_1934132 441395273440858637046709 := by
  unfold tailWord_1934132
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271794714488781146158325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47029059619318374861544433 35271794714488781146158325)
  ·
    refine ⟨3306730754483323232452343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35271794714488781146158325 3306730754483323232452343)
    ·
      refine ⟨4960096131724984848678515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306730754483323232452343 4960096131724984848678515)
      ·
        refine ⟨7440144197587477273017773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960096131724984848678515 7440144197587477273017773)
        ·
          refine ⟨2790054074095303977381665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7440144197587477273017773 2790054074095303977381665)
          ·
            refine ⟨2092540555571477983036249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790054074095303977381665 2092540555571477983036249)
            ·
              refine ⟨1569405416678608487277187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092540555571477983036249 1569405416678608487277187)
              ·
                refine ⟨2354108125017912730915781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569405416678608487277187 2354108125017912730915781)
                ·
                  refine ⟨441395273440858637046709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354108125017912730915781 441395273440858637046709)
                  ·
                    rfl

theorem cell21_1934132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1934132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934132 prefixEnd_1934132 := by exact prefixLift 1934132
  have htrace : WordTrace (prefixWord ++ tailWord_1934132) baseStart_1934132 baseEnd_1934132 := by
    simpa [prefixWord, tailWord_1934132, baseEnd_1934132] using wordTrace_append hprefix tailTrace_1934132
  have hstable : (prefixWord ++ tailWord_1934132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934132).length < 2 ^ (prefixWord ++ tailWord_1934132).sum := by decide
  have hdescent : baseEnd_1934132 < baseStart_1934132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934264 : List Nat := [2, 1, 2, 1, 2, 6, 2, 5]
def baseStart_1934264 : Nat := 118140960795 + 1934264 * 2 ^ 59
def prefixEnd_1934264 : Nat := 4983230072969 + 3 ^ 40 * 1934264 * 2
def baseEnd_1934264 : Nat := 147141799213085246948813

theorem tailTrace_1934264 : CollatzResearch.WordTrace tailWord_1934264 prefixEnd_1934264 147141799213085246948813 := by
  unfold tailWord_1934264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274201932249674418060923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47032269242999565890747897 35274201932249674418060923)
  ·
    refine ⟨52911302898374511627091385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35274201932249674418060923 52911302898374511627091385)
    ·
      refine ⟨39683477173780883720318539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52911302898374511627091385 39683477173780883720318539)
      ·
        refine ⟨59525215760671325580477809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39683477173780883720318539 59525215760671325580477809)
        ·
          refine ⟨44643911820503494185358357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59525215760671325580477809 44643911820503494185358357)
          ·
            refine ⟨2092683366586101289938673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44643911820503494185358357 2092683366586101289938673)
            ·
              refine ⟨1569512524939575967454005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092683366586101289938673 1569512524939575967454005)
              ·
                refine ⟨147141799213085246948813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1569512524939575967454005 147141799213085246948813)
                ·
                  rfl

theorem cell21_1934264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_1934264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934264 prefixEnd_1934264 := by exact prefixLift 1934264
  have htrace : WordTrace (prefixWord ++ tailWord_1934264) baseStart_1934264 baseEnd_1934264 := by
    simpa [prefixWord, tailWord_1934264, baseEnd_1934264] using wordTrace_append hprefix tailTrace_1934264
  have hstable : (prefixWord ++ tailWord_1934264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934264).length < 2 ^ (prefixWord ++ tailWord_1934264).sum := by decide
  have hdescent : baseEnd_1934264 < baseStart_1934264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934388 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1934388 : Nat := 118140960795 + 1934388 * 2 ^ 59
def prefixEnd_1934388 : Nat := 4983230072969 + 3 ^ 40 * 1934388 * 2
def baseEnd_1934388 : Nat := 441453696128659080779519

theorem tailTrace_1934388 : CollatzResearch.WordTrace tailWord_1934388 prefixEnd_1934388 441453696128659080779519 := by
  unfold tailWord_1934388
  simp only [CollatzResearch.WordTrace]
  refine ⟨35276463258025059006817909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47035284344033412009090545 35276463258025059006817909)
  ·
    refine ⟨3307168430439849281889179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35276463258025059006817909 3307168430439849281889179)
    ·
      refine ⟨4960752645659773922833769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3307168430439849281889179 4960752645659773922833769)
      ·
        refine ⟨3720564484244830442125327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4960752645659773922833769 3720564484244830442125327)
        ·
          refine ⟨5580846726367245663187991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720564484244830442125327 5580846726367245663187991)
          ·
            refine ⟨8371270089550868494781987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580846726367245663187991 8371270089550868494781987)
            ·
              refine ⟨12556905134326302742172981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371270089550868494781987 12556905134326302742172981)
              ·
                refine ⟨1177209856343090882078717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12556905134326302742172981 1177209856343090882078717)
                ·
                  refine ⟨441453696128659080779519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177209856343090882078717 441453696128659080779519)
                  ·
                    rfl

theorem cell21_1934388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1934388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934388 prefixEnd_1934388 := by exact prefixLift 1934388
  have htrace : WordTrace (prefixWord ++ tailWord_1934388) baseStart_1934388 baseEnd_1934388 := by
    simpa [prefixWord, tailWord_1934388, baseEnd_1934388] using wordTrace_append hprefix tailTrace_1934388
  have hstable : (prefixWord ++ tailWord_1934388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934388).length < 2 ^ (prefixWord ++ tailWord_1934388).sum := by decide
  have hdescent : baseEnd_1934388 < baseStart_1934388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934478 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1934478 : Nat := 118140960795 + 1934478 * 2 ^ 59
def prefixEnd_1934478 : Nat := 4983230072969 + 3 ^ 40 * 1934478 * 2
def baseEnd_1934478 : Nat := 441474235354838924279335

theorem tailTrace_1934478 : CollatzResearch.WordTrace tailWord_1934478 prefixEnd_1934478 441474235354838924279335 := by
  unfold tailWord_1934478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819526135715507923051511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47037472723816042256274725 8819526135715507923051511)
  ·
    refine ⟨13229289203573261884577267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8819526135715507923051511 13229289203573261884577267)
    ·
      refine ⟨19843933805359892826865901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13229289203573261884577267 19843933805359892826865901)
      ·
        refine ⟨7441475177009959810074713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19843933805359892826865901 7441475177009959810074713)
        ·
          refine ⟨5581106382757469857556035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441475177009959810074713 5581106382757469857556035)
          ·
            refine ⟨8371659574136204786334053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581106382757469857556035 8371659574136204786334053)
            ·
              refine ⟨1569686170150538397437635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8371659574136204786334053 1569686170150538397437635)
              ·
                refine ⟨2354529255225807596156453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569686170150538397437635 2354529255225807596156453)
                ·
                  refine ⟨441474235354838924279335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354529255225807596156453 441474235354838924279335)
                  ·
                    rfl

theorem cell21_1934478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1934478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934478 prefixEnd_1934478 := by exact prefixLift 1934478
  have htrace : WordTrace (prefixWord ++ tailWord_1934478) baseStart_1934478 baseEnd_1934478 := by
    simpa [prefixWord, tailWord_1934478, baseEnd_1934478] using wordTrace_append hprefix tailTrace_1934478
  have hstable : (prefixWord ++ tailWord_1934478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934478).length < 2 ^ (prefixWord ++ tailWord_1934478).sum := by decide
  have hdescent : baseEnd_1934478 < baseStart_1934478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934678 : List Nat := [5, 2, 3, 1, 2, 8]
def baseStart_1934678 : Nat := 118140960795 + 1934678 * 2 ^ 59
def prefixEnd_1934678 : Nat := 4983230072969 + 3 ^ 40 * 1934678 * 2
def baseEnd_1934678 : Nat := 16352588077025297072059

theorem tailTrace_1934678 : CollatzResearch.WordTrace tailWord_1934678 prefixEnd_1934678 16352588077025297072059 := by
  unfold tailWord_1934678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410218980312468596355793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47042335789999665027795125 4410218980312468596355793)
  ·
    refine ⟨3307664235234351447266845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4410218980312468596355793 3307664235234351447266845)
    ·
      refine ⟨1240374088212881792725067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3307664235234351447266845 1240374088212881792725067)
      ·
        refine ⟨1860561132319322689087601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240374088212881792725067 1860561132319322689087601)
        ·
          refine ⟨1395420849239492016815701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860561132319322689087601 1395420849239492016815701)
          ·
            refine ⟨16352588077025297072059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1395420849239492016815701 16352588077025297072059)
            ·
              rfl

theorem cell21_1934678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 8].length) (baseStart_1934678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934678 prefixEnd_1934678 := by exact prefixLift 1934678
  have htrace : WordTrace (prefixWord ++ tailWord_1934678) baseStart_1934678 baseEnd_1934678 := by
    simpa [prefixWord, tailWord_1934678, baseEnd_1934678] using wordTrace_append hprefix tailTrace_1934678
  have hstable : (prefixWord ++ tailWord_1934678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934678).length < 2 ^ (prefixWord ++ tailWord_1934678).sum := by decide
  have hdescent : baseEnd_1934678 < baseStart_1934678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934692 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1934692 : Nat := 118140960795 + 1934692 * 2 ^ 59
def prefixEnd_1934692 : Nat := 4983230072969 + 3 ^ 40 * 1934692 * 2
def baseEnd_1934692 : Nat := 441523073070422107712231

theorem tailTrace_1934692 : CollatzResearch.WordTrace tailWord_1934692 prefixEnd_1934692 441523073070422107712231 := by
  unfold tailWord_1934692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35282007153474388966351165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47042676204632518621801553 35282007153474388966351165)
  ·
    refine ⟨13230752682552895862381687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35282007153474388966351165 13230752682552895862381687)
    ·
      refine ⟨19846129023829343793572531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230752682552895862381687 19846129023829343793572531)
      ·
        refine ⟨29769193535744015690358797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19846129023829343793572531 29769193535744015690358797)
        ·
          refine ⟨11163447575904005883884549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29769193535744015690358797 11163447575904005883884549)
          ·
            refine ⟨2093146420482001103228353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11163447575904005883884549 2093146420482001103228353)
            ·
              refine ⟨1569859815361500827421265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093146420482001103228353 1569859815361500827421265)
              ·
                refine ⟨1177394861521125620565949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569859815361500827421265 1177394861521125620565949)
                ·
                  refine ⟨441523073070422107712231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177394861521125620565949 441523073070422107712231)
                  ·
                    rfl

theorem cell21_1934692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1934692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934692 prefixEnd_1934692 := by exact prefixLift 1934692
  have htrace : WordTrace (prefixWord ++ tailWord_1934692) baseStart_1934692 baseEnd_1934692 := by
    simpa [prefixWord, tailWord_1934692, baseEnd_1934692] using wordTrace_append hprefix tailTrace_1934692
  have hstable : (prefixWord ++ tailWord_1934692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934692).length < 2 ^ (prefixWord ++ tailWord_1934692).sum := by decide
  have hdescent : baseEnd_1934692 < baseStart_1934692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934717 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1934717 : Nat := 118140960795 + 1934717 * 2 ^ 59
def prefixEnd_1934717 : Nat := 4983230072969 + 3 ^ 40 * 1934717 * 2
def baseEnd_1934717 : Nat := 441528778411027619795513

theorem tailTrace_1934717 : CollatzResearch.WordTrace tailWord_1934717 prefixEnd_1934717 441528778411027619795513 := by
  unfold tailWord_1934717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70564926131858207202362405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47043284087905471468241603 70564926131858207202362405)
  ·
    refine ⟨13230923649723413850442951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70564926131858207202362405 13230923649723413850442951)
    ·
      refine ⟨19846385474585120775664427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230923649723413850442951 19846385474585120775664427)
      ·
        refine ⟨29769578211877681163496641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19846385474585120775664427 29769578211877681163496641)
        ·
          refine ⟨22327183658908260872622481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29769578211877681163496641 22327183658908260872622481)
          ·
            refine ⟨16745387744181195654466861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22327183658908260872622481 16745387744181195654466861)
            ·
              refine ⟨6279520404067948370425073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16745387744181195654466861 6279520404067948370425073)
              ·
                refine ⟨4709640303050961277818805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279520404067948370425073 4709640303050961277818805)
                ·
                  refine ⟨441528778411027619795513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4709640303050961277818805 441528778411027619795513)
                  ·
                    rfl

theorem cell21_1934717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1934717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934717 prefixEnd_1934717 := by exact prefixLift 1934717
  have htrace : WordTrace (prefixWord ++ tailWord_1934717) baseStart_1934717 baseEnd_1934717 := by
    simpa [prefixWord, tailWord_1934717, baseEnd_1934717] using wordTrace_append hprefix tailTrace_1934717
  have hstable : (prefixWord ++ tailWord_1934717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934717).length < 2 ^ (prefixWord ++ tailWord_1934717).sum := by decide
  have hdescent : baseEnd_1934717 < baseStart_1934717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934731 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_1934731 : Nat := 118140960795 + 1934731 * 2 ^ 59
def prefixEnd_1934731 : Nat := 4983230072969 + 3 ^ 40 * 1934731 * 2
def baseEnd_1934731 : Nat := 441531973401766706562151

theorem tailTrace_1934731 : CollatzResearch.WordTrace tailWord_1934731 prefixEnd_1934731 441531973401766706562151 := by
  unfold tailWord_1934731
  simp only [CollatzResearch.WordTrace]
  refine ⟨70565436753807487593372047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47043624502538325062248031 70565436753807487593372047)
  ·
    refine ⟨105848155130711231390058071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70565436753807487593372047 105848155130711231390058071)
    ·
      refine ⟨158772232696066847085087107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105848155130711231390058071 158772232696066847085087107)
      ·
        refine ⟨238158349044100270627630661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158772232696066847085087107 238158349044100270627630661)
        ·
          refine ⟨44654690445768800742680749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238158349044100270627630661 44654690445768800742680749)
          ·
            refine ⟨16745508917163300278505281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44654690445768800742680749 16745508917163300278505281)
            ·
              refine ⟨12559131687872475208878961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16745508917163300278505281 12559131687872475208878961)
              ·
                refine ⟨9419348765904356406659221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12559131687872475208878961 9419348765904356406659221)
                ·
                  refine ⟨441531973401766706562151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9419348765904356406659221 441531973401766706562151)
                  ·
                    rfl

theorem cell21_1934731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_1934731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934731 prefixEnd_1934731 := by exact prefixLift 1934731
  have htrace : WordTrace (prefixWord ++ tailWord_1934731) baseStart_1934731 baseEnd_1934731 := by
    simpa [prefixWord, tailWord_1934731, baseEnd_1934731] using wordTrace_append hprefix tailTrace_1934731
  have hstable : (prefixWord ++ tailWord_1934731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934731).length < 2 ^ (prefixWord ++ tailWord_1934731).sum := by decide
  have hdescent : baseEnd_1934731 < baseStart_1934731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934810 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_1934810 : Nat := 118140960795 + 1934810 * 2 ^ 59
def prefixEnd_1934810 : Nat := 4983230072969 + 3 ^ 40 * 1934810 * 2
def baseEnd_1934810 : Nat := 441550002278080124745323

theorem tailTrace_1934810 : CollatzResearch.WordTrace tailWord_1934810 prefixEnd_1934810 441550002278080124745323 := by
  unfold tailWord_1934810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642079530130321021374471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47045545413680856056998589 17642079530130321021374471)
  ·
    refine ⟨26463119295195481532061707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17642079530130321021374471 26463119295195481532061707)
    ·
      refine ⟨39694678942793222298092561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463119295195481532061707 39694678942793222298092561)
      ·
        refine ⟨29771009207094916723569421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39694678942793222298092561 29771009207094916723569421)
        ·
          refine ⟨11164128452660593771338533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29771009207094916723569421 11164128452660593771338533)
          ·
            refine ⟨2093274084873861332125975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11164128452660593771338533 2093274084873861332125975)
            ·
              refine ⟨3139911127310791998188963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093274084873861332125975 3139911127310791998188963)
              ·
                refine ⟨4709866690966187997283445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139911127310791998188963 4709866690966187997283445)
                ·
                  refine ⟨441550002278080124745323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4709866690966187997283445 441550002278080124745323)
                  ·
                    rfl

theorem cell21_1934810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_1934810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934810 prefixEnd_1934810 := by exact prefixLift 1934810
  have htrace : WordTrace (prefixWord ++ tailWord_1934810) baseStart_1934810 baseEnd_1934810 := by
    simpa [prefixWord, tailWord_1934810, baseEnd_1934810] using wordTrace_append hprefix tailTrace_1934810
  have hstable : (prefixWord ++ tailWord_1934810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934810).length < 2 ^ (prefixWord ++ tailWord_1934810).sum := by decide
  have hdescent : baseEnd_1934810 < baseStart_1934810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934824 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_1934824 : Nat := 118140960795 + 1934824 * 2 ^ 59
def prefixEnd_1934824 : Nat := 4983230072969 + 3 ^ 40 * 1934824 * 2
def baseEnd_1934824 : Nat := 441553197268819211511961

theorem tailTrace_1934824 : CollatzResearch.WordTrace tailWord_1934824 prefixEnd_1934824 441553197268819211511961 := by
  unfold tailWord_1934824
  simp only [CollatzResearch.WordTrace]
  refine ⟨35284414371235282238253763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47045885828313709651005017 35284414371235282238253763)
  ·
    refine ⟨52926621556852923357380645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35284414371235282238253763 52926621556852923357380645)
    ·
      refine ⟨9923741541909923129508871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52926621556852923357380645 9923741541909923129508871)
      ·
        refine ⟨14885612312864884694263307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9923741541909923129508871 14885612312864884694263307)
        ·
          refine ⟨22328418469297327041394961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14885612312864884694263307 22328418469297327041394961)
          ·
            refine ⟨16746313851972995281046221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22328418469297327041394961 16746313851972995281046221)
            ·
              refine ⟨6279867694489873230392333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16746313851972995281046221 6279867694489873230392333)
              ·
                refine ⟨2354950385433702461397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6279867694489873230392333 2354950385433702461397125)
                ·
                  refine ⟨441553197268819211511961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354950385433702461397125 441553197268819211511961)
                  ·
                    rfl

theorem cell21_1934824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_1934824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934824 prefixEnd_1934824 := by exact prefixLift 1934824
  have htrace : WordTrace (prefixWord ++ tailWord_1934824) baseStart_1934824 baseEnd_1934824 := by
    simpa [prefixWord, tailWord_1934824, baseEnd_1934824] using wordTrace_append hprefix tailTrace_1934824
  have hstable : (prefixWord ++ tailWord_1934824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934824).length < 2 ^ (prefixWord ++ tailWord_1934824).sum := by decide
  have hdescent : baseEnd_1934824 < baseStart_1934824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934861 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1934861 : Nat := 118140960795 + 1934861 * 2 ^ 59
def prefixEnd_1934861 : Nat := 4983230072969 + 3 ^ 40 * 1934861 * 2
def baseEnd_1934861 : Nat := 441561641172915369395219

theorem tailTrace_1934861 : CollatzResearch.WordTrace tailWord_1934861 prefixEnd_1934861 441561641172915369395219 := by
  unfold tailWord_1934861
  simp only [CollatzResearch.WordTrace]
  refine ⟨70570178243336519795604437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47046785495557679863736291 70570178243336519795604437)
  ·
    refine ⟨1653988552578199682709479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 70570178243336519795604437 1653988552578199682709479)
    ·
      refine ⟨2480982828867299524064219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653988552578199682709479 2480982828867299524064219)
      ·
        refine ⟨3721474243300949286096329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480982828867299524064219 3721474243300949286096329)
        ·
          refine ⟨2791105682475711964572247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721474243300949286096329 2791105682475711964572247)
          ·
            refine ⟨4186658523713567946858371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791105682475711964572247 4186658523713567946858371)
            ·
              refine ⟨6279987785570351920287557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186658523713567946858371 6279987785570351920287557)
              ·
                refine ⟨1177497709794440985053917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6279987785570351920287557 1177497709794440985053917)
                ·
                  refine ⟨441561641172915369395219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177497709794440985053917 441561641172915369395219)
                  ·
                    rfl

theorem cell21_1934861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1934861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934861 prefixEnd_1934861 := by exact prefixLift 1934861
  have htrace : WordTrace (prefixWord ++ tailWord_1934861) baseStart_1934861 baseEnd_1934861 := by
    simpa [prefixWord, tailWord_1934861, baseEnd_1934861] using wordTrace_append hprefix tailTrace_1934861
  have hstable : (prefixWord ++ tailWord_1934861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934861).length < 2 ^ (prefixWord ++ tailWord_1934861).sum := by decide
  have hdescent : baseEnd_1934861 < baseStart_1934861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934872 : List Nat := [2, 1, 2, 3, 5, 1, 1, 6]
def baseStart_1934872 : Nat := 118140960795 + 1934872 * 2 ^ 59
def prefixEnd_1934872 : Nat := 4983230072969 + 3 ^ 40 * 1934872 * 2
def baseEnd_1934872 : Nat := 147188050507593931570621

theorem tailTrace_1934872 : CollatzResearch.WordTrace tailWord_1934872 prefixEnd_1934872 147188050507593931570621 := by
  unfold tailWord_1934872
  simp only [CollatzResearch.WordTrace]
  refine ⟨35285289723148334337127435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47047052964197779116169913 35285289723148334337127435)
  ·
    refine ⟨52927934584722501505691153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35285289723148334337127435 52927934584722501505691153)
    ·
      refine ⟨39695950938541876129268365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52927934584722501505691153 39695950938541876129268365)
      ·
        refine ⟨14885981601953203548475637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39695950938541876129268365 14885981601953203548475637)
        ·
          refine ⟨1395560775183112832669591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14885981601953203548475637 1395560775183112832669591)
          ·
            refine ⟨2093341162774669249004387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395560775183112832669591 2093341162774669249004387)
            ·
              refine ⟨3140011744162003873506581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093341162774669249004387 3140011744162003873506581)
              ·
                refine ⟨147188050507593931570621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3140011744162003873506581 147188050507593931570621)
                ·
                  rfl

theorem cell21_1934872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_1934872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934872 prefixEnd_1934872 := by exact prefixLift 1934872
  have htrace : WordTrace (prefixWord ++ tailWord_1934872) baseStart_1934872 baseEnd_1934872 := by
    simpa [prefixWord, tailWord_1934872, baseEnd_1934872] using wordTrace_append hprefix tailTrace_1934872
  have hstable : (prefixWord ++ tailWord_1934872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934872).length < 2 ^ (prefixWord ++ tailWord_1934872).sum := by decide
  have hdescent : baseEnd_1934872 < baseStart_1934872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934990 : List Nat := [4, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1934990 : Nat := 118140960795 + 1934990 * 2 ^ 59
def prefixEnd_1934990 : Nat := 4983230072969 + 3 ^ 40 * 1934990 * 2
def baseEnd_1934990 : Nat := 147197026910146603914985

theorem tailTrace_1934990 : CollatzResearch.WordTrace tailWord_1934990 prefixEnd_1934990 147197026910146603914985 := by
  unfold tailWord_1934990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821860407483646853381303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47049922173246116551366949 8821860407483646853381303)
  ·
    refine ⟨13232790611225470280071955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8821860407483646853381303 13232790611225470280071955)
    ·
      refine ⟨19849185916838205420107933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13232790611225470280071955 19849185916838205420107933)
      ·
        refine ⟨7443444718814327032540475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19849185916838205420107933 7443444718814327032540475)
        ·
          refine ⟨11165167078221490548810713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443444718814327032540475 11165167078221490548810713)
          ·
            refine ⟨8373875308666117911608035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165167078221490548810713 8373875308666117911608035)
            ·
              refine ⟨12560812962999176867412053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373875308666117911608035 12560812962999176867412053)
              ·
                refine ⟨147197026910146603914985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12560812962999176867412053 147197026910146603914985)
                ·
                  rfl

theorem cell21_1934990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1934990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1934990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1934990 prefixEnd_1934990 := by exact prefixLift 1934990
  have htrace : WordTrace (prefixWord ++ tailWord_1934990) baseStart_1934990 baseEnd_1934990 := by
    simpa [prefixWord, tailWord_1934990, baseEnd_1934990] using wordTrace_append hprefix tailTrace_1934990
  have hstable : (prefixWord ++ tailWord_1934990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934990).length < 2 ^ (prefixWord ++ tailWord_1934990).sum := by decide
  have hdescent : baseEnd_1934990 < baseStart_1934990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935232 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_1935232 : Nat := 118140960795 + 1935232 * 2 ^ 59
def prefixEnd_1935232 : Nat := 4983230072969 + 3 ^ 40 * 1935232 * 2
def baseEnd_1935232 : Nat := 441646308427501168711127

theorem tailTrace_1935232 : CollatzResearch.WordTrace tailWord_1935232 prefixEnd_1935232 441646308427501168711127 := by
  unfold tailWord_1935232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35291854862496225078679975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47055806483328300104906633 35291854862496225078679975)
  ·
    refine ⟨52937782293744337618019963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35291854862496225078679975 52937782293744337618019963)
    ·
      refine ⟨79406673440616506427029945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52937782293744337618019963 79406673440616506427029945)
      ·
        refine ⟨59555005080462379820272459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79406673440616506427029945 59555005080462379820272459)
        ·
          refine ⟨89332507620693569730408689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59555005080462379820272459 89332507620693569730408689)
          ·
            refine ⟨66999380715520177297806517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89332507620693569730408689 66999380715520177297806517)
            ·
              refine ⟨6281191942080016621669361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66999380715520177297806517 6281191942080016621669361)
              ·
                refine ⟨4710893956560012466252021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6281191942080016621669361 4710893956560012466252021)
                ·
                  refine ⟨441646308427501168711127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4710893956560012466252021 441646308427501168711127)
                  ·
                    rfl

theorem cell21_1935232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_1935232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935232 prefixEnd_1935232 := by exact prefixLift 1935232
  have htrace : WordTrace (prefixWord ++ tailWord_1935232) baseStart_1935232 baseEnd_1935232 := by
    simpa [prefixWord, tailWord_1935232, baseEnd_1935232] using wordTrace_append hprefix tailTrace_1935232
  have hstable : (prefixWord ++ tailWord_1935232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935232).length < 2 ^ (prefixWord ++ tailWord_1935232).sum := by decide
  have hdescent : baseEnd_1935232 < baseStart_1935232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935249 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 3]
def baseStart_1935249 : Nat := 118140960795 + 1935249 * 2 ^ 59
def prefixEnd_1935249 : Nat := 4983230072969 + 3 ^ 40 * 1935249 * 2
def baseEnd_1935249 : Nat := 441650188059112916927759

theorem tailTrace_1935249 : CollatzResearch.WordTrace tailWord_1935249 prefixEnd_1935249 441650188059112916927759 := by
  unfold tailWord_1935249
  simp only [CollatzResearch.WordTrace]
  refine ⟨70584329765930862060728801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47056219843953908040485867 70584329765930862060728801)
  ·
    refine ⟨52938247324448146545546601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70584329765930862060728801 52938247324448146545546601)
    ·
      refine ⟨39703685493336109909159951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52938247324448146545546601 39703685493336109909159951)
      ·
        refine ⟨59555528240004164863739927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39703685493336109909159951 59555528240004164863739927)
        ·
          refine ⟨89333292360006247295609891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59555528240004164863739927 89333292360006247295609891)
          ·
            refine ⟨133999938540009370943414837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89333292360006247295609891 133999938540009370943414837)
            ·
              refine ⟨12562494238125878525945141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133999938540009370943414837 12562494238125878525945141)
              ·
                refine ⟨1177733834824301111807357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12562494238125878525945141 1177733834824301111807357)
                ·
                  refine ⟨441650188059112916927759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177733834824301111807357 441650188059112916927759)
                  ·
                    rfl

theorem cell21_1935249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_1935249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935249 prefixEnd_1935249 := by exact prefixLift 1935249
  have htrace : WordTrace (prefixWord ++ tailWord_1935249) baseStart_1935249 baseEnd_1935249 := by
    simpa [prefixWord, tailWord_1935249, baseEnd_1935249] using wordTrace_append hprefix tailTrace_1935249
  have hstable : (prefixWord ++ tailWord_1935249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935249).length < 2 ^ (prefixWord ++ tailWord_1935249).sum := by decide
  have hdescent : baseEnd_1935249 < baseStart_1935249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935266 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1935266 : Nat := 118140960795 + 1935266 * 2 ^ 59
def prefixEnd_1935266 : Nat := 4983230072969 + 3 ^ 40 * 1935266 * 2
def baseEnd_1935266 : Nat := 441654067690724665144391

theorem tailTrace_1935266 : CollatzResearch.WordTrace tailWord_1935266 prefixEnd_1935266 441654067690724665144391 := by
  unfold tailWord_1935266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646237451717318491024413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47056633204579515976065101 17646237451717318491024413)
  ·
    refine ⟨6617339044393994434134155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17646237451717318491024413 6617339044393994434134155)
    ·
      refine ⟨9926008566590991651201233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6617339044393994434134155 9926008566590991651201233)
      ·
        refine ⟨7444506424943243738400925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9926008566590991651201233 7444506424943243738400925)
        ·
          refine ⟨2791689909353716401900347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7444506424943243738400925 2791689909353716401900347)
          ·
            refine ⟨4187534864030574602850521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791689909353716401900347 4187534864030574602850521)
            ·
              refine ⟨3140651148022930952137891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4187534864030574602850521 3140651148022930952137891)
              ·
                refine ⟨4710976722034396428206837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140651148022930952137891 4710976722034396428206837)
                ·
                  refine ⟨441654067690724665144391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4710976722034396428206837 441654067690724665144391)
                  ·
                    rfl

theorem cell21_1935266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1935266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935266 prefixEnd_1935266 := by exact prefixLift 1935266
  have htrace : WordTrace (prefixWord ++ tailWord_1935266) baseStart_1935266 baseEnd_1935266 := by
    simpa [prefixWord, tailWord_1935266, baseEnd_1935266] using wordTrace_append hprefix tailTrace_1935266
  have hstable : (prefixWord ++ tailWord_1935266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935266).length < 2 ^ (prefixWord ++ tailWord_1935266).sum := by decide
  have hdescent : baseEnd_1935266 < baseStart_1935266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935294 : List Nat := [4, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1935294 : Nat := 118140960795 + 1935294 * 2 ^ 59
def prefixEnd_1935294 : Nat := 4983230072969 + 3 ^ 40 * 1935294 * 2
def baseEnd_1935294 : Nat := 147220152557400946225889

theorem tailTrace_1935294 : CollatzResearch.WordTrace tailWord_1935294 prefixEnd_1935294 147220152557400946225889 := by
  unfold tailWord_1935294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823246381345979343264617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47057314033845223164077957 8823246381345979343264617)
  ·
    refine ⟨6617434786009484507448463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8823246381345979343264617 6617434786009484507448463)
    ·
      refine ⟨9926152179014226761172695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6617434786009484507448463 9926152179014226761172695)
      ·
        refine ⟨14889228268521340141759043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9926152179014226761172695 14889228268521340141759043)
        ·
          refine ⟨22333842402782010212638565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14889228268521340141759043 22333842402782010212638565)
          ·
            refine ⟨4187595450521626914869731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22333842402782010212638565 4187595450521626914869731)
            ·
              refine ⟨6281393175782440372304597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187595450521626914869731 6281393175782440372304597)
              ·
                refine ⟨147220152557400946225889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6281393175782440372304597 147220152557400946225889)
                ·
                  rfl

theorem cell21_1935294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1935294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935294 prefixEnd_1935294 := by exact prefixLift 1935294
  have htrace : WordTrace (prefixWord ++ tailWord_1935294) baseStart_1935294 baseEnd_1935294 := by
    simpa [prefixWord, tailWord_1935294, baseEnd_1935294] using wordTrace_append hprefix tailTrace_1935294
  have hstable : (prefixWord ++ tailWord_1935294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935294).length < 2 ^ (prefixWord ++ tailWord_1935294).sum := by decide
  have hdescent : baseEnd_1935294 < baseStart_1935294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935353 : List Nat := [1, 2, 1, 3, 1, 4, 2, 7]
def baseStart_1935353 : Nat := 118140960795 + 1935353 * 2 ^ 59
def prefixEnd_1935353 : Nat := 4983230072969 + 3 ^ 40 * 1935353 * 2
def baseEnd_1935353 : Nat := 147224640758677282398071

theorem tailTrace_1935353 : CollatzResearch.WordTrace tailWord_1935353 prefixEnd_1935353 147224640758677282398071 := by
  unfold tailWord_1935353
  simp only [CollatzResearch.WordTrace]
  refine ⟨70588122957554087822514713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47058748638369391881676475 70588122957554087822514713)
  ·
    refine ⟨52941092218165565866886035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70588122957554087822514713 52941092218165565866886035)
    ·
      refine ⟨79411638327248348800329053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52941092218165565866886035 79411638327248348800329053)
      ·
        refine ⟨29779364372718130800123395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79411638327248348800329053 29779364372718130800123395)
        ·
          refine ⟨44669046559077196200185093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29779364372718130800123395 44669046559077196200185093)
          ·
            refine ⟨8375446229826974287534705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44669046559077196200185093 8375446229826974287534705)
            ·
              refine ⟨6281584672370230715651029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375446229826974287534705 6281584672370230715651029)
              ·
                refine ⟨147224640758677282398071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6281584672370230715651029 147224640758677282398071)
                ·
                  rfl

theorem cell21_1935353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_1935353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935353 prefixEnd_1935353 := by exact prefixLift 1935353
  have htrace : WordTrace (prefixWord ++ tailWord_1935353) baseStart_1935353 baseEnd_1935353 := by
    simpa [prefixWord, tailWord_1935353, baseEnd_1935353] using wordTrace_append hprefix tailTrace_1935353
  have hstable : (prefixWord ++ tailWord_1935353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935353).length < 2 ^ (prefixWord ++ tailWord_1935353).sum := by decide
  have hdescent : baseEnd_1935353 < baseStart_1935353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935370 : List Nat := [3, 1, 2, 2, 5, 8]
def baseStart_1935370 : Nat := 118140960795 + 1935370 * 2 ^ 59
def prefixEnd_1935370 : Nat := 4983230072969 + 3 ^ 40 * 1935370 * 2
def baseEnd_1935370 : Nat := 16358437107690503533735

theorem tailTrace_1935370 : CollatzResearch.WordTrace tailWord_1935370 prefixEnd_1935370 16358437107690503533735 := by
  unfold tailWord_1935370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647185749623124931470891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47059161998994999817255709 17647185749623124931470891)
  ·
    refine ⟨26470778624434687397206337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17647185749623124931470891 26470778624434687397206337)
    ·
      refine ⟨19853083968326015547904753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26470778624434687397206337 19853083968326015547904753)
      ·
        refine ⟨14889812976244511660928565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19853083968326015547904753 14889812976244511660928565)
        ·
          refine ⟨1395919966522922968212053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14889812976244511660928565 1395919966522922968212053)
          ·
            refine ⟨16358437107690503533735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1395919966522922968212053 16358437107690503533735)
            ·
              rfl

theorem cell21_1935370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 8].length) (baseStart_1935370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935370 prefixEnd_1935370 := by exact prefixLift 1935370
  have htrace : WordTrace (prefixWord ++ tailWord_1935370) baseStart_1935370 baseEnd_1935370 := by
    simpa [prefixWord, tailWord_1935370, baseEnd_1935370] using wordTrace_append hprefix tailTrace_1935370
  have hstable : (prefixWord ++ tailWord_1935370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935370).length < 2 ^ (prefixWord ++ tailWord_1935370).sum := by decide
  have hdescent : baseEnd_1935370 < baseStart_1935370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935384 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1935384 : Nat := 118140960795 + 1935384 * 2 ^ 59
def prefixEnd_1935384 : Nat := 4983230072969 + 3 ^ 40 * 1935384 * 2
def baseEnd_1935384 : Nat := 441680996898382682177483

theorem tailTrace_1935384 : CollatzResearch.WordTrace tailWord_1935384 prefixEnd_1935384 441680996898382682177483 := by
  unfold tailWord_1935384
  simp only [CollatzResearch.WordTrace]
  refine ⟨35294626810220890058446603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47059502413627853411262137 35294626810220890058446603)
  ·
    refine ⟨52941940215331335087669905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35294626810220890058446603 52941940215331335087669905)
    ·
      refine ⟨39706455161498501315752429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52941940215331335087669905 39706455161498501315752429)
      ·
        refine ⟨14889920685561937993407161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39706455161498501315752429 14889920685561937993407161)
        ·
          refine ⟨11167440514171453495055371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14889920685561937993407161 11167440514171453495055371)
          ·
            refine ⟨16751160771257180242583057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167440514171453495055371 16751160771257180242583057)
            ·
              refine ⟨12563370578442885181937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16751160771257180242583057 12563370578442885181937293)
              ·
                refine ⟨4711263966916081943226485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12563370578442885181937293 4711263966916081943226485)
                ·
                  refine ⟨441680996898382682177483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4711263966916081943226485 441680996898382682177483)
                  ·
                    rfl

theorem cell21_1935384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1935384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935384 prefixEnd_1935384 := by exact prefixLift 1935384
  have htrace : WordTrace (prefixWord ++ tailWord_1935384) baseStart_1935384 baseEnd_1935384 := by
    simpa [prefixWord, tailWord_1935384, baseEnd_1935384] using wordTrace_append hprefix tailTrace_1935384
  have hstable : (prefixWord ++ tailWord_1935384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935384).length < 2 ^ (prefixWord ++ tailWord_1935384).sum := by decide
  have hdescent : baseEnd_1935384 < baseStart_1935384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935460 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_1935460 : Nat := 118140960795 + 1935460 * 2 ^ 59
def prefixEnd_1935460 : Nat := 4983230072969 + 3 ^ 40 * 1935460 * 2
def baseEnd_1935460 : Nat := 441698341133823438910661

theorem tailTrace_1935460 : CollatzResearch.WordTrace tailWord_1935460 prefixEnd_1935460 441698341133823438910661 := by
  unfold tailWord_1935460
  simp only [CollatzResearch.WordTrace]
  refine ⟨35296012784083222548329917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47061350378777630064439889 35296012784083222548329917)
  ·
    refine ⟨13236004794031208455623719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35296012784083222548329917 13236004794031208455623719)
    ·
      refine ⟨19854007191046812683435579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236004794031208455623719 19854007191046812683435579)
      ·
        refine ⟨29781010786570219025153369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19854007191046812683435579 29781010786570219025153369)
        ·
          refine ⟨22335758089927664268865027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29781010786570219025153369 22335758089927664268865027)
          ·
            refine ⟨33503637134891496403297541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22335758089927664268865027 33503637134891496403297541)
            ·
              refine ⟨6281931962792155575618289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33503637134891496403297541 6281931962792155575618289)
              ·
                refine ⟨4711448972094116681713717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6281931962792155575618289 4711448972094116681713717)
                ·
                  refine ⟨441698341133823438910661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4711448972094116681713717 441698341133823438910661)
                  ·
                    rfl

theorem cell21_1935460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_1935460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935460 prefixEnd_1935460 := by exact prefixLift 1935460
  have htrace : WordTrace (prefixWord ++ tailWord_1935460) baseStart_1935460 baseEnd_1935460 := by
    simpa [prefixWord, tailWord_1935460, baseEnd_1935460] using wordTrace_append hprefix tailTrace_1935460
  have hstable : (prefixWord ++ tailWord_1935460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935460).length < 2 ^ (prefixWord ++ tailWord_1935460).sum := by decide
  have hdescent : baseEnd_1935460 < baseStart_1935460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935522 : List Nat := [3, 3, 1, 3, 1, 1, 2, 7]
def baseStart_1935522 : Nat := 118140960795 + 1935522 * 2 ^ 59
def prefixEnd_1935522 : Nat := 4983230072969 + 3 ^ 40 * 1935522 * 2
def baseEnd_1935522 : Nat := 147237496792841702959067

theorem tailTrace_1935522 : CollatzResearch.WordTrace tailWord_1935522 prefixEnd_1935522 147237496792841702959067 := by
  unfold tailWord_1935522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648571723485457421354205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47062857929294553123611213 17648571723485457421354205)
  ·
    refine ⟨6618214396307046533007827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17648571723485457421354205 6618214396307046533007827)
    ·
      refine ⟨9927321594460569799511741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618214396307046533007827 9927321594460569799511741)
      ·
        refine ⟨3722745597922713674816903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9927321594460569799511741 3722745597922713674816903)
        ·
          refine ⟨5584118396884070512225355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722745597922713674816903 5584118396884070512225355)
          ·
            refine ⟨8376177595326105768338033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584118396884070512225355 8376177595326105768338033)
            ·
              refine ⟨6282133196494579326253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8376177595326105768338033 6282133196494579326253525)
              ·
                refine ⟨147237496792841702959067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6282133196494579326253525 147237496792841702959067)
                ·
                  rfl

theorem cell21_1935522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_1935522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935522 prefixEnd_1935522 := by exact prefixLift 1935522
  have htrace : WordTrace (prefixWord ++ tailWord_1935522) baseStart_1935522 baseEnd_1935522 := by
    simpa [prefixWord, tailWord_1935522, baseEnd_1935522] using wordTrace_append hprefix tailTrace_1935522
  have hstable : (prefixWord ++ tailWord_1935522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935522).length < 2 ^ (prefixWord ++ tailWord_1935522).sum := by decide
  have hdescent : baseEnd_1935522 < baseStart_1935522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935587 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 3]
def baseStart_1935587 : Nat := 118140960795 + 1935587 * 2 ^ 59
def prefixEnd_1935587 : Nat := 4983230072969 + 3 ^ 40 * 1935587 * 2
def baseEnd_1935587 : Nat := 441727324264099440293735

theorem tailTrace_1935587 : CollatzResearch.WordTrace tailWord_1935587 prefixEnd_1935587 441727324264099440293735 := by
  unfold tailWord_1935587
  simp only [CollatzResearch.WordTrace]
  refine ⟨70596657638706345786533015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47064438425804230524355343 70596657638706345786533015)
  ·
    refine ⟨105894986458059518679799523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70596657638706345786533015 105894986458059518679799523)
    ·
      refine ⟨158842479687089278019699285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105894986458059518679799523 158842479687089278019699285)
      ·
        refine ⟨1861435308833077476793351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 158842479687089278019699285 1861435308833077476793351)
        ·
          refine ⟨2792152963249616215190027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861435308833077476793351 2792152963249616215190027)
          ·
            refine ⟨4188229444874424322785041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792152963249616215190027 4188229444874424322785041)
            ·
              refine ⟨3141172083655818242088781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188229444874424322785041 3141172083655818242088781)
              ·
                refine ⟨1177939531370931840783293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3141172083655818242088781 1177939531370931840783293)
                ·
                  refine ⟨441727324264099440293735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177939531370931840783293 441727324264099440293735)
                  ·
                    rfl

theorem cell21_1935587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3].length) (baseStart_1935587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935587 prefixEnd_1935587 := by exact prefixLift 1935587
  have htrace : WordTrace (prefixWord ++ tailWord_1935587) baseStart_1935587 baseEnd_1935587 := by
    simpa [prefixWord, tailWord_1935587, baseEnd_1935587] using wordTrace_append hprefix tailTrace_1935587
  have hstable : (prefixWord ++ tailWord_1935587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935587).length < 2 ^ (prefixWord ++ tailWord_1935587).sum := by decide
  have hdescent : baseEnd_1935587 < baseStart_1935587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935595 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_1935595 : Nat := 118140960795 + 1935595 * 2 ^ 59
def prefixEnd_1935595 : Nat := 4983230072969 + 3 ^ 40 * 1935595 * 2
def baseEnd_1935595 : Nat := 441729149973093204160385

theorem tailTrace_1935595 : CollatzResearch.WordTrace tailWord_1935595 prefixEnd_1935595 441729149973093204160385 := by
  unfold tailWord_1935595
  simp only [CollatzResearch.WordTrace]
  refine ⟨70596949422677363152824239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47064632948451575435216159 70596949422677363152824239)
  ·
    refine ⟨105895424134016044729236359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70596949422677363152824239 105895424134016044729236359)
    ·
      refine ⟨158843136201024067093854539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105895424134016044729236359 158843136201024067093854539)
      ·
        refine ⟨238264704301536100640781809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158843136201024067093854539 238264704301536100640781809)
        ·
          refine ⟨178698528226152075480586357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238264704301536100640781809 178698528226152075480586357)
          ·
            refine ⟨16752987021201757076304971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178698528226152075480586357 16752987021201757076304971)
            ·
              refine ⟨25129480531802635614457457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16752987021201757076304971 25129480531802635614457457)
              ·
                refine ⟨18847110398851976710843093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25129480531802635614457457 18847110398851976710843093)
                ·
                  refine ⟨441729149973093204160385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18847110398851976710843093 441729149973093204160385)
                  ·
                    rfl

theorem cell21_1935595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_1935595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935595 prefixEnd_1935595 := by exact prefixLift 1935595
  have htrace : WordTrace (prefixWord ++ tailWord_1935595) baseStart_1935595 baseEnd_1935595 := by
    simpa [prefixWord, tailWord_1935595, baseEnd_1935595] using wordTrace_append hprefix tailTrace_1935595
  have hstable : (prefixWord ++ tailWord_1935595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935595).length < 2 ^ (prefixWord ++ tailWord_1935595).sum := by decide
  have hdescent : baseEnd_1935595 < baseStart_1935595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935612 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1935612 : Nat := 118140960795 + 1935612 * 2 ^ 59
def prefixEnd_1935612 : Nat := 4983230072969 + 3 ^ 40 * 1935612 * 2
def baseEnd_1935612 : Nat := 441733029604704952377017

theorem tailTrace_1935612 : CollatzResearch.WordTrace tailWord_1935612 prefixEnd_1935612 441733029604704952377017 := by
  unfold tailWord_1935612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298784731807887528096545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47065046309077183370795393 35298784731807887528096545)
  ·
    refine ⟨26474088548855915646072409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35298784731807887528096545 26474088548855915646072409)
    ·
      refine ⟨19855566411641936734554307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26474088548855915646072409 19855566411641936734554307)
      ·
        refine ⟨29783349617462905101831461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855566411641936734554307 29783349617462905101831461)
        ·
          refine ⟨5584378053274294706593399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29783349617462905101831461 5584378053274294706593399)
          ·
            refine ⟨8376567079911442059890099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584378053274294706593399 8376567079911442059890099)
            ·
              refine ⟨12564850619867163089835149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376567079911442059890099 12564850619867163089835149)
              ·
                refine ⟨4711818982450186158688181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12564850619867163089835149 4711818982450186158688181)
                ·
                  refine ⟨441733029604704952377017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4711818982450186158688181 441733029604704952377017)
                  ·
                    rfl

theorem cell21_1935612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1935612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935612 prefixEnd_1935612 := by exact prefixLift 1935612
  have htrace : WordTrace (prefixWord ++ tailWord_1935612) baseStart_1935612 baseEnd_1935612 := by
    simpa [prefixWord, tailWord_1935612, baseEnd_1935612] using wordTrace_append hprefix tailTrace_1935612
  have hstable : (prefixWord ++ tailWord_1935612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935612).length < 2 ^ (prefixWord ++ tailWord_1935612).sum := by decide
  have hdescent : baseEnd_1935612 < baseStart_1935612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935719 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_1935719 : Nat := 118140960795 + 1935719 * 2 ^ 59
def prefixEnd_1935719 : Nat := 4983230072969 + 3 ^ 40 * 1935719 * 2
def baseEnd_1935719 : Nat := 441757448462496544093465

theorem tailTrace_1935719 : CollatzResearch.WordTrace tailWord_1935719 prefixEnd_1935719 441757448462496544093465 := by
  unfold tailWord_1935719
  simp only [CollatzResearch.WordTrace]
  refine ⟨70601472074228132330338211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47067648049485421553558807 70601472074228132330338211)
  ·
    refine ⟨105902208111342198495507317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70601472074228132330338211 105902208111342198495507317)
    ·
      refine ⟨9928332010438331108953811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105902208111342198495507317 9928332010438331108953811)
      ·
        refine ⟨14892498015657496663430717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928332010438331108953811 14892498015657496663430717)
        ·
          refine ⟨5584686755871561248786519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14892498015657496663430717 5584686755871561248786519)
          ·
            refine ⟨8377030133807341873179779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584686755871561248786519 8377030133807341873179779)
            ·
              refine ⟨12565545200711012809769669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377030133807341873179779 12565545200711012809769669)
              ·
                refine ⟨2356039725133314901831813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12565545200711012809769669 2356039725133314901831813)
                ·
                  refine ⟨441757448462496544093465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2356039725133314901831813 441757448462496544093465)
                  ·
                    rfl

theorem cell21_1935719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_1935719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935719 prefixEnd_1935719 := by exact prefixLift 1935719
  have htrace : WordTrace (prefixWord ++ tailWord_1935719) baseStart_1935719 baseEnd_1935719 := by
    simpa [prefixWord, tailWord_1935719, baseEnd_1935719] using wordTrace_append hprefix tailTrace_1935719
  have hstable : (prefixWord ++ tailWord_1935719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935719).length < 2 ^ (prefixWord ++ tailWord_1935719).sum := by decide
  have hdescent : baseEnd_1935719 < baseStart_1935719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935722 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_1935722 : Nat := 118140960795 + 1935722 * 2 ^ 59
def prefixEnd_1935722 : Nat := 4983230072969 + 3 ^ 40 * 1935722 * 2
def baseEnd_1935722 : Nat := 441758133103369205543459

theorem tailTrace_1935722 : CollatzResearch.WordTrace tailWord_1935722 prefixEnd_1935722 441758133103369205543459 := by
  unfold tailWord_1935722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17650395373304315960674355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47067720995478175895131613 17650395373304315960674355)
  ·
    refine ⟨26475593059956473941011533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17650395373304315960674355 26475593059956473941011533)
    ·
      refine ⟨9928347397483677727879325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26475593059956473941011533 9928347397483677727879325)
      ·
        refine ⟨3723130274056379147954747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9928347397483677727879325 3723130274056379147954747)
        ·
          refine ⟨5584695411084568721932121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723130274056379147954747 5584695411084568721932121)
          ·
            refine ⟨4188521558313426541449091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584695411084568721932121 4188521558313426541449091)
            ·
              refine ⟨6282782337470139812173637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188521558313426541449091 6282782337470139812173637)
              ·
                refine ⟨1178021688275651214782557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6282782337470139812173637 1178021688275651214782557)
                ·
                  refine ⟨441758133103369205543459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178021688275651214782557 441758133103369205543459)
                  ·
                    rfl

theorem cell21_1935722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_1935722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935722 prefixEnd_1935722 := by exact prefixLift 1935722
  have htrace : WordTrace (prefixWord ++ tailWord_1935722) baseStart_1935722 baseEnd_1935722 := by
    simpa [prefixWord, tailWord_1935722, baseEnd_1935722] using wordTrace_append hprefix tailTrace_1935722
  have hstable : (prefixWord ++ tailWord_1935722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935722).length < 2 ^ (prefixWord ++ tailWord_1935722).sum := by decide
  have hdescent : baseEnd_1935722 < baseStart_1935722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935933 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 3]
def baseStart_1935933 : Nat := 118140960795 + 1935933 * 2 ^ 59
def prefixEnd_1935933 : Nat := 4983230072969 + 3 ^ 40 * 1935933 * 2
def baseEnd_1935933 : Nat := 441806286178079727526361

theorem tailTrace_1935933 : CollatzResearch.WordTrace tailWord_1935933 prefixEnd_1935933 441806286178079727526361 := by
  unfold tailWord_1935933
  simp only [CollatzResearch.WordTrace]
  refine ⟨70609277295452846878628453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47072851530301897919085635 70609277295452846878628453)
  ·
    refine ⟨13239239492897408789742835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70609277295452846878628453 13239239492897408789742835)
    ·
      refine ⟨19858859239346113184614253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13239239492897408789742835 19858859239346113184614253)
      ·
        refine ⟨7447072214754792444230345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19858859239346113184614253 7447072214754792444230345)
        ·
          refine ⟨5585304161066094333172759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7447072214754792444230345 5585304161066094333172759)
          ·
            refine ⟨8377956241599141499759139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585304161066094333172759 8377956241599141499759139)
            ·
              refine ⟨12566934362398712249638709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377956241599141499759139 12566934362398712249638709)
              ·
                refine ⟨1178150096474879273403629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12566934362398712249638709 1178150096474879273403629)
                ·
                  refine ⟨441806286178079727526361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178150096474879273403629 441806286178079727526361)
                  ·
                    rfl

theorem cell21_1935933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_1935933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1935933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1935933 prefixEnd_1935933 := by exact prefixLift 1935933
  have htrace : WordTrace (prefixWord ++ tailWord_1935933) baseStart_1935933 baseEnd_1935933 := by
    simpa [prefixWord, tailWord_1935933, baseEnd_1935933] using wordTrace_append hprefix tailTrace_1935933
  have hstable : (prefixWord ++ tailWord_1935933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935933).length < 2 ^ (prefixWord ++ tailWord_1935933).sum := by decide
  have hdescent : baseEnd_1935933 < baseStart_1935933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936054 : List Nat := [5, 1, 3, 1, 2, 9]
def baseStart_1936054 : Nat := 118140960795 + 1936054 * 2 ^ 59
def prefixEnd_1936054 : Nat := 4983230072969 + 3 ^ 40 * 1936054 * 2
def baseEnd_1936054 : Nat := 16364218519504089111461

theorem tailTrace_1936054 : CollatzResearch.WordTrace tailWord_1936054 prefixEnd_1936054 16364218519504089111461 := by
  unfold tailWord_1936054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413355658000905283986451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47075793685342989695855477 4413355658000905283986451)
  ·
    refine ⟨6620033487001357925979677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4413355658000905283986451 6620033487001357925979677)
    ·
      refine ⟨2482512557625509222242379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6620033487001357925979677 2482512557625509222242379)
      ·
        refine ⟨3723768836438263833363569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482512557625509222242379 3723768836438263833363569)
        ·
          refine ⟨2792826627328697875022677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723768836438263833363569 2792826627328697875022677)
          ·
            refine ⟨16364218519504089111461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2792826627328697875022677 16364218519504089111461)
            ·
              rfl

theorem cell21_1936054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 9].length) (baseStart_1936054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936054 prefixEnd_1936054 := by exact prefixLift 1936054
  have htrace : WordTrace (prefixWord ++ tailWord_1936054) baseStart_1936054 baseEnd_1936054 := by
    simpa [prefixWord, tailWord_1936054, baseEnd_1936054] using wordTrace_append hprefix tailTrace_1936054
  have hstable : (prefixWord ++ tailWord_1936054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936054).length < 2 ^ (prefixWord ++ tailWord_1936054).sum := by decide
  have hdescent : baseEnd_1936054 < baseStart_1936054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936085 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1936085 : Nat := 118140960795 + 1936085 * 2 ^ 59
def prefixEnd_1936085 : Nat := 4983230072969 + 3 ^ 40 * 1936085 * 2
def baseEnd_1936085 : Nat := 441840974648961240992717

theorem tailTrace_1936085 : CollatzResearch.WordTrace tailWord_1936085 prefixEnd_1936085 441840974648961240992717 := by
  unfold tailWord_1936085
  simp only [CollatzResearch.WordTrace]
  refine ⟨70614821190902176838161709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47076547460601451225441139 70614821190902176838161709)
  ·
    refine ⟨26480557946588316314310641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70614821190902176838161709 26480557946588316314310641)
    ·
      refine ⟨19860418459941237235732981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26480557946588316314310641 19860418459941237235732981)
      ·
        refine ⟨1861914230619490990849967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19860418459941237235732981 1861914230619490990849967)
        ·
          refine ⟨2792871345929236486274951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861914230619490990849967 2792871345929236486274951)
          ·
            refine ⟨4189307018893854729412427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792871345929236486274951 4189307018893854729412427)
            ·
              refine ⟨6283960528340782094118641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189307018893854729412427 6283960528340782094118641)
              ·
                refine ⟨4712970396255586570588981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283960528340782094118641 4712970396255586570588981)
                ·
                  refine ⟨441840974648961240992717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4712970396255586570588981 441840974648961240992717)
                  ·
                    rfl

theorem cell21_1936085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1936085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936085 prefixEnd_1936085 := by exact prefixLift 1936085
  have htrace : WordTrace (prefixWord ++ tailWord_1936085) baseStart_1936085 baseEnd_1936085 := by
    simpa [prefixWord, tailWord_1936085, baseEnd_1936085] using wordTrace_append hprefix tailTrace_1936085
  have hstable : (prefixWord ++ tailWord_1936085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936085).length < 2 ^ (prefixWord ++ tailWord_1936085).sum := by decide
  have hdescent : baseEnd_1936085 < baseStart_1936085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936265 : List Nat := [1, 2, 1, 1, 5, 3, 3, 5]
def baseStart_1936265 : Nat := 118140960795 + 1936265 * 2 ^ 59
def prefixEnd_1936265 : Nat := 4983230072969 + 3 ^ 40 * 1936265 * 2
def baseEnd_1936265 : Nat := 147294017700440309330783

theorem tailTrace_1936265 : CollatzResearch.WordTrace tailWord_1936265 prefixEnd_1936265 147294017700440309330783 := by
  unfold tailWord_1936265
  simp only [CollatzResearch.WordTrace]
  refine ⟨70621386330250067579714249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47080924220166711719809499 70621386330250067579714249)
  ·
    refine ⟨52966039747687550684785687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70621386330250067579714249 52966039747687550684785687)
    ·
      refine ⟨79449059621531326027178531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52966039747687550684785687 79449059621531326027178531)
      ·
        refine ⟨119173589432296989040767797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79449059621531326027178531 119173589432296989040767797)
        ·
          refine ⟨11172524009277842722571981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119173589432296989040767797 11172524009277842722571981)
          ·
            refine ⟨4189696503479191020964493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11172524009277842722571981 4189696503479191020964493)
            ·
              refine ⟨1571136188804696632861685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4189696503479191020964493 1571136188804696632861685)
              ·
                refine ⟨147294017700440309330783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571136188804696632861685 147294017700440309330783)
                ·
                  rfl

theorem cell21_1936265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 5].length) (baseStart_1936265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936265 prefixEnd_1936265 := by exact prefixLift 1936265
  have htrace : WordTrace (prefixWord ++ tailWord_1936265) baseStart_1936265 baseEnd_1936265 := by
    simpa [prefixWord, tailWord_1936265, baseEnd_1936265] using wordTrace_append hprefix tailTrace_1936265
  have hstable : (prefixWord ++ tailWord_1936265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936265).length < 2 ^ (prefixWord ++ tailWord_1936265).sum := by decide
  have hdescent : baseEnd_1936265 < baseStart_1936265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936341 : List Nat := [1, 3, 2, 3, 3, 2, 7]
def baseStart_1936341 : Nat := 118140960795 + 1936341 * 2 ^ 59
def prefixEnd_1936341 : Nat := 4983230072969 + 3 ^ 40 * 1936341 * 2
def baseEnd_1936341 : Nat := 49099933037417964969503

theorem tailTrace_1936341 : CollatzResearch.WordTrace tailWord_1936341 prefixEnd_1936341 49099933037417964969503 := by
  unfold tailWord_1936341
  simp only [CollatzResearch.WordTrace]
  refine ⟨70624158277974732559480877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47082772185316488372987251 70624158277974732559480877)
  ·
    refine ⟨26484059354240524709805329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70624158277974732559480877 26484059354240524709805329)
    ·
      refine ⟨19863044515680393532353997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26484059354240524709805329 19863044515680393532353997)
      ·
        refine ⟨7448641693380147574632749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19863044515680393532353997 7448641693380147574632749)
        ·
          refine ⟨2793240635017555340487281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7448641693380147574632749 2793240635017555340487281)
          ·
            refine ⟨2094930476263166505365461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793240635017555340487281 2094930476263166505365461)
            ·
              refine ⟨49099933037417964969503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2094930476263166505365461 49099933037417964969503)
              ·
                rfl

theorem cell21_1936341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 7].length) (baseStart_1936341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936341 prefixEnd_1936341 := by exact prefixLift 1936341
  have htrace : WordTrace (prefixWord ++ tailWord_1936341) baseStart_1936341 baseEnd_1936341 := by
    simpa [prefixWord, tailWord_1936341, baseEnd_1936341] using wordTrace_append hprefix tailTrace_1936341
  have hstable : (prefixWord ++ tailWord_1936341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936341).length < 2 ^ (prefixWord ++ tailWord_1936341).sum := by decide
  have hdescent : baseEnd_1936341 < baseStart_1936341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936417 : List Nat := [1, 2, 3, 2, 3, 3, 1, 6]
def baseStart_1936417 : Nat := 118140960795 + 1936417 * 2 ^ 59
def prefixEnd_1936417 : Nat := 4983230072969 + 3 ^ 40 * 1936417 * 2
def baseEnd_1936417 : Nat := 147305580524067480486235

theorem tailTrace_1936417 : CollatzResearch.WordTrace tailWord_1936417 prefixEnd_1936417 147305580524067480486235 := by
  unfold tailWord_1936417
  simp only [CollatzResearch.WordTrace]
  refine ⟨70626930225699397539247505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47084620150466265026165003 70626930225699397539247505)
  ·
    refine ⟨52970197669274548154435629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70626930225699397539247505 52970197669274548154435629)
    ·
      refine ⟨19863824125977955557913361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52970197669274548154435629 19863824125977955557913361)
      ·
        refine ⟨14897868094483466668435021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19863824125977955557913361 14897868094483466668435021)
        ·
          refine ⟨5586700535431300000663133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14897868094483466668435021 5586700535431300000663133)
          ·
            refine ⟨2095012700786737500248675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5586700535431300000663133 2095012700786737500248675)
            ·
              refine ⟨3142519051180106250373013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095012700786737500248675 3142519051180106250373013)
              ·
                refine ⟨147305580524067480486235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3142519051180106250373013 147305580524067480486235)
                ·
                  rfl

theorem cell21_1936417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 6].length) (baseStart_1936417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936417 prefixEnd_1936417 := by exact prefixLift 1936417
  have htrace : WordTrace (prefixWord ++ tailWord_1936417) baseStart_1936417 baseEnd_1936417 := by
    simpa [prefixWord, tailWord_1936417, baseEnd_1936417] using wordTrace_append hprefix tailTrace_1936417
  have hstable : (prefixWord ++ tailWord_1936417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936417).length < 2 ^ (prefixWord ++ tailWord_1936417).sum := by decide
  have hdescent : baseEnd_1936417 < baseStart_1936417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936448 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_1936448 : Nat := 118140960795 + 1936448 * 2 ^ 59
def prefixEnd_1936448 : Nat := 4983230072969 + 3 ^ 40 * 1936448 * 2
def baseEnd_1936448 : Nat := 441923816194553276441975

theorem tailTrace_1936448 : CollatzResearch.WordTrace tailWord_1936448 prefixEnd_1936448 441923816194553276441975 := by
  unfold tailWord_1936448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314030444293544916812999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47085373925724726555750665 35314030444293544916812999)
  ·
    refine ⟨52971045666440317375219499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35314030444293544916812999 52971045666440317375219499)
    ·
      refine ⟨79456568499660476062829249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52971045666440317375219499 79456568499660476062829249)
      ·
        refine ⟨59592426374745357047121937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79456568499660476062829249 59592426374745357047121937)
        ·
          refine ⟨44694319781059017785341453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59592426374745357047121937 44694319781059017785341453)
          ·
            refine ⟨16760369917897131669503045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44694319781059017785341453 16760369917897131669503045)
            ·
              refine ⟨3142569359605712188031821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16760369917897131669503045 3142569359605712188031821)
              ·
                refine ⟨1178463509852142070511933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3142569359605712188031821 1178463509852142070511933)
                ·
                  refine ⟨441923816194553276441975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178463509852142070511933 441923816194553276441975)
                  ·
                    rfl

theorem cell21_1936448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_1936448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936448 prefixEnd_1936448 := by exact prefixLift 1936448
  have htrace : WordTrace (prefixWord ++ tailWord_1936448) baseStart_1936448 baseEnd_1936448 := by
    simpa [prefixWord, tailWord_1936448, baseEnd_1936448] using wordTrace_append hprefix tailTrace_1936448
  have hstable : (prefixWord ++ tailWord_1936448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936448).length < 2 ^ (prefixWord ++ tailWord_1936448).sum := by decide
  have hdescent : baseEnd_1936448 < baseStart_1936448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936476 : List Nat := [2, 2, 4, 1, 1, 1, 2, 8]
def baseStart_1936476 : Nat := 118140960795 + 1936476 * 2 ^ 59
def prefixEnd_1936476 : Nat := 4983230072969 + 3 ^ 40 * 1936476 * 2
def baseEnd_1936476 : Nat := 147310068725343816658417

theorem tailTrace_1936476 : CollatzResearch.WordTrace tailWord_1936476 prefixEnd_1936476 147310068725343816658417 := by
  unfold tailWord_1936476
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314541066242825307822641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47086054754990433743763521 35314541066242825307822641)
  ·
    refine ⟨26485905799682118980866981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35314541066242825307822641 26485905799682118980866981)
    ·
      refine ⟨4966107337440397308912559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26485905799682118980866981 4966107337440397308912559)
      ·
        refine ⟨7449161006160595963368839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966107337440397308912559 7449161006160595963368839)
        ·
          refine ⟨11173741509240893945053259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449161006160595963368839 11173741509240893945053259)
          ·
            refine ⟨16760612263861340917579889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173741509240893945053259 16760612263861340917579889)
            ·
              refine ⟨12570459197896005688184917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16760612263861340917579889 12570459197896005688184917)
              ·
                refine ⟨147310068725343816658417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12570459197896005688184917 147310068725343816658417)
                ·
                  rfl

theorem cell21_1936476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_1936476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936476 prefixEnd_1936476 := by exact prefixLift 1936476
  have htrace : WordTrace (prefixWord ++ tailWord_1936476) baseStart_1936476 baseEnd_1936476 := by
    simpa [prefixWord, tailWord_1936476, baseEnd_1936476] using wordTrace_append hprefix tailTrace_1936476
  have hstable : (prefixWord ++ tailWord_1936476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936476).length < 2 ^ (prefixWord ++ tailWord_1936476).sum := by decide
  have hdescent : baseEnd_1936476 < baseStart_1936476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936493 : List Nat := [1, 5, 1, 1, 2, 2, 4, 5]
def baseStart_1936493 : Nat := 118140960795 + 1936493 * 2 ^ 59
def prefixEnd_1936493 : Nat := 4983230072969 + 3 ^ 40 * 1936493 * 2
def baseEnd_1936493 : Nat := 147311361935881066063961

theorem tailTrace_1936493 : CollatzResearch.WordTrace tailWord_1936493 prefixEnd_1936493 147311361935881066063961 := by
  unfold tailWord_1936493
  simp only [CollatzResearch.WordTrace]
  refine ⟨70629702173424062519014133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47086468115616041679342755 70629702173424062519014133)
  ·
    refine ⟨6621534578758505861157575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70629702173424062519014133 6621534578758505861157575)
    ·
      refine ⟨9932301868137758791736363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6621534578758505861157575 9932301868137758791736363)
      ·
        refine ⟨14898452802206638187604545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932301868137758791736363 14898452802206638187604545)
        ·
          refine ⟨11173839601654978640703409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14898452802206638187604545 11173839601654978640703409)
          ·
            refine ⟨8380379701241233980527557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11173839601654978640703409 8380379701241233980527557)
            ·
              refine ⟨1571321193982731371348917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8380379701241233980527557 1571321193982731371348917)
              ·
                refine ⟨147311361935881066063961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571321193982731371348917 147311361935881066063961)
                ·
                  rfl

theorem cell21_1936493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 5].length) (baseStart_1936493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936493 prefixEnd_1936493 := by exact prefixLift 1936493
  have htrace : WordTrace (prefixWord ++ tailWord_1936493) baseStart_1936493 baseEnd_1936493 := by
    simpa [prefixWord, tailWord_1936493, baseEnd_1936493] using wordTrace_append hprefix tailTrace_1936493
  have hstable : (prefixWord ++ tailWord_1936493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936493).length < 2 ^ (prefixWord ++ tailWord_1936493).sum := by decide
  have hdescent : baseEnd_1936493 < baseStart_1936493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936521 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_1936521 : Nat := 118140960795 + 1936521 * 2 ^ 59
def prefixEnd_1936521 : Nat := 4983230072969 + 3 ^ 40 * 1936521 * 2
def baseEnd_1936521 : Nat := 441940475789121371725159

theorem tailTrace_1936521 : CollatzResearch.WordTrace tailWord_1936521 prefixEnd_1936521 441940475789121371725159 := by
  unfold tailWord_1936521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70630723417322623301033417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47087148944881748867355611 70630723417322623301033417)
  ·
    refine ⟨52973042562991967475775063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70630723417322623301033417 52973042562991967475775063)
    ·
      refine ⟨79459563844487951213662595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52973042562991967475775063 79459563844487951213662595)
      ·
        refine ⟨119189345766731926820493893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79459563844487951213662595 119189345766731926820493893)
        ·
          refine ⟨22348002331262236278842605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119189345766731926820493893 22348002331262236278842605)
          ·
            refine ⟨8380500874223338604565977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22348002331262236278842605 8380500874223338604565977)
            ·
              refine ⟨6285375655667503953424483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8380500874223338604565977 6285375655667503953424483)
              ·
                refine ⟨9428063483501255930136725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285375655667503953424483 9428063483501255930136725)
                ·
                  refine ⟨441940475789121371725159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9428063483501255930136725 441940475789121371725159)
                  ·
                    rfl

theorem cell21_1936521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_1936521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936521 prefixEnd_1936521 := by exact prefixLift 1936521
  have htrace : WordTrace (prefixWord ++ tailWord_1936521) baseStart_1936521 baseEnd_1936521 := by
    simpa [prefixWord, tailWord_1936521, baseEnd_1936521] using wordTrace_append hprefix tailTrace_1936521
  have hstable : (prefixWord ++ tailWord_1936521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936521).length < 2 ^ (prefixWord ++ tailWord_1936521).sum := by decide
  have hdescent : baseEnd_1936521 < baseStart_1936521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936693 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 3]
def baseStart_1936693 : Nat := 118140960795 + 1936693 * 2 ^ 59
def prefixEnd_1936693 : Nat := 4983230072969 + 3 ^ 40 * 1936693 * 2
def baseEnd_1936693 : Nat := 441979728532487294858141

theorem tailTrace_1936693 : CollatzResearch.WordTrace tailWord_1936693 prefixEnd_1936693 441979728532487294858141 := by
  unfold tailWord_1936693
  simp only [CollatzResearch.WordTrace]
  refine ⟨70636996772699496676294733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47091331181799664450863155 70636996772699496676294733)
  ·
    refine ⟨26488873789762311253610525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70636996772699496676294733 26488873789762311253610525)
    ·
      refine ⟨9933327671160866720103947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26488873789762311253610525 9933327671160866720103947)
      ·
        refine ⟨14899991506741300080155921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933327671160866720103947 14899991506741300080155921)
        ·
          refine ⟨11174993630055975060116941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14899991506741300080155921 11174993630055975060116941)
          ·
            refine ⟨4190622611270990647543853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11174993630055975060116941 4190622611270990647543853)
            ·
              refine ⟨1571483479226621492828945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4190622611270990647543853 1571483479226621492828945)
              ·
                refine ⟨1178612609419966119621709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571483479226621492828945 1178612609419966119621709)
                ·
                  refine ⟨441979728532487294858141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178612609419966119621709 441979728532487294858141)
                  ·
                    rfl

theorem cell21_1936693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_1936693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936693 prefixEnd_1936693 := by exact prefixLift 1936693
  have htrace : WordTrace (prefixWord ++ tailWord_1936693) baseStart_1936693 baseEnd_1936693 := by
    simpa [prefixWord, tailWord_1936693, baseEnd_1936693] using wordTrace_append hprefix tailTrace_1936693
  have hstable : (prefixWord ++ tailWord_1936693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936693).length < 2 ^ (prefixWord ++ tailWord_1936693).sum := by decide
  have hdescent : baseEnd_1936693 < baseStart_1936693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936718 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1936718 : Nat := 118140960795 + 1936718 * 2 ^ 59
def prefixEnd_1936718 : Nat := 4983230072969 + 3 ^ 40 * 1936718 * 2
def baseEnd_1936718 : Nat := 441985433873092806941423

theorem tailTrace_1936718 : CollatzResearch.WordTrace tailWord_1936718 prefixEnd_1936718 441985433873092806941423 := by
  unfold tailWord_1936718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829738574701115743244351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47091939065072617297303205 8829738574701115743244351)
  ·
    refine ⟨13244607862051673614866527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8829738574701115743244351 13244607862051673614866527)
    ·
      refine ⟨19866911793077510422299791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13244607862051673614866527 19866911793077510422299791)
      ·
        refine ⟨29800367689616265633449687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19866911793077510422299791 29800367689616265633449687)
        ·
          refine ⟨44700551534424398450174531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29800367689616265633449687 44700551534424398450174531)
          ·
            refine ⟨67050827301636597675261797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44700551534424398450174531 67050827301636597675261797)
            ·
              refine ⟨12572030119056862064111587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67050827301636597675261797 12572030119056862064111587)
              ·
                refine ⟨18858045178585293096167381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572030119056862064111587 18858045178585293096167381)
                ·
                  refine ⟨441985433873092806941423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18858045178585293096167381 441985433873092806941423)
                  ·
                    rfl

theorem cell21_1936718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1936718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936718 prefixEnd_1936718 := by exact prefixLift 1936718
  have htrace : WordTrace (prefixWord ++ tailWord_1936718) baseStart_1936718 baseEnd_1936718 := by
    simpa [prefixWord, tailWord_1936718, baseEnd_1936718] using wordTrace_append hprefix tailTrace_1936718
  have hstable : (prefixWord ++ tailWord_1936718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936718).length < 2 ^ (prefixWord ++ tailWord_1936718).sum := by decide
  have hdescent : baseEnd_1936718 < baseStart_1936718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936735 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 3]
def baseStart_1936735 : Nat := 118140960795 + 1936735 * 2 ^ 59
def prefixEnd_1936735 : Nat := 4983230072969 + 3 ^ 40 * 1936735 * 2
def baseEnd_1936735 : Nat := 441989313504704555158055

theorem tailTrace_1936735 : CollatzResearch.WordTrace tailWord_1936735 prefixEnd_1936735 441989313504704555158055 := by
  unfold tailWord_1936735
  simp only [CollatzResearch.WordTrace]
  refine ⟨70638528638547337849323659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47092352425698225232882439 70638528638547337849323659)
  ·
    refine ⟨105957792957821006773985489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70638528638547337849323659 105957792957821006773985489)
    ·
      refine ⟨79468344718365755080489117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105957792957821006773985489 79468344718365755080489117)
      ·
        refine ⟨29800629269387158155183419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79468344718365755080489117 29800629269387158155183419)
        ·
          refine ⟨44700943904080737232775129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29800629269387158155183419 44700943904080737232775129)
          ·
            refine ⟨33525707928060552924581347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44700943904080737232775129 33525707928060552924581347)
            ·
              refine ⟨50288561892090829386872021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33525707928060552924581347 50288561892090829386872021)
              ·
                refine ⟨1178638169345878813754813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50288561892090829386872021 1178638169345878813754813)
                ·
                  refine ⟨441989313504704555158055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178638169345878813754813 441989313504704555158055)
                  ·
                    rfl

theorem cell21_1936735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3].length) (baseStart_1936735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936735 prefixEnd_1936735 := by exact prefixLift 1936735
  have htrace : WordTrace (prefixWord ++ tailWord_1936735) baseStart_1936735 baseEnd_1936735 := by
    simpa [prefixWord, tailWord_1936735, baseEnd_1936735] using wordTrace_append hprefix tailTrace_1936735
  have hstable : (prefixWord ++ tailWord_1936735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936735).length < 2 ^ (prefixWord ++ tailWord_1936735).sum := by decide
  have hdescent : baseEnd_1936735 < baseStart_1936735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936780 : List Nat := [2, 2, 1, 2, 1, 3, 5, 5]
def baseStart_1936780 : Nat := 118140960795 + 1936780 * 2 ^ 59
def prefixEnd_1936780 : Nat := 4983230072969 + 3 ^ 40 * 1936780 * 2
def baseEnd_1936780 : Nat := 147333194372598158969321

theorem tailTrace_1936780 : CollatzResearch.WordTrace tailWord_1936780 prefixEnd_1936780 147333194372598158969321 := by
  unfold tailWord_1936780
  simp only [CollatzResearch.WordTrace]
  refine ⟨35320084961692155267355897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47093446615589540356474529 35320084961692155267355897)
  ·
    refine ⟨26490063721269116450516923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35320084961692155267355897 26490063721269116450516923)
    ·
      refine ⟨39735095581903674675775385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26490063721269116450516923 39735095581903674675775385)
      ·
        refine ⟨29801321686427756006831539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39735095581903674675775385 29801321686427756006831539)
        ·
          refine ⟨44701982529641634010247309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29801321686427756006831539 44701982529641634010247309)
          ·
            refine ⟨16763243448615612753842741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44701982529641634010247309 16763243448615612753842741)
            ·
              refine ⟨1571554073307713695672757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16763243448615612753842741 1571554073307713695672757)
              ·
                refine ⟨147333194372598158969321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571554073307713695672757 147333194372598158969321)
                ·
                  rfl

theorem cell21_1936780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_1936780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936780 prefixEnd_1936780 := by exact prefixLift 1936780
  have htrace : WordTrace (prefixWord ++ tailWord_1936780) baseStart_1936780 baseEnd_1936780 := by
    simpa [prefixWord, tailWord_1936780, baseEnd_1936780] using wordTrace_append hprefix tailTrace_1936780
  have hstable : (prefixWord ++ tailWord_1936780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936780).length < 2 ^ (prefixWord ++ tailWord_1936780).sum := by decide
  have hdescent : baseEnd_1936780 < baseStart_1936780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936786 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1936786 : Nat := 118140960795 + 1936786 * 2 ^ 59
def prefixEnd_1936786 : Nat := 4983230072969 + 3 ^ 40 * 1936786 * 2
def baseEnd_1936786 : Nat := 442000952399539799807951

theorem tailTrace_1936786 : CollatzResearch.WordTrace tailWord_1936786 prefixEnd_1936786 442000952399539799807951 := by
  unfold tailWord_1936786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660097190340643389857553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47093592507575049039620141 17660097190340643389857553)
  ·
    refine ⟨13245072892755482542393165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17660097190340643389857553 13245072892755482542393165)
    ·
      refine ⟨4966902334783305953397437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13245072892755482542393165 4966902334783305953397437)
      ·
        refine ⟨1862588375543739732524039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4966902334783305953397437 1862588375543739732524039)
        ·
          refine ⟨2793882563315609598786059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862588375543739732524039 2793882563315609598786059)
          ·
            refine ⟨4190823844973414398179089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793882563315609598786059 4190823844973414398179089)
            ·
              refine ⟨3143117883730060798634317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4190823844973414398179089 3143117883730060798634317)
              ·
                refine ⟨1178669206398772799487869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3143117883730060798634317 1178669206398772799487869)
                ·
                  refine ⟨442000952399539799807951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178669206398772799487869 442000952399539799807951)
                  ·
                    rfl

theorem cell21_1936786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1936786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936786 prefixEnd_1936786 := by exact prefixLift 1936786
  have htrace : WordTrace (prefixWord ++ tailWord_1936786) baseStart_1936786 baseEnd_1936786 := by
    simpa [prefixWord, tailWord_1936786, baseEnd_1936786] using wordTrace_append hprefix tailTrace_1936786
  have hstable : (prefixWord ++ tailWord_1936786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936786).length < 2 ^ (prefixWord ++ tailWord_1936786).sum := by decide
  have hdescent : baseEnd_1936786 < baseStart_1936786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936794 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1936794 : Nat := 118140960795 + 1936794 * 2 ^ 59
def prefixEnd_1936794 : Nat := 4983230072969 + 3 ^ 40 * 1936794 * 2
def baseEnd_1936794 : Nat := 442002778108533563674601

theorem tailTrace_1936794 : CollatzResearch.WordTrace tailWord_1936794 prefixEnd_1936794 442002778108533563674601 := by
  unfold tailWord_1936794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660170136333397731430359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47093787030222393950480957 17660170136333397731430359)
  ·
    refine ⟨26490255204500096597145539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17660170136333397731430359 26490255204500096597145539)
    ·
      refine ⟨39735382806750144895718309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26490255204500096597145539 39735382806750144895718309)
      ·
        refine ⟨7450384276265652167947183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39735382806750144895718309 7450384276265652167947183)
        ·
          refine ⟨11175576414398478251920775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450384276265652167947183 11175576414398478251920775)
          ·
            refine ⟨16763364621597717377881163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175576414398478251920775 16763364621597717377881163)
            ·
              refine ⟨25145046932396576066821745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16763364621597717377881163 25145046932396576066821745)
              ·
                refine ⟨18858785199297432050116309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25145046932396576066821745 18858785199297432050116309)
                ·
                  refine ⟨442002778108533563674601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18858785199297432050116309 442002778108533563674601)
                  ·
                    rfl

theorem cell21_1936794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1936794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936794 prefixEnd_1936794 := by exact prefixLift 1936794
  have htrace : WordTrace (prefixWord ++ tailWord_1936794) baseStart_1936794 baseEnd_1936794 := by
    simpa [prefixWord, tailWord_1936794, baseEnd_1936794] using wordTrace_append hprefix tailTrace_1936794
  have hstable : (prefixWord ++ tailWord_1936794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936794).length < 2 ^ (prefixWord ++ tailWord_1936794).sum := by decide
  have hdescent : baseEnd_1936794 < baseStart_1936794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936839 : List Nat := [1, 1, 4, 1, 1, 3, 3, 7]
def baseStart_1936839 : Nat := 118140960795 + 1936839 * 2 ^ 59
def prefixEnd_1936839 : Nat := 4983230072969 + 3 ^ 40 * 1936839 * 2
def baseEnd_1936839 : Nat := 147337682573874495141503

theorem tailTrace_1936839 : CollatzResearch.WordTrace tailWord_1936839 prefixEnd_1936839 147337682573874495141503 := by
  unfold tailWord_1936839
  simp only [CollatzResearch.WordTrace]
  refine ⟨70642321830170563611109571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47094881220113709074073047 70642321830170563611109571)
  ·
    refine ⟨105963482745255845416664357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70642321830170563611109571 105963482745255845416664357)
    ·
      refine ⟨19868153014735471015624567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105963482745255845416664357 19868153014735471015624567)
      ·
        refine ⟨29802229522103206523436851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19868153014735471015624567 29802229522103206523436851)
        ·
          refine ⟨44703344283154809785155277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29802229522103206523436851 44703344283154809785155277)
          ·
            refine ⟨16763754106183053669433229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44703344283154809785155277 16763754106183053669433229)
            ·
              refine ⟨6286407789818645126037461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16763754106183053669433229 6286407789818645126037461)
              ·
                refine ⟨147337682573874495141503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6286407789818645126037461 147337682573874495141503)
                ·
                  rfl

theorem cell21_1936839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_1936839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936839 prefixEnd_1936839 := by exact prefixLift 1936839
  have htrace : WordTrace (prefixWord ++ tailWord_1936839) baseStart_1936839 baseEnd_1936839 := by
    simpa [prefixWord, tailWord_1936839, baseEnd_1936839] using wordTrace_append hprefix tailTrace_1936839
  have hstable : (prefixWord ++ tailWord_1936839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936839).length < 2 ^ (prefixWord ++ tailWord_1936839).sum := by decide
  have hdescent : baseEnd_1936839 < baseStart_1936839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936960 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_1936960 : Nat := 118140960795 + 1936960 * 2 ^ 59
def prefixEnd_1936960 : Nat := 4983230072969 + 3 ^ 40 * 1936960 * 2
def baseEnd_1936960 : Nat := 442040661570154163907595

theorem tailTrace_1936960 : CollatzResearch.WordTrace tailWord_1936960 prefixEnd_1936960 442040661570154163907595 := by
  unfold tailWord_1936960
  simp only [CollatzResearch.WordTrace]
  refine ⟨35323367531366100638132167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47097823375154800850842889 35323367531366100638132167)
  ·
    refine ⟨52985051297049150957198251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35323367531366100638132167 52985051297049150957198251)
    ·
      refine ⟨79477576945573726435797377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52985051297049150957198251 79477576945573726435797377)
      ·
        refine ⟨59608182709180294826848033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79477576945573726435797377 59608182709180294826848033)
        ·
          refine ⟨44706137031885221120136025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59608182709180294826848033 44706137031885221120136025)
          ·
            refine ⟨33529602773913915840102019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44706137031885221120136025 33529602773913915840102019)
            ·
              refine ⟨50294404160870873760153029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33529602773913915840102019 50294404160870873760153029)
              ·
                refine ⟨9430200780163288830028693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50294404160870873760153029 9430200780163288830028693)
                ·
                  refine ⟨442040661570154163907595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9430200780163288830028693 442040661570154163907595)
                  ·
                    rfl

theorem cell21_1936960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_1936960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1936960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1936960 prefixEnd_1936960 := by exact prefixLift 1936960
  have htrace : WordTrace (prefixWord ++ tailWord_1936960) baseStart_1936960 baseEnd_1936960 := by
    simpa [prefixWord, tailWord_1936960, baseEnd_1936960] using wordTrace_append hprefix tailTrace_1936960
  have hstable : (prefixWord ++ tailWord_1936960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936960).length < 2 ^ (prefixWord ++ tailWord_1936960).sum := by decide
  have hdescent : baseEnd_1936960 < baseStart_1936960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937008 : List Nat := [2, 1, 1, 1, 6, 1, 4, 5]
def baseStart_1937008 : Nat := 118140960795 + 1937008 * 2 ^ 59
def prefixEnd_1937008 : Nat := 4983230072969 + 3 ^ 40 * 1937008 * 2
def baseEnd_1937008 : Nat := 147350538608038915702499

theorem tailTrace_1937008 : CollatzResearch.WordTrace tailWord_1937008 prefixEnd_1937008 147350538608038915702499 := by
  unfold tailWord_1937008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324242883279152737005839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47098990511038870316007785 35324242883279152737005839)
  ·
    refine ⟨52986364324918729105508759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35324242883279152737005839 52986364324918729105508759)
    ·
      refine ⟨79479546487378093658263139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52986364324918729105508759 79479546487378093658263139)
      ·
        refine ⟨119219319731067140487394709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79479546487378093658263139 119219319731067140487394709)
        ·
          refine ⟨5588405612393772210346627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119219319731067140487394709 5588405612393772210346627)
          ·
            refine ⟨8382608418590658315519941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588405612393772210346627 8382608418590658315519941)
            ·
              refine ⟨1571739078485748434159989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8382608418590658315519941 1571739078485748434159989)
              ·
                refine ⟨147350538608038915702499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571739078485748434159989 147350538608038915702499)
                ·
                  rfl

theorem cell21_1937008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_1937008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937008 prefixEnd_1937008 := by exact prefixLift 1937008
  have htrace : WordTrace (prefixWord ++ tailWord_1937008) baseStart_1937008 baseEnd_1937008 := by
    simpa [prefixWord, tailWord_1937008, baseEnd_1937008] using wordTrace_append hprefix tailTrace_1937008
  have hstable : (prefixWord ++ tailWord_1937008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937008).length < 2 ^ (prefixWord ++ tailWord_1937008).sum := by decide
  have hdescent : baseEnd_1937008 < baseStart_1937008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937036 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1937036 : Nat := 118140960795 + 1937036 * 2 ^ 59
def prefixEnd_1937036 : Nat := 4983230072969 + 3 ^ 40 * 1937036 * 2
def baseEnd_1937036 : Nat := 442058005805594920640773

theorem tailTrace_1937036 : CollatzResearch.WordTrace tailWord_1937036 prefixEnd_1937036 442058005805594920640773 := by
  unfold tailWord_1937036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324753505228433128015481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47099671340304577504020641 35324753505228433128015481)
  ·
    refine ⟨26493565128921324846011611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35324753505228433128015481 26493565128921324846011611)
    ·
      refine ⟨39740347693381987269017417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26493565128921324846011611 39740347693381987269017417)
      ·
        refine ⟨29805260770036490451763063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39740347693381987269017417 29805260770036490451763063)
        ·
          refine ⟨44707891155054735677644595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29805260770036490451763063 44707891155054735677644595)
          ·
            refine ⟨67061836732582103516466893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44707891155054735677644595 67061836732582103516466893)
            ·
              refine ⟨25148188774718288818675085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67061836732582103516466893 25148188774718288818675085)
              ·
                refine ⟨9430570790519358307003157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25148188774718288818675085 9430570790519358307003157)
                ·
                  refine ⟨442058005805594920640773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9430570790519358307003157 442058005805594920640773)
                  ·
                    rfl

theorem cell21_1937036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1937036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937036 prefixEnd_1937036 := by exact prefixLift 1937036
  have htrace : WordTrace (prefixWord ++ tailWord_1937036) baseStart_1937036 baseEnd_1937036 := by
    simpa [prefixWord, tailWord_1937036, baseEnd_1937036] using wordTrace_append hprefix tailTrace_1937036
  have hstable : (prefixWord ++ tailWord_1937036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937036).length < 2 ^ (prefixWord ++ tailWord_1937036).sum := by decide
  have hdescent : baseEnd_1937036 < baseStart_1937036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937101 : List Nat := [1, 6, 2, 1, 1, 1, 3, 6]
def baseStart_1937101 : Nat := 118140960795 + 1937101 * 2 ^ 59
def prefixEnd_1937101 : Nat := 4983230072969 + 3 ^ 40 * 1937101 * 2
def baseEnd_1937101 : Nat := 147357613230389750685769

theorem tailTrace_1937101 : CollatzResearch.WordTrace tailWord_1937101 prefixEnd_1937101 147357613230389750685769 := by
  unfold tailWord_1937101
  simp only [CollatzResearch.WordTrace]
  refine ⟨70651877755221382357147157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47101251836814254904764771 70651877755221382357147157)
  ·
    refine ⟨3311806769776002297991273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70651877755221382357147157 3311806769776002297991273)
    ·
      refine ⟨2483855077332001723493455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3311806769776002297991273 2483855077332001723493455)
      ·
        refine ⟨3725782615998002585240183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483855077332001723493455 3725782615998002585240183)
        ·
          refine ⟨5588673923997003877860275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725782615998002585240183 5588673923997003877860275)
          ·
            refine ⟨8383010885995505816790413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588673923997003877860275 8383010885995505816790413)
            ·
              refine ⟨3143629082248314681296405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8383010885995505816790413 3143629082248314681296405)
              ·
                refine ⟨147357613230389750685769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3143629082248314681296405 147357613230389750685769)
                ·
                  rfl

theorem cell21_1937101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_1937101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937101 prefixEnd_1937101 := by exact prefixLift 1937101
  have htrace : WordTrace (prefixWord ++ tailWord_1937101) baseStart_1937101 baseEnd_1937101 := by
    simpa [prefixWord, tailWord_1937101, baseEnd_1937101] using wordTrace_append hprefix tailTrace_1937101
  have hstable : (prefixWord ++ tailWord_1937101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937101).length < 2 ^ (prefixWord ++ tailWord_1937101).sum := by decide
  have hdescent : baseEnd_1937101 < baseStart_1937101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937208 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_1937208 : Nat := 118140960795 + 1937208 * 2 ^ 59
def prefixEnd_1937208 : Nat := 4983230072969 + 3 ^ 40 * 1937208 * 2
def baseEnd_1937208 : Nat := 442097258548960843773755

theorem tailTrace_1937208 : CollatzResearch.WordTrace tailWord_1937208 prefixEnd_1937208 442097258548960843773755 := by
  unfold tailWord_1937208
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327890182916869815646139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47103853577222493087528185 35327890182916869815646139)
  ·
    refine ⟨52991835274375304723469209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35327890182916869815646139 52991835274375304723469209)
    ·
      refine ⟨39743876455781478542601907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52991835274375304723469209 39743876455781478542601907)
      ·
        refine ⟨59615814683672217813902861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39743876455781478542601907 59615814683672217813902861)
        ·
          refine ⟨22355930506377081680213573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59615814683672217813902861 22355930506377081680213573)
          ·
            refine ⟨4191736969945702815040045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22355930506377081680213573 4191736969945702815040045)
            ·
              refine ⟨1571901363729638555640017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4191736969945702815040045 1571901363729638555640017)
              ·
                refine ⟨1178926022797228916730013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571901363729638555640017 1178926022797228916730013)
                ·
                  refine ⟨442097258548960843773755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1178926022797228916730013 442097258548960843773755)
                  ·
                    rfl

theorem cell21_1937208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_1937208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937208 prefixEnd_1937208 := by exact prefixLift 1937208
  have htrace : WordTrace (prefixWord ++ tailWord_1937208) baseStart_1937208 baseEnd_1937208 := by
    simpa [prefixWord, tailWord_1937208, baseEnd_1937208] using wordTrace_append hprefix tailTrace_1937208
  have hstable : (prefixWord ++ tailWord_1937208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937208).length < 2 ^ (prefixWord ++ tailWord_1937208).sum := by decide
  have hdescent : baseEnd_1937208 < baseStart_1937208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937219 : List Nat := [1, 1, 1, 3, 1, 6, 2, 6]
def baseStart_1937219 : Nat := 118140960795 + 1937219 * 2 ^ 59
def prefixEnd_1937219 : Nat := 4983230072969 + 3 ^ 40 * 1937219 * 2
def baseEnd_1937219 : Nat := 147366589632942423030133

theorem tailTrace_1937219 : CollatzResearch.WordTrace tailWord_1937219 prefixEnd_1937219 147366589632942423030133 := by
  unfold tailWord_1937219
  simp only [CollatzResearch.WordTrace]
  refine ⟨70656181568793888509942711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47104121045862592339961807 70656181568793888509942711)
  ·
    refine ⟨105984272353190832764914067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70656181568793888509942711 105984272353190832764914067)
    ·
      refine ⟨158976408529786249147371101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105984272353190832764914067 158976408529786249147371101)
      ·
        refine ⟨59616153198669843430264163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158976408529786249147371101 59616153198669843430264163)
        ·
          refine ⟨89424229798004765145396245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59616153198669843430264163 89424229798004765145396245)
          ·
            refine ⟨4191760771781473366190449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89424229798004765145396245 4191760771781473366190449)
            ·
              refine ⟨3143820578836105024642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191760771781473366190449 3143820578836105024642837)
              ·
                refine ⟨147366589632942423030133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3143820578836105024642837 147366589632942423030133)
                ·
                  rfl

theorem cell21_1937219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_1937219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937219 prefixEnd_1937219 := by exact prefixLift 1937219
  have htrace : WordTrace (prefixWord ++ tailWord_1937219) baseStart_1937219 baseEnd_1937219 := by
    simpa [prefixWord, tailWord_1937219, baseEnd_1937219] using wordTrace_append hprefix tailTrace_1937219
  have hstable : (prefixWord ++ tailWord_1937219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937219).length < 2 ^ (prefixWord ++ tailWord_1937219).sum := by decide
  have hdescent : baseEnd_1937219 < baseStart_1937219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937270 : List Nat := [5, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1937270 : Nat := 118140960795 + 1937270 * 2 ^ 59
def prefixEnd_1937270 : Nat := 4983230072969 + 3 ^ 40 * 1937270 * 2
def baseEnd_1937270 : Nat := 147370469264554171246765

theorem tailTrace_1937270 : CollatzResearch.WordTrace tailWord_1937270 prefixEnd_1937270 147370469264554171246765 := by
  unfold tailWord_1937270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416127605725570263753079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47105361127739416146699509 4416127605725570263753079)
  ·
    refine ⟨6624191408588355395629619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4416127605725570263753079 6624191408588355395629619)
    ·
      refine ⟨9936287112882533093444429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624191408588355395629619 9936287112882533093444429)
      ·
        refine ⟨3726107667330949910041661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9936287112882533093444429 3726107667330949910041661)
        ·
          refine ⟨1397290375249106216265623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3726107667330949910041661 1397290375249106216265623)
          ·
            refine ⟨2095935562873659324398435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397290375249106216265623 2095935562873659324398435)
            ·
              refine ⟨3143903344310488986597653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095935562873659324398435 3143903344310488986597653)
              ·
                refine ⟨147370469264554171246765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3143903344310488986597653 147370469264554171246765)
                ·
                  rfl

theorem cell21_1937270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1937270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937270 prefixEnd_1937270 := by exact prefixLift 1937270
  have htrace : WordTrace (prefixWord ++ tailWord_1937270) baseStart_1937270 baseEnd_1937270 := by
    simpa [prefixWord, tailWord_1937270, baseEnd_1937270] using wordTrace_append hprefix tailTrace_1937270
  have hstable : (prefixWord ++ tailWord_1937270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937270).length < 2 ^ (prefixWord ++ tailWord_1937270).sum := by decide
  have hdescent : baseEnd_1937270 < baseStart_1937270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937332 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1937332 : Nat := 118140960795 + 1937332 * 2 ^ 59
def prefixEnd_1937332 : Nat := 4983230072969 + 3 ^ 40 * 1937332 * 2
def baseEnd_1937332 : Nat := 442125557038364183706835

theorem tailTrace_1937332 : CollatzResearch.WordTrace tailWord_1937332 prefixEnd_1937332 442125557038364183706835 := by
  unfold tailWord_1937332
  simp only [CollatzResearch.WordTrace]
  refine ⟨35330151508692254404403125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47106868678256339205870833 35330151508692254404403125)
  ·
    refine ⟨3312201703939898850412793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35330151508692254404403125 3312201703939898850412793)
    ·
      refine ⟨2484151277954924137809595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3312201703939898850412793 2484151277954924137809595)
      ·
        refine ⟨3726226916932386206714393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484151277954924137809595 3726226916932386206714393)
        ·
          refine ⟨2794670187699289655035795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726226916932386206714393 2794670187699289655035795)
          ·
            refine ⟨4192005281548934482553693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794670187699289655035795 4192005281548934482553693)
            ·
              refine ⟨1572001980580850430957635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4192005281548934482553693 1572001980580850430957635)
              ·
                refine ⟨2358002970871275646436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572001980580850430957635 2358002970871275646436453)
                ·
                  refine ⟨442125557038364183706835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358002970871275646436453 442125557038364183706835)
                  ·
                    rfl

theorem cell21_1937332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1937332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937332 prefixEnd_1937332 := by exact prefixLift 1937332
  have htrace : WordTrace (prefixWord ++ tailWord_1937332) baseStart_1937332 baseEnd_1937332 := by
    simpa [prefixWord, tailWord_1937332, baseEnd_1937332] using wordTrace_append hprefix tailTrace_1937332
  have hstable : (prefixWord ++ tailWord_1937332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937332).length < 2 ^ (prefixWord ++ tailWord_1937332).sum := by decide
  have hdescent : baseEnd_1937332 < baseStart_1937332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937430 : List Nat := [5, 16]
def baseStart_1937430 : Nat := 118140960795 + 1937430 * 2 ^ 59
def prefixEnd_1937430 : Nat := 4983230072969 + 3 ^ 40 * 1937430 * 2
def baseEnd_1937430 : Nat := 202170974839294829023

theorem tailTrace_1937430 : CollatzResearch.WordTrace tailWord_1937430 prefixEnd_1937430 202170974839294829023 := by
  unfold tailWord_1937430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416492335689341971617109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47109251580686314363915829 4416492335689341971617109)
  ·
    refine ⟨202170974839294829023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 16 4416492335689341971617109 202170974839294829023)
    ·
      rfl

theorem cell21_1937430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 16].length) (baseStart_1937430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937430 prefixEnd_1937430 := by exact prefixLift 1937430
  have htrace : WordTrace (prefixWord ++ tailWord_1937430) baseStart_1937430 baseEnd_1937430 := by
    simpa [prefixWord, tailWord_1937430, baseEnd_1937430] using wordTrace_append hprefix tailTrace_1937430
  have hstable : (prefixWord ++ tailWord_1937430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937430).length < 2 ^ (prefixWord ++ tailWord_1937430).sum := by decide
  have hdescent : baseEnd_1937430 < baseStart_1937430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937436 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_1937436 : Nat := 118140960795 + 1937436 * 2 ^ 59
def prefixEnd_1937436 : Nat := 4983230072969 + 3 ^ 40 * 1937436 * 2
def baseEnd_1937436 : Nat := 442149291255283113973289

theorem tailTrace_1937436 : CollatzResearch.WordTrace tailWord_1937436 prefixEnd_1937436 442149291255283113973289 := by
  unfold tailWord_1937436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35332048104503867285296081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47109397472671823047061441 35332048104503867285296081)
  ·
    refine ⟨26499036078377900463972061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35332048104503867285296081 26499036078377900463972061)
    ·
      refine ⟨9937138529391712673989523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26499036078377900463972061 9937138529391712673989523)
      ·
        refine ⟨14905707794087569010984285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937138529391712673989523 14905707794087569010984285)
        ·
          refine ⟨5589640422782838379119107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14905707794087569010984285 5589640422782838379119107)
          ·
            refine ⟨8384460634174257568678661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589640422782838379119107 8384460634174257568678661)
            ·
              refine ⟨1572086368907673294127249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8384460634174257568678661 1572086368907673294127249)
              ·
                refine ⟨1179064776680754970595437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572086368907673294127249 1179064776680754970595437)
                ·
                  refine ⟨442149291255283113973289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179064776680754970595437 442149291255283113973289)
                  ·
                    rfl

theorem cell21_1937436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_1937436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937436 prefixEnd_1937436 := by exact prefixLift 1937436
  have htrace : WordTrace (prefixWord ++ tailWord_1937436) baseStart_1937436 baseEnd_1937436 := by
    simpa [prefixWord, tailWord_1937436, baseEnd_1937436] using wordTrace_append hprefix tailTrace_1937436
  have hstable : (prefixWord ++ tailWord_1937436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937436).length < 2 ^ (prefixWord ++ tailWord_1937436).sum := by decide
  have hdescent : baseEnd_1937436 < baseStart_1937436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937461 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_1937461 : Nat := 118140960795 + 1937461 * 2 ^ 59
def prefixEnd_1937461 : Nat := 4983230072969 + 3 ^ 40 * 1937461 * 2
def baseEnd_1937461 : Nat := 442154996595888626056571

theorem tailTrace_1937461 : CollatzResearch.WordTrace tailWord_1937461 prefixEnd_1937461 442154996595888626056571 := by
  unfold tailWord_1937461
  simp only [CollatzResearch.WordTrace]
  refine ⟨70665008033917163840252237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47110005355944775893501491 70665008033917163840252237)
  ·
    refine ⟨26499378012718936440094589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70665008033917163840252237 26499378012718936440094589)
    ·
      refine ⟨9937266754769601165035471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26499378012718936440094589 9937266754769601165035471)
      ·
        refine ⟨14905900132154401747553207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937266754769601165035471 14905900132154401747553207)
        ·
          refine ⟨22358850198231602621329811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14905900132154401747553207 22358850198231602621329811)
          ·
            refine ⟨33538275297347403931994717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22358850198231602621329811 33538275297347403931994717)
            ·
              refine ⟨12576853236505276474498019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33538275297347403931994717 12576853236505276474498019)
              ·
                refine ⟨18865279854757914711747029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12576853236505276474498019 18865279854757914711747029)
                ·
                  refine ⟨442154996595888626056571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18865279854757914711747029 442154996595888626056571)
                  ·
                    rfl

theorem cell21_1937461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_1937461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937461 prefixEnd_1937461 := by exact prefixLift 1937461
  have htrace : WordTrace (prefixWord ++ tailWord_1937461) baseStart_1937461 baseEnd_1937461 := by
    simpa [prefixWord, tailWord_1937461, baseEnd_1937461] using wordTrace_append hprefix tailTrace_1937461
  have hstable : (prefixWord ++ tailWord_1937461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937461).length < 2 ^ (prefixWord ++ tailWord_1937461).sum := by decide
  have hdescent : baseEnd_1937461 < baseStart_1937461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937464 : List Nat := [2, 1, 2, 1, 6, 1, 3, 5]
def baseStart_1937464 : Nat := 118140960795 + 1937464 * 2 ^ 59
def prefixEnd_1937464 : Nat := 4983230072969 + 3 ^ 40 * 1937464 * 2
def baseEnd_1937464 : Nat := 147385227078920429168855

theorem tailTrace_1937464 : CollatzResearch.WordTrace tailWord_1937464 prefixEnd_1937464 147385227078920429168855 := by
  unfold tailWord_1937464
  simp only [CollatzResearch.WordTrace]
  refine ⟨35332558726453147676305723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47110078301937530235074297 35332558726453147676305723)
  ·
    refine ⟨52998838089679721514458585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35332558726453147676305723 52998838089679721514458585)
    ·
      refine ⟨39749128567259791135843939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52998838089679721514458585 39749128567259791135843939)
      ·
        refine ⟨59623692850889686703765909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39749128567259791135843939 59623692850889686703765909)
        ·
          refine ⟨2794860602385454064239027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59623692850889686703765909 2794860602385454064239027)
          ·
            refine ⟨4192290903578181096358541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794860602385454064239027 4192290903578181096358541)
            ·
              refine ⟨1572109088841817911134453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4192290903578181096358541 1572109088841817911134453)
              ·
                refine ⟨147385227078920429168855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1572109088841817911134453 147385227078920429168855)
                ·
                  rfl

theorem cell21_1937464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_1937464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937464 prefixEnd_1937464 := by exact prefixLift 1937464
  have htrace : WordTrace (prefixWord ++ tailWord_1937464) baseStart_1937464 baseEnd_1937464 := by
    simpa [prefixWord, tailWord_1937464, baseEnd_1937464] using wordTrace_append hprefix tailTrace_1937464
  have hstable : (prefixWord ++ tailWord_1937464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937464).length < 2 ^ (prefixWord ++ tailWord_1937464).sum := by decide
  have hdescent : baseEnd_1937464 < baseStart_1937464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937647 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 3]
def baseStart_1937647 : Nat := 118140960795 + 1937647 * 2 ^ 59
def prefixEnd_1937647 : Nat := 4983230072969 + 3 ^ 40 * 1937647 * 2
def baseEnd_1937647 : Nat := 442197444329993635956191

theorem tailTrace_1937647 : CollatzResearch.WordTrace tailWord_1937647 prefixEnd_1937647 442197444329993635956191 := by
  unfold tailWord_1937647
  simp only [CollatzResearch.WordTrace]
  refine ⟨70671792011243317606523195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47114528007495545071015463 70671792011243317606523195)
  ·
    refine ⟨106007688016864976409784793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70671792011243317606523195 106007688016864976409784793)
    ·
      refine ⟨79505766012648732307338595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106007688016864976409784793 79505766012648732307338595)
      ·
        refine ⟨119258649018973098461007893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79505766012648732307338595 119258649018973098461007893)
        ·
          refine ⟨5590249172764363990359745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119258649018973098461007893 5590249172764363990359745)
          ·
            refine ⟨4192686879573272992769809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590249172764363990359745 4192686879573272992769809)
            ·
              refine ⟨3144515159679954744577357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192686879573272992769809 3144515159679954744577357)
              ·
                refine ⟨1179193184879983029216509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3144515159679954744577357 1179193184879983029216509)
                ·
                  refine ⟨442197444329993635956191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179193184879983029216509 442197444329993635956191)
                  ·
                    rfl

theorem cell21_1937647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3].length) (baseStart_1937647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937647 prefixEnd_1937647 := by exact prefixLift 1937647
  have htrace : WordTrace (prefixWord ++ tailWord_1937647) baseStart_1937647 baseEnd_1937647 := by
    simpa [prefixWord, tailWord_1937647, baseEnd_1937647] using wordTrace_append hprefix tailTrace_1937647
  have hstable : (prefixWord ++ tailWord_1937647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937647).length < 2 ^ (prefixWord ++ tailWord_1937647).sum := by decide
  have hdescent : baseEnd_1937647 < baseStart_1937647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937658 : List Nat := [3, 1, 1, 1, 1, 6, 8]
def baseStart_1937658 : Nat := 118140960795 + 1937658 * 2 ^ 59
def prefixEnd_1937658 : Nat := 4983230072969 + 3 ^ 40 * 1937658 * 2
def baseEnd_1937658 : Nat := 49133328297762229030315

theorem tailTrace_1937658 : CollatzResearch.WordTrace tailWord_1937658 prefixEnd_1937658 49133328297762229030315 := by
  unfold tailWord_1937658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668048303550866621293407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47114795476135644323449085 17668048303550866621293407)
  ·
    refine ⟨26502072455326299931940111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17668048303550866621293407 26502072455326299931940111)
    ·
      refine ⟨39753108682989449897910167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26502072455326299931940111 39753108682989449897910167)
      ·
        refine ⟨59629663024484174846865251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39753108682989449897910167 59629663024484174846865251)
        ·
          refine ⟨89444494536726262270297877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59629663024484174846865251 89444494536726262270297877)
          ·
            refine ⟨4192710681409043543920213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89444494536726262270297877 4192710681409043543920213)
            ·
              refine ⟨49133328297762229030315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4192710681409043543920213 49133328297762229030315)
              ·
                rfl

theorem cell21_1937658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 8].length) (baseStart_1937658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937658 prefixEnd_1937658 := by exact prefixLift 1937658
  have htrace : WordTrace (prefixWord ++ tailWord_1937658) baseStart_1937658 baseEnd_1937658 := by
    simpa [prefixWord, tailWord_1937658, baseEnd_1937658] using wordTrace_append hprefix tailTrace_1937658
  have hstable : (prefixWord ++ tailWord_1937658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937658).length < 2 ^ (prefixWord ++ tailWord_1937658).sum := by decide
  have hdescent : baseEnd_1937658 < baseStart_1937658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937709 : List Nat := [1, 5, 3, 1, 3, 1, 7]
def baseStart_1937709 : Nat := 118140960795 + 1937709 * 2 ^ 59
def prefixEnd_1937709 : Nat := 4983230072969 + 3 ^ 40 * 1937709 * 2
def baseEnd_1937709 : Nat := 49134621508299478435859

theorem tailTrace_1937709 : CollatzResearch.WordTrace tailWord_1937709 prefixEnd_1937709 49134621508299478435859 := by
  unfold tailWord_1937709
  simp only [CollatzResearch.WordTrace]
  refine ⟨70674053337018702195280181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47116035558012468130186787 70674053337018702195280181)
  ·
    refine ⟨6625692500345503330807517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70674053337018702195280181 6625692500345503330807517)
    ·
      refine ⟨2484634687629563749052819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6625692500345503330807517 2484634687629563749052819)
      ·
        refine ⟨3726952031444345623579229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484634687629563749052819 3726952031444345623579229)
        ·
          refine ⟨1397607011791629608842211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3726952031444345623579229 1397607011791629608842211)
          ·
            refine ⟨2096410517687444413263317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397607011791629608842211 2096410517687444413263317)
            ·
              refine ⟨49134621508299478435859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2096410517687444413263317 49134621508299478435859)
              ·
                rfl

theorem cell21_1937709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 7].length) (baseStart_1937709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937709 prefixEnd_1937709 := by exact prefixLift 1937709
  have htrace : WordTrace (prefixWord ++ tailWord_1937709) baseStart_1937709 baseEnd_1937709 := by
    simpa [prefixWord, tailWord_1937709, baseEnd_1937709] using wordTrace_append hprefix tailTrace_1937709
  have hstable : (prefixWord ++ tailWord_1937709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937709).length < 2 ^ (prefixWord ++ tailWord_1937709).sum := by decide
  have hdescent : baseEnd_1937709 < baseStart_1937709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937796 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1937796 : Nat := 118140960795 + 1937796 * 2 ^ 59
def prefixEnd_1937796 : Nat := 4983230072969 + 3 ^ 40 * 1937796 * 2
def baseEnd_1937796 : Nat := 442231448160002487972553

theorem tailTrace_1937796 : CollatzResearch.WordTrace tailWord_1937796 prefixEnd_1937796 442231448160002487972553 := by
  unfold tailWord_1937796
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338613243851758026848621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47118150991802344035798161 35338613243851758026848621)
  ·
    refine ⟨13251979966444409260068233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35338613243851758026848621 13251979966444409260068233)
    ·
      refine ⟨9938984974833306945051175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13251979966444409260068233 9938984974833306945051175)
      ·
        refine ⟨14908477462249960417576763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9938984974833306945051175 14908477462249960417576763)
        ·
          refine ⟨22362716193374940626365145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14908477462249960417576763 22362716193374940626365145)
          ·
            refine ⟨16772037145031205469773859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22362716193374940626365145 16772037145031205469773859)
            ·
              refine ⟨25158055717546808204660789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772037145031205469773859 25158055717546808204660789)
              ·
                refine ⟨2358567723520013269186949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25158055717546808204660789 2358567723520013269186949)
                ·
                  refine ⟨442231448160002487972553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358567723520013269186949 442231448160002487972553)
                  ·
                    rfl

theorem cell21_1937796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1937796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937796 prefixEnd_1937796 := by exact prefixLift 1937796
  have htrace : WordTrace (prefixWord ++ tailWord_1937796) baseStart_1937796 baseEnd_1937796 := by
    simpa [prefixWord, tailWord_1937796, baseEnd_1937796] using wordTrace_append hprefix tailTrace_1937796
  have hstable : (prefixWord ++ tailWord_1937796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937796).length < 2 ^ (prefixWord ++ tailWord_1937796).sum := by decide
  have hdescent : baseEnd_1937796 < baseStart_1937796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937841 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_1937841 : Nat := 118140960795 + 1937841 * 2 ^ 59
def prefixEnd_1937841 : Nat := 4983230072969 + 3 ^ 40 * 1937841 * 2
def baseEnd_1937841 : Nat := 442241717773092409722461

theorem tailTrace_1937841 : CollatzResearch.WordTrace tailWord_1937841 prefixEnd_1937841 442241717773092409722461 := by
  unfold tailWord_1937841
  simp only [CollatzResearch.WordTrace]
  refine ⟨70678867772540488739085377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47119245181693659159390251 70678867772540488739085377)
  ·
    refine ⟨53009150829405366554314033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70678867772540488739085377 53009150829405366554314033)
    ·
      refine ⟨39756863122054024915735525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53009150829405366554314033 39756863122054024915735525)
      ·
        refine ⟨7454411835385129671700411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39756863122054024915735525 7454411835385129671700411)
        ·
          refine ⟨11181617753077694507550617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454411835385129671700411 11181617753077694507550617)
          ·
            refine ⟨8386213314808270880662963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11181617753077694507550617 8386213314808270880662963)
            ·
              refine ⟨12579319972212406320994445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386213314808270880662963 12579319972212406320994445)
              ·
                refine ⟨4717244989579652370372917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12579319972212406320994445 4717244989579652370372917)
                ·
                  refine ⟨442241717773092409722461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4717244989579652370372917 442241717773092409722461)
                  ·
                    rfl

theorem cell21_1937841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_1937841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937841 prefixEnd_1937841 := by exact prefixLift 1937841
  have htrace : WordTrace (prefixWord ++ tailWord_1937841) baseStart_1937841 baseEnd_1937841 := by
    simpa [prefixWord, tailWord_1937841, baseEnd_1937841] using wordTrace_append hprefix tailTrace_1937841
  have hstable : (prefixWord ++ tailWord_1937841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937841).length < 2 ^ (prefixWord ++ tailWord_1937841).sum := by decide
  have hdescent : baseEnd_1937841 < baseStart_1937841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937948 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1937948 : Nat := 118140960795 + 1937948 * 2 ^ 59
def prefixEnd_1937948 : Nat := 4983230072969 + 3 ^ 40 * 1937948 * 2
def baseEnd_1937948 : Nat := 442266136630884001438909

theorem tailTrace_1937948 : CollatzResearch.WordTrace tailWord_1937948 prefixEnd_1937948 442266136630884001438909 := by
  unfold tailWord_1937948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35341385191576423006615249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47121846922101897342153665 35341385191576423006615249)
  ·
    refine ⟨26506038893682317254961437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35341385191576423006615249 26506038893682317254961437)
    ·
      refine ⟨9939764585130868970610539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26506038893682317254961437 9939764585130868970610539)
      ·
        refine ⟨14909646877696303455915809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939764585130868970610539 14909646877696303455915809)
        ·
          refine ⟨11182235158272227591936857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14909646877696303455915809 11182235158272227591936857)
          ·
            refine ⟨8386676368704170693952643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11182235158272227591936857 8386676368704170693952643)
            ·
              refine ⟨12580014553056256040928965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386676368704170693952643 12580014553056256040928965)
              ·
                refine ⟨2358752728698048007674181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12580014553056256040928965 2358752728698048007674181)
                ·
                  refine ⟨442266136630884001438909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358752728698048007674181 442266136630884001438909)
                  ·
                    rfl

theorem cell21_1937948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1937948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1937948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1937948 prefixEnd_1937948 := by exact prefixLift 1937948
  have htrace : WordTrace (prefixWord ++ tailWord_1937948) baseStart_1937948 baseEnd_1937948 := by
    simpa [prefixWord, tailWord_1937948, baseEnd_1937948] using wordTrace_append hprefix tailTrace_1937948
  have hstable : (prefixWord ++ tailWord_1937948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937948).length < 2 ^ (prefixWord ++ tailWord_1937948).sum := by decide
  have hdescent : baseEnd_1937948 < baseStart_1937948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938007 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_1938007 : Nat := 118140960795 + 1938007 * 2 ^ 59
def prefixEnd_1938007 : Nat := 4983230072969 + 3 ^ 40 * 1938007 * 2
def baseEnd_1938007 : Nat := 442279601234713009955455

theorem tailTrace_1938007 : CollatzResearch.WordTrace tailWord_1938007 prefixEnd_1938007 442279601234713009955455 := by
  unfold tailWord_1938007
  simp only [CollatzResearch.WordTrace]
  refine ⟨70684922289939099089628275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47123281526626066059752183 70684922289939099089628275)
  ·
    refine ⟨106027383434908648634442413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70684922289939099089628275 106027383434908648634442413)
    ·
      refine ⟨39760268788090743237915905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106027383434908648634442413 39760268788090743237915905)
      ·
        refine ⟨29820201591068057428436929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39760268788090743237915905 29820201591068057428436929)
        ·
          refine ⟨22365151193301043071327697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29820201591068057428436929 22365151193301043071327697)
          ·
            refine ⟨16773863394975782303495773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22365151193301043071327697 16773863394975782303495773)
            ·
              refine ⟨6290198773115918363810915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16773863394975782303495773 6290198773115918363810915)
              ·
                refine ⟨9435298159673877545716373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290198773115918363810915 9435298159673877545716373)
                ·
                  refine ⟨442279601234713009955455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9435298159673877545716373 442279601234713009955455)
                  ·
                    rfl

theorem cell21_1938007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_1938007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938007 prefixEnd_1938007 := by exact prefixLift 1938007
  have htrace : WordTrace (prefixWord ++ tailWord_1938007) baseStart_1938007 baseEnd_1938007 := by
    simpa [prefixWord, tailWord_1938007, baseEnd_1938007] using wordTrace_append hprefix tailTrace_1938007
  have hstable : (prefixWord ++ tailWord_1938007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938007).length < 2 ^ (prefixWord ++ tailWord_1938007).sum := by decide
  have hdescent : baseEnd_1938007 < baseStart_1938007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938145 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_1938145 : Nat := 118140960795 + 1938145 * 2 ^ 59
def prefixEnd_1938145 : Nat := 4983230072969 + 3 ^ 40 * 1938145 * 2
def baseEnd_1938145 : Nat := 442311094714855436655173

theorem tailTrace_1938145 : CollatzResearch.WordTrace tailWord_1938145 prefixEnd_1938145 442311094714855436655173 := by
  unfold tailWord_1938145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70689955563439148658151889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47126637042292765772101259 70689955563439148658151889)
  ·
    refine ⟨53017466672579361493613917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70689955563439148658151889 53017466672579361493613917)
    ·
      refine ⟨19881550002217260560105219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53017466672579361493613917 19881550002217260560105219)
      ·
        refine ⟨29822325003325890840157829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19881550002217260560105219 29822325003325890840157829)
        ·
          refine ⟨5591685938123604532529593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29822325003325890840157829 5591685938123604532529593)
          ·
            refine ⟨4193764453592703399397195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591685938123604532529593 4193764453592703399397195)
            ·
              refine ⟨6290646680389055099095793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193764453592703399397195 6290646680389055099095793)
              ·
                refine ⟨4717985010291791324321845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6290646680389055099095793 4717985010291791324321845)
                ·
                  refine ⟨442311094714855436655173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4717985010291791324321845 442311094714855436655173)
                  ·
                    rfl

theorem cell21_1938145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_1938145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938145 prefixEnd_1938145 := by exact prefixLift 1938145
  have htrace : WordTrace (prefixWord ++ tailWord_1938145) baseStart_1938145 baseEnd_1938145 := by
    simpa [prefixWord, tailWord_1938145, baseEnd_1938145] using wordTrace_append hprefix tailTrace_1938145
  have hstable : (prefixWord ++ tailWord_1938145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938145).length < 2 ^ (prefixWord ++ tailWord_1938145).sum := by decide
  have hdescent : baseEnd_1938145 < baseStart_1938145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938162 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1938162 : Nat := 118140960795 + 1938162 * 2 ^ 59
def prefixEnd_1938162 : Nat := 4983230072969 + 3 ^ 40 * 1938162 * 2
def baseEnd_1938162 : Nat := 442314974346467184871805

theorem tailTrace_1938162 : CollatzResearch.WordTrace tailWord_1938162 prefixEnd_1938162 442314974346467184871805 := by
  unfold tailWord_1938162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672643901094390140380185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47127050402918373707680493 17672643901094390140380185)
  ·
    refine ⟨13254482925820792605285139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17672643901094390140380185 13254482925820792605285139)
    ·
      refine ⟨19881724388731188907927709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13254482925820792605285139 19881724388731188907927709)
      ·
        refine ⟨7455646645774195840472891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19881724388731188907927709 7455646645774195840472891)
        ·
          refine ⟨11183469968661293760709337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455646645774195840472891 11183469968661293760709337)
          ·
            refine ⟨8387602476495970320532003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183469968661293760709337 8387602476495970320532003)
            ·
              refine ⟨12581403714743955480798005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387602476495970320532003 12581403714743955480798005)
              ·
                refine ⟨1179506598257245826324813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12581403714743955480798005 1179506598257245826324813)
                ·
                  refine ⟨442314974346467184871805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179506598257245826324813 442314974346467184871805)
                  ·
                    rfl

theorem cell21_1938162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1938162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938162 prefixEnd_1938162 := by exact prefixLift 1938162
  have htrace : WordTrace (prefixWord ++ tailWord_1938162) baseStart_1938162 baseEnd_1938162 := by
    simpa [prefixWord, tailWord_1938162, baseEnd_1938162] using wordTrace_append hprefix tailTrace_1938162
  have hstable : (prefixWord ++ tailWord_1938162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938162).length < 2 ^ (prefixWord ++ tailWord_1938162).sum := by decide
  have hdescent : baseEnd_1938162 < baseStart_1938162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938173 : List Nat := [1, 4, 1, 1, 1, 1, 12]
def baseStart_1938173 : Nat := 118140960795 + 1938173 * 2 ^ 59
def prefixEnd_1938173 : Nat := 4983230072969 + 3 ^ 40 * 1938173 * 2
def baseEnd_1938173 : Nat := 49146387188481512243161

theorem tailTrace_1938173 : CollatzResearch.WordTrace tailWord_1938173 prefixEnd_1938173 49146387188481512243161 := by
  unfold tailWord_1938173
  simp only [CollatzResearch.WordTrace]
  refine ⟨70690976807337709440171173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47127317871558472960114115 70690976807337709440171173)
  ·
    refine ⟨13254558151375820520032095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70690976807337709440171173 13254558151375820520032095)
    ·
      refine ⟨19881837227063730780048143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13254558151375820520032095 19881837227063730780048143)
      ·
        refine ⟨29822755840595596170072215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19881837227063730780048143 29822755840595596170072215)
        ·
          refine ⟨44734133760893394255108323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29822755840595596170072215 44734133760893394255108323)
          ·
            refine ⟨67101200641340091382662485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44734133760893394255108323 67101200641340091382662485)
            ·
              refine ⟨49146387188481512243161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67101200641340091382662485 49146387188481512243161)
              ·
                rfl

theorem cell21_1938173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 12].length) (baseStart_1938173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938173 prefixEnd_1938173 := by exact prefixLift 1938173
  have htrace : WordTrace (prefixWord ++ tailWord_1938173) baseStart_1938173 baseEnd_1938173 := by
    simpa [prefixWord, tailWord_1938173, baseEnd_1938173] using wordTrace_append hprefix tailTrace_1938173
  have hstable : (prefixWord ++ tailWord_1938173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938173).length < 2 ^ (prefixWord ++ tailWord_1938173).sum := by decide
  have hdescent : baseEnd_1938173 < baseStart_1938173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938207 : List Nat := [1, 1, 2, 4, 2, 4, 2, 5]
def baseStart_1938207 : Nat := 118140960795 + 1938207 * 2 ^ 59
def prefixEnd_1938207 : Nat := 4983230072969 + 3 ^ 40 * 1938207 * 2
def baseEnd_1938207 : Nat := 147441747986519035540571

theorem tailTrace_1938207 : CollatzResearch.WordTrace tailWord_1938207 prefixEnd_1938207 147441747986519035540571 := by
  unfold tailWord_1938207
  simp only [CollatzResearch.WordTrace]
  refine ⟨70692216889214533246908875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47128144592809688831272583 70692216889214533246908875)
  ·
    refine ⟨106038325333821799870363313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70692216889214533246908875 106038325333821799870363313)
    ·
      refine ⟨79528744000366349902772485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106038325333821799870363313 79528744000366349902772485)
      ·
        refine ⟨14911639500068690606769841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79528744000366349902772485 14911639500068690606769841)
        ·
          refine ⟨11183729625051517955077381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14911639500068690606769841 11183729625051517955077381)
          ·
            refine ⟨2096949304697159616577009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11183729625051517955077381 2096949304697159616577009)
            ·
              refine ⟨1572711978522869712432757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096949304697159616577009 1572711978522869712432757)
              ·
                refine ⟨147441747986519035540571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1572711978522869712432757 147441747986519035540571)
                ·
                  rfl

theorem cell21_1938207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 5].length) (baseStart_1938207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938207 prefixEnd_1938207 := by exact prefixLift 1938207
  have htrace : WordTrace (prefixWord ++ tailWord_1938207) baseStart_1938207 baseEnd_1938207 := by
    simpa [prefixWord, tailWord_1938207, baseEnd_1938207] using wordTrace_append hprefix tailTrace_1938207
  have hstable : (prefixWord ++ tailWord_1938207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938207).length < 2 ^ (prefixWord ++ tailWord_1938207).sum := by decide
  have hdescent : baseEnd_1938207 < baseStart_1938207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938244 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_1938244 : Nat := 118140960795 + 1938244 * 2 ^ 59
def prefixEnd_1938244 : Nat := 4983230072969 + 3 ^ 40 * 1938244 * 2
def baseEnd_1938244 : Nat := 442333687863653264504971

theorem tailTrace_1938244 : CollatzResearch.WordTrace tailWord_1938244 prefixEnd_1938244 442333687863653264504971 := by
  unfold tailWord_1938244
  simp only [CollatzResearch.WordTrace]
  refine ⟨35346783195040244283002893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47129044260053659044003857 35346783195040244283002893)
  ·
    refine ⟨13255043698140091606126085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35346783195040244283002893 13255043698140091606126085)
    ·
      refine ⟨2485320693401267176148641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13255043698140091606126085 2485320693401267176148641)
      ·
        refine ⟨1863990520050950382111481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2485320693401267176148641 1863990520050950382111481)
        ·
          refine ⟨1397992890038212786583611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863990520050950382111481 1397992890038212786583611)
          ·
            refine ⟨2096989335057319179875417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397992890038212786583611 2096989335057319179875417)
            ·
              refine ⟨1572742001292989384906563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096989335057319179875417 1572742001292989384906563)
              ·
                refine ⟨2359113001939484077359845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572742001292989384906563 2359113001939484077359845)
                ·
                  refine ⟨442333687863653264504971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359113001939484077359845 442333687863653264504971)
                  ·
                    rfl

theorem cell21_1938244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_1938244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938244 prefixEnd_1938244 := by exact prefixLift 1938244
  have htrace : WordTrace (prefixWord ++ tailWord_1938244) baseStart_1938244 baseEnd_1938244 := by
    simpa [prefixWord, tailWord_1938244, baseEnd_1938244] using wordTrace_append hprefix tailTrace_1938244
  have hstable : (prefixWord ++ tailWord_1938244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938244).length < 2 ^ (prefixWord ++ tailWord_1938244).sum := by decide
  have hdescent : baseEnd_1938244 < baseStart_1938244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938249 : List Nat := [1, 2, 1, 1, 2, 5, 1, 8]
def baseStart_1938249 : Nat := 118140960795 + 1938249 * 2 ^ 59
def prefixEnd_1938249 : Nat := 4983230072969 + 3 ^ 40 * 1938249 * 2
def baseEnd_1938249 : Nat := 147444942977258122307209

theorem tailTrace_1938249 : CollatzResearch.WordTrace tailWord_1938249 prefixEnd_1938249 147444942977258122307209 := by
  unfold tailWord_1938249
  simp only [CollatzResearch.WordTrace]
  refine ⟨70693748755062374419937801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47129165836708249613291867 70693748755062374419937801)
  ·
    refine ⟨53020311566296780814953351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70693748755062374419937801 53020311566296780814953351)
    ·
      refine ⟨79530467349445171222430027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53020311566296780814953351 79530467349445171222430027)
      ·
        refine ⟨119295701024167756833645041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79530467349445171222430027 119295701024167756833645041)
        ·
          refine ⟨89471775768125817625233781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119295701024167756833645041 89471775768125817625233781)
          ·
            refine ⟨8387978978261795402365667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89471775768125817625233781 8387978978261795402365667)
            ·
              refine ⟨12581968467392693103548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387978978261795402365667 12581968467392693103548501)
              ·
                refine ⟨147444942977258122307209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12581968467392693103548501 147444942977258122307209)
                ·
                  rfl

theorem cell21_1938249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_1938249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938249 prefixEnd_1938249 := by exact prefixLift 1938249
  have htrace : WordTrace (prefixWord ++ tailWord_1938249) baseStart_1938249 baseEnd_1938249 := by
    simpa [prefixWord, tailWord_1938249, baseEnd_1938249] using wordTrace_append hprefix tailTrace_1938249
  have hstable : (prefixWord ++ tailWord_1938249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938249).length < 2 ^ (prefixWord ++ tailWord_1938249).sum := by decide
  have hdescent : baseEnd_1938249 < baseStart_1938249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938252 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1938252 : Nat := 118140960795 + 1938252 * 2 ^ 59
def prefixEnd_1938252 : Nat := 4983230072969 + 3 ^ 40 * 1938252 * 2
def baseEnd_1938252 : Nat := 442335513572647028371621

theorem tailTrace_1938252 : CollatzResearch.WordTrace tailWord_1938252 prefixEnd_1938252 442335513572647028371621 := by
  unfold tailWord_1938252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35346929087025752966148505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47129238782701003954864673 35346929087025752966148505)
  ·
    refine ⟨26510196815269314724611379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35346929087025752966148505 26510196815269314724611379)
    ·
      refine ⟨39765295222903972086917069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26510196815269314724611379 39765295222903972086917069)
      ·
        refine ⟨14911985708588989532593901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39765295222903972086917069 14911985708588989532593901)
        ·
          refine ⟨5591994640720871074722713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14911985708588989532593901 5591994640720871074722713)
          ·
            refine ⟨4193995980540653306042035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591994640720871074722713 4193995980540653306042035)
            ·
              refine ⟨6290993970810979959063053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193995980540653306042035 6290993970810979959063053)
              ·
                refine ⟨2359122739054117484648645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6290993970810979959063053 2359122739054117484648645)
                ·
                  refine ⟨442335513572647028371621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359122739054117484648645 442335513572647028371621)
                  ·
                    rfl

theorem cell21_1938252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1938252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938252 prefixEnd_1938252 := by exact prefixLift 1938252
  have htrace : WordTrace (prefixWord ++ tailWord_1938252) baseStart_1938252 baseEnd_1938252 := by
    simpa [prefixWord, tailWord_1938252, baseEnd_1938252] using wordTrace_append hprefix tailTrace_1938252
  have hstable : (prefixWord ++ tailWord_1938252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938252).length < 2 ^ (prefixWord ++ tailWord_1938252).sum := by decide
  have hdescent : baseEnd_1938252 < baseStart_1938252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938376 : List Nat := [2, 1, 3, 1, 6, 1, 2, 5]
def baseStart_1938376 : Nat := 118140960795 + 1938376 * 2 ^ 59
def prefixEnd_1938376 : Nat := 4983230072969 + 3 ^ 40 * 1938376 * 2
def baseEnd_1938376 : Nat := 147454604020683456101567

theorem tailTrace_1938376 : CollatzResearch.WordTrace tailWord_1938376 prefixEnd_1938376 147454604020683456101567 := by
  unfold tailWord_1938376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35349190412801137554905491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47132253883734850073207321 35349190412801137554905491)
  ·
    refine ⟨53023785619201706332358237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35349190412801137554905491 53023785619201706332358237)
    ·
      refine ⟨19883919607200639874634339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53023785619201706332358237 19883919607200639874634339)
      ·
        refine ⟨29825879410800959811951509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883919607200639874634339 29825879410800959811951509)
        ·
          refine ⟨1398088097381294991185227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29825879410800959811951509 1398088097381294991185227)
          ·
            refine ⟨2097132146071942486777841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398088097381294991185227 2097132146071942486777841)
            ·
              refine ⟨1572849109553956865083381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097132146071942486777841 1572849109553956865083381)
              ·
                refine ⟨147454604020683456101567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1572849109553956865083381 147454604020683456101567)
                ·
                  rfl

theorem cell21_1938376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_1938376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938376 prefixEnd_1938376 := by exact prefixLift 1938376
  have htrace : WordTrace (prefixWord ++ tailWord_1938376) baseStart_1938376 baseEnd_1938376 := by
    simpa [prefixWord, tailWord_1938376, baseEnd_1938376] using wordTrace_append hprefix tailTrace_1938376
  have hstable : (prefixWord ++ tailWord_1938376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938376).length < 2 ^ (prefixWord ++ tailWord_1938376).sum := by decide
  have hdescent : baseEnd_1938376 < baseStart_1938376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938407 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 3]
def baseStart_1938407 : Nat := 118140960795 + 1938407 * 2 ^ 59
def prefixEnd_1938407 : Nat := 4983230072969 + 3 ^ 40 * 1938407 * 2
def baseEnd_1938407 : Nat := 442370886684401203287971

theorem tailTrace_1938407 : CollatzResearch.WordTrace tailWord_1938407 prefixEnd_1938407 442370886684401203287971 := by
  unfold tailWord_1938407
  simp only [CollatzResearch.WordTrace]
  refine ⟨70699511488489967404189475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47133007658993311602792983 70699511488489967404189475)
  ·
    refine ⟨106049267232734951106284213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70699511488489967404189475 106049267232734951106284213)
    ·
      refine ⟨9942118803068901666214145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106049267232734951106284213 9942118803068901666214145)
      ·
        refine ⟨7456589102301676249660609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942118803068901666214145 7456589102301676249660609)
        ·
          refine ⟨5592441826726257187245457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456589102301676249660609 5592441826726257187245457)
          ·
            refine ⟨4194331370044692890434093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5592441826726257187245457 4194331370044692890434093)
            ·
              refine ⟨1572874263766759833912785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4194331370044692890434093 1572874263766759833912785)
              ·
                refine ⟨1179655697825069875434589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572874263766759833912785 1179655697825069875434589)
                ·
                  refine ⟨442370886684401203287971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179655697825069875434589 442370886684401203287971)
                  ·
                    rfl

theorem cell21_1938407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3].length) (baseStart_1938407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938407 prefixEnd_1938407 := by exact prefixLift 1938407
  have htrace : WordTrace (prefixWord ++ tailWord_1938407) baseStart_1938407 baseEnd_1938407 := by
    simpa [prefixWord, tailWord_1938407, baseEnd_1938407] using wordTrace_append hprefix tailTrace_1938407
  have hstable : (prefixWord ++ tailWord_1938407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938407).length < 2 ^ (prefixWord ++ tailWord_1938407).sum := by decide
  have hdescent : baseEnd_1938407 < baseStart_1938407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938463 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_1938463 : Nat := 118140960795 + 1938463 * 2 ^ 59
def prefixEnd_1938463 : Nat := 4983230072969 + 3 ^ 40 * 1938463 * 2
def baseEnd_1938463 : Nat := 442383666647357550354523

theorem tailTrace_1938463 : CollatzResearch.WordTrace tailWord_1938463 prefixEnd_1938463 442383666647357550354523 := by
  unfold tailWord_1938463
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701553976287088968228043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47134369317524725978818695 70701553976287088968228043)
  ·
    refine ⟨106052330964430633452342065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70701553976287088968228043 106052330964430633452342065)
    ·
      refine ⟨79539248223322975089256549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106052330964430633452342065 79539248223322975089256549)
      ·
        refine ⟨14913609041873057829235603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79539248223322975089256549 14913609041873057829235603)
        ·
          refine ⟨22370413562809586743853405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14913609041873057829235603 22370413562809586743853405)
          ·
            refine ⟨8388905086053595028945027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22370413562809586743853405 8388905086053595028945027)
            ·
              refine ⟨12583357629080392543417541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388905086053595028945027 12583357629080392543417541)
              ·
                refine ⟨2359379555452573601890789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12583357629080392543417541 2359379555452573601890789)
                ·
                  refine ⟨442383666647357550354523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359379555452573601890789 442383666647357550354523)
                  ·
                    rfl

theorem cell21_1938463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_1938463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938463 prefixEnd_1938463 := by exact prefixLift 1938463
  have htrace : WordTrace (prefixWord ++ tailWord_1938463) baseStart_1938463 baseEnd_1938463 := by
    simpa [prefixWord, tailWord_1938463, baseEnd_1938463] using wordTrace_append hprefix tailTrace_1938463
  have hstable : (prefixWord ++ tailWord_1938463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938463).length < 2 ^ (prefixWord ++ tailWord_1938463).sum := by decide
  have hdescent : baseEnd_1938463 < baseStart_1938463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938466 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1938466 : Nat := 118140960795 + 1938466 * 2 ^ 59
def prefixEnd_1938466 : Nat := 4983230072969 + 3 ^ 40 * 1938466 * 2
def baseEnd_1938466 : Nat := 442384351288230211804517

theorem tailTrace_1938466 : CollatzResearch.WordTrace tailWord_1938466 prefixEnd_1938466 442384351288230211804517 := by
  unfold tailWord_1938466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17675415848819055120146813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47134442263517480320391501 17675415848819055120146813)
  ·
    refine ⟨6628280943307145670055055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17675415848819055120146813 6628280943307145670055055)
    ·
      refine ⟨9942421414960718505082583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628280943307145670055055 9942421414960718505082583)
      ·
        refine ⟨14913632122441077757623875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942421414960718505082583 14913632122441077757623875)
        ·
          refine ⟨22370448183661616636435813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14913632122441077757623875 22370448183661616636435813)
          ·
            refine ⟨4194459034436553119331715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22370448183661616636435813 4194459034436553119331715)
            ·
              refine ⟨6291688551654829678997573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194459034436553119331715 6291688551654829678997573)
              ·
                refine ⟨1179691603435280564812045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6291688551654829678997573 1179691603435280564812045)
                ·
                  refine ⟨442384351288230211804517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179691603435280564812045 442384351288230211804517)
                  ·
                    rfl

theorem cell21_1938466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1938466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938466 prefixEnd_1938466 := by exact prefixLift 1938466
  have htrace : WordTrace (prefixWord ++ tailWord_1938466) baseStart_1938466 baseEnd_1938466 := by
    simpa [prefixWord, tailWord_1938466, baseEnd_1938466] using wordTrace_append hprefix tailTrace_1938466
  have hstable : (prefixWord ++ tailWord_1938466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938466).length < 2 ^ (prefixWord ++ tailWord_1938466).sum := by decide
  have hdescent : baseEnd_1938466 < baseStart_1938466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938590 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1938590 : Nat := 118140960795 + 1938590 * 2 ^ 59
def prefixEnd_1938590 : Nat := 4983230072969 + 3 ^ 40 * 1938590 * 2
def baseEnd_1938590 : Nat := 442412649777633551737597

theorem tailTrace_1938590 : CollatzResearch.WordTrace tailWord_1938590 prefixEnd_1938590 442412649777633551737597 := by
  unfold tailWord_1938590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838273255853373707262653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47137457364551326438734149 8838273255853373707262653)
  ·
    refine ⟨3314352470945015140223495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8838273255853373707262653 3314352470945015140223495)
    ·
      refine ⟨4971528706417522710335243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3314352470945015140223495 4971528706417522710335243)
      ·
        refine ⟨7457293059626284065502865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971528706417522710335243 7457293059626284065502865)
        ·
          refine ⟨5592969794719713049127149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7457293059626284065502865 5592969794719713049127149)
          ·
            refine ⟨2097363673019892393422681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5592969794719713049127149 2097363673019892393422681)
            ·
              refine ⟨1573022754764919295067011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097363673019892393422681 1573022754764919295067011)
              ·
                refine ⟨2359534132147378942600517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573022754764919295067011 2359534132147378942600517)
                ·
                  refine ⟨442412649777633551737597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359534132147378942600517 442412649777633551737597)
                  ·
                    rfl

theorem cell21_1938590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1938590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938590 prefixEnd_1938590 := by exact prefixLift 1938590
  have htrace : WordTrace (prefixWord ++ tailWord_1938590) baseStart_1938590 baseEnd_1938590 := by
    simpa [prefixWord, tailWord_1938590, baseEnd_1938590] using wordTrace_append hprefix tailTrace_1938590
  have hstable : (prefixWord ++ tailWord_1938590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938590).length < 2 ^ (prefixWord ++ tailWord_1938590).sum := by decide
  have hdescent : baseEnd_1938590 < baseStart_1938590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938663 : List Nat := [1, 1, 5, 3, 2, 1, 3, 5]
def baseStart_1938663 : Nat := 118140960795 + 1938663 * 2 ^ 59
def prefixEnd_1938663 : Nat := 4983230072969 + 3 ^ 40 * 1938663 * 2
def baseEnd_1938663 : Nat := 147476436457400549006927

theorem tailTrace_1938663 : CollatzResearch.WordTrace tailWord_1938663 prefixEnd_1938663 147476436457400549006927 := by
  unfold tailWord_1938663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70708848575562523125508643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47139232383708348750339095 70708848575562523125508643)
  ·
    refine ⟨106063272863343784688262965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70708848575562523125508643 106063272863343784688262965)
    ·
      refine ⟨9943431830938479814524653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106063272863343784688262965 9943431830938479814524653)
      ·
        refine ⟨3728786936601929930446745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9943431830938479814524653 3728786936601929930446745)
        ·
          refine ⟨2796590202451447447835059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3728786936601929930446745 2796590202451447447835059)
          ·
            refine ⟨4194885303677171171752589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796590202451447447835059 4194885303677171171752589)
            ·
              refine ⟨1573081988878939189407221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4194885303677171171752589 1573081988878939189407221)
              ·
                refine ⟨147476436457400549006927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1573081988878939189407221 147476436457400549006927)
                ·
                  rfl

theorem cell21_1938663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 5].length) (baseStart_1938663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938663 prefixEnd_1938663 := by exact prefixLift 1938663
  have htrace : WordTrace (prefixWord ++ tailWord_1938663) baseStart_1938663 baseEnd_1938663 := by
    simpa [prefixWord, tailWord_1938663, baseEnd_1938663] using wordTrace_append hprefix tailTrace_1938663
  have hstable : (prefixWord ++ tailWord_1938663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938663).length < 2 ^ (prefixWord ++ tailWord_1938663).sum := by decide
  have hdescent : baseEnd_1938663 < baseStart_1938663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938691 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_1938691 : Nat := 118140960795 + 1938691 * 2 ^ 59
def prefixEnd_1938691 : Nat := 4983230072969 + 3 ^ 40 * 1938691 * 2
def baseEnd_1938691 : Nat := 442435699353679820554057

theorem tailTrace_1938691 : CollatzResearch.WordTrace tailWord_1938691 prefixEnd_1938691 442435699353679820554057 := by
  unfold tailWord_1938691
  simp only [CollatzResearch.WordTrace]
  refine ⟨70709869819461083907527927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47139913212974055938351951 70709869819461083907527927)
  ·
    refine ⟨106064804729191625861291891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70709869819461083907527927 106064804729191625861291891)
    ·
      refine ⟨159097207093787438791937837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106064804729191625861291891 159097207093787438791937837)
      ·
        refine ⟨59661452660170289546976689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159097207093787438791937837 59661452660170289546976689)
        ·
          refine ⟨44746089495127717160232517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59661452660170289546976689 44746089495127717160232517)
          ·
            refine ⟨8389891780336446967543597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44746089495127717160232517 8389891780336446967543597)
            ·
              refine ⟨3146209417626167612828849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8389891780336446967543597 3146209417626167612828849)
              ·
                refine ⟨2359657063219625709621637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146209417626167612828849 2359657063219625709621637)
                ·
                  refine ⟨442435699353679820554057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359657063219625709621637 442435699353679820554057)
                  ·
                    rfl

theorem cell21_1938691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_1938691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938691 prefixEnd_1938691 := by exact prefixLift 1938691
  have htrace : WordTrace (prefixWord ++ tailWord_1938691) baseStart_1938691 baseEnd_1938691 := by
    simpa [prefixWord, tailWord_1938691, baseEnd_1938691] using wordTrace_append hprefix tailTrace_1938691
  have hstable : (prefixWord ++ tailWord_1938691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938691).length < 2 ^ (prefixWord ++ tailWord_1938691).sum := by decide
  have hdescent : baseEnd_1938691 < baseStart_1938691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938722 : List Nat := [3, 3, 1, 1, 4, 1, 1, 7]
def baseStart_1938722 : Nat := 118140960795 + 1938722 * 2 ^ 59
def prefixEnd_1938722 : Nat := 4983230072969 + 3 ^ 40 * 1938722 * 2
def baseEnd_1938722 : Nat := 147480924658676885179109

theorem tailTrace_1938722 : CollatzResearch.WordTrace tailWord_1938722 prefixEnd_1938722 147480924658676885179109 := by
  unfold tailWord_1938722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677750120587194050476605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47140666988232517467937613 17677750120587194050476605)
  ·
    refine ⟨6629156295220197768928727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17677750120587194050476605 6629156295220197768928727)
    ·
      refine ⟨9943734442830296653393091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629156295220197768928727 9943734442830296653393091)
      ·
        refine ⟨14915601664245444980089637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943734442830296653393091 14915601664245444980089637)
        ·
          refine ⟨2796675312046020933766807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14915601664245444980089637 2796675312046020933766807)
          ·
            refine ⟨4195012968069031400650211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796675312046020933766807 4195012968069031400650211)
            ·
              refine ⟨6292519452103547100975317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195012968069031400650211 6292519452103547100975317)
              ·
                refine ⟨147480924658676885179109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6292519452103547100975317 147480924658676885179109)
                ·
                  rfl

theorem cell21_1938722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_1938722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938722 prefixEnd_1938722 := by exact prefixLift 1938722
  have htrace : WordTrace (prefixWord ++ tailWord_1938722) baseStart_1938722 baseEnd_1938722 := by
    simpa [prefixWord, tailWord_1938722, baseEnd_1938722] using wordTrace_append hprefix tailTrace_1938722
  have hstable : (prefixWord ++ tailWord_1938722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938722).length < 2 ^ (prefixWord ++ tailWord_1938722).sum := by decide
  have hdescent : baseEnd_1938722 < baseStart_1938722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938753 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 5]
def baseStart_1938753 : Nat := 118140960795 + 1938753 * 2 ^ 59
def prefixEnd_1938753 : Nat := 4983230072969 + 3 ^ 40 * 1938753 * 2
def baseEnd_1938753 : Nat := 442449848598381490520597

theorem tailTrace_1938753 : CollatzResearch.WordTrace tailWord_1938753 prefixEnd_1938753 442449848598381490520597 := by
  unfold tailWord_1938753
  simp only [CollatzResearch.WordTrace]
  refine ⟨70712131145236468496284913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47141420763490978997523275 70712131145236468496284913)
  ·
    refine ⟨53034098358927351372213685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70712131145236468496284913 53034098358927351372213685)
    ·
      refine ⟨4971946721149439191145033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53034098358927351372213685 4971946721149439191145033)
      ·
        refine ⟨3728960040862079393358775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4971946721149439191145033 3728960040862079393358775)
        ·
          refine ⟨5593440061293119090038163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728960040862079393358775 5593440061293119090038163)
          ·
            refine ⟨8390160091939678635057245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593440061293119090038163 8390160091939678635057245)
            ·
              refine ⟨3146310034477379488146467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8390160091939678635057245 3146310034477379488146467)
              ·
                refine ⟨4719465051716069232219701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146310034477379488146467 4719465051716069232219701)
                ·
                  refine ⟨442449848598381490520597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4719465051716069232219701 442449848598381490520597)
                  ·
                    rfl

theorem cell21_1938753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_1938753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938753 prefixEnd_1938753 := by exact prefixLift 1938753
  have htrace : WordTrace (prefixWord ++ tailWord_1938753) baseStart_1938753 baseEnd_1938753 := by
    simpa [prefixWord, tailWord_1938753, baseEnd_1938753] using wordTrace_append hprefix tailTrace_1938753
  have hstable : (prefixWord ++ tailWord_1938753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938753).length < 2 ^ (prefixWord ++ tailWord_1938753).sum := by decide
  have hdescent : baseEnd_1938753 < baseStart_1938753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938798 : List Nat := [4, 1, 2, 4, 1, 9]
def baseStart_1938798 : Nat := 118140960795 + 1938798 * 2 ^ 59
def prefixEnd_1938798 : Nat := 4983230072969 + 3 ^ 40 * 1938798 * 2
def baseEnd_1938798 : Nat := 16387411785610052306315

theorem tailTrace_1938798 : CollatzResearch.WordTrace tailWord_1938798 prefixEnd_1938798 16387411785610052306315 := by
  unfold tailWord_1938798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839221553759180147709131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47142514953382294121115365 8839221553759180147709131)
  ·
    refine ⟨13258832330638770221563697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839221553759180147709131 13258832330638770221563697)
    ·
      refine ⟨9944124247979077666172773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13258832330638770221563697 9944124247979077666172773)
      ·
        refine ⟨1864523296496077062407395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9944124247979077666172773 1864523296496077062407395)
        ·
          refine ⟨2796784944744115593611093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864523296496077062407395 2796784944744115593611093)
          ·
            refine ⟨16387411785610052306315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2796784944744115593611093 16387411785610052306315)
            ·
              rfl

theorem cell21_1938798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 9].length) (baseStart_1938798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938798 prefixEnd_1938798 := by exact prefixLift 1938798
  have htrace : WordTrace (prefixWord ++ tailWord_1938798) baseStart_1938798 baseEnd_1938798 := by
    simpa [prefixWord, tailWord_1938798, baseEnd_1938798] using wordTrace_append hprefix tailTrace_1938798
  have hstable : (prefixWord ++ tailWord_1938798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938798).length < 2 ^ (prefixWord ++ tailWord_1938798).sum := by decide
  have hdescent : baseEnd_1938798 < baseStart_1938798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938905 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 3]
def baseStart_1938905 : Nat := 118140960795 + 1938905 * 2 ^ 59
def prefixEnd_1938905 : Nat := 4983230072969 + 3 ^ 40 * 1938905 * 2
def baseEnd_1938905 : Nat := 442484537069263003986953

theorem tailTrace_1938905 : CollatzResearch.WordTrace tailWord_1938905 prefixEnd_1938905 442484537069263003986953 := by
  unfold tailWord_1938905
  simp only [CollatzResearch.WordTrace]
  refine ⟨70717675040685798455818169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47145116693790532303878779 70717675040685798455818169)
  ·
    refine ⟨53038256280514348841863627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70717675040685798455818169 53038256280514348841863627)
    ·
      refine ⟨79557384420771523262795441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53038256280514348841863627 79557384420771523262795441)
      ·
        refine ⟨59668038315578642447096581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79557384420771523262795441 59668038315578642447096581)
        ·
          refine ⟨11187757184170995458830609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59668038315578642447096581 11187757184170995458830609)
          ·
            refine ⟨8390817888128246594122957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11187757184170995458830609 8390817888128246594122957)
            ·
              refine ⟨3146556708048092472796109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8390817888128246594122957 3146556708048092472796109)
              ·
                refine ⟨1179958765518034677298541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3146556708048092472796109 1179958765518034677298541)
                ·
                  refine ⟨442484537069263003986953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1179958765518034677298541 442484537069263003986953)
                  ·
                    rfl

theorem cell21_1938905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_1938905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938905 prefixEnd_1938905 := by exact prefixLift 1938905
  have htrace : WordTrace (prefixWord ++ tailWord_1938905) baseStart_1938905 baseEnd_1938905 := by
    simpa [prefixWord, tailWord_1938905, baseEnd_1938905] using wordTrace_append hprefix tailTrace_1938905
  have hstable : (prefixWord ++ tailWord_1938905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938905).length < 2 ^ (prefixWord ++ tailWord_1938905).sum := by decide
  have hdescent : baseEnd_1938905 < baseStart_1938905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938922 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_1938922 : Nat := 118140960795 + 1938922 * 2 ^ 59
def prefixEnd_1938922 : Nat := 4983230072969 + 3 ^ 40 * 1938922 * 2
def baseEnd_1938922 : Nat := 442488416700874752203585

theorem tailTrace_1938922 : CollatzResearch.WordTrace tailWord_1938922 prefixEnd_1938922 442488416700874752203585 := by
  unfold tailWord_1938922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679573770406052589796755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47145530054416140239458013 17679573770406052589796755)
  ·
    refine ⟨26519360655609078884695133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17679573770406052589796755 26519360655609078884695133)
    ·
      refine ⟨9944760245853404581760675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26519360655609078884695133 9944760245853404581760675)
      ·
        refine ⟨14917140368780106872641013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944760245853404581760675 14917140368780106872641013)
        ·
          refine ⟨1398481909573135019310095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14917140368780106872641013 1398481909573135019310095)
          ·
            refine ⟨2097722864359702528965143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398481909573135019310095 2097722864359702528965143)
            ·
              refine ⟨3146584296539553793447715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097722864359702528965143 3146584296539553793447715)
              ·
                refine ⟨4719876444809330690171573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146584296539553793447715 4719876444809330690171573)
                ·
                  refine ⟨442488416700874752203585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4719876444809330690171573 442488416700874752203585)
                  ·
                    rfl

theorem cell21_1938922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_1938922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938922 prefixEnd_1938922 := by exact prefixLift 1938922
  have htrace : WordTrace (prefixWord ++ tailWord_1938922) baseStart_1938922 baseEnd_1938922 := by
    simpa [prefixWord, tailWord_1938922, baseEnd_1938922] using wordTrace_append hprefix tailTrace_1938922
  have hstable : (prefixWord ++ tailWord_1938922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938922).length < 2 ^ (prefixWord ++ tailWord_1938922).sum := by decide
  have hdescent : baseEnd_1938922 < baseStart_1938922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938936 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_1938936 : Nat := 118140960795 + 1938936 * 2 ^ 59
def prefixEnd_1938936 : Nat := 4983230072969 + 3 ^ 40 * 1938936 * 2
def baseEnd_1938936 : Nat := 442491611691613838970223

theorem tailTrace_1938936 : CollatzResearch.WordTrace tailWord_1938936 prefixEnd_1938936 442491611691613838970223 := by
  unfold tailWord_1938936
  simp only [CollatzResearch.WordTrace]
  refine ⟨35359402851786745375098331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47145870469048993833464441 35359402851786745375098331)
  ·
    refine ⟨53039104277680118062647497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35359402851786745375098331 53039104277680118062647497)
    ·
      refine ⟨39779328208260088546985623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53039104277680118062647497 39779328208260088546985623)
      ·
        refine ⟨59668992312390132820478435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39779328208260088546985623 59668992312390132820478435)
        ·
          refine ⟨89503488468585199230717653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59668992312390132820478435 89503488468585199230717653)
          ·
            refine ⟨2097738010982465606969945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89503488468585199230717653 2097738010982465606969945)
            ·
              refine ⟨1573303508236849205227459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097738010982465606969945 1573303508236849205227459)
              ·
                refine ⟨2359955262355273807841189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573303508236849205227459 2359955262355273807841189)
                ·
                  refine ⟨442491611691613838970223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359955262355273807841189 442491611691613838970223)
                  ·
                    rfl

theorem cell21_1938936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_1938936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938936 prefixEnd_1938936 := by exact prefixLift 1938936
  have htrace : WordTrace (prefixWord ++ tailWord_1938936) baseStart_1938936 baseEnd_1938936 := by
    simpa [prefixWord, tailWord_1938936, baseEnd_1938936] using wordTrace_append hprefix tailTrace_1938936
  have hstable : (prefixWord ++ tailWord_1938936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938936).length < 2 ^ (prefixWord ++ tailWord_1938936).sum := by decide
  have hdescent : baseEnd_1938936 < baseStart_1938936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938978 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1938978 : Nat := 118140960795 + 1938978 * 2 ^ 59
def prefixEnd_1938978 : Nat := 4983230072969 + 3 ^ 40 * 1938978 * 2
def baseEnd_1938978 : Nat := 442501196663831099270137

theorem tailTrace_1938978 : CollatzResearch.WordTrace tailWord_1938978 prefixEnd_1938978 442501196663831099270137 := by
  unfold tailWord_1938978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680084392355332980806397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47146891712947554615483725 17680084392355332980806397)
  ·
    refine ⟨6630031647133249867802399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17680084392355332980806397 6630031647133249867802399)
    ·
      refine ⟨9945047470699874801703599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630031647133249867802399 9945047470699874801703599)
      ·
        refine ⟨14917571206049812202555399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945047470699874801703599 14917571206049812202555399)
        ·
          refine ⟨22376356809074718303833099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917571206049812202555399 22376356809074718303833099)
          ·
            refine ⟨33564535213612077455749649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22376356809074718303833099 33564535213612077455749649)
            ·
              refine ⟨25173401410209058091812237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33564535213612077455749649 25173401410209058091812237)
              ·
                refine ⟨9440025528828396784429589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25173401410209058091812237 9440025528828396784429589)
                ·
                  refine ⟨442501196663831099270137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9440025528828396784429589 442501196663831099270137)
                  ·
                    rfl

theorem cell21_1938978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1938978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1938978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1938978 prefixEnd_1938978 := by exact prefixLift 1938978
  have htrace : WordTrace (prefixWord ++ tailWord_1938978) baseStart_1938978 baseEnd_1938978 := by
    simpa [prefixWord, tailWord_1938978, baseEnd_1938978] using wordTrace_append hprefix tailTrace_1938978
  have hstable : (prefixWord ++ tailWord_1938978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938978).length < 2 ^ (prefixWord ++ tailWord_1938978).sum := by decide
  have hdescent : baseEnd_1938978 < baseStart_1938978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939102 : List Nat := [4, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1939102 : Nat := 118140960795 + 1939102 * 2 ^ 59
def prefixEnd_1939102 : Nat := 4983230072969 + 3 ^ 40 * 1939102 * 2
def baseEnd_1939102 : Nat := 147509831717744813067739

theorem tailTrace_1939102 : CollatzResearch.WordTrace tailWord_1939102 prefixEnd_1939102 147509831717744813067739 := by
  unfold tailWord_1939102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840607527621512637592445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47149906813981400733826373 8840607527621512637592445)
  ·
    refine ⟨3315227822858067239097167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8840607527621512637592445 3315227822858067239097167)
    ·
      refine ⟨4972841734287100858645751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315227822858067239097167 4972841734287100858645751)
      ·
        refine ⟨7459262601430651287968627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972841734287100858645751 7459262601430651287968627)
        ·
          refine ⟨11188893902145976931952941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459262601430651287968627 11188893902145976931952941)
          ·
            refine ⟨4195835213304741349482353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11188893902145976931952941 4195835213304741349482353)
            ·
              refine ⟨3146876409978556012111765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195835213304741349482353 3146876409978556012111765)
              ·
                refine ⟨147509831717744813067739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3146876409978556012111765 147509831717744813067739)
                ·
                  rfl

theorem cell21_1939102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1939102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939102 prefixEnd_1939102 := by exact prefixLift 1939102
  have htrace : WordTrace (prefixWord ++ tailWord_1939102) baseStart_1939102 baseEnd_1939102 := by
    simpa [prefixWord, tailWord_1939102, baseEnd_1939102] using wordTrace_append hprefix tailTrace_1939102
  have hstable : (prefixWord ++ tailWord_1939102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939102).length < 2 ^ (prefixWord ++ tailWord_1939102).sum := by decide
  have hdescent : baseEnd_1939102 < baseStart_1939102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939161 : List Nat := [1, 2, 1, 2, 3, 5, 1, 6]
def baseStart_1939161 : Nat := 118140960795 + 1939161 * 2 ^ 59
def prefixEnd_1939161 : Nat := 4983230072969 + 3 ^ 40 * 1939161 * 2
def baseEnd_1939161 : Nat := 147514319919021149239921

theorem tailTrace_1939161 : CollatzResearch.WordTrace tailWord_1939161 prefixEnd_1939161 147514319919021149239921 := by
  unfold tailWord_1939161
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727012127758354177137337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47151341418505569451424891 70727012127758354177137337)
  ·
    refine ⟨53045259095818765632853003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70727012127758354177137337 53045259095818765632853003)
    ·
      refine ⟨79567888643728148449279505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53045259095818765632853003 79567888643728148449279505)
      ·
        refine ⟨59675916482796111336959629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79567888643728148449279505 59675916482796111336959629)
        ·
          refine ⟨22378468681048541751359861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59675916482796111336959629 22378468681048541751359861)
          ·
            refine ⟨2097981438848300789189987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22378468681048541751359861 2097981438848300789189987)
            ·
              refine ⟨3146972158272451183784981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097981438848300789189987 3146972158272451183784981)
              ·
                refine ⟨147514319919021149239921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3146972158272451183784981 147514319919021149239921)
                ·
                  rfl

theorem cell21_1939161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 6].length) (baseStart_1939161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939161 prefixEnd_1939161 := by exact prefixLift 1939161
  have htrace : WordTrace (prefixWord ++ tailWord_1939161) baseStart_1939161 baseEnd_1939161 := by
    simpa [prefixWord, tailWord_1939161, baseEnd_1939161] using wordTrace_append hprefix tailTrace_1939161
  have hstable : (prefixWord ++ tailWord_1939161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939161).length < 2 ^ (prefixWord ++ tailWord_1939161).sum := by decide
  have hdescent : baseEnd_1939161 < baseStart_1939161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939237 : List Nat := [1, 3, 1, 2, 3, 2, 4, 5]
def baseStart_1939237 : Nat := 118140960795 + 1939237 * 2 ^ 59
def prefixEnd_1939237 : Nat := 4983230072969 + 3 ^ 40 * 1939237 * 2
def baseEnd_1939237 : Nat := 147520101330834734817647

theorem tailTrace_1939237 : CollatzResearch.WordTrace tailWord_1939237 prefixEnd_1939237 147520101330834734817647 := by
  unfold tailWord_1939237
  simp only [CollatzResearch.WordTrace]
  refine ⟨70729784075483019156903965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47153189383655346104602643 70729784075483019156903965)
  ·
    refine ⟨26523669028306132183838987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70729784075483019156903965 26523669028306132183838987)
    ·
      refine ⟨39785503542459198275758481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26523669028306132183838987 39785503542459198275758481)
      ·
        refine ⟨29839127656844398706818861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39785503542459198275758481 29839127656844398706818861)
        ·
          refine ⟨11189672871316649515057073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29839127656844398706818861 11189672871316649515057073)
          ·
            refine ⟨8392254653487487136292805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11189672871316649515057073 8392254653487487136292805)
            ·
              refine ⟨1573547747528903838054901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8392254653487487136292805 1573547747528903838054901)
              ·
                refine ⟨147520101330834734817647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1573547747528903838054901 147520101330834734817647)
                ·
                  rfl

theorem cell21_1939237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 5].length) (baseStart_1939237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939237 prefixEnd_1939237 := by exact prefixLift 1939237
  have htrace : WordTrace (prefixWord ++ tailWord_1939237) baseStart_1939237 baseEnd_1939237 := by
    simpa [prefixWord, tailWord_1939237, baseEnd_1939237] using wordTrace_append hprefix tailTrace_1939237
  have hstable : (prefixWord ++ tailWord_1939237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939237).length < 2 ^ (prefixWord ++ tailWord_1939237).sum := by decide
  have hdescent : baseEnd_1939237 < baseStart_1939237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939254 : List Nat := [5, 1, 2, 2, 1, 3, 7]
def baseStart_1939254 : Nat := 118140960795 + 1939254 * 2 ^ 59
def prefixEnd_1939254 : Nat := 4983230072969 + 3 ^ 40 * 1939254 * 2
def baseEnd_1939254 : Nat := 49173798180457328074397

theorem tailTrace_1939254 : CollatzResearch.WordTrace tailWord_1939254 prefixEnd_1939254 49173798180457328074397 := by
  unfold tailWord_1939254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420650257276339441267051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47153602744280954040181877 4420650257276339441267051)
  ·
    refine ⟨6630975385914509161900577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4420650257276339441267051 6630975385914509161900577)
    ·
      refine ⟨4973231539435881871425433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6630975385914509161900577 4973231539435881871425433)
      ·
        refine ⟨3729923654576911403569075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4973231539435881871425433 3729923654576911403569075)
        ·
          refine ⟨5594885481865367105353613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729923654576911403569075 5594885481865367105353613)
          ·
            refine ⟨2098082055699512664507605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5594885481865367105353613 2098082055699512664507605)
            ·
              refine ⟨49173798180457328074397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2098082055699512664507605 49173798180457328074397)
              ·
                rfl

theorem cell21_1939254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 7].length) (baseStart_1939254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1939254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1939254 prefixEnd_1939254 := by exact prefixLift 1939254
  have htrace : WordTrace (prefixWord ++ tailWord_1939254) baseStart_1939254 baseEnd_1939254 := by
    simpa [prefixWord, tailWord_1939254, baseEnd_1939254] using wordTrace_append hprefix tailTrace_1939254
  have hstable : (prefixWord ++ tailWord_1939254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939254).length < 2 ^ (prefixWord ++ tailWord_1939254).sum := by decide
  have hdescent : baseEnd_1939254 < baseStart_1939254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
